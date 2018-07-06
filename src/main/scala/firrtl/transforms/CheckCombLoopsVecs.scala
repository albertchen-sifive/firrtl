// See LICENSE for license details.

package firrtl.transforms

import firrtl.Utils.BoolType
import firrtl._
import firrtl.analyses.InstanceGraph
import firrtl.graph.{DiGraph, MutableDiGraph}
import firrtl.ir._

import scala.collection.mutable

object CheckCombLoopsVecs {
  val fieldDelimiter = '.'

  case class CandidateVec(name: String, tpe: VectorType)(val hasDefault: Boolean) {
    def toNode: Node = Node(name, tpe)
  }

  case class Node(name: String, tpe: Type)

  object Node {
    def apply(expr: Expression): Node = {
      val first = getOuterVec(expr)
      Node(first.serialize, first.tpe)
    }

    private def fromExpr(expression: Expression, suffix: String = ""): Node = expression match {
      case WRef(name, tpe, _, _) => Node(name + suffix, tpe)
      case WSubField(expr, name, _, _) => fromExpr(expr, CheckCombLoopsVecs.fieldDelimiter + name)
      case WSubAccess(expr, _, _, _) => fromExpr(expr)
      case WSubIndex(expr, _, _, _) => fromExpr(expr)
    }
  }


  def getOuterVec(expr: Expression): Expression = {
    var curr = expr
    var firstVec = expr
    while (!curr.isInstanceOf[WRef]) {
      curr = curr match {
        case WSubField(bundle, _, _, _) => bundle
        case WSubAccess(vec, _, _, _) =>
          firstVec = vec
          vec
        case WSubIndex(vec, _, _, _) =>
          firstVec = vec
          vec
      }
    }
    firstVec
  }

  class NodeDigraph {
    private val diGraph = new MutableDiGraph[Node]
    def addDep(lhs: Node, rhs: Node): Unit = diGraph.addEdgeIfValid(lhs, rhs)
    def addDeps(lhs: Node, rhs: Seq[Node]): Unit = rhs.foreach(addDep(lhs, _))
    def addNode(connectable: Node): Unit = diGraph.addVertex(connectable)
    def toDigraph: DiGraph[Node] = DiGraph(diGraph)

    def getPortDigraph(ports: Set[Node]): NodeDigraph = {
      val simplifiedGraph = diGraph.simplify(ports)
      val result = new NodeDigraph
      val edges = simplifiedGraph.getEdgeMap
      edges.foreach { case (v, _) => result.addNode(v) }
      edges.foreach { case (v, us) => us.foreach(result.addDep(v, _)) }
      result
    }
/*
    def mergeDigraph(other: NodeDigraph): Unit = {
      val result = new NodeDigraph

      other.diGraph.transformNodes()
        val iGraph = simplifiedModules(i.module).transformNodes(n => n.copy(inst = Some(i.name)))
        iGraph.getVertices.foreach(deps.addVertex(_))
        iGraph.getVertices.foreach({ v => iGraph.getEdges(v).foreach { deps.addEdge(v,_) } })
    }
    */
  }

  private class Scoreboard {
    private val vecNodes = new mutable.HashMap[CandidateVec, mutable.ArraySeq[Boolean]]()

    def printNodes(): Unit = println(vecNodes)

    def addCandidate(candidate: CandidateVec): Unit = {
      if (candidate.hasDefault) {
        vecNodes.put(candidate, new mutable.ArraySeq[Boolean](0))
      } else {
        val VectorType(BoolType, size) = candidate.tpe
        val scoreboard = new mutable.ArraySeq[Boolean](size)
        (0 until size).foreach(scoreboard(_) = false)
        vecNodes.put(candidate, scoreboard)
      }
    }

    def markScoreboard(candidate: CandidateVec, index: Int): Unit = {
      if (vecNodes.contains(candidate) && vecNodes(candidate).nonEmpty) {
        vecNodes(candidate)(index) = true
      }
    }

    def getValidCandidates(): Set[CandidateVec] = {
      vecNodes.collect { case (candidate, score) if score.forall(b => b) => candidate }(collection.breakOut)
    }

    def makeConditionalScoreboard(): Scoreboard = {
      val clonedScoreboard = new Scoreboard
      clonedScoreboard.vecNodes ++= vecNodes
      vecNodes.foreach { case (c, _) =>
        val score = clonedScoreboard.vecNodes(c)
        score.indices.foreach(score(_) = false)
      }
      clonedScoreboard
    }

    def mergeConditionalScoreboards(conseqScoreboard: Scoreboard, altScoreboard: Scoreboard): Unit = {
      val conseqVecs = conseqScoreboard.vecNodes
      val altVecs = altScoreboard.vecNodes

      val currentKeys = vecNodes.keySet
      (conseqVecs.keySet &~ currentKeys).foreach(key => vecNodes += key -> conseqVecs(key))
      (altVecs.keySet &~ currentKeys).foreach(key => vecNodes += key -> altVecs(key))

      for (k <- currentKeys) {
        vecNodes(k).indices.foreach(i => vecNodes(k)(i) |= conseqVecs(k)(i) && altVecs(k)(i))
      }
    }
  }

  private def getStmtDeps(deps: NodeDigraph,
                          scoreboard: Scoreboard,
                          portMap: Map[String, NodeDigraph],
                          conds: Seq[Node])(s: Statement): Statement = {
    s match {
      case Connect(_, loc: WSubAccess, expr) =>
        val node = Node(loc)
        deps.addNode(node)
        deps.addDeps(node, getDeps(loc.index))
        deps.addDeps(node, getDeps(expr))
        deps.addDeps(node, conds)

      case Connect(_, loc @ WSubIndex(vec, index, _, _), expr) =>
        getCandidates(vec).foreach(scoreboard.markScoreboard(_, index))
        val node = Node(loc)
        deps.addNode(node)
        deps.addDeps(node, getDeps(expr))
        deps.addDeps(node, conds)

      case Connect(_, loc, expr) =>
        getCandidates(loc).foreach { v =>
          val VectorType(_, size) = v.tpe
          (0 until size).foreach(scoreboard.markScoreboard(v, _))
        }
        val node = Node(loc)
        deps.addNode(node)
        deps.addDeps(node, getDeps(expr))
        deps.addDeps(node, conds)

      case DefRegister(_, name, tpe, _, _, _) =>
        getCandidates(name, tpe).foreach { c =>
          scoreboard.addCandidate(c.copy()(hasDefault = true))
        }

      case DefWire(_, name, tpe) =>
        getCandidates(name, tpe).foreach { c =>
          scoreboard.addCandidate(c.copy()(hasDefault = false))
        }

        getNodes(name, tpe).foreach(deps.addNode)

      case DefNode(_, name, expr) =>
        getCandidates(name, expr.tpe).foreach { c =>
          scoreboard.addCandidate(c.copy()(hasDefault = true))
        }

        val nodes = getNodes(name, expr.tpe)
        val exprDeps = getDeps(expr)
        nodes.foreach { n =>
          deps.addNode(n)
          deps.addDeps(n, exprDeps)
        }

      case WDefInstance(_, name, _, tpe) =>
        getNodes(name, tpe).foreach { n =>
          deps.addNode(n)
        }

      case m: DefMemory if m.readLatency == 0 =>
        val addrType = UIntType(UnknownWidth)
        val enType = UIntType(IntWidth(1))
        for (rp <- m.readers) {
          val portName = m.name + fieldDelimiter + rp

          val dataNode = Node(portName + "data", m.dataType)
          deps.addNode(dataNode)
          val addrNode = Node(portName + "addr", addrType)
          deps.addNode(addrNode)
          val enNode = Node(portName + "en", enType)
          deps.addNode(enNode)

          deps.addDeps(dataNode, Seq(addrNode, enNode))
        }
      case Conditionally(_, cond, conseq, alt) =>
        val conditionDeps = getDeps(cond) ++: conds

        val conseqScoreboard = scoreboard.makeConditionalScoreboard()
        getStmtDeps(deps, conseqScoreboard, portMap, conditionDeps)(conseq)

        val altScoreboard = scoreboard.makeConditionalScoreboard()
        getStmtDeps(deps, altScoreboard, portMap, conditionDeps)(alt)

        scoreboard.mergeConditionalScoreboards(conseqScoreboard, altScoreboard)
      case _ => s mapStmt getStmtDeps(deps, scoreboard, portMap, conds)
    }
    s
  }

  def getDeps(expression: Expression): Seq[Node] = expression match {
    case _: WRef | _: WSubIndex | _: WSubAccess | _: WSubField =>
      val outerVec = getOuterVec(expression)
      getNodes(outerVec.serialize, outerVec.tpe)
    case other =>
      val deps = new mutable.ArrayBuffer[Node]
      other.mapExpr { e =>
        deps ++= getDeps(e)
        e
      }
      deps
  }

  def getNodes(name: String, tpe: Type): Seq[Node] = tpe match {
    case b: BundleType =>
      b.fields.flatMap(f => getNodes(name + fieldDelimiter + f.name, f.tpe))
    case _ => Seq(Node(name, tpe))
  }

  def getCandidates(expression: Expression): Seq[CandidateVec] = {
    getCandidates(expression.serialize, expression.tpe)
  }

  def getCandidates(name: String, tpe: Type, hasDefault: Boolean = false): Seq[CandidateVec] = {
    tpe match {
      case b: BundleType =>
        b.fields.flatMap(f => getCandidates(name + fieldDelimiter + f.name, f.tpe, hasDefault ^ (f.flip == Flip)))
      case v @ VectorType(BoolType, size) if size > 0 && ((size & (size - 1)) == 0) =>
        Seq(CandidateVec(name, v)(hasDefault))
      case _ => Seq.empty
    }
  }

  def getCandidateVecs(m: DefModule,
                       portDigraphs: Map[String, NodeDigraph]): (NodeDigraph, Set[CandidateVec]) = {
    val internalDeps = new NodeDigraph
    val scoreboard = new Scoreboard
    val portCandidates = new mutable.HashSet[CandidateVec]()
    m.ports.foreach { p =>
      getCandidates(p.name, p.tpe, p.direction == Input).foreach { c =>
        //scoreboard.addCandidate(c)
        portCandidates.add(c)
      }

      getNodes(p.name, p.tpe).foreach(internalDeps.addNode)
    }
    m.mapStmt(getStmtDeps(internalDeps, scoreboard, portDigraphs, Seq.empty))

    val diGraph = internalDeps.toDigraph
    val initializedVecs = scoreboard.getValidCandidates()
    val simplified = diGraph.simplify(initializedVecs.collect{case v if !v.hasDefault => v.toNode})

    val sccs  = simplified.findSCCs.filter(_.length > 1)

    if (sccs.nonEmpty | diGraph.getEdgeMap.exists { case (k, v) => v.contains(k) }) {
      (new NodeDigraph, Set.empty)
    } else {
      (internalDeps.getPortDigraph((initializedVecs & portCandidates).map(_.toNode)), initializedVecs)
    }
  }

  def getCandidateVecsC(c: Circuit): Map[String, Set[CandidateVec]] = {
    val instanceGraph = new InstanceGraph(c)
    val portMap = new mutable.HashMap[String, NodeDigraph]()
    val candidateMap = new mutable.HashMap[String, Set[CandidateVec]]()
    instanceGraph.moduleOrder.reverse.foreach { mod =>
      val (ports, candidates) = getCandidateVecs(mod, portMap.toMap)
      portMap.put(mod.name, ports)
      candidateMap.put(mod.name, candidates)
    }
    candidateMap.toMap
  }
}
