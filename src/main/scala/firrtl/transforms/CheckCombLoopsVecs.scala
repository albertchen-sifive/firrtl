// See LICENSE for license details.

package firrtl.transforms

import scala.collection.mutable
import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.Utils.BoolType
import firrtl.analyses.InstanceGraph
import firrtl.graph.{DiGraph, MutableDiGraph}


sealed trait BaseNode {
  def name: String
  def tpe: Type

  override def equals(obj: scala.Any): Boolean = obj match {
    case b: BaseNode => (b.name == name) && (b.tpe == tpe)
    case _ => false
  }

  override def hashCode(): Int = name.hashCode + tpe.hashCode()
}

case class CandidateVec(name: String, tpe: VectorType, hasDefault: Boolean) extends BaseNode

object CheckCombLoopsVecs {

  private val fieldDelimeter = '.'

  private case class LogicNode(name: String)

  private case class Node(name: String, tpe: Type) extends BaseNode {
    private def expandBundle(tpe: Type): Seq[String] = tpe match {
      case BundleType(fields) => fields.flatMap(f => expandBundle(f.tpe).map(fieldDelimeter + f.name + _))
      case _ => Seq("")
    }
  }

  private object Node {
    def apply(expr: Expression): Node = {
      val first = getFirstIndex(expr)
      Node(first.serialize, first.tpe)
    }

    private def fromExpr(expression: Expression, suffix: String = ""): Node = expression match {
      case WRef(name, tpe, _, _) => Node(name + suffix, tpe)
      case WSubField(expr, name, _, _) => fromExpr(expr, fieldDelimeter + name)
      case WSubAccess(expr, _, _, _) => fromExpr(expr)
      case WSubIndex(expr, _, _, _) => fromExpr(expr)
    }

    def getDeps(source: Expression): Seq[Node] = source match {
      case _: WRef | _: WSubIndex | _: WSubAccess | _: WSubField => Seq(Node(source))
      case other =>
        val deps = new mutable.ArrayBuffer[Node]
        other.mapExpr { e =>
          deps ++= getDeps(e)
          e
        }
        deps
    }
  }

  def getFirstIndex(expr: Expression): Expression = {
    var curr = expr
    var firstVec = expr
    while(!curr.isInstanceOf[WRef]) {
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

  private class NodeDigraph {
    private val diGraph = new MutableDiGraph[BaseNode]
    def addDep(lhs: BaseNode, rhs: BaseNode): Unit = {
      diGraph.addEdgeIfValid(lhs, rhs)
    }
    def addDeps(lhs: BaseNode, rhs: Seq[BaseNode]): Unit = rhs.foreach(addDep(lhs, _))
    def addNode(connectable: BaseNode): Unit = diGraph.addVertex(connectable)
    def toDigraph: DiGraph[BaseNode] = DiGraph(diGraph)
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
                          portMap: Map[String, Set[CandidateVec]],
                          conds: Seq[Node])(s: Statement): Statement = {
    s match {
      case Connect(_, loc @ WSubAccess(vec, index, _, _), expr) =>
        val lhs = vec.tpe match {
          case v @ VectorType(BoolType, size) if size > 0 && ((size & (size - 1)) == 0) =>
            CandidateVec(vec.serialize, v, hasDefault = false)
          case _ => Node(loc)
        }
        deps.addNode(lhs)
        deps.addDeps(lhs, Node.getDeps(index))
        deps.addDeps(lhs, Node.getDeps(expr))
        deps.addDeps(lhs, conds)
      case Connect(_, loc @ WSubIndex(vec, index, _, _), expr) =>
        val lhs = vec.tpe match {
          case v @ VectorType(BoolType, size) if size > 0 && ((size & (size - 1)) == 0) =>
            val candidate = CandidateVec(vec.serialize, v, hasDefault = false)
            scoreboard.markScoreboard(candidate, index)
            candidate
          case _ => Node(loc)
        }

        deps.addNode(lhs)
        deps.addDeps(lhs, Node.getDeps(expr))
        deps.addDeps(lhs, conds)
      case Connect(_, loc, expr) =>
        val lhs = loc.tpe match {
          case v @ VectorType(BoolType, size) if size > 0 && ((size & (size - 1)) == 0) =>
            val candidate = CandidateVec(loc.serialize, v, hasDefault = false)
            (0 until size).foreach(scoreboard.markScoreboard(candidate, _))
            candidate
          case _ => Node(loc)
        }

        deps.addNode(lhs)
        deps.addDeps(lhs, Node.getDeps(expr))
        deps.addDeps(lhs, conds)

      case DefRegister(_, name, tpe, _, _, _) =>
        collectCandidates(name, tpe, Input).map {
          case v: CandidateVec =>
            val candidate = v.copy(hasDefault = true)
            scoreboard.addCandidate(candidate)
            candidate
          case node => node
        }
      case DefWire(_, name, tpe) =>
        val nodes = collectCandidates(name, tpe, Input).map {
          case v: CandidateVec =>
            val candidate = v.copy(hasDefault = false)
            scoreboard.addCandidate(candidate)
            candidate
          case node => node
        }
        nodes.foreach(deps.addNode)

      case DefNode(_, name, expr) =>
        val nodes = collectCandidates(name, expr.tpe, Input).map {
          case v: CandidateVec =>
            val candidate = v.copy(hasDefault = true)
            scoreboard.addCandidate(candidate)
            candidate
          case node => node
        }
        val exprDeps = Node.getDeps(expr)

        nodes.foreach { n =>
          deps.addNode(n)
          deps.addDeps(n, exprDeps)
        }

      case WDefInstance(_, name, module, tpe) =>
        val nodes = collectCandidates(name, tpe, Input)
        /*
        val nodes = portMap(module).map { candidate =>
          candidate.copy(name = name + fieldDelimeter + candidate.name, hasDefault = !candidate.hasDefault)
        }*/
        nodes.foreach { n =>
          //scoreboard.addCandidate(n)
          deps.addNode(n)
        }

      case m: DefMemory if m.readLatency == 0 =>
        val addrType = UIntType(UnknownWidth)
        val enType = UIntType(IntWidth(1))
        for (rp <- m.readers) {
          val portName = m.name + fieldDelimeter + rp

          val dataNode = Node(portName + "data", m.dataType)
          deps.addNode(dataNode)
          val addrNode = Node(portName + "addr", addrType)
          deps.addNode(addrNode)
          val enNode = Node(portName + "en", enType)
          deps.addNode(enNode)

          deps.addDeps(dataNode, Seq(addrNode, enNode))
        }
      case Conditionally(_, cond, conseq, alt) =>
        val conditionDeps = Node.getDeps(cond) ++: conds

        val conseqScoreboard = scoreboard.makeConditionalScoreboard()
        getStmtDeps(deps, conseqScoreboard, portMap, conditionDeps)(conseq)

        val altScoreboard = scoreboard.makeConditionalScoreboard()
        getStmtDeps(deps, altScoreboard, portMap, conditionDeps)(alt)

        scoreboard.mergeConditionalScoreboards(conseqScoreboard, altScoreboard)
      case _ => s mapStmt getStmtDeps(deps, scoreboard, portMap, conds)
    }
    s
  }

  def collectCandidates(name: String, tpe: Type, direction: Direction): Seq[BaseNode] = {
    tpe match {
      case b: BundleType => expandBundle(name, b, direction == Input)
      case v @ VectorType(BoolType, size) if size > 0 && ((size & (size - 1)) == 0) =>
        Seq(CandidateVec(name, v, direction == Input))
      case _ => Seq(Node(name, tpe))
    }
  }

  private def expandBundle(name: String, bundle: BundleType, isInput: Boolean): Seq[BaseNode] = {
    bundle.fields.flatMap { field =>
      val partialName = name + fieldDelimeter + field.name
      field.tpe match {
        case b: BundleType => expandBundle(partialName, b, isInput ^ (field.flip == Flip))
        case v @ VectorType(BoolType, size) if size > 0 && ((size & (size - 1)) == 0) =>
          Seq(CandidateVec(partialName, v, isInput))
        case _ => Seq(Node(partialName, field.tpe))
      }
    }
  }

  def getCandidateVecs(m: DefModule,
                       portMap: Map[String, Set[CandidateVec]]): (Set[CandidateVec], Set[CandidateVec]) = {
    val internalDeps = new NodeDigraph
    val scoreboard = new Scoreboard
    val portCandidates = new mutable.HashSet[CandidateVec]()
    m.ports.foreach { p =>
      val connectables = collectCandidates(p.name, p.tpe, p.direction)
      for (c <- connectables) {
        c match {
          case v: CandidateVec =>
            //scoreboard.addCandidate(v)
            portCandidates.add(v)
          case _ =>
        }
        internalDeps.addNode(c)
      }
    }
    m.mapStmt(getStmtDeps(internalDeps, scoreboard, portMap, Seq.empty))

    val diGraph = internalDeps.toDigraph
    val initializedVecs = scoreboard.getValidCandidates()
    val simplified = diGraph.simplify(initializedVecs.filterNot(_.hasDefault).toSet)

    //scoreboard.printNodes()

    val sccs  = simplified.findSCCs.filter(_.length > 1)
    //println(diGraph.getEdgeMap)
    //println()
    if (sccs.nonEmpty | diGraph.getEdgeMap.exists{ case (k, v) => v.contains(k) }) {
      (Set.empty, Set.empty)
    } else {
      (initializedVecs & portCandidates, initializedVecs)
    }
  }

  def getCandidateVecsC(c: Circuit): Map[String, Set[CandidateVec]] = {
    val instanceGraph = new InstanceGraph(c)
    val portMap = new mutable.HashMap[String, Set[CandidateVec]]()
    val candidateMap = new mutable.HashMap[String, Set[CandidateVec]]()
    instanceGraph.moduleOrder.reverse.foreach { mod =>
      val (ports, candidates) = getCandidateVecs(mod, portMap.toMap)
      portMap.put(mod.name, ports)
      candidateMap.put(mod.name, candidates)
    }
    candidateMap.toMap
  }
}
