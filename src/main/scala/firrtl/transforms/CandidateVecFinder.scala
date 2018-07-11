// See LICENSE for license details.

package firrtl.transforms

import firrtl.Utils.BoolType
import firrtl._
import firrtl.analyses.InstanceGraph
import firrtl.graph.{DiGraph, MutableDiGraph}
import firrtl.ir._

import scala.collection.mutable

object CandidateVecFinder {
  val fieldDelimiter = '.'

  case class Node(name: String, tpe: Type)

  object Node {
    def apply(expr: Expression): Node = {
      val outerVec = getOuterVec(expr)
      Node(outerVec.serialize, outerVec.tpe)
    }

    private def getOuterVec(expr: Expression): Expression = expr match {
      case r: WRef => r
      case sf: WSubField =>
        val outerVec = getOuterVec(sf.expr)
        if (outerVec == sf.expr) sf else outerVec
      case si: WSubIndex => getOuterVec(si.expr)
      case sa: WSubAccess => getOuterVec(sa.expr)
    }
  }

  case class CandidateVec(name: String, tpe: VectorType)
                         (val hasDefault: Boolean, val module: Option[String] = Option.empty) {
    def toNode: Node = Node(name, tpe)
  }

  class NodeDigraph {
    private val diGraph = new MutableDiGraph[Node]

    def addDep(lhs: Node, rhs: Node): Unit = diGraph.addEdgeIfValid(lhs, rhs)

    def addDeps(lhs: Node, rhs: Seq[Node]): Unit = rhs.foreach(addDep(lhs, _))

    def addNode(node: Node): Unit = diGraph.addVertex(node)

    def toDigraph: DiGraph[Node] = DiGraph(diGraph)

    def mergeDigraph(inst: String, other: NodeDigraph): Unit = {
      val iGraph = other.diGraph.transformNodes(n => n.copy(name = inst + fieldDelimiter + n.name))
      iGraph.getVertices.foreach(diGraph.addVertex)
      iGraph.getVertices.foreach { v =>
        iGraph.getEdges(v).foreach(diGraph.addEdge(v, _))
      }
    }

    def getSubgraph(nodes: Set[Node]): NodeDigraph = {
      val result = new NodeDigraph
      val myNodes = nodes & diGraph.getVertices
      myNodes.foreach(result.addNode)
      myNodes.foreach { v =>
        (diGraph.reachableFrom(v) & nodes).foreach(result.addDep(v, _))
      }
      result
    }
  }

  private class Scoreboard {
    private val vecNodes = new mutable.HashMap[CandidateVec, mutable.ArraySeq[Boolean]]()

    def addCandidate(candidate: CandidateVec): Unit = {
      if (candidate.hasDefault) {
        vecNodes.put(candidate, new mutable.ArraySeq[Boolean](0))
      } else {
        val scoreboard = new mutable.ArraySeq[Boolean](candidate.tpe.size)
        (0 until candidate.tpe.size).foreach(scoreboard(_) = false)
        vecNodes.put(candidate, scoreboard)
      }
    }

    def markScoreboard(candidate: CandidateVec, index: Int): Unit = {
      if (vecNodes.contains(candidate) && vecNodes(candidate).nonEmpty) {
        vecNodes(candidate)(index) = true
      }
    }

    def getCandidates: Set[CandidateVec] = vecNodes.keys.toSet

    def getValidCandidates: Set[CandidateVec] = {
      vecNodes.collect { case (candidate, score) if score.forall(b => b) => candidate }(collection.breakOut)
    }

    def getInvalidCandidates: Set[CandidateVec] = {
      vecNodes.collect { case (candidate, score) if score.exists(b => !b) => candidate }(collection.breakOut)
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
      for (k <- currentKeys) {
        vecNodes(k).indices.foreach(i => vecNodes(k)(i) |= conseqVecs(k)(i) && altVecs(k)(i))
      }

      (conseqVecs.keySet &~ currentKeys).foreach(key => vecNodes += key -> conseqVecs(key))
      (altVecs.keySet &~ currentKeys).foreach(key => vecNodes += key -> altVecs(key))
    }
  }

  private def getStmtDeps(deps: NodeDigraph,
                          scoreboard: Scoreboard,
                          externalDeps: Map[String, (NodeDigraph, Set[Node])],
                          conds: Seq[Node])(s: Statement): Statement = {
    s match {
      case Connect(_, loc: WSubAccess, expr) =>
        val node = Node(loc)
        deps.addDeps(node, getDeps(loc.index))
        deps.addDeps(node, getDeps(expr))
        deps.addDeps(node, conds)

      case Connect(_, loc @ WSubIndex(vec, index, _, _), expr) =>
        getCandidates(vec).foreach(scoreboard.markScoreboard(_, index))
        val node = Node(loc)
        deps.addDeps(node, getDeps(expr))
        deps.addDeps(node, conds)

      case Connect(_, loc, expr) =>
        getCandidates(loc).foreach { v =>
          (0 until v.tpe.size).foreach(scoreboard.markScoreboard(v, _))
        }
        val node = Node(loc)
        deps.addDeps(node, getDeps(expr))
        deps.addDeps(node, conds)

      case DefRegister(_, name, tpe, _, _, _) =>
        getCandidates(name, tpe).foreach { c =>
          scoreboard.addCandidate(c.copy()(hasDefault = true, Option.empty))
        }

      case DefWire(_, name, tpe) =>
        getCandidates(name, tpe).foreach { c =>
          scoreboard.addCandidate(c.copy()(hasDefault = false, Option.empty))
        }
        getNodes(name, tpe).foreach(deps.addNode)

      case DefNode(_, name, expr) =>
        getCandidates(name, expr.tpe).foreach { c =>
          scoreboard.addCandidate(c.copy()(hasDefault = true, Option.empty))
        }
        val nodes = getNodes(name, expr.tpe)
        val exprDeps = getDeps(expr)
        nodes.foreach { n =>
          deps.addNode(n)
          deps.addDeps(n, exprDeps)
        }

      case WDefInstance(_, inst, module, tpe) =>
        val nodes = getNodes(inst, tpe)
        nodes.foreach(deps.addNode)
        deps.mergeDigraph(inst, externalDeps(module)._1)

        getCandidates(inst, tpe, hasDefault = true)
          .filter(c => externalDeps(module)._2.contains(
            Node(c.name.split(fieldDelimiter).tail.mkString(fieldDelimiter.toString), c.tpe)))
          .map(c => c.copy()(c.hasDefault, Some(module)))
          .foreach(scoreboard.addCandidate)

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
        getStmtDeps(deps, conseqScoreboard, externalDeps, conditionDeps)(conseq)

        val altScoreboard = scoreboard.makeConditionalScoreboard()
        getStmtDeps(deps, altScoreboard, externalDeps, conditionDeps)(alt)

        scoreboard.mergeConditionalScoreboards(conseqScoreboard, altScoreboard)
      case _ => s mapStmt getStmtDeps(deps, scoreboard, externalDeps, conds)
    }
    s
  }

  def getDeps(expression: Expression): Seq[Node] = expression match {
    case _: WRef | _: WSubIndex | _: WSubAccess | _: WSubField => Seq(Node(expression))
    case other =>
      val deps = new mutable.ArrayBuffer[Node]
      other.mapExpr { e =>
        deps ++= getDeps(e)
        e
      }
      deps
  }

  def getNodes(name: String, tpe: Type): Seq[Node] = tpe match {
    case BundleType(fields) => fields.flatMap(f => getNodes(name + fieldDelimiter + f.name, f.tpe))
    case _ => Seq(Node(name, tpe))
  }

  def getCandidates(expression: Expression): Seq[CandidateVec] = {
    getCandidates(expression.serialize, expression.tpe)
  }

  def getCandidates(name: String, tpe: Type, hasDefault: Boolean = false): Seq[CandidateVec] = tpe match {
    case BundleType(fields) =>
      fields.flatMap(f => getCandidates(name + fieldDelimiter + f.name, f.tpe, hasDefault ^ (f.flip == Flip)))
    case v @ VectorType(BoolType, size) if size > 0 && ((size & (size - 1)) == 0) =>
      Seq(CandidateVec(name, v)(hasDefault))
    case _ => Seq.empty
  }

  private def getModuleCandidates(currentModule: DefModule,
                                  validPorts: Map[String, (NodeDigraph, Set[Node])]):
  (Map[String, (NodeDigraph, Set[Node])], Set[CandidateVec]) = {
    val scoreboard = new Scoreboard
    val internalDeps = new NodeDigraph

    val portCandidates = currentModule.ports.flatMap { case Port(_, name, direction, tpe) =>
      getCandidates(name, tpe, direction == Input).map { candidate =>
        candidate.copy()(candidate.hasDefault, Some(currentModule.name))
      }
    }.toSet
    portCandidates.foreach(scoreboard.addCandidate)

    val portNodes = currentModule.ports.flatMap(p => getNodes(p.name, p.tpe)).toSet
    portNodes.foreach(internalDeps.addNode)

    currentModule.mapStmt(getStmtDeps(internalDeps, scoreboard, validPorts, Seq.empty))

    val validCandidates = scoreboard.getValidCandidates
    val portDiGraph = internalDeps.getSubgraph(portNodes)

    val candidateGraph = internalDeps.getSubgraph(validCandidates.map(_.toNode)).toDigraph
    val sccs = candidateGraph.findSCCs.filter(_.length > 1)
    if (sccs.nonEmpty | candidateGraph.getEdgeMap.exists { case (k, v) => v.contains(k) }) {
      val empties = scoreboard.getCandidates.flatMap(_.module).collect {
        case moduleName if validPorts.contains(moduleName) =>
          moduleName -> validPorts(moduleName).copy(_2 = Set.empty[Node])
      }
      (validPorts ++ empties + (currentModule.name -> (portDiGraph, Set.empty[Node])), Set.empty)
    } else {

      val updatedPorts = scoreboard.getCandidates
        .filter(_.module.exists(_ != currentModule.name))
        .groupBy(_.module.get)
        .collect { case (k, v) =>
          val commonCandidates = v.groupBy(_.name.takeWhile(_ != '.')).values.map { candidates =>
            candidates.collect { case candidate if validCandidates.contains(candidate) =>
              val pathName = candidate.name.split(fieldDelimiter).tail.mkString(fieldDelimiter.toString)
              Node(pathName, candidate.tpe)
            }
          }.reduce(_ & _)
          k -> validPorts(k).copy(_2 = validPorts(k)._2 & commonCandidates)
        }

      val currentModulePorts = currentModule.name -> (portDiGraph, (validCandidates & portCandidates).map(_.toNode))

      (validPorts ++ updatedPorts + currentModulePorts, validCandidates)
    }
  }

  def getCandidateVecs(c: Circuit): Map[String, Set[CandidateVec]] = {
    val instanceGraph = new InstanceGraph(c)
    val moduleOrder = instanceGraph.moduleOrder.reverse
    val candidateMap = new mutable.HashMap[String, Set[CandidateVec]]()
    val validPorts = moduleOrder.foldLeft(Map.empty[String, (NodeDigraph, Set[Node])]) { case (inputPortMap, mod) =>
      val (outputPortMap, candidates) = getModuleCandidates(mod, inputPortMap)
      candidateMap.put(mod.name, candidates)
      outputPortMap
    }.mapValues(_._2)

    val filteredCandidates = new mutable.HashMap[String, Set[CandidateVec]]()
    candidateMap.foreach { case (moduleName, candidates) =>
      val filtered = candidates.collect {
        case internalWire if internalWire.module.isEmpty => internalWire
        case port if port.module.get == moduleName && validPorts(moduleName).contains(port.toNode) => port
        case port if validPorts(port.module.get).contains(
          Node(port.name.split(fieldDelimiter).tail.mkString(fieldDelimiter.toString), port.tpe)) => port
      }
      filteredCandidates.put(moduleName, filtered)
    }

    filteredCandidates.toMap
  }
}
