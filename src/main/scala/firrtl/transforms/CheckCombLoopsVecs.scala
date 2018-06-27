// See LICENSE for license details.

package firrtl.transforms

import scala.collection.mutable
import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.graph.{DiGraph, MutableDiGraph}

class CheckCombLoopsVecs {

  private val fieldDelimeter = '.'

  private case class LogicNode(name: String)

  private case class Connectable(name: String, tpe: Type) {
    def toLogicNodes: Seq[LogicNode] = {
      expandBundle(tpe).map(s => LogicNode(name + s))
    }

    private def expandBundle(tpe: Type): Seq[String] = tpe match {
      case BundleType(fields) => fields.flatMap(f => expandBundle(f.tpe).map(fieldDelimeter + f.name + _))
      case _ => Seq("")
    }
  }

  private object Connectable {
    def apply(expression: Expression): Connectable = fromExpr(expression)

    def fromExpr(expression: Expression, suffix: String = ""): Connectable = expression match {
      case WRef(name, tpe, _, _) => Connectable(name + suffix, tpe)
      case WSubField(expr, name, _, _) => fromExpr(expr, fieldDelimeter + name)
      case WSubAccess(expr, _, _, _) => fromExpr(expr)
      case WSubIndex(expr, _, _, _) => fromExpr(expr)
    }

    def getDeps(source: Expression): Seq[Connectable] = source match {
      case _: WRef |
           _: WSubIndex |
           _: WSubAccess |
           _: WSubField => Seq(Connectable(source))
      case other =>
        val deps = new mutable.ArrayBuffer[Connectable]
        other.mapExpr { e =>
          deps ++= getDeps(e)
          e
        }
        deps
    }
  }

  private class MyDigraph(diGraph: MutableDiGraph[LogicNode]) {
    val vecNodes = new mutable.HashSet[LogicNode]()

    def addDep(lhs: Connectable, rhs: Connectable): Unit = {
      val lhsExpanded = lhs.toLogicNodes
      val rhsExpanded = rhs.toLogicNodes
      lhsExpanded.zip(rhsExpanded).foreach { case (u, v) =>
        diGraph.addEdgeIfValid(u, v)
      }
    }

    def addDeps(lhs: Connectable, rhs: Seq[Connectable]): Unit = rhs.foreach(r => addDep(lhs, r))

    def addNode(connectable: Connectable): Unit = {
      val logicNodes = connectable.toLogicNodes
      if (connectable.tpe.isInstanceOf[VectorType]) {
        vecNodes ++= logicNodes
      }
      logicNodes.foreach(n => diGraph.addVertex(n))
    }

    def toDigraph: DiGraph[LogicNode] = {
      DiGraph(diGraph).simplify(vecNodes)
    }

    def containsVecCycle: Boolean = {
      val hasSelfEdges = diGraph.getEdgeMap.filterKeys(vecNodes.contains).exists{ case (k, v) => v.contains(k) }
      diGraph.simplify(vecNodes).findSCCs.exists(_.length > 1) | hasSelfEdges
    }
  }

  private def getStmtDeps(deps: MyDigraph, conds: Seq[Connectable])(s: Statement): Statement = {
    s match {
      case Connect(_, loc @ SubAccess(vec, index, _), expr) =>
        val lhs = Connectable(loc)
        deps.addDep(lhs, Connectable(index))
        deps.addDeps(lhs, Connectable.getDeps(expr))
      case Connect(_, loc, expr) =>
        val lhs = Connectable(loc)
        deps.addDeps(lhs, Connectable.getDeps(expr))
      case DefWire(_, name, tpe) => deps.addNode(Connectable(name, tpe))
      case DefNode(_, name, expr) =>
        val lhs = Connectable(name, expr.tpe)
        deps.addDeps(lhs, Connectable.getDeps(expr))
      case m: DefMemory if m.readLatency == 0 =>
        val addrType = UIntType(UnknownWidth)
        val enType = UIntType(IntWidth(1))
        for (rp <- m.readers) {
          val portName = m.name + fieldDelimeter + rp

          val dataNode = Connectable(portName + "data", m.dataType)
          deps.addNode(dataNode)
          val addrNode = Connectable(portName + "addr", addrType)
          deps.addNode(addrNode)
          val enNode = Connectable(portName + "en", enType)
          deps.addNode(enNode)

          deps.addDeps(dataNode, Seq(addrNode, enNode))
        }
      case WDefInstance(_, name, _, tpe) => deps.addNode(Connectable(name, tpe))
      case Conditionally(_, cond, conseq, alt) =>
        val condConnectables = Connectable.getDeps(cond) ++: conds
        getStmtDeps(deps, condConnectables)(conseq)
        getStmtDeps(deps, condConnectables)(alt)
      case _ => s map getStmtDeps(deps, conds)
    }
    s
  }

  private def findCycleInSCC[T](sccGraph: DiGraph[T]): Seq[T] = {
    val walk = new mutable.ArrayBuffer[T]
    val visited = new mutable.HashSet[T]
    var current = sccGraph.getVertices.head
    while (!visited.contains(current)) {
      walk += current
      visited += current
      current = sccGraph.getEdges(current).head
    }
    walk.drop(walk.indexOf(current)) :+ current
  }

  def hasBadVecs(m: Module): Boolean = {
    val internalDeps = new MyDigraph(new MutableDiGraph[LogicNode])
    m.ports.foreach(p => internalDeps.addNode(Connectable(p.name, p.tpe)))
    m map getStmtDeps(internalDeps, Seq.empty)
    internalDeps.containsVecCycle
  }

  def collectBadVecs(m: Module): Set[String] = {
    val internalDeps = new MyDigraph(new MutableDiGraph[LogicNode])
    m.ports.foreach(p => internalDeps.addNode(Connectable(p.name, p.tpe)))
    m map getStmtDeps(internalDeps, Seq.empty)
    val moduleGraph = internalDeps.toDigraph

    val badVecs = new mutable.HashSet[String]
    val cycles = moduleGraph.findSCCs.filter(_.length > 1) map { scc =>
      val sccSubgraph = moduleGraph.subgraph(scc.toSet)
      val cycle = findCycleInSCC(sccSubgraph)
      (cycle zip cycle.tail).foreach { case (a, b) => require(moduleGraph.getEdges(a).contains(b)) }

      badVecs += scc.head.name//cycle.map(n => n.name)
    }

    badVecs.toSet
  }
}
