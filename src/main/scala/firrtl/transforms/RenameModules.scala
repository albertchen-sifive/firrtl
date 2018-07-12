// See LICENSE for license details.

package firrtl.transforms

import firrtl.{CircuitState, LowForm, Namespace, Transform, WDefInstance, WRef}
import firrtl.Utils._
import firrtl.analyses.InstanceGraph
import firrtl.ir._
import firrtl.passes.ExpandConnects
import firrtl.transforms.CandidateVecFinder.CandidateVec

import scala.collection.mutable

/** Replace Vec of Bools
  *
  * This transform replaces Vecs of Bools with UInts
  */
class RenameModules(namespace: Namespace, newTopName: String) extends Transform {
  def inputForm: LowForm.type = LowForm
  def outputForm: LowForm.type = LowForm

  def collectNameMapping(namespace: Namespace, moduleNameMap: mutable.HashMap[String, String])
                        (mod: DefModule): Unit = {
    val newName = namespace.newName(mod.name)
    moduleNameMap.put(mod.name, newName)
  }

  def onStmt(moduleNameMap: mutable.HashMap[String, String])
            (stmt: Statement): Statement = stmt match {
    case inst: WDefInstance if moduleNameMap.contains(inst.module) => inst.copy(module = moduleNameMap(inst.module))
    case other => other.mapStmt(onStmt(moduleNameMap))
  }

  def execute(state: CircuitState): CircuitState = {
    val moduleOrder = new InstanceGraph(state.circuit).moduleOrder.reverse
    val nameMappings = new mutable.HashMap[String, String]()
    moduleOrder.foreach(collectNameMapping(namespace, nameMappings))

    val modulesx = state.circuit.modules.map {
      case mod: Module if mod.name == state.circuit.main => mod.copy(name = newTopName).mapStmt(onStmt(nameMappings))
      case mod: Module => mod.mapStmt(onStmt(nameMappings)).mapString(nameMappings)
      case ext: ExtModule => ext
    }

    val newState = state.copy(circuit = state.circuit.copy(modules = modulesx, main = newTopName))
    newState
  }
}

/** Replace Vec of Bools
  *
  * This transform replaces Vecs of Bools with UInts
  */
class GetNamespace extends Transform {
  var namespace: Option[Namespace] = Option.empty
  var newTopName: Option[String] = Option.empty
  def inputForm: LowForm.type = LowForm
  def outputForm: LowForm.type = LowForm

  def execute(state: CircuitState): CircuitState = {
    namespace = Some(Namespace(state.circuit))
    newTopName = namespace.map(_.newName(state.circuit.main))
    state
  }
}
