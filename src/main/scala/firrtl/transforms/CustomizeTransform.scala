// See LICENSE for license details.

package firrtl.transforms

import firrtl._
import firrtl.ir._

case class WrapperStatement(info: Info, id: String, stmt: Statement) extends CustomStatement {
  def update(stmt: Statement): Statement = this.copy(stmt = stmt)
  def serialize: String = stmt match {
    case EmptyStmt => ""
    case _ => stmt.serialize
  }
}

class CustomizeTransform extends Transform {
  override def inputForm: CircuitForm = LowForm
  override def outputForm: CircuitForm = LowForm

  def execute(state: CircuitState): CircuitState = {
    def customizeMod(mod: DefModule): DefModule = {
      val namespace = Namespace(mod)

      def customizeStmt(stmt: Statement): Statement = {
        WrapperStatement(NoInfo, namespace.newName(mod.name), stmt.mapStmt(customizeStmt))
      }

      mod.mapStmt(customizeStmt)
    }

    state.copy(circuit = state.circuit.mapModule(customizeMod))
  }
}
