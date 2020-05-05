// See LICENSE for license details.

package firrtlTests.transforms

import firrtl._
import firrtl.annotations._
import firrtl.transforms.{ModuleNameAnnotation, StabilizeModuleNames}
import firrtl.testutils.{FirrtlMatchers, FirrtlPropSpec}

class StabilizeModuleNamesSpec extends FirrtlPropSpec with FirrtlMatchers {
  val transform = new StabilizeModuleNames
  def stabilizeNames(state: CircuitState): CircuitState = {
    transform.runTransform(state)
  }

  property("It should rename different modules") {
    val input =
    """|circuit Foo:
       |  module Bar_1:
       |    skip
       |  module Bar_2:
       |    node dummy = UInt<1>(0)
       |  module Foo:
       |    inst bar_1 of Bar_1
       |    inst bar_2 of Bar_2
       |""".stripMargin

    val top = CircuitTarget("Foo")
    val annos = Seq(
      ModuleNameAnnotation("Bar", top.module("Bar_1")),
      ModuleNameAnnotation("Bar", top.module("Bar_2"))
    )
    val inputState = CircuitState(passes.ToWorkingIR.run(Parser.parse(input)), UnknownForm, annos)
    val outputState = stabilizeNames(inputState)
    println(outputState.circuit.serialize)
  }

  property("It should rename modules to original name if only one module") {
    val input =
    """|circuit Foo:
       |  module Bar_1:
       |    skip
       |  module Foo:
       |    inst bar_1 of Bar_1
       |    inst bar_2 of Bar_1
       |""".stripMargin

    val top = CircuitTarget("Foo")
    val annos = Seq(
      ModuleNameAnnotation("Bar", top.module("Foo").instOf("bar_1", "Bar_1")),
      ModuleNameAnnotation("Bar", top.module("Foo").instOf("bar_2", "Bar_1"))
    )
    val inputState = CircuitState(passes.ToWorkingIR.run(Parser.parse(input)), UnknownForm, annos)
    val outputState = stabilizeNames(inputState)
    val output = 
    """|circuit Foo:
       |  module Bar:
       |    skip
       |  module Foo:
       |    inst bar_1 of Bar
       |    inst bar_2 of Bar
       |""".stripMargin
    outputState.circuit.serialize should be (Parser.parse(output).serialize)
  }
}
