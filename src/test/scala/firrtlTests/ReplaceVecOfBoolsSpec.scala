// See LICENSE for license details.

package firrtlTests

import firrtl.passes.CheckInitialization.RefNotInitializedException
import firrtl.transforms.CheckCombLoops.CombLoopException
import firrtl.transforms.ReplaceVecOfBools

class ReplaceVecOfBoolsSpec extends FirrtlPropSpec {
  private val srcDir = "/replaceVecOfBoolsTests"
  private val transforms = Seq(new ReplaceVecOfBools)

  property(s"should be able to optimize simple bool-vec registers") {
    firrtlEquivalenceTest("simpleRegTest", srcDir, transforms, resets = Seq((1, "reset", 1)))
  }

  property(s"init values of registers should be correctly optimized") {
    firrtlEquivalenceTest("testRegInit", srcDir, transforms, resets = Seq((1, "reset", 1)))
  }

  property(s"should be able to optimize registers") {
    firrtlEquivalenceTest("testRegBundle", srcDir, transforms, resets = Seq((1, "reset", 1)))
  }

  property(s"vecs should not be flattened if it would result in a combinational loop") {
    firrtlEquivalenceTest("testCombLoop", srcDir, transforms)
  }

  property(s"should also avoid combinational loops that span across different modules") {
    firrtlEquivalenceTest("testCombLoop2", srcDir, transforms)
  }

  property(s"handle simple conditionals") {
    firrtlEquivalenceTest("testConditional1", srcDir, transforms)
  }

  property(s"handle nested conditionals") {
    firrtlEquivalenceTest("testConditional2", srcDir, transforms)
  }

  property(s"handle wires declared within conditionals") {
    firrtlEquivalenceTest("testConditional3", srcDir, transforms)
  }

  property(s"conditional register assignments should work too") {
    firrtlEquivalenceTest("testConditionalReg", srcDir, transforms, resets = Seq((1, "reset", 1)))
  }

  property(s"should be able to optimize ports of nested module instances") {
    firrtlEquivalenceTest("testNestedModules", srcDir, transforms)
  }

  property(s"should be work with deeply nested modules") {
    firrtlEquivalenceTest("testNestedModules1", srcDir, transforms)
  }

  property(s"it shouldn't break when there are nested vectors") {
    firrtlEquivalenceTest("testVecBundle", srcDir, transforms, resets = Seq((1, "reset", 1)))
  }
}

class ReplaceVecOfBoolsErrorsSpec extends FirrtlFlatSpec {
  private val srcDir = "/replaceVecOfBoolsTests"
  private val transforms = Seq(new ReplaceVecOfBools)

  "Circuits with combinational loops" should "still have combinational loops" in {
    an [CombLoopException] should be thrownBy compileFirrtlTest("combLoopErrorTest", srcDir, transforms)
  }

  "Vecs that are not fully initialized" should "should not be initialized" in {
    an [RefNotInitializedException] should be thrownBy compileFirrtlTest("testInit", srcDir, transforms)
  }
}
