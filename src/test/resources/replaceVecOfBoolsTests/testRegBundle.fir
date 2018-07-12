circuit testRegBundle:
  module testRegBundle:
    input vec: UInt<2>
    input reset : UInt<1>
    input clock : Clock
    input invec1: UInt<2>
    input invec2: UInt<2>
    output outvec1: UInt<2>
    output outvec2: UInt<2>

    wire init : {vec: UInt<1>[2], field: {vec: UInt<1>[2]}}
    init is invalid
    init.vec[0] <= UInt<1>("h00")
    init.vec[1] <= UInt<1>("h00")
    init.field.vec[0] <= UInt<1>("h00")
    init.field.vec[1] <= UInt<1>("h00")
    reg r1 : {vec: UInt<1>[2], field: {vec: UInt<1>[2]}}, clock with : (reset => (reset, init))
    r1.vec[0] <= bits(invec1, 0, 0)
    r1.vec[1] <= bits(invec1, 1, 1)
    r1.field.vec[0] <= bits(invec1, 0, 0)
    r1.field.vec[1] <= bits(invec1, 1, 1)

    outvec1 <= cat(r1.vec[1], r1.vec[0])
    outvec2 <= cat(r1.field.vec[1], r1.field.vec[0])
