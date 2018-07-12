circuit testConditionalReg:
  module testConditionalReg:
    input clock: Clock
    input in: UInt<2>
    input cond: UInt<1>
    input reset: UInt<1>
    output out: UInt<2>

    wire zeros: UInt<1>[2]
    zeros[0] <= UInt<1>("h0")
    zeros[1] <= UInt<1>("h0")
    reg vecreg : UInt<1>[2], clock with : (reset => (reset, zeros))
    when cond :
      vecreg[0] <= bits(in, 0, 0)
      vecreg[1] <= bits(in, 1, 1)
      skip

    out <= cat(vecreg[0], vecreg[1])
