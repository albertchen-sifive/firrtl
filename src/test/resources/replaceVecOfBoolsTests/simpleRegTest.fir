circuit simpleRegTest :
  module simpleRegTest :
    input clk : Clock
    input reset : UInt<1>
    input value : UInt<4>
    output out : UInt<4>

    wire initValue : UInt<1>[4]
    initValue[0] <= UInt<1>("h0")
    initValue[1] <= UInt<1>("h0")
    initValue[2] <= UInt<1>("h0")
    initValue[3] <= UInt<1>("h0")
    reg r : UInt<1>[4], clk with : (reset => (reset, initValue))
    r[0] <= bits(value, 0, 0)
    r[1] <= bits(value, 1, 1)
    r[2] <= bits(value, 2, 2)
    r[3] <= bits(value, 3, 3)


    out <= cat(r[3], cat(r[2], cat(r[1], r[0])))
