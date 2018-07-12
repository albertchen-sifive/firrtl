circuit combLoopErrorTest :
  module combLoopErrorTest :
    input clk : Clock
    input in : UInt<4>
    output out : UInt<4>

    wire value : UInt<1>[4]
    value[0] <= value[1]
    value[1] <= value[2]
    value[2] <= value[3]
    value[3] <= value[0]


    out <= cat(value[3], cat(value[2], cat(value[1], value[0])))
