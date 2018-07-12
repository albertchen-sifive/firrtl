circuit testInit:
  module testInit:
    input in1: UInt<2>
    input clock : Clock
    output outvec: UInt<2>
    
    wire vec : UInt<1>[2] @[compatibility.scala 117:12]
    vec[0] <= in1

    when in1:
        vec[1] <= in1


    outvec <= cat(vec[1], vec[0])
