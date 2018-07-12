circuit Top:
  module InnerModule:
    input in1: UInt<1>
    input in2: UInt<1>
    output outVec: UInt<1>[2]

    outVec[0] <= in1
    outVec[1] <= in2

  module Top:
    input in1: UInt<1>
    output outVec: UInt<2>

    inst inner of InnerModule
    inner.in1 <= in1
    inner.in2 <= inner.outVec[0]

    outVec <= cat(inner.outVec[1], inner.outVec[0])
