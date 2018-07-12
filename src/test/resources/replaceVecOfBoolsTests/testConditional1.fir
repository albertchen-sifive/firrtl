circuit testConditional1:
  module Dummy:
    input select1: UInt<1>
    input select2: UInt<1>
    input cond3: UInt<1>
    output condResult: UInt<1>[2]

    condResult[0] <= UInt(0)
    condResult[1] <= UInt(0)
    when cond3:
      condResult[0] <= UInt(1)
    else:
      condResult[1] <= UInt(1)
      
  module testConditional1:
    input select1: UInt<1>
    input select2: UInt<1>
    input cond3: UInt<1>
    output condResult: UInt<2>

    inst myDummy of Dummy
    myDummy.select1 <= select1
    myDummy.select2 <= select2
    myDummy.cond3 <= cond3

    condResult <= cat(myDummy.condResult[1], myDummy.condResult[0])
