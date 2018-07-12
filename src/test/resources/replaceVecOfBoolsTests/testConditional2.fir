circuit testConditional2:
  module Dummy:
    input select: UInt<3>
    input cond1: UInt<1>
    input cond2: UInt<1>
    input cond3: UInt<1>
    input cond4: UInt<1>
    output condResult: UInt<1>[4]

    condResult[0] <= UInt(0)
    condResult[1] <= UInt(0)
    condResult[2] <= UInt(0)
    condResult[3] <= UInt(0)
    when cond1:
      condResult[0] <= UInt(0)
      when cond2:
        condResult[1] <= UInt(0)
        when cond4:
          condResult[1] <= UInt(0)
        else:
          condResult[2] <= UInt(1)
      else:
        condResult[2] <= UInt(1)
    else when cond2:
      condResult[1] <= UInt(1)

    when cond3:
      condResult[0] <= UInt(1)
      condResult[1] <= UInt(0)
    else:
      condResult[0] <= UInt(0)
      condResult[2] <= UInt(1)
      
  module testConditional2:
    input select: UInt<3>
    input cond1: UInt<1>
    input cond2: UInt<1>
    input cond3: UInt<1>
    input cond4: UInt<1>
    output condResult: UInt<3>

    inst myDummy of Dummy
    myDummy.select <= select
    myDummy.cond1 <= cond1
    myDummy.cond2 <= cond2
    myDummy.cond3 <= cond3
    myDummy.cond4 <= cond4

    condResult <= cat(myDummy.condResult[2], cat(myDummy.condResult[1], myDummy.condResult[0]))
