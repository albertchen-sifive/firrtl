circuit testNestedModules:
  module Dummy:
    input boolVec: UInt<1>[8]
    input select: UInt<3>
    output selected: UInt<1>
    output badVecOut: UInt<1>[2]

    selected <= boolVec[select]

    wire badVec: UInt<1>[2]
    badVec[0] <= bits(select, 0, 0)
    badVec[1] <= bits(select, 1, 1)
    badVecOut <= badVec

  module testNestedModules:
    input boolVec: UInt<8>
    input select: UInt<3>
    output topSelected: UInt<1>
    output dummySelected: UInt<1>
    output badVec: UInt<2>

    topSelected <= bits(dshr(boolVec, select), 0, 0)

    inst myDummy of Dummy
    myDummy.boolVec[0] <= bits(boolVec, 0, 0)
    myDummy.boolVec[1] <= bits(boolVec, 1, 1)
    myDummy.boolVec[2] <= bits(boolVec, 2, 2)
    myDummy.boolVec[3] <= bits(boolVec, 3, 3)
    myDummy.boolVec[4] <= bits(boolVec, 4, 4)
    myDummy.boolVec[5] <= bits(boolVec, 5, 5)
    myDummy.boolVec[6] <= bits(boolVec, 6, 6)
    myDummy.boolVec[7] <= bits(boolVec, 7, 7)
    myDummy.select <= select
    dummySelected <= myDummy.selected

    badVec <= cat(myDummy.badVecOut[1], myDummy.badVecOut[0])
