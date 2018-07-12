circuit testNestedModules:
  module Dummy:
    input boolVec: UInt<1>[8]
    input select: UInt<3>
    output selected: UInt<1>
    output badVecOut: UInt<1>[2]

    selected <= boolVec[select]

    wire badVec: UInt<1>[2]
    badVec[0] <= bits(select, 0, 0)
    ;badVec[1] <= badVec[0]
    ;badVec[0] <= bits(select, 1, 1)
    badVec[1] <= bits(select, 1, 1)
    badVecOut <= badVec

  module testNestedModules:
    input boolVec: UInt<1>[8]
    input select: UInt<3>
    output topSelected: UInt<1>
    output dummySelected: UInt<1>
    output badVec: UInt<1>[2]

    topSelected <= boolVec[select]

    inst myDummy of Dummy
    myDummy.boolVec <= boolVec
    myDummy.boolVec[0] <= boolVec[5]
    myDummy.select <= select
    dummySelected <= myDummy.selected

    badVec <= myDummy.badVecOut
