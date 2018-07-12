circuit testConditional3:
  module Dummy:
    input boolVec: UInt<1>[8]
    input select: UInt<3>
    output selected: UInt<1>

    when bits(select, 1, 1):
      wire whenVec : UInt<1>[2]
      selected <= boolVec[7]
      selected <= boolVec[select]
      whenVec[0] <= boolVec[2]
      whenVec[1] <= boolVec[3]
    else:
      selected <= or(whenVec[0], boolVec[select])
    whenVec[0] <= boolVec[4]
    whenVec[1] <= boolVec[5]
  module Asdf:
    input boolVec: UInt<1>[8]
    input select: UInt<3>
    output topSelected: UInt<1>
    output dummySelected: UInt<1>

    topSelected <= boolVec[select]

    inst myDummy of Dummy
    myDummy.boolVec <= boolVec
    myDummy.boolVec[0] <= boolVec[5]
    myDummy.select <= select
    dummySelected <= myDummy.selected
  module testConditional3:
    input boolVec: UInt<8>
    input select: UInt<3>
    output topSelected: UInt<1>
    output dummySelected: UInt<1>

    inst myDummy of Asdf
    myDummy.select <= select
    myDummy.boolVec[0] <= bits(boolVec, 0, 0)
    myDummy.boolVec[1] <= bits(boolVec, 1, 1)
    myDummy.boolVec[2] <= bits(boolVec, 2, 2)
    myDummy.boolVec[3] <= bits(boolVec, 3, 3)
    myDummy.boolVec[4] <= bits(boolVec, 4, 4)
    myDummy.boolVec[5] <= bits(boolVec, 5, 5)
    myDummy.boolVec[6] <= bits(boolVec, 6, 6)
    myDummy.boolVec[7] <= bits(boolVec, 7, 7)

    topSelected <= myDummy.topSelected
    dummySelected <= myDummy.dummySelected
