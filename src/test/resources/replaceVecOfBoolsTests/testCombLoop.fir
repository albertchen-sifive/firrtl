circuit testCombLoop:
  module MyModule:
    input boolVec: UInt<1>[8]
    input dummyVec: UInt<1>[1]
    input select: UInt<3>
    input setVal: UInt<1>
    output selected: UInt<1>
    output outVec: UInt<1>[8]
    output copy: UInt<1>[8]

    wire dummy: UInt<1>
    copy <= boolVec
    selected <= boolVec[select]
    dummy <= boolVec[boolVec[select]]
    copy[5] <= boolVec[select]
    copy[1] <= copy[5]
    copy[5] <= setVal
    copy[select] <= boolVec[select]

    dummy <= dummy

    outVec <= boolVec
    outVec[0] <= setVal
  
  module testCombLoop:
    input boolVec: UInt<8>
    input dummyVec: UInt<1>
    input select: UInt<3>
    input setVal: UInt<1>
    output selected: UInt<1>
    output outVec: UInt<8>
    output copy: UInt<8>

    inst myinstance of MyModule
    myinstance.boolVec[0] <= bits(boolVec,0, 0)
    myinstance.boolVec[1] <= bits(boolVec,1, 1)
    myinstance.boolVec[2] <= bits(boolVec,2, 2)
    myinstance.boolVec[3] <= bits(boolVec,3, 3)
    myinstance.boolVec[4] <= bits(boolVec,4, 4)
    myinstance.boolVec[5] <= bits(boolVec,5, 5)
    myinstance.boolVec[6] <= bits(boolVec,6, 6)
    myinstance.boolVec[7] <= bits(boolVec,7, 7)

    
    myinstance.dummyVec[0] <= dummyVec

    myinstance.select <= select
    myinstance.setVal <= setVal
    selected <= myinstance.selected
    outVec <= cat(myinstance.outVec[7],cat(myinstance.outVec[6],cat(myinstance.outVec[5],cat(myinstance.outVec[4],cat(myinstance.outVec[3],cat(myinstance.outVec[2],cat(myinstance.outVec[1], myinstance.outVec[0])))))))
    copy <= cat(myinstance.copy[7],cat(myinstance.copy[6],cat(myinstance.copy[5],cat(myinstance.copy[4],cat(myinstance.copy[3],cat(myinstance.copy[2],cat(myinstance.copy[1], myinstance.copy[0])))))))
