circuit testVecBundle:
  module MyModule:
    input inbundle: {boolVec: UInt<1>[8]}[3]
    input select1: UInt<3>
    input select2: UInt<3>
    input setVal: UInt<1>
    output selected: UInt<1>

    node boolVec = inbundle[select1].boolVec
    selected <= boolVec[select2]

  module testVecBundle:
    input boolVec: UInt<8>[3]
    input select1: UInt<3>
    input select2: UInt<3>
    input setVal: UInt<1>
    output selected: UInt<1>

    inst myinstance of MyModule
    myinstance.inbundle[0].boolVec[0] <= bits(boolVec[0],0, 0)
    myinstance.inbundle[0].boolVec[1] <= bits(boolVec[0],1, 1)
    myinstance.inbundle[0].boolVec[2] <= bits(boolVec[0],2, 2)
    myinstance.inbundle[0].boolVec[3] <= bits(boolVec[0],3, 3)
    myinstance.inbundle[0].boolVec[4] <= bits(boolVec[0],4, 4)
    myinstance.inbundle[0].boolVec[5] <= bits(boolVec[0],5, 5)
    myinstance.inbundle[0].boolVec[6] <= bits(boolVec[0],6, 6)
    myinstance.inbundle[0].boolVec[7] <= bits(boolVec[0],7, 7)
                                                        
    myinstance.inbundle[1].boolVec[0] <= bits(boolVec[1],0, 0)
    myinstance.inbundle[1].boolVec[1] <= bits(boolVec[1],1, 1)
    myinstance.inbundle[1].boolVec[2] <= bits(boolVec[1],2, 2)
    myinstance.inbundle[1].boolVec[3] <= bits(boolVec[1],3, 3)
    myinstance.inbundle[1].boolVec[4] <= bits(boolVec[1],4, 4)
    myinstance.inbundle[1].boolVec[5] <= bits(boolVec[1],5, 5)
    myinstance.inbundle[1].boolVec[6] <= bits(boolVec[1],6, 6)
    myinstance.inbundle[1].boolVec[7] <= bits(boolVec[1],7, 7)
                                                        
    myinstance.inbundle[2].boolVec[0] <= bits(boolVec[2],0, 0)
    myinstance.inbundle[2].boolVec[1] <= bits(boolVec[2],1, 1)
    myinstance.inbundle[2].boolVec[2] <= bits(boolVec[2],2, 2)
    myinstance.inbundle[2].boolVec[3] <= bits(boolVec[2],3, 3)
    myinstance.inbundle[2].boolVec[4] <= bits(boolVec[2],4, 4)
    myinstance.inbundle[2].boolVec[5] <= bits(boolVec[2],5, 5)
    myinstance.inbundle[2].boolVec[6] <= bits(boolVec[2],6, 6)
    myinstance.inbundle[2].boolVec[7] <= bits(boolVec[2],7, 7)

    
    myinstance.select1 <= select1
    myinstance.select2 <= select2
    myinstance.setVal <= setVal
    selected <= myinstance.selected
