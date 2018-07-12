circuit testRegInit:
  module inner:
    output out : {a : UInt<1>, b : {c : UInt<1>[2], d : UInt<1>}}

    out.a <= UInt<1>("h0")
    out.b.c[0] <= UInt<1>("h0")
    out.b.c[1] <= out.b.c[0]
    out.b.d <= UInt<1>("h0")

  module testRegInit:
    input clock : Clock @[:tlspi.fir@3.4]
    input reset : UInt<1> @[:tlspi.fir@4.4]
    output out : {a : UInt<1>, b : {c : UInt<2>, d : UInt<1>}}

    inst resetVal of inner
    reg bundleReg : {a : UInt<1>, b : {c : UInt<1>[2], d : UInt<1>}}, clock with :
      reset => (reset, resetVal.out)

    out.a <= bundleReg.a
    out.b.c <= cat(bundleReg.b.c[0], bundleReg.b.c[1])
    out.b.d <= bundleReg.b.d
