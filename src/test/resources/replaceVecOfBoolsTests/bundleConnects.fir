circuit bundleConnects:
  module bundleConnects:
    input in: UInt<2>

    output out_a_0: UInt<1>
    output out_b_c_f_0: UInt<1>
    output out_b_c_f_1: UInt<1>
    output out_b_c_f_2: UInt<1>
    output out_b_c_f_3: UInt<1>
    output out_b_e_0: UInt<1>
    output out_b_e_1: UInt<1>

    wire bundle1: {a: UInt<1>[1], b: {c: {d: UInt<1>[4]}, e: UInt<1>[2]}}
    wire bundle2: {a: UInt<1>[1], b: {c: {f: UInt<1>[4]}, e: UInt<1>[2]}}
    wire bundle3: {a: UInt<1>[1], b: {c: {f: UInt<1>[4]}, e: UInt<1>[2]}}

    bundle1.b.e[0] <= bits(in, 0, 0)
    bundle1.b.e[1] <= bits(in, 1, 1)
    bundle1.b.c.d[0] <= bits(in, 0, 0)
    bundle1.b.c.d[1] <= bits(in, 1, 1)
    bundle1.b.c.d[2] <= and(bits(in, 0, 0), bits(in, 1, 1))
    bundle1.b.c.d[3] <= or(bits(in, 0, 0), bits(in, 1, 1))
    bundle1.a[0] <= xor(bits(in, 0, 0), bits(in, 1, 1))

    bundle2 <- bundle1

    bundle2.b.c.f[0] <= bundle1.b.c.d[0]
    bundle2.b.c.f[1] <= bundle1.b.c.d[1]
    bundle2.b.c.f[2] <= bundle1.b.c.d[2]
    bundle2.b.c.f[3] <= bundle1.b.c.d[3]

    bundle3 <= bundle2

    out_a_0 <= bundle3.a[0]
    out_b_c_f_0 <= bundle3.b.c.f[0]
    out_b_c_f_1 <= bundle3.b.c.f[1]
    out_b_c_f_2 <= bundle3.b.c.f[2]
    out_b_c_f_3 <= bundle3.b.c.f[3]
    out_b_e_0 <= bundle3.b.e[0]
    out_b_e_1 <= bundle3.b.e[1]
