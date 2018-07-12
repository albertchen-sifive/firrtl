circuit testCombLoop3:
  module testCombLoop3:
    input in: UInt<2>
    output out: UInt<2>

    wire vec: UInt<1>[2]
    vec[0] <= bits(in, 0, 0)
    vec[1] <= bits(in, 1, 1)

    when vec[0]:
        vec[1] <= bits(in, 0, 0)

    out <= cat(vec[1], vec[0])
