circuit invalidated:
  module invalidated:
    input clock : Clock
    input reset : UInt<1>
    input refill_done : UInt<1>
    input in : UInt<1>
    input s1_clk_en : UInt<1>
    input inv_cond_0 : UInt<1>
    input inv_cond_1 : UInt<1>
    input inv_cond_2 : UInt<1>
    input in624_0 : UInt<1>
    input in624_1 : UInt<1>
    output out : UInt<1>

    wire invalidate : UInt<1>
    invalidate <= UInt<1>("h0")
    reg invalidated : UInt<1>, clock with : (reset => (reset, UInt<1>("h00")))@[ICache.scala 140:24]
    reg refill_valid : UInt<1>, clock with : (reset => (reset, UInt<1>("h00"))) @[ICache.scala 141:29]
    reg send_hint : UInt<1>, clock with : (reset => (reset, UInt<1>("h00"))) @[ICache.scala 142:26]

    node refill_fire = send_hint @[ICache.scala 143:37]

    wire resetvec : UInt<1>[2]
    resetvec[0] <= UInt<1>("h0")
    resetvec[1] <= UInt<1>("h0")
    reg _T_624 : UInt<1>[2], clock  with : (reset => (reset, resetvec))@[Reg.scala 11:16]
    when s1_clk_en : @[Reg.scala 12:19]
      _T_624[0] <= in624_0 @[Reg.scala 12:23]
      _T_624[1] <= in624_1 @[Reg.scala 12:23]
      skip @[Reg.scala 12:19]

    node s2_tag_disparity = neq(cat(_T_624[1], _T_624[0]), UInt<1>("h00")) @[ICache.scala 266:72]
    when s2_tag_disparity : @[ICache.scala 289:39]
      invalidate <= UInt<1>("h01") @[ICache.scala 289:52]
      skip @[ICache.scala 289:39]
    when inv_cond_0 : @[ICache.scala 310:30]
      when inv_cond_1 : @[ICache.scala 314:41]
        when inv_cond_2 : @[ICache.scala 316:65]
          invalidate <= UInt<1>("h01") @[ICache.scala 318:26]

    when invalidate : @[ICache.scala 196:21]
      invalidated <= UInt<1>("h01") @[ICache.scala 198:17]
      skip @[ICache.scala 196:21]

    when refill_valid : @[ICache.scala 413:24]
      invalidated <= UInt<1>("h00") @[ICache.scala 413:38]
      skip @[ICache.scala 413:24]

    when refill_fire : @[ICache.scala 414:22]
      refill_valid <= UInt<1>("h01") @[ICache.scala 414:37]
      skip @[ICache.scala 414:22]
    when refill_done : @[ICache.scala 415:22]
      refill_valid <= UInt<1>("h00") @[ICache.scala 415:37]
      skip @[ICache.scala 415:22]

    out <= invalidated
