# packed data, inlined

  https://en.wikipedia.org/wiki/Struct_(C_programming_language)

byte : Type ? N =
  _, N0? 1
  _, N1? 2
  _, N2? 4
  _, Row s? bytes s # inline, unbox, unpack
  ? 8

bytes s:Types : N = List.map_sum_nat s byte

exps_of_exp : Exp, Type? Exps =
  (_, Tree (_, (_, exps))), (_, Row _)? exps # (Row 32 (3,74) (3,125) (3,25) (3,121))
  exp, type? [(Exp.spot exp, Row_ [(Exp.spot exp, Nat type.Row.rank), exp])]

exps_of_exps exps:Exps types:Types : Exps = List.map_pair exps types exps_of_exp . List.adds

of_exps spot:Spot exps:Exps types:Types : Exp =
  spot, Tree ((spot, Name 'Box'), ((spot, Nat types.bytes), exps_of_exps exps types))

size = 8                                # the number of bytes for a 64-bit integer or reference
