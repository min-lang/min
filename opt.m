# optional, nullable, some, pointed

  https://en.wikipedia.org/wiki/Option_type
  https://en.wikipedia.org/wiki/Nullable_type  
  http://en.wikipedia.org/wiki/Pointed_set

# do not use [Cast.any x] since [Opt.un x:B] != 0
of x:B : !Z = x & 0.N.opt.Cast.any
Fact !((of 0) . bit)
Fact ((of 1) . bit)

to x:!N : N = Cast.opt_nat x

one x:!0 : 0 = Cast.any x

nil _ : !0 = Cast.any 0

bit x:!0 : B = Cast.any x
Fact !(bit 0)
Fact (bit (N.opt 0))
Fact (bit (N.opt \a))

must x:!0 : 0 = Cast.any x # check 0 is not N
#Fact (must 3.N.opt == 3) # FIXME should be type error
Fact (must 'foo' == 'foo')

# https://en.wikipedia.org/wiki/Null_coalescing_operator default
or x:!N y:N : N = x & N.must x | y
Fact (or 1.N.opt 7 == 1)
Fact (or 0 7 == 7)

max x:!N y:N : N = x & N.max x.N.must y | y
Fact (max 4.N.opt 2 == 4)
Fact (max 4.N.opt 7 == 7)
Fact (max 0 7 == 7)

min x:!N y:N : N = x & N.min x.N.must y | y
Fact (min 4.N.opt 2 == 2)
Fact (min 4.N.opt 7 == 4)
Fact (min 0 7 == 7)

out x:!S = Out (x | '!!')

line x:S = (out x; Out.char 0a . Z)

map2 must:!0?0 x:!0 f:0?1?1 y:1 : 1 = x & f x.must y | y
Fact (map2 N.must 0 N.add 5 == 5)
Fact (map2 N.must 3.N.opt N.add 5 == 8)

do x:!0 f:0?1 : B = x & f x

map x:!0 f:0?1 : !1 = x & f x
Fact (map 0 (_ x:N : N = x + 3) == 0)
Fact (map 7.N.opt (_ x:N : N = x + 3) == 10.N.opt)

main0 x:!0 : 0 = x | Fail '0'

get_nat x:!N error:S : N = x & N.must x | Fail error

get x:!0 error:S : 0 = x | Fail error

seq x:!0 : *0 = x & [x]
Fact (seq 0 == 0) 
Fact (List.all2 (seq 0.N.opt) [0.N.opt] N.eq)

# support only ptr - fixme - proper encoding for opt to support both nat/pointer 
add x:!0 s:*0 : *0 = x & x,s | s 
Fact (List.all2 (add 0 [42]) [42] N.eq)
Fact (List.all2 (add 13 [42]) [13, 42] N.eq)
Fact (List.all2 (add 0 ['bar']) ['bar'] S.eq)
Fact (List.all2 (add 'foo' ['bar']) ['foo', 'bar'] S.eq)

bit x:!0 : B = Cast.any x
Fact (bit 'foo')
Fact !(bit 0)

at0 x:!(0,1) : !0 = x & x.0
Fact (at0 0 == 0)
Fact (at0 13,42 == 13)

eq_by eq:0?0?B x:!0 y:!0 : B = (!x.bit & !y.bit) | (x & y & eq x.one y.one)
Fact (eq_by N.eq 42 42)
Fact !(eq_by N.eq 42 0)
Fact !(eq_by N.eq 13 42)
Fact !(eq_by S.eq 'foo' 0)
Fact (eq_by (Pair.eq_by S.eq N.eq) 'foo',13 'foo',13)
Fact (eq_by (Pair.eq_by N.eq S.eq) 13,'foo' 13,'foo')
Fact !(eq_by (Pair.eq_by N.eq S.eq) 13,'foo' 42,'bar')

eq0 x:!Z y:!Z : B = N.eq x.Cast.any y.Cast.any 

any x:0 : !0 = Cast.any x

str_by0 f:0?S x:!0 : S = x & f x | '0'
Fact (str_by0 N.str 0 == '0')

str_by must:!0?0 f:0?S x:!0 : S = x & f x.must | '0'
Fact (str_by N.must N.str 0 == '0')
Fact (str_by N.must N.str 1.N.opt == '1')
Fact (str_by N.must N.str 1.C.opt == '1')
Fact (str 'foo':!S == 'foo')
Fact (str 'foo'.any == 'foo')
Fact (str 1.N.opt == '1')
Fact (str 1.C.opt == "\01")
