# two data, product, cons

  https://en.wikipedia.org/wiki/Product_type
  https://en.wikipedia.org/wiki/Cons

cast x:0 : 1, 2 = Cast.any x

main x:0 y:1 : 0, 1 = (s = Mem 16; Mem.set s x; Mem.set s+8 y; Cast.any s)

at0 x,_:0,1 : 0 = x

at1 _,y:0,1 : 1 = y

Fact (13,'foo' == 13,'foo')
Fact !(13,'foo' == 13,'bar')
Fact (N.max3,2 == N.max3,2)

eq0 f:0?0?B y:0 x,_:0,1 : B = f x y
Fact (eq0 N.eq 13 13,'foo')

eq1 f:1?1?B y:1 _,x:0,1 : B = f x y
Fact (eq1 S.eq 'foo' 13,'foo')

str_by f:0?S g:1?S x,y:0,1 : S = f x + ',' + g y
#str _f:0?S _g:1?S x,y:0,1 : S = _f x + ',' + _g y # Pair.str in Type.of_exp_do 
Fact (str_by R.str N.str 3.14,42 == '3.14,42')
Fact (str 13,42 == '13,42')
Fact (str (3,13),42 == '3,13,42') # (3,13),42
Fact (str 'foo','bar' == 'foo,bar')
Fact (str 42,'foo' == '42,foo')
Fact (str 'foo',42 == 'foo,42')

str2 x:S y:S : S = x + ',' + y
Fact (str2 '3.14' '42' == '3.14,42')
Fact (str N.max3,'foo' == '18446744073709551615,foo')

map f:0?1 x,y:0,0 : 1,1 = f x, f y
Fact (map N.tick 13,42 == 14,43)

map1 f:1?2 x,y:0,1 : 0,2 = x, f y
Fact (map1 N.tick 13,42 == 13,43)

eq_by eq0:0?0?B eq1:1?1?B x,y:0,1 z,w:0,1 : B = eq0 x z & eq1 y w
Fact (eq_by N.eq S.eq 13,'foo' 13,'foo')
Fact !(eq_by N.eq S.eq 13,'foo' 13,'bar')
Fact (eq_by N.mod2 S.eq 13,'foo' 43,'foo')
Fact (13,'foo' ==  13,'foo')
Fact !(13,'foo' == 13,'bar')

ne_by ne0:0?0?B ne1:1?1?B x,y:0,1 z,w:0,1 : B = ne0 x z | ne1 y w
Fact !(ne_by N.ne S.ne 13,'foo' 13,'foo')
Fact (ne_by N.ne S.ne 13,'foo' 13,'bar')
Fact !(13,'foo' != 13,'foo')
Fact (13,'foo' != 13,'bar')
Fact !(ne_by N.mod2_ne S.ne 13,'foo' 43,'foo')
