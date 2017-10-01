# array, tuple, vector

  https://en.wikipedia.org/wiki/Tuple
  https://en.wikipedia.org/wiki/Array_data_type
  https://en.wikipedia.org/wiki/Row_(database)
    
new1 x:0 : Mem = (s = Mem 8; Mem.set s x; Cast.any s)
new2 x:0 y:1 : 0, 1 = (s = Mem 16; Mem.set s x; Mem.set s+8 y; Cast.any s)
new3 x:0 y:1 z:2 : 0, 1, 2 = (s = Mem 24; Mem.set s x; Mem.set s+8 y; Mem.set s+16 z; Cast.any s)
new4 x:0 y:1 z:2 w:3 : 0, 1, 2, 3 = (s = Mem 32; Mem.set s x; Mem.set s+8 y; Mem.set s+16 z; Mem.set s+24 w; Cast.any s)
new5 x:0 y:1 z:2 w:3 u:4 : 0, 1, 2, 3, 4 = (s = Mem 40; Mem.set s x; Mem.set s+8 y; Mem.set s+16 z; Mem.set s+24 w; Mem.set s+32 u; Cast.any s)
new6 x:0 y:1 z:2 w:3 u:4 v:5 : 0, 1, 2, 3, 4, 5 = (s = Mem 48; Mem.set s x; Mem.set s+8 y; Mem.set s+16 z; Mem.set s+24 w; Mem.set s+32 u; Mem.set s+40 v; Cast.any s)
new7 x:0 y:1 z:2 w:3 u:4 v:5 p:6 : 0, 1, 2, 3, 4, 5, 6 = (s = Mem 56; Mem.set s x; Mem.set s+8 y; Mem.set s+16 z; Mem.set s+24 w; Mem.set s+32 u; Mem.set s+40 v; Mem.set s+48 p; Cast.any s)
new8 x:0 y:1 z:2 w:3 u:4 v:5 p:6 q:7 : 0, 1, 2, 3, 4, 5, 6, 7 = (s = Mem 64; Mem.set s x; Mem.set s+8 y; Mem.set s+16 z; Mem.set s+24 w; Mem.set s+32 u; Mem.set s+40 v; Mem.set s+48 p; Mem.set s+56 q;  Cast.any s)

getx s:Mem : 0 = Mem.get s . Cast.any
get s:0^ i:N : 1 = Mem.get (s.Mem.of + i*8) . Cast.any

mem s:0^ : Mem = Cast.any s

get0 s:0^ : 0 = Mem.get s.Mem.of . Cast.any
get1 s:0^ : 1 = Mem.get (s.Mem.of + 1*8) . Cast.any
get2 s:0^ : 2 = Mem.get (s.Mem.of + 2*8) . Cast.any
get3 s:0^ : 3 = Mem.get (s.Mem.of + 3*8) . Cast.any
get4 s:0^ : 4 = Mem.get (s.Mem.of + 4*8) . Cast.any
get5 s:0^ : 5 = Mem.get (s.Mem.of + 5*8) . Cast.any

at0 s:0,1 : 0 = Mem.get s.Mem.of . Cast.any
at1 s:0,1 : 1 = Mem.get (s.Mem.of + 1*8) . Cast.any
at2 s:0,1,2 : 2 = Mem.get (s.Mem.of + 2*8) . Cast.any
at3 s:0,1,2,3 : 3 = Mem.get (s.Mem.of + 3*8) . Cast.any
at4 s:0,1,2,3,4 : 4 = Mem.get (s.Mem.of + 4*8) . Cast.any
at5 s:0,1,2,3,4,5 : 5 = Mem.get (s.Mem.of + 5*8) . Cast.any

name n:N i:N : Term = Name2 'Row' ('at' + n.N.str + '_' + i.N.str)

Fact (at0 13,'foo' == 13) 
Fact (at1 13,'foo' == 'foo')

at2_0 s:0,1 : 0 = Mem.get s.Mem.of . Cast.any
at3_0 s:0,1,2 : 0 = Mem.get s.Mem.of . Cast.any
at4_0 s:0,1,2,3 : 0 = Mem.get s.Mem.of . Cast.any
at5_0 s:0,1,2,3,4 : 0 = Mem.get s.Mem.of . Cast.any
at6_0 s:0,1,2,3,4,5 : 0 = Mem.get s.Mem.of . Cast.any

at2_1 s:0,1 : 1 = Mem.get (s.Mem.of + 1*8) . Cast.any
at3_1 s:0,1,2 : 1 = Mem.get (s.Mem.of + 1*8) . Cast.any
at4_1 s:0,1,2,3 : 1 = Mem.get (s.Mem.of + 1*8) . Cast.any
at5_1 s:0,1,2,3,4 : 1 = Mem.get (s.Mem.of + 1*8) . Cast.any
at6_1 s:0,1,2,3,4,5 : 1 = Mem.get (s.Mem.of + 1*8) . Cast.any

at3_2 s:0,1,2 : 2 = Mem.get (s.Mem.of + 2*8) . Cast.any
at4_2 s:0,1,2,3 : 2 = Mem.get (s.Mem.of + 2*8) . Cast.any
at5_2 s:0,1,2,3,4 : 2 = Mem.get (s.Mem.of + 2*8) . Cast.any
at6_2 s:0,1,2,3,4,5 : 2 = Mem.get (s.Mem.of + 2*8) . Cast.any

at4_3 s:0,1,2,3 : 3 = Mem.get (s.Mem.of + 3*8) . Cast.any
at5_3 s:0,1,2,3,4 : 3 = Mem.get (s.Mem.of + 3*8) . Cast.any
at6_3 s:0,1,2,3,4,5 : 3 = Mem.get (s.Mem.of + 3*8) . Cast.any

at5_4 s:0,1,2,3,4 : 4 = Mem.get (s.Mem.of + 4*8) . Cast.any
at6_4 s:0,1,2,3,4,5 : 4 = Mem.get (s.Mem.of + 4*8) . Cast.any

at6_5 s:0,1,2,3,4,5 : 5 = Mem.get (s.Mem.of + 5*8) . Cast.any

main n:N : Mem = Mem 8*n

at s:Mem i:N : N = Mem.get (s + Box.size*i)
atx s:0^ i:N : 0 = Mem.get (s.mem + Box.size*i) . Cast.any
Fact (s = 13,42 . Cast.any; at s 1 == 42)
Fact (s = 13,42 : N^; atx s 1 == 42) 

set s:Mem i:N x:Mem = Mem.set (s + 8*i) x
setx s:0^ i:N x:N = Mem.set (s.mem + 8*i) x

of_atx s:*0 r:0^ = s & (Mem.set r.mem s.List.head; of_atx s.List.tail (off_by r 8))
of_at s:*0 r:Mem = s & (Mem.set r s.List.head; of_at s.List.tail r+8)

of s:*0 : 1 = (r = Mem 8*s.List.size . Cast.any; of_at s r; Cast.any r) # [x,..]  -> (x,..)

Fact (s = new2 2 3; [s.at2_0, s.at2_1] == [2, 3])
Fact (s = new3 2 3 5; [s.at0, s.at1, s.at2] == [2, 3, 5])
Fact (s = new4 2 3 5 8; [s.at0, s.at1, s.at2, s.at3] == [2, 3, 5, 8])
Fact (s = new5 2 3 5 8 13; [s.at0, s.at1, s.at2, s.at3, s.at4] == [2, 3, 5, 8, 13])
Fact (s = new6 2 3 5 8 13 21; [s.at0, s.at1, s.at2, s.at3, s.at4, s.at5] == [2, 3, 5, 8, 13, 21])

byte : Type ? N =
  _, N0? 1
  _, N1? 2
  _, N2? 4
  ? 8

rank : Type ? N =
  _, N0? 0
  _, N1? 1
  _, N2? 2
  ? 3

bytes s:Types : N = List.map_sum_nat s byte
Fact (byte 'N0'.Type.of_str2 == 1)
Fact (byte 'N0,N'.Type.of_str2 == 8) # todo boxed, 9
Fact (byte 'N0,(N1,N2),N,B'.Type.of_str2 == 8) # unboxed, 23

of_exp_set spot:Spot name:Exp base:N exp:Exp type:Type : N, Exp =
  mem = spot, Tree [(spot, Name2 'N' 'add'), name, (spot, Nat base)]
  base + byte type, (spot, Tree [(spot, Name2 'Mem' 'set'), mem, exp])

of_exp3 exp:Exp : Exp =                                               # 64-bit
  spot = Exp.spot exp
  spot, Row_ [(spot, Nat 3), exp]

of_exp2 exp:Exp type:Type : Exp =
  spot = Exp.spot exp
  spot, Row_ [(spot, Nat type.rank), exp]

of_exps2 spot:Spot exps:Exps types:Types : Exp =
  spot, Tree ((spot, Name 'Row'), ((spot, Nat types.bytes), List.map2 exps types of_exp2))

of_exps3 spot:Spot exps:Exps : Exp =
  spot, Tree ((spot, Name 'Row'), ((spot, Nat (8 * exps.List.size)), List.map exps of_exp3))

#Fact ((0d:N0, 02a:N1, 0a:N0).0 == 0a002a0d) # fixme

off s:Mem : Mem = Mem.off s Box.size
offx s:0^ : 0^ = Mem.off s.mem Box.size . Cast.any
off_by s:0^ i:N : 0^ = Mem.off s.mem i*Box.size . Cast.any

for f:0?1 s:Mem n:N = n & (Mem.set s s.Mem.get.f; for f s.off n-1) # lenient return type, s[i] = f s[i]
forx f:0?1 s:0^ n:N = n & (Mem.set s.mem s.get0.f; forx f s.offx n-1) # lenient return type, s[i] = f s[i]
Fact (s = 13,42; for N.tick s.Mem.of 2; s.0 == 14 & s.1 == 43)

do f:0?1 s:Mem n:N = n & (s.getx.f; do f s.off n-1)
dox f:0?1 s:0^ n:N = n & (s.get0.f; dox f s.offx n-1)
Fact (x = %0; do (Ref.add x) (row3 2,3,5) 3; !x == 10)

eq r:Mem s:Mem n:N : B = Mem.eq r s n*Box.size
eqx r:0^ s:0^ n:N : B = Mem.eq r.mem s.mem n*Box.size
mem_eq3 r:0,1,2 s:Mem : B = eq r.Mem.of s 3
mem_eq5 r:0,1,2,3,4 s:Mem : B = eq r.Mem.of s 5

eq_by3 eq0:0?0?B eq1:1?1?B eq2:2?2?B a,b,c:0,1,2 x,y,z:0,1,2 : B = eq0 a x & eq1 b y & eq2 c z
ne_by3 ne0:0?0?B ne1:1?1?B ne2:2?2?B a,b,c:0,1,2 x,y,z:0,1,2 : B = ne0 a x | ne1 b y | ne2 c z
Fact (5,7,13 . eq_by3 N.eq N.eq N.eq 5,7,13)
Fact !(5,7,13 . eq_by3 N.eq N.eq N.eq 5,7,42)
Fact ('foo',5,7 . eq_by3 S.eq N.eq N.eq 'foo',5,7)
Fact !('foo',5,7 . eq_by3 S.eq N.eq N.eq 'foo',42,7)

eq_by4 eq0:0?0?B eq1:1?1?B eq2:2?2?B eq3:3?3?B a,b,c,d:0,1,2,3 x,y,z,w:0,1,2,3 : B = eq0 a x & eq1 b y & eq2 c z & eq3 d w
eq_by5 eq0:0?0?B eq1:1?1?B eq2:2?2?B eq3:3?3?B eq4:4?4?B a,b,c,d,e:0,1,2,3,4 x,y,z,w,u:0,1,2,3,4 : B = eq0 a x & eq1 b y & eq2 c z & eq3 d w & eq4 e u
eq_by6 eq0:0?0?B eq1:1?1?B eq2:2?2?B eq3:3?3?B eq4:4?4?B eq5:5?5?B a,b,c,d,e,f:0,1,2,3,4,5 x,y,z,w,u,v:0,1,2,3,4,5 : B = eq0 a x & eq1 b y & eq2 c z & eq3 d w & eq4 e u & eq5 f v

# FIXME Rewrite.NAME_BUG
str_by3 f:0?S g:1?S h_:2?S x,y,z:0,1,2 : S = f x + ',' + g y + ',' + h_ z 
Fact (str_by3 N.str S.str N.str 13,'foo',42 == '13,foo,42')
Fact (str_by3 N.str S.str (Pair.str_by S.str N.str) 13,'foo',('bar',42) == '13,foo,bar,42')

str_by4 f:0?S g:1?S h_:2?S i_:3?S x,y,z,w:0,1,2,3 : S = f x + ',' + g y + ',' + h_ z + ',' + i_ w
str_by5 f:0?S g:1?S h_:2?S i_:3?S j_:4?S x,y,z,w,v:0,1,2,3,4 : S = f x + ',' + g y + ',' + h_ z + ',' + i_ w + ',' + j_ v 
str_by6 f:0?S g:1?S h_:2?S i_:3?S j_:4?S k_:5?S x,y,z,w,v,p:0,1,2,3,4,5 : S = f x + ',' + g y + ',' + h_ z + ',' + i_ w + ',' + j_ v + ',' + k_ p

Fact (5,7,13 == 5,7,13)
Fact !(5,7,13 == 5,7,42)
Fact ('foo',5,7 == 'foo',5,7)
Fact ('foo',5,7 != 'bar',5,7)
Fact (5,7,13,'foo',21 == 5,7,13,'foo',21)
Fact (5,7,13,'foo',21,'bar' == 5,7,13,'foo',21,'bar')

Fact (str 'foo',42,'bar' == 'foo,42,bar')
Fact (str 2,3,5,7 == '2,3,5,7')
Fact (str 'foo',5,'bar',7,13 == 'foo,5,bar,7,13')
Fact (str 'foo',5,'bar',7,13,21 == 'foo,5,bar,7,13,21')

init n:N : Mem, 0?Z =
  s = main n
  i = %0
  s, (_ s_:Mem n_:N i_:%N x:0 = (!i_ < n_ | Fail.fill '$s - $h expect $n but $n' [$Fun, s_, n_, !i_]; set s_ !i_ x; Ref.add1 i_)) s n i 
  #s, (_ s_:Mem n_:N i_:%N x:0 = (!i_ < n_ | (Mem.get0 0.Cast.any; Fail.fill '$s - $h expect $n but $n' [$Fun, s_, n_, !i_]); set s_ !i_ x; Ref.add1 i_)) s n i 
Fact (s, f = init 2; f 13; f 42; at s 0 == 13 & at s 1 == 42)
Fact (Job.err ?(s, f = init 1; f 0; f 0; 0) . Regex "Row.f.* - .* expect 1 but 1\.") 
  
fold f:0?1?1 a:1 s:Mem n:N : 1 = (x = f (at s n-1) a; n > 1 & fold f x s n-1 | x)
foldx f:0?1?1 a:1 s:0^ n:N : 1 = (x = f (atx s n-1) a; n > 1 & foldx f x s n-1 | x)
Fact (fold N.add 0 (row3 2,3,5) 3 == 10)
Fact (fold List.main 0 (row3 2,3,5) 3 == [2, 3, 5])

sum f:1?0?1 a:1 s:Mem n:N : 1 = n & sum f (f a s.getx) s.off n-1 | a
sumx f:1?0?1 a:1 s:0^ n:N : 1 = n & sumx f (f a s.get0) s.offx n-1 | a
Fact (sum N.add 0 (row3 2,3,5) 3 == 10)

row3 s:0,0,0 : Mem = s.Cast.any
row3x s:0,0,0 : 0^ = s.Cast.any
