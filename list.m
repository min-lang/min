# singly linked list

  *type == List type
  [2, 3, 5, 8] == (2, (3, (5, (8, 0))))

  https://en.wikipedia.org/wiki/List_(abstract_data_type)

main x:0 s:*0 : *0 = Pair.main x s

head x:*0 : 0 = x.Row.at0                                                       # sugar for x.0
Fact ([13, 42].head == 13)
Fact ([13, 42].0 == 13)

tail x:*0 : *0 = x.Row.at1
Fact ([13, 42].tail.head == 42)
Fact ([13, 42].tail.tail == 0)
Fact ([13, 42].tail == [42])

at_opt n:N s:*0 : !0 = (n & s) & at_opt n-1 s.tail | (s & s.head)
Fact (at_opt 4 [2, 3, 5, 8, 13, 21] == 13)
Fact (at_opt 4 [2, 3] == 0)

at n:N s:*0 : 0 = n & at n-1 s.tail | s.head
Fact (at 4 [2, 3, 5, 8, 13, 21] == 13)

at0 x:*0 : 0 = head x
at1 x:*0 : 0 = x.tail.head
at2 x:*0 : 0 = x.tail.tail.head
at3 x:*0 : 0 = x.tail.tail.tail.head
at4 x:*0 : 0 = x.tail.tail.tail.tail.head
Fact ([2, 3, 5, 8, 13, 21].at4 == 13)

opt_head x:*0 : 0 = Cast.any (x & x.head)
Fact ([].opt_head == 0)
Fact ([2, 3].opt_head == 2)

opt_tail x:*0 : *0 = x & x.tail
Fact ([].opt_tail == 0)
Fact ([2, 3].opt_tail == [3])

opt0 x:*0 : !0 = x.opt_head

opt1 x:*0 : !0 = x.opt_tail.opt_head

opt2 x:*0 : !0 = x.opt_tail.opt_tail.opt_head
Fact ([2, 3].opt2 == 0)
Fact ([2, 3, 5, 8].opt2 == 5)

Fact (at0 [2] == 2)
Fact (!Trap.was_bit | Regex.search 'List.at0' (Job.err (? at0 [])))

rev_add_pure r:*0 s:*0 : *0 = s & rev_add_pure s.head,r s.tail | r
Fact (rev_add_pure [4, 5] [3, 2, 1] == [1, 2, 3, 4, 5])
rev_add_pure r:*0 s:*0 : *0 = s & rev_add_pure s.head,r s.tail | r
rev_add r:*0 s:*0 : *0 = Asm
  mov c sp 16
  mov a sp 8
  @List.rev_add0
  cmp a 0
  j e List.rev_add1
  mov d a 0

  mov r11 16
  call Mem.main_reg
  mov r11 0 d
  mov r11 8 c
  mov c r11

  mov a a 8
  j List.rev_add0
  @List.rev_add1
  mov sp 24 c
  ret
Fact (rev_add [4, 5] [3, 2, 1] == [1, 2, 3, 4, 5])
Fact (rev_add [4, 5] [3, 2, 1] == add [3, 2, 1].rev [4, 5]) # rev_add x y = add y.rev x
Fact (add [1, 2, 3] [4, 5] == rev_add [4, 5] [1, 2, 3].rev) # add x y = rev_add y x.rev

rev s:*0 : *0 = rev_add 0 s
Fact ([2, 3, 5].rev == [5, 3, 2])

# sum, fold, reduce, accumulate, aggregate, compress, or inject
  https://en.wikipedia.org/wiki/Fold_(higher-order_function)
    http://haslab.uminho.pt/alcino/files/tese.pdf Point-free Program Calculation  
  https://en.wikipedia.org/wiki/Iterated_binary_operation
  https://en.wikipedia.org/wiki/Aggregate_function

sum_bad s:*0 f:0?1?1 a:1 : 1 = s & sum_bad s.tail f (f s.head a) | a

sum_right s:*0 f:0?1?1 a:1 : 1 = s & f s.head (sum_right s.tail f a) | a
Fact (sum_right [2, 3, 5] N.add 1 == 11)

# f (f a x) y..
sum_left s:*0 f:1?0?1 a:1 : 1 = s & sum_left s.tail f (f a s.head) | a
Fact (sum_left [2, 3, 5] N.add 1 == 11)

# opt if all elements are aggregated, 0 if early terminated
sum_opt f:1?0?!1 a:1 s:*0 opt:1?!1 must:!1?1 : !1 = s & (x = f a s.head; x & sum_opt f x.must s.tail opt must) | opt a
Fact (sum_opt (_ a:N x:N : !N = x < 5 & N.add a x . N.opt) 0 [2, 3, 4] N.opt N.must == N.opt 9)
Fact (sum_opt (_ a:N x:N : !N = x < 5 & N.add a x . N.opt) 0 [2, 3, 0, 5] N.opt N.must == 0)
Fact (sum_opt (N.gt 7).Seq.bit_opt 0 [] Z.opt Z.must . Opt.bit)
Fact (sum_opt (N.gt 7).Seq.bit_opt 0 [3, 5] Z.opt Z.must . Opt.bit)
Fact !(sum_opt (N.gt 1).Seq.bit_opt 0 [3, 5] Z.opt Z.must . Opt.bit)

# use Either - left/right
sum_key f:1?0?!1 a:1 s:*0 must:!1?1 : B, 1 = s & (b = f a s.head; b & sum_key f b.must s.tail must | 0, a) | 1, a
Fact (sum_key (_ a:N x:N : !N = x < 5 & N.add a x . N.opt) 0 [2, 3, 4] N.must == 1,9)
Fact (sum_key (_ a:N x:N : !N = x < 5 & N.add a x . N.opt) 0 [2, 3, 0, 5] N.must == 0,5)

map_sum_nat s:*0 f:0?N : N = s f . sum_nat
Fact (map_sum_nat [2, 3, 5] N.tick == 13)

sum_nat s:*N : N = s & s.head + sum_nat s.tail
Fact (sum_nat [2, 3, 5] == 10)

sum2 s:*0 f:0?0?0 : 0 = s & (s.tail & f s.head (sum2 s.tail f) | s.head) | Fail $Fun # assume nonempty [s]?

map_with_rev a:0 r:*2 s:*1 f:0?1?0,2 : 0, *2 =
  | s &
    b, x = f a s.head
    map_with_rev b x,r s.tail f
  | a, r
  
map_with a:0 s:*1 f:0?1?0,2 : *2 = map_with_rev a 0 s f . 1 . rev
Fact (map_with 0 [2, 3, 5] (_ a:N x:N : N, N = a + 1, a + x) == [0 + 2, 1 + 3, 2 + 5])

map2_with_rev a:0 p:*3 r:*1 s:*2 f:0?1?2?0,3 : 0, *3 =
  | r & s &
    b, x = f a r.head s.head
    map2_with_rev b x,p r.tail s.tail f
  | a, p

map2_with a:0 r:*1 s:*2 f:0?1?2?0,3 : *3 = map2_with_rev a 0 r s f . 1 . rev
# a? x? y? a + 1, a + x + y
Fact (map2_with 0 [2, 3, 5] [8, 13, 21] (_ a:N x:N y:N : N, N = a + 1, a + x + y) == [0 + 2 + 8, 1 + 3 + 13, 2 + 5 + 21])

size s:*0 : N = s & 1 + size s.tail
Fact (size [2, 3, 5] == 3)

one s:*0 : B = s.bit & ! s.tail.bit
Fact !(one [])
Fact (one [2])
Fact !(one [2, 3])

map_rev s:*0 f:0?1 r:*1 : *1 = s & map_rev s.tail f (f s.head, r) | r
Fact (map_rev [2, 3, 5] (_ x:N : N = x + 3) [] == rev [5, 6, 8])

map s:*0 f:0?1 : *1 = rev (map_rev s f 0)
mapx f:0?1 s:*0 : *1 = map s f
Fact (map [2, 3, 5] (_ x:N : N = x + 3) == [5, 6, 8])

Fact ([0, 2, 3] == [0, 2, 3])
Fact ([0, 2, 3, 5] == [0, 2, 3, 5])

map_at s:*0 f:N?0?1 i:N : *1 = s & f i s.head, map_at s.tail f i+1
Fact ([(0,2)] == [(0,2)])
Fact ([0,2, 1,3] == [0,2, 1,3])
Fact ([1,3, 2,5] == [1,3, 2,5])
Fact ([0,2, 1,3, 2,5] == [0,2, 1,3, 2,5])
Fact (map_at [2, 3, 5] Pair 0 == [0,2, 1,3, 2,5])

map2 r:*0 s:*1 f:0?1?2 : *2 = r & s & f r.head s.head, map2 r.tail s.tail f
Fact (map2 [2, 3, 5] [8, 13, 21] N.add == [10, 16, 26])
Fact (map2 [2, 3, 5] [8, 13] N.add == [10, 16])

map_pair r:*0 s:*1 f:0,1?2 : *2 = r & s & (f r.head,s.head, map_pair r.tail s.tail f)
Fact (map_pair [2, 3, 5] [8, 13, 21] (_ x,y:N,N : N = x + y) == [10, 16, 26])

map3 r:*0 s:*1 p:*2 f:0?1?2?3 : *3 = r & s & p & f r.head s.head p.head, map3 r.tail s.tail p.tail f
Fact (map3 [2, 3, 5] [8, 13, 21] [34, 55] (_ x:N y:N z:N : N = x + y + z) == [44, 71])

do s:*0 f:0?_ = s & (f s.head; do s.tail f)
Fact (x = %0; do [2, 3, 5] (Ref.add x); !x == 10)

do2 r:*0 s:*1 f:0?1?Z = r & s & (f r.head s.head; do2 r.tail s.tail f)
Fact (n = %0; do2 [2, 3, 5] [8, 13] (_ x:N y:N = Ref.add n y-x); !n == 16)

str_prefix s:*S bar:S prefix:B : S = s & (prefix & bar | '') + s.head + (str_prefix s.tail bar 1) | ''

str0 s:*S : S = str_prefix s '' 0
Fact (str0 ['foo', 'bar'] == 'foobar')

str_by f:0?S s:*0 : S = str_prefix (map s f) ' ' 0
Fact (str_by N.str [13,42] == '13 42')
Fact (str_by (str_by N.str) [[2,3], [13,42]] == '2 3 13 42')
Fact (str_by (str_by N.str) [[2,3,5], [13,29,42]] == '2 3 5 13 29 42')
Fact (List.str_by (List.str_by N.str) [[2,3,5], [13,29,42]] == '2 3 5 13 29 42')

sum_n s:*N : N = sum N.add 0 s
Fact (sum_n [2,3,5] == 10)

#str _f:0?S s:*0 : S = str_prefix (map s _f) ' ' 0 # List.str in Type.of_exp_do
Fact (str [[2,3], [13,42]] == '2 3 13 42')
Fact (str [[2,'a'], [13,'b']] == '2,a 13,b')
Fact (str [[2,3,5], [13,19,42]] == '2 3 5 13 19 42')

strx s:*S : S = str_prefix s ' ' 0
Fact (strx ['foo', 'bar'] == 'foo bar')

# same as [str] but uses [,] as divisor
str_pair s:*S : S = str_prefix s ',' 0
Fact (str_pair ['foo', 'bar'] == 'foo,bar')
Fact (str_pair ['foo', 'bar', 'qux'] == 'foo,bar,qux')

str_seq s:*S : S = str_prefix s ', ' 0
Fact (str_seq ['foo', 'bar'] == 'foo, bar')
Fact (str_seq ['foo', 'bar', 'qux'] == 'foo, bar, qux')

str_line s:*S : S = str_prefix s "\." 0
Fact (str_line ['foo', 'bar'] == "foo\.bar")

nat_str s:*N : S = (map s N.str).strx
Fact (nat_str [13, 42] == '13 42')

map_str s:*0 f:0?S : S = (map s f).strx

map_str_pair s:*0 f:0?S : S = (map s f).str_pair

map_str_seq s:*0 f:0?S : S = (map s f).str_seq

map_line s:*0 f:0?S : S = (map s f).str_line

put s:*S = s.strx.Put

log s:*S = s.strx.Log

#info s:*S = s.str.Info

info s:*S = do s Info

nat_put s:*N = s.nat_str.Put

nat_log s:*N = s.nat_str.Log

map_put s:*0 f:0?S = (map_str s f).Put

map_log s:*0 f:0?S = (map_str s f).Log

map_out s:*0 f:0?S = (map_str s f).Out

map_err s:*0 f:0?S = (map_str s f).Err

map_add s:*0 f:0?*1 : *1 = adds (map s f)                                       # map_join

map_opt_rev s:*0 f:0?!1 : *1 = adds_opt_rev (map s f)

add0 x:*0 y:*0 : *0 = x & x.head, add0 x.tail y | y

add_tail_rec x:*0 y:*0 : *0 = rev_add y x.rev 
Fact (add_tail_rec [2, 3] [5, 8] == [2, 3, 5, 8])

add_pure x:*0 y:*0 : *0 = rev_add y x.rev
Fact (add_pure [2, 3] [5, 8] == [2, 3, 5, 8])

add x:*0 y:*0 : *0 = Asm                # 39% faster than add_pure 
  mov a sp 16 # r
  cmp a 0
  j e List.add_1

  mov r11 16
  call Mem.main_reg
  mov sp 24 r11

  mov c a 0
  mov r11 0 c
  mov a a 8
  mov d r11 # q

  mov r11 16
  call Mem.main_reg

  @List.add_0
  cmp a 0
  j e List.add_2

  mov d 8 r11
  mov d r11

  mov r11 16
  call Mem.main_reg  

  mov c a 0
  mov d 0 c
  mov a a 8
  j List.add_0

  @List.add_1                                                                       # r == []
  mov a sp 8 # s
  mov sp 24 a
  ret

  @List.add_2
  mov a sp 8 # s
  mov d 8 a
  ret  
Fact (add [2, 3] [5, 8] == [2, 3, 5, 8]) 

Fact ([2, 3] + [5, 8] == [2, 3, 5, 8])
Fact ([2, 3] + [5, 8, 13, 21] == [2, 3, 5, 8, 13, 21])
Fact ([0, 0] + [0, 0, 0, 0] == [0, 0, 0, 0, 0, 0])
Fact ([2, 3] + [] == [2, 3])
Fact ([] + [5, 8, 13, 21] == [5, 8, 13, 21])
Fact ([] + [] == [])

add3 x:*0 y:*0 z:*0 : *0 = adds [x, y, z]
Fact (add3 [2, 3] [5, 8] [13, 21, 34] == [2, 3, 5, 8, 13, 21, 34])

add4 x:*0 y:*0 z:*0 w:*0 : *0 = adds [x, y, z, w]
Fact (add4 [2, 3] [5, 8] [13] [21, 34] == [2, 3, 5, 8, 13, 21, 34])

add_opt s:*0 x:!0 : *0 = x & x,s | s
Fact (add_opt [2, 3] 1 == [1, 2, 3])
Fact (add_opt [2, 3] 0 == [2, 3])

adds_opt_rev s:*!0 : *0 = sum_left s add_opt 0
Fact (adds_opt_rev [2, 3, 0, 5, 8] == [8, 5, 3, 2])

adds_slow s:**0 : *0 = sum_left s add 0
Fact (adds_slow [[2, 3], [5], [8, 13, 21]] == [2, 3, 5, 8, 13, 21])

adds_to r:*0 : **0? *0 =
  u, s? adds_to (rev_add r u) s
  ? r
Fact (List.adds_ [2] [3, 5] [8] == adds [[2], [3, 5], [8]])
Fact (List.adds_ [2] [3, 5] [8] == [2, 3, 5, 8])

adds s:**0 : *0 = adds_to [] s . rev
Fact (adds [[2, 3], [5], [8, 13, 21]] == [2, 3, 5, 8, 13, 21])

in eq:0?0?B s:*0 x:0 : B = s & (eq x s.head & 1 | in eq s.tail x)                       
Fact (x = 'bar'; in S.eq ['foo', x] 'bar')
Fact (in N.eq [2, 3, 5] 3)
Fact !(in N.eq [2, 3, 5] 7)

last s:*0 : !0 = s & (s.tail & s.tail.last | s.head)
Fact (last [2, 3, 5] == 5)

key eq:0?0?B s:*0 x:0 i:N : !N = s & (eq s.0 x & i | key eq s.tail x i+1)
Fact (key N.eq [2, 3, 5] 3 0 == 1)
Fact (key S.eq ['foo', 'bar', 'quz'] 'bar' 0 == 1)

all s:*1 f:0?B : B = ! s.bit | ((f & f s.0 | s.0) & all s.tail f)
Fact (all [1, 3, 5] N.odd)
Fact !(all [2, 3, 5] N.even)

all2 r:*0 s:*1 f:0?1?B : B = r & s & f r.0 s.0 & all2 r.tail s.tail f | ! r.bit & ! s.bit
Fact (all2 [2, 3] [8, 7] (_ x:N y:N : B = x + y == 10))
Fact !(all2 [2, 3, 5] [8, 7] (_ x:N y:N : B = x + y == 10))

any2 r:*0 s:*1 f:0?1?B : B = r & s & (f r.0 s.0 | any2 r.tail s.tail f)
Fact (any2 [2, 3] [8, 7] (_ x:N y:N : B = x + y == 10))
Fact (any2 [2, 3] [8] (_ x:N y:N : B = x + y == 10))
Fact (any2 [2, 3, 5] [7, 8, 5] (_ x:N y:N : B = x + y == 10))
Fact !(any2 [2, 3] [7, 8] (_ x:N y:N : B = x + y == 10))
Fact !(any2 [2, 3, 5] [7, 5] (_ x:N y:N : B = x + y == 10))

eq_by eq:0?0?B r:*0 s:*0 : B = all2 r s eq
Fact (eq_by N.eq [2, 3, 5] [2, 3, 5])
Fact !(eq_by N.eq [2, 3, 5] [2, 3, 42])
Fact (eq_by N.mod2 [3, 5] [5, 19])
Fact ([2, 3, 5] == [2, 3, 5])
Fact !([2, 3, 5] == [2, 3])

ne_by ne:0?0?B r:*0 s:*1 : B = any2 r s ne | r.size != s.size
Fact !(ne_by N.ne [2, 3, 5] [2, 3, 5])
Fact (ne_by N.ne [2, 3, 5] [2, 3])
Fact (ne_by N.ne [2, 3, 5] [2, 3, 42])
Fact !(ne_by N.mod2_ne [3, 5] [5, 19])
Fact !([2, 3, 5] != [2, 3, 5])
Fact ([2, 3, 5] != [2, 3])
Fact ([2, 3, 5] != [2, 3, 42])

all3 q:*0 r:*0 s:*1 f:0?1?2?B : B = q & r & s & f q.0 r.0 s.0 & all3 q.tail r.tail s.tail f | ! q.bit & ! r.bit & ! s.bit
Fact (all3 [2, 3, 5] [8, 13, 21] [16, 10, 0] (_ x:N y:N z:N : B = x + y + z == 26))

unzip s:*(0,1) p=0:*0 q=0:*1 : *0, *1 = s & (x, y = s.head; unzip s.tail x,p y,q) | rev p, rev q
Fact (r, s = unzip [2,3, 5,8]; r == [2, 5] & s == [3, 8])

unzip3 s:*(0,1,2) p=0:*0 q=0:*1 r=0:*2 : *0, *1, *2 = s & (x, y, z = s.head; unzip3 s.tail x,p y,q z,r) | rev p, rev q, rev r
Fact (q, r, s = unzip3 [2,3,5, 8,13,21]; q == [2, 8] & r == [3, 13] & s == [5, 21])

unzip4 s:*(0,1,2,3) p=0:*0 q=0:*1 r=0:*2 t=0:*3 : *0, *1, *2, *3 = s & (x, y, z, w = s.head; unzip4 s.tail x,p y,q z,r w,t) | rev p, rev q, rev r, rev t
Fact (p, q, r, s = unzip4 [2,3,5,8, 13,21,34,55]; p == [2, 13] & q == [3, 21] & r == [5, 34] & s == [8, 55])

# http://stackoverflow.com/questions/235148/implement-zip-using-foldr/26285107#26285107
  http://research.microsoft.com/en-us/um/people/simonpj/Papers/deforestation-short-cut.pdf A short cut to deforestation - p.9
  http://www.willamette.edu/~fruehr/haskell/evolution.html# The Evolution of a Haskell Programmer
sum f:0?1?1 a:1 s:*0 : 1 = s & f s.head (sum f a s.tail) | a

zip1 x:0 f:*1?*(0,1) : *1? *(0,1) = y,u? x,y, f u
# Fact (zip [1, 3, 5] [2, 4, 6] == [1,2, 3,4, 5,6]) # fixme

bit x:*0 : B = x & 1 | 0
Fact (bit [2])
Fact (bit [2, 3])
Fact !(bit [])

heads_tail s:*0 : *0, 0 = (r = s.rev; r.tail.rev, r.head)

any s:*0 f:0?B : B = s & (f s.head | any s.tail f)
Fact (any ['foo', 'bar'] (S.eq 'bar'))
Fact !(any ['foo', 'bar'] (S.eq 'qux'))

any1 f:0?1?B x:0 s:*1  : B = s & (f x s.head | any1 f x s.tail)
Fact (any1 S.eq 'bar' ['foo', 'bar'])
Fact !(any1 S.eq 'qux' ['foo', 'bar'])

get s:*S x:S : !S = s & (x == s.head & s.head | get s.tail x)
Fact (x = 'bar'; S.id (get ['foo', x] 'bar') x)

get_by s:*0 f:0?B : !0 = s & (f s.head & s.head | get_by s.tail f)
Fact (get_by [13,'foo', 42,'bar'] (Pair.eq0 N.eq 42) == 42,'bar') 

hash s:*(S,0) : S/0 =
  r = Hash 2*(size s)
  Map.do s (Hash.set r)
  r
Fact (s = hash ['foo',13, 'bar',42]; Hash.get s 'foo' == 13 & Hash.get s 'bar' == 42)

set s:*0 : 0/Z =
  r = Set 2*(size s)
  do s (Set.add r)
  r
Fact (s = set ['foo', 'bar']; Set.in S.eq s 'foo' & Set.in S.eq s 'bar' & ! Set.in S.eq s 'qux')

if_add b:B x:0 s:*0 : *0 = b & x,s | s
Fact (if_add 1 2 [3, 5] == [2, 3, 5])
Fact (if_add 0 2 [3, 5] == [3, 5])

take n:N : *0? *0 = x,s & n? x, take n-1 s
Fact (take 3 [2] == [2])
Fact (take 3 [2, 3, 5, 8, 13] == [2, 3, 5])

skip n:N s:*0 : *0 = (n & s) & skip n-1 s.tail | s
Fact (skip 2 [2] == [])
Fact (skip 2 [2, 3, 5, 8, 13] == [5, 8, 13])

pop0 : *0? *(0, *0) = x, s? x, s
pop s:*0 : !(0, *0) = pop0 s . Cast.any
Fact (pop [] == 0)
Fact (x, s = pop [13, 42]; x == 13 & s == [42])

nat n:N : *N = n & n-1, nat n-1 
Fact (nat 3 == [2, 1, 0])

# merge. assumed sorted
fuse u:*N v:*N : *N = u,v .
  x,r, y,s? x < y & x, fuse r y,s | y, fuse x,r s
  r, 0? r
  0, s? s
Fact (fuse [1, 3, 5] [2, 4] == [1, 2, 3, 4, 5])

# unique, distinct. assumed sorted
sole_by eq:0?0?B : *0? B = (x, r=y,s? ! eq x y & sole_by eq r; _? 1)
Fact (sole_by N.eq [])
Fact (sole_by N.eq [1, 3, 5])
Fact (sole_by N.eq [1, 3, 5, 3]) # only check consecutives
Fact !(sole_by N.eq [1, 3, 3, 5])
Fact !(sole_by N.mod2 [1, 3])

head_tail : *0? 0, *0 =
  x, s? x, s
  ? Fail $Fun
