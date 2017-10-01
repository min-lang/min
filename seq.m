# sequence, container, collection, generator 

 https://en.wikipedia.org/wiki/Collection_(abstract_data_type)
 https://en.wikipedia.org/wiki/Stream_(computing)
 
str0 skip:N take:!N : +C? S =
  Sstr n s? s
  Sskip n s? str0 skip+n take s
  Stake n s? str0 skip (N.opt n) s
  ? Fail $Fun
str_char s:+C : S = str0 0 0 s
Fact (str_char 'foo'.S.seq == 'foo') 

size : +0? N =
  Sskip n s? size s - n
  Stake n s? N.min s.size n
  Slist s? List.size s
  Sstr n _? n
  # Srow r s? s - r
  Srow n s? n
  Sfun n f? n | 0                                                               # fixme, opt return
  Slink x s? 1 + size s
  Sadd r s? size r + size s
  Smap _ s? size s
  Sseq s? List.map_sum_nat s size

# bound : +0? N

row3 s:0,0,0 : +0 = Srow 3 s.Cast.any

Fact (size 'foo'.S.seq == 3)
Fact (Sskip 1 'foo'.S.seq . size == 2)
Fact (Stake 2 'foo'.S.seq . size == 2)
Fact (Stake 5 'foo'.S.seq . size == 3)
Fact (size (row3 2,3,5) == 3)
Fact (size Slist[13, 42] == 2)
Fact (size (Slink 3 Slist[5, 13]) == 3)
Fact (size (Smap N.tick Slist[13, 42]) == 2)
Fact (size (Sseq [Slist[1, 2], Slist[3, 5, 8]]) == 5)

do_fun f:0?Z g:Z?!0 : Z =
  x = g 0
  x & (f x.N.must; do_fun f g)

# producer yield
pump : +0? Z? !0 =
  # Sstr n s? S.pump s : Z?!0
  Sstr _ s? (S.pump s : Z?!0)
  ? Fail $Fun
Fact (x = pump 'foo'.S.seq; !x == N.opt \f & x 0 == N.opt \o & x 0 == N.opt \o) 
  
do f:0?_ : +0? Z =
  Sstr n s? S.do f s n
  Slink x s? (f x; do f s)
  Sone x? f x
  Sadd r s ? (do f r; do f s)
  Sseq s? List.do s (do f)  
  Slist s? List.do s f
  Srow n s? Row.do f s n
  Spair r s? (g = pump r; do ((_ f_:1,2?_ g_:Z?!1 y:2 : Z = (x = g_ 0; x & f_ x.N.must,y)) f g) s) # Rewrite.NAME_BUG
  Smap g s? do (Fun.of f g) s
  Skeep g s? do ((_ g_:1?B f_:0?_ x:2 : Z = g_ x & f_ x) g f) s 
  Sfun _ g? do_fun f g
  0? 0
  x? Fail.main2 $Fun x.Term.tag.N.str
Fact (x = %0; do (Ref.add x) 'foo'.S.seq; !x == \f + \o + \o)
Fact (x = %0; do (Ref.add x) Slist[2, 3, 5]; !x == 10)
Fact (x = %0; do (Ref.add x) (Sadd Slist[2, 3, 5] Slist[8, 13]); !x == 31)
Fact (x = %0; do (Ref.add x) (Sadd Slist[2, 3, 5] Slist[8, 13, 21]); !x == 52)
Fact (x = %0; do (Ref.add x) (row3 2,3,5); !x == 10)
Fact (x = %0; do (Ref.add x) (Smap N.tick Slist[2, 3]); !x == 7)
Fact (x = %0; do (Ref.add x) (Skeep N.odd Slist[2, 3, 5]); !x == 8)
Fact (s = %0; do (_ x,y:C,C : Z = Ref.add s y-x) (Spair 'abc'.S.seq 'def'.S.seq); !s == 9)
Fact (s = %0; do (_ x,y:C,C : Z = Ref.add s y-x) (Spair 'abc'.S.seq 'de'.S.seq); !s == 6)
Fact (s = %0; do (_ x,y:C,C : Z = Ref.add s y-x) (Spair 'ab'.S.seq 'def'.S.seq); !s == 6)
Fact (s = %0; do (_ x,y:C,C : Z = Ref.add s y-x) (Spair 'ab'.S.seq ''.S.seq); !s == 0)
Fact (do S.size (Smap List.head Slist[['foo']]); 1)
Fact (x = %0; do (Ref.add x) (Sfun 3 (tick 3)); !x == 3)

# skip/take span range slice interval
do_span0 skip:N take:!N f:0?_ : +0? Z =                                         # do_span skip take 
  Sskip n s? do_span0 skip+n take f s
  Stake n s? do_span0 skip (N.opt n) f s
  Sstr n s? S.do f s+skip (Opt.min take n)-skip
  Spair r s? (g = pump r; do_span0 skip take ((_ f_:1,2?_ g_:Z?!1 y:2 : Z = (x = g_ 0; x & f_ x.N.must,y)) f g) s) # Rewrite.NAME_BUG
  Slist s? List.do s.(List.skip skip).(Opt.map2 N.must (Opt.map take (N.sub2 skip)) List.take) f
  #Srow n s? Row.do f s n
  Smap g s? do_span0 skip take (Fun.of f g) s
  Skeep g s? do_span0 skip take ((_ g_:1?B f_:0?_ x:2 : Z = g_ x & f_ x) g f) s
  Sseq s? List.do s (do_span0 skip take f)
  #Sfun _ g? do_fun f g
  ? Fail $Fun
do_span f:0?_ s:+0 = do_span0 0 0 f s
Fact (x = %0; do_span (Ref.add x) (Sskip 1 'foo'.S.seq); !x == \o + \o)
Fact (x = %0; do_span (Ref.add x) (Stake 2 'foo'.S.seq); !x == \f + \o)
Fact (x = %0; do_span (Ref.add x) (Smap N.tick 'foo'.S.seq); !x == \f+1 + \o+1 + \o+1)
Fact (x = %0; do_span (Ref.add x) ('foo'.S.seq . Smap N.tick . Sskip 1); !x == \o+1 + \o+1)
Fact (x = %0; do_span (Ref.add x) ('foo'.S.seq . Sskip 1 . Smap N.tick); !x == \o+1 + \o+1)
Fact (x = %0; do_span (Ref.add x) (Skeep N.odd Slist[2, 3, 5]); !x == 8)
Fact (s = %0; do_span (_ x,y:C,C : Z = Ref.add s y-x) (Stake 2 (Spair 'abc'.S.seq 'def'.S.seq)); !s == 6)
Fact (s = %0; do_span (_ x,y:C,C : Z = Ref.add s y-x) (Spair 'abc'.S.seq 'def'.S.seq.(Stake 2)); !s == 6)

sum_seq f:0?1?1 a:1 s:*+0 : 1 = s & sum f (sum_seq f a s.List.tail) s.List.head | a   # similar to List.flat = sum add

sum_fun f:0?1?1 a:1 g:Z?!0 : 1 =
  x = g 0
  x & sum_fun f (f x.N.must a) g | a

# pair/cons fold aggregate
# https://wiki.haskell.org/Foldl_as_foldr
# https://wiki.haskell.org/Foldr_Foldl_Foldl'
sum f:0?1?1 a:1 : +0? 1 =
  Sstr n s? S.fold f a s n
  Sone x? f x a
  Sadd r s? sum f (sum f a s) r
  Slist s? List.sum_right s f a
  Srow n s? Row.fold f a s n
  Spair r s? (z = pump r; sum ((_ f_:1,2?3?3 z_:Z?!1 y:2 a_:3 : 3 = (x = z_ 0; x & f_ x.N.must,y a_ | a_)) f z) a s) 
  Smap g s? sum ((_ g_:2?0 f_:0?1?1 x:2 a_:1 : 1 = f_ (g_ x) a_) g f) a s
  Skeep g s? sum ((_ g_:1?B f_:0?1?1 x:2 a_:1 : 1 = g_ x & f_ x a_ | a_) g f) a s
  Sfun _ g? sum_fun f a g
  Sseq s? sum_seq f a s
  # Snil _? a
  0? a
  x? Fail.main2 $Fun x.Term.tag.N.str
  
Fact (sum N.add 0 'foo'.S.seq == \f + \o + \o)
Fact (sum N.add 0 Slist[2, 3, 5] == 10)
Fact (sum N.add 0 (row3 2,3,5) == 10)
Fact (sum N.min N.max3 Slist[3, 2, 13, 5] == 2)
Fact (sum N.max 0 Slist[2, 3, 13, 5] == 13)
Fact (sum N.add 0 (Skeep N.odd Slist[2, 3, 5]) == 8)
Fact (sum (_ x,y:C,C s:N : N = s + y-x) 0 (Spair 'abc'.S.seq 'def'.S.seq) == 9)

# http://okmij.org/ftp/Streams.html#1enum2iter Parallel composition of iteratees: one source to several sinks
sum_size f:0?1?1 a:1 s:+0 : 1, N = sum ((_ f_:0?1?1 x:0 a,n:1,N : 1, N = f_ x a, n+1) f) a,0 s
# Fact (sum_size N.add 42 Slist[] == 42,0) # FIX_TYPE_ANNOTATE
Fact (sum_size N.add 42 Slist([]:*N) == 42,0)                                   
Fact (sum_size N.add 0 Slist[2, 3, 5] == 10,3)

sum_nat s:+N : N = sum N.add 0 s
Fact (sum_nat Slist[2, 3, 5] == 10)

sum_size_nat s:+N : N, N = sum_size N.add 0 s
Fact (sum_size_nat Slist[2, 3, 5] == 10,3)

#mean s:+N : R = sum_nat s / size s
Fact (sum_nat Slist[2, 3, 5] == 10)

# while/break, short circuit, early termination
# todo - need another function for returning B,1
# list anamorphism [Functional Programming with Bananas, Lenses, Envelopes and Barbed Wire]
sum_opt f:1?0?!1 a:1 opt:1?!1 must:!1?1 : +0? !1 = 
  Sstr _ s? S.sum_opt f a s opt must
  Slist s? List.sum_opt f a s opt must
  Smap g s? sum_opt ((_ g_:2?0 f_:1?0?!1 a_:1 x:2 : !1 = f_ a_ (g_ x)) g f) a opt must s
  Skeep g s? sum_opt ((_ g_:0?B f_:1?0?!1 opt_:1?!1 a_:1 x:0 : !1 = g_ x & f_ a_ x | opt_ a_) g f opt) a opt must s
  # Sfun _ g? sum_fun f a g
  # Sseq s? sum2 f a s
  ? Fail $Fun
# Fact (sum_opt N.even.bit_opt 0 Slist[2, 4, 10] == Opt 0) # todo - Opt.eq
Fact (Opt.eq_by Z.eq (sum_opt N.even.bit_opt 0 Z.opt Z.must Slist[2, 4, 10]) !Z.opt)
Fact (sum_opt N.even.bit_opt 0 Z.opt Z.must Slist[2, 4, 7, 10] == 0)

# paramorphisms  
sum_key f:1?0?!1 a:1 must:!1?1 : +0? B, 1 =
  #Sstr _ s? S.sum_key f a s
  Slist s? List.sum_key f a s must
  #Smap g s? sum_key ((_ g_:2?0 f_:1?0?!1 a_:1 x:2 : !1 = f_ a_ (g_ x)) g f) a s
  #Skeep g s? sum_key ((_ g_:1?B f_:0?1?!1 x:2 a_:1 : !1 = g_ x & f_ x a_ | a_) g f) a s  
  # Sfun _ g? sum_fun f a g
  # Sseq s? sum2 f a s
  ? Fail $Fun
Fact (sum_key N.even.bit_opt 0 Z.must Slist[2, 4, 10] == 1,0)
Fact (sum_key N.even.bit_opt 0 Z.must Slist[2, 4, 7, 10] == 0,0)

sum_at f:1?0?!1 a:1 opt:0?!0 s:+0 : N, !0, 1 =
  sum_key ((_ f_:1?0?!1 opt_:1?!1 i,x0,a:N,!0,1 x:0 : !(N, !0, 1) = (x0 & (i, x0, a) | (b = f_ a x; i+1, (!b & opt_ x):!0, b:1))) f opt) 0,0,a Opt.must s . Row.at1
Fact (sum_at N.even.bit_opt 0 N.opt Slist[2, 4, 7, 10] == 3,7.N.opt,0)

# find
get opt:0?!0 must:!1?1 f:0?B s:+0 : !(N, 0) =
  i, x, _ = sum_at f.not.bit_opt 0 opt s
  x & (i, must x):!(N, 0)
Fact (get N.opt N.must N.odd Slist[2, 4, 7, 10] == 3,7)
bit_opt f:0?B : f:Z?0?!Z = (_ f_:0?B _:Z x:0 : !Z = f_ x . Opt.of) f

bit_and f:0?B : f:0?B?B = (_ f_:0?B x:0 y:B : B = f_ x & y) f

#not f:0?B : 0?B = (_ f_:0?B x:0 : B = !(f_ x)) f
not f:0?B : 0?B = (_ f:0?B x:0 : B = !(f x)) f

all f:0?B s:+0 : B = sum_opt f.bit_opt 0 Z.opt Z.must s . Opt.bit
Fact (all C.is_lower 'foo'.S.seq)
Fact !(all C.is_upper 'foo'.S.seq)
Fact (all N.odd Slist[1, 3, 5])
Fact !(all N.odd Slist[1, 2, 5])
Fact !(all (N.le 5) (Skeep N.odd Slist[3, 10, 5]))
Fact (all (N.gt 7) Slist[3, 5]) 
Fact (all (N.gt 7) (Skeep N.odd Slist[3, 10, 5]))
Fact (all S.bit (Skeep S.bit Slist['foo', '']))
Fact !(all (_ x:Z?N : B = N.lt !x 3) Slist[(_ _ : N = 2), (_ _ : N = 5), (_ _ : N = !Fail.nil)])
Fact (Job.err (? all_full (_ x:Z?N : B = N.lt (x 0) 3) Slist[(_ _ : N = 2), (_ _ : N = 5), (_ _ : N = Fail 'foo')] . Z) == "foo: error \.") 

all_full f:0?B s:+0 : B = sum f.bit_and 1 s
Fact (all_full N.odd Slist[1, 3, 5])
Fact !(all_full N.odd Slist[1, 2, 5])

# in has mem member
any f:0?B s:+0 : B = sum_opt f.not.bit_opt 0 Z.opt Z.must s . Opt.bit . B.not
Fact (any C.is_lower 'Foo'.S.seq)
Fact !(any C.is_upper 'foo'.S.seq)
Fact (any N.even Slist[1, 2, 5])
Fact !(any N.even Slist[1, 3, 5])
Fact (any (N.eq 5) (Skeep N.odd Slist[3, 10, 5]))
Fact (any (_ x:Z?N : B = N.gt !x 3) Slist[(_ _ : N = 2), (_ _ : N = 5), (_ _ : N = !Fail.nil)])
Fact (any (N.lt 3) (Smap Fun.do (Slist[(_ _ : N = 2), (_ _ : N = 5), (_ _ : N = !Fail.nil)])))

any_full f:0?B s:+0 : B = sum f.not.bit_and 1 s . B.not
Fact (any_full N.even Slist[1, 2, 5])
Fact !(any_full N.even Slist[1, 3, 5])
Fact (Job.err (? any_full (_ x:Z?N : B = N.gt !x 3) Slist[(_ _ : N = 2), (_ _ : N = 5), (_ _ : N = Fail 'foo')] . Z) == "foo: error \.") 

list s:+0 : *0 = sum List.main 0 s
Fact (list 'foo'.S.seq == [\f, \o, \o])
Fact (list Slist[2, 3, 5] == [2, 3, 5])
Fact (list (Smap N.tick Slist[13, 42]) == [14, 43])
Fact (list (Sseq [Slist[1, 2], Slist[3, 5, 8], Slist[11, 13]]) == [1, 2, 3, 5, 8, 11, 13])
Fact (list (Sfun 3 (tick 3)) == [2, 1, 0])
Fact (list (Smap Fun.do Slist[(_ _ : N = 2), (_ _ : N = 5)]) == [2, 5])
Fact (list (Skeep N.odd Slist[2, 3, 5, 8]) == [3, 5])

tick n:N : Z? !N =
  i = %0
  (_ n_:N i_:%N _:Z : !N = (!i_ < n_ & Ref.tick0 i_ . N.opt)) n i
Fact (f = tick 3; !f == N.opt 0 & !f == N.opt 1 & !f == N.opt 2 & !f == 0)
 
row s:+0 : Mem = (n = s.size; r, f = Row.init n; do f s; r)
Fact (row Slist[2, 3, 5] . Row.mem_eq3 2,3,5)
Fact (row (Sseq [Slist[1, 2], Slist[3], Slist[5, 8]]) . Row.mem_eq5 1,2,3,5,8)
Fact (row (Sfun 3 (tick 3)) . Row.mem_eq3 0,1,2)

pop : +0? !(0, +0) =
  # Sstr n s? (S.pop s . (x, r? (x, (Sstr n-1 r : +0))))                        
  Sstr n s? (S.pop s . (x, r? (x:0, (Sstr n-1 r : +0))))                        # FIX_TYPE_ANNOTATE
  Slist s? (List.pop s . (x, r? x, Slist r))
  # Srow n s? Row.do f s n
  # Spair r s? (z = pump r; do ((_ f_:1,2?_ z_:Z?!1 y:2 : Z = (x = z_ 0; x & f_ x.Opt.un,y)) f z) s) # FIXME - failed if [p] not [z]
  # Smap g s? do (Fun.of f g) s
  # Skeep g s? do ((_ g_:1?B f_:0?_ x:2 : Z = g_ x & f_ x) g f) s 
  # Sseq s? List.do s (do f)
  # Sfun _ g? do_fun f g
  ? Fail $Fun
Fact (x, s = pop Slist[13, 42]; x == 13 & list s == [42])
#Fact (pop 'foo'.S.seq == \f,'oo'.S.seq) # todo Seq.eq_by

peek s:+0 : !0 = pop s . Opt.at0
# Fact (peek Slist[] == 0) 
Fact (peek Slist([]:*N) == 0)
Fact (peek Slist[13, 42] == 13)

cores f:0?_ s:+0 opt:0?!0 must:!0?0 : Z =
  r = % list s
  Thread.all (_ _:N = Ref.do f r opt must)
  0
Fact (s = %0; cores (_ x:N = Ref.padd s x) 100.List.nat.Slist N.opt N.must; !s == 4950) # n(n+1)/2 = (99*100)/2 = 4950

add r:+0 s:+0 : +0 = Sadd r s
Fact (add Slist[2, 3, 5] Slist[8, 13] . list == [2, 3, 5, 8, 13])
Fact (Slist[2, 3, 5]+Slist[8, 13] . list == [2, 3, 5, 8, 13])

adds s:*+0 : +0 = List.sum add 0 s
Fact (adds [Slist[2, 3, 5], Slist[8, 13]] . list == [2, 3, 5, 8, 13])

eq r:+0 s:+0 : B = N.eq r.Cast.any s.Cast.any 
Fact (eq 0 0)

eq_by f:0?0?B r:+0 s:+0 : B = Fail $Fun # TODO

map_line s:+0 f:0?S : S = List.map_line s.list f

str_by f:0?S s:+0 : S = List.str_by f s.list 
