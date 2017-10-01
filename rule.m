# rewrite rule, pattern matching

  https://en.wikipedia.org/wiki/Pattern_matching
  http://en.wikipedia.org/wiki/Guard_(computer_science)

# f x,y:t : u = a    ->  f z:t   : u = (x,y = z; a)
# f z=x,y:t : u = a  ->  f z:t   : u = (x,y = z; a)
binds : rule:Exp? arg:Exp, body:Exps =
  # todo - generalize for arbitrary equal-rule (use tests_binds below?) such as f x=(y,z=(u,v)):t
  #   vs default argument  f x:N=3 : t = a
  spot, Binary name '=' (_, Binary (_, Row rules) ':' type)?                    # note, f z=(x,y:t)  not f (z=x,y):t
    (spot, Binary name ':' type), [(spot, Binary (spot, Row_ rules) '=' name)]

  _, Binary (spot, Row rules) ':' type?
    name = spot, Name 'x'.S.tick
    (spot, Binary name ':' type), [(spot, Binary (spot, Row_ rules) '=' name)]

  exp? exp, []

test_bind_row arg,size:Exp,N index:N rule:Exp : Exps, Exps =
  spot = Exp.spot arg
  tests_binds rule (spot, Tree [(spot, Row.name size index), arg])

# {A?a e}  =>  {{[A == e], [], a}}  =>  tag e == A & a
# {x?a e}  =>  {{[], [x = e], a}}  =>  (x = e; a)
# {A,B?a e}  =>  {{[tag e.0 == A, tag e.1 == B], [], a}}  =>  tag e.0 == A & tag e.1 == B & a
# {A,x?a e}  =>  {{[tag e.0 == A], [x == e.1], a}}  =>  tag e.0 == A & (x = e.1; a)
# {(A B)?a e}  =>  {{[tag e.0 == A, tag e.term == B], [], a}}  =>  tag e.0 == A & tag e.term == B & a
# http://research.microsoft.com/pubs/79947/p29-syme.pdf# Extensible Pattern Matching Via a Lightweight Language Extension, [Don Syme, Microsoft Research]
tests_binds rule:Exp arg:Exp : Exps, Exps =
  spot = Exp.spot rule
  rule.Exp.tree .
    Char _? [(spot, Binary arg '==' rule)], 0                                # c

    Nat _? [(spot, Binary arg '==' rule)], 0                                 # n
    
    Str _? [(spot, Tree [(spot, Name2 'S' 'eq'), rule, arg])], 0                # S.eq

    Name x & x.S.char.C.is_upper? [(spot, Binary arg '==' rule)], 0                                # tag X
    Name _? 0, [(spot, Binary rule '=' arg)]                                    # var - (x? a) b  =>  x = b; a
    Name2 _ _? [(spot, Binary arg '==' rule)], 0                                # tag X
  
    Binary rule2 '&' test?                                               # {r & e}  =>  [t & (b; e)], b  @ t, b = {r}
      tests, binds = tests_binds rule2 arg
      test2 = Exp.binary_exps ';' binds+[test]
      Exp.binary_exps '&' tests+[test2] . Opt.seq, binds                
  
    Listy rule2? tests_binds rule2 arg                                            # fixme
    
    Row [rule2]? tests_binds rule2 arg                                            # fixme, singleton row - n for [Nat n] is not boxed
    
    Row rules?                                               # {r1, r2}  =>  [t1 & t2], b1 + b2  @  t1, b1 = {r1}; t2, b2 = {r2}
      tests, binds = List.map_at rules (test_bind_row arg,!rules) 0 . List.unzip
      # must group the tests here, else: (A, B? a; b) (A, C) gives 0 not b because A=A then B!=C instead of A=A and B!=C before branching
      test = spot, Tree [(spot, Name2 'B' 'cast'), arg]                              # B.cast - todo - only check arg.Bit for t,u! (opt type)
      Exp.binary_exps '&' (test, List.adds tests) . Opt.seq, List.adds binds

    # - todo
    # f z=x,y:t : u = a
    # f z:t     : u = (x,y = z; a)    
    # f z:t     : u = (z = x,y; a)    
    Binary rule1 '=' rule2?                                                     # alias {x = r}  =>  t, (x = r), b  @  t, b = {r}
      tests, binds = tests_binds rule2 arg
      tests, ((spot, Binary rule1 '=' arg), binds)
  
    Tree (_, Name name),rules & name.S.char.C.is_upper?                    # {X r..} a  =>  [t1 & t2], b1 + b2  @  t1, b1 = {[X]_tag} a.term_tag; t2, b2 = {r2} a.[X]_item
      arg0 = spot, Tree [(spot, Name2 'Term' 'tag'), arg]
      arg1 = spot, Tree [(spot, Name2 'Term' name+'_term'), arg]
      tests0, binds0 = tests_binds (spot, Name2 'Term' name+'_tag') arg0 # t1, b1 = {[X]_Tag} a.term_tag
      tests1, binds1 = tests_binds (spot, Row_ rules) arg1                                # t2, b2 = {r2} a.[X]_item
      # must group the tests here, else: (A, B? a; b) (A, C) gives 0 not b because A=A then B!=C instead of A=A and B!=C before branching
      Exp.binary_exps '&' tests0+tests1 . Opt.seq, binds0+binds1
  
    ? Exp.seq_error $Fun 'invalid' [rule, arg]
  
bind_exp bind:!Exp exp:Exp : Exp =
  bind & Exp.spot bind, Binary bind ';' exp | exp

# arg must be generated via [Exp.bind_name] so that bind_exp around the outermost (a?b; c?d) in rewrite_exps
rewrite rule:Exp body:Exp arg:Exp : Exp =                                         # (rule? body) arg
  bind, arg2 = Exp.bind_name arg
  tests, binds = tests_binds rule arg2
  # rewrite_match must not rewrite_exp, so that
  #   (a? b; c) d --> (op_if (op_if (== a d) b 0) (op_if (== a d) b 0) (c d))
  #   vs the correct (op_if (== a d) b (c d))
  bind_exp bind (Exp.binary_exps '&' (tests + (Exp.binary_exps ';' binds+[body] . Opt.seq)) . Opt.main0)
