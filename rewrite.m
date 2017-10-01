# tree rewrite

 https://en.wikipedia.org/wiki/Rewriting
 
# {| a; | b}  -->  a | {| b}
# tree_bar recurses into tree_bar, not exps or exp, else:
#   | a; (| b; | c)
#   --> | a; op_if ...
# but (| b; | c) is rewritten with op_if rule below, and that cannot be simplify further to have a | b | c
# : Exps
tree_bar : Exp? Exp =
  spot, Binary (_, Pre '|' a) ';' b? spot, Binary a '|' b
  a? a

# a, (b, c)   -> a, b, c
# a, ((b, c)) -> a, (b, c)
pair_row : Exp? Exps =
  _, Binary a ',' b? a, pair_row b
  _, Tree [a]? [a]                                                              # special for last node - a,b, c,d  ->  ((a, b), (c, d))
  a? [a]

pair_seq : Exp? Exp =
  spot, Binary a ',' b? spot, Row_ [a, b.pair_seq]
  _, Tree [a]? a
  a? a

exps0 s:Exps : Exps = s exp

exps s:Exps : Exps = s exp + !nameless_funs

exp a:Exp : Exp = a.do_exp1.do_exp2

do_exp1 exp=spot,term:Exp : Exp =
  term .
    Pre o a? spot, Pre o a.do_exp1
    Post a o? spot, Post a.do_exp1 o
    Binary a o b? o .
      ','? spot, Row_ (List.map (pair_row exp) do_exp1)                     # a, (b, c)  ->  a, b, c
      ? spot, Binary a.do_exp1 o b.do_exp1
    Tree [(_, Name 'List'), a]? spot, Listy a.pair_seq.do_exp1
    Tree s? spot, Tree do_exp1.s
    Row s? spot, Row_ do_exp1.s
    ? exp                                           

do_exps2 : Exps? Exps  =
  (_, Tree r), s? do_exps2 r+s

  # x = f a
  # | x & ((y, z) = x; g y z)
  # | h 0
  # 
  # -->
  # 
  # f a .
  #   (y, z)? g y z
  #   ? h 0

  # match rule sequence - {(a? b; c) d} === eq {a} {d} & b | {c d}
  #   if (a == d) b {c d}
  [(_, Binary (spot, Binary rule '?' body) ';' also), arg]?                     # ;-exp recursion
    bind, arg2 = Exp.bind_name arg
    else = spot, Tree [also, arg2]
    [exp (Rule.bind_exp bind (spot, Binary (Rule.rewrite rule body arg2) '|' else))]
  
  [(spot, Binary rule '?' body), arg]?                                          # ;-exp base
    bind, arg2 = Exp.bind_name arg
    [exp (Rule.bind_exp bind (Rule.rewrite rule body arg2))]

  [(spot, Pre '?' body), arg]?                                                  # _?a  ->  ?a
    bind, arg2 = Exp.bind_name arg
    [exp (Rule.bind_exp bind (Rule.rewrite (spot, Name '_') body arg2))]

  s? s exp

# seq of all bindings across ; - else, [x,y = a,b; c]  ->  [(x=a; y=b); c]  not  [x=a; (y=b; c)]
do_exp_exps2 exp=spot,term:Exp : Exps = term .
  # https://en.wikipedia.org/wiki/Guard_(computer_science)
  # consecutive conditionals: | a; | b; | c  -->  a | (b | c)
  #   {; (| 0 a) (| 0 b)} --> {| 0 (| a b)}
  Binary (_, Pre '|' _) ';' _? [do_exp2 (tree_bar exp)]

  Binary a ';' b? do_exp_exps2 a + do_exp_exps2 b

  Binary (_, Row s) '=' a?
    bind, body = Exp.bind_name a
    tests, binds = List.map_at s (Rule.test_bind_row body,!s) 0 . List.unzip # fixme - need tests?
    List.map (Opt.add bind binds.List.adds) do_exp2

  ? [do_exp_exp2 exp]

do_exp2 exp:Exp : Exp = Opt.get (Exp.binary_exps ';' (do_exp_exps2 exp)) $Fun

# https://en.wikipedia.org/wiki/Anonymous_function
# https://en.wikipedia.org/wiki/Closure_(computer_programming)
# https://en.wikipedia.org/wiki/Partial_application
nameless_funs = %0 : %Exps

arg_vars _,e:Exp : *S = e .
  Binary (_, Name x) ':' _? [x]
  # Binary (_, (Binary (_, Name x) ',' (_, Name y))) ':' _? [x, y]
  Binary (_, (Row s)) ':' _? List.map_opt_rev s (_ : Exp? !S = (_, Name x)? x)

# todo
# 1. ignore the function itself, need names in lexical scope during typing in Type.m to determine if f or X.f are free variable, todo for higher-order functions REWRITE_FREE_VARS_FUN
# 2. also local top-level in the unit, such as Thread.lock in Thread.main REWRITE_FREE_VARS_LOCAL
# 3. also need to done rewriting ((a . X) . y) -> X.y a in do_exp2 do_exp_exps2 before [free_vars], see REWRITE_UNIT_NAME
# 4. need types of free variables to rewrite into full function def - f x:t in [do_exp_exp2] below
# free_vars s:*S e=_,m:Exp : *S = m .
# Rewrite.NAME_BUG: some varialbe names such as [p] with local functions cause crashes, or [h] in parameter
free_vars s:*S e=_,m:Exp : *Exp = m .
  Name x & S.is_lower x? ! List.in S.eq s x & [e]
  Pre _ a? free_vars s a
  Post a _? free_vars s a
  Binary (_, Name _) '.' _? []
  Binary (_, Binary (_, Name x) '=' a) ';' b? free_vars s a + free_vars x,s b
  Binary (_, Binary (_, Row r) '=' _) ';' a? free_vars (List.add (List.map_opt_rev r (_ : Exp? !S = (_, Name x)? x)) s) a
  Binary (_, Binary a '.' (_, Name x)) '.' (_, Name _) & S.is_capital x? free_vars s a # REWRITE_UNIT_NAME
  Binary (_, Binary (_, Tree (_, Name '_'),args) ':' _) '=' body? free_vars (List.add (List.map_add args arg_vars) s) body # inside function, same as REWRITE_NAMELESS below
  Binary a ':' _? free_vars s a
  Binary a _ b? List.add (free_vars s a) (free_vars s b)
  Tree _,r? List.map_add r (free_vars s)                                        
  Row r? List.map_add r (free_vars s)
  _? []

do_exp_exp2 spot,term:Exp : Exp = term .
  Pre '|' a? do_exp2 a                                                    # | a  ->  a

  Pre '?' body?                                                                 # nameless local function
    free = free_vars [] body
    args = [(spot, Binary (spot, Name '_') ':' (spot, Name '_'))]
    all_args = (free & List.map free (_ x:Exp : Exp = spot, Binary x ':' (spot, Name 'Any'))) + args
    name = spot, Name 'f'.S.tick
    #free & (Tree name,all_args) . Term.log
    Ref.seq_add nameless_funs
      do_exp2                                                               # f _:_ : 0 = a  where the type is Any, not Z
        spot, Binary
         spot, Binary
          spot, Tree name,all_args 
          ':'
          (spot, Name 'Z')
         '='
         body
    # free & (spot, Tree name,free | name) . Exp.log
    free & spot, Tree name,free | name                                          # f x:t y:u  @ free y
  
  Pre '$' a=(spot2, Str _)? spot, Row_ [(spot, Pre '$' (spot2, Name 'Spot')), a]                     # $'foo'  ->  $Spot, 'foo'
  
  Pre o a? spot, Pre o (do_exp2 a)

  # see REWRITE_REAL2 for disabling this rewrite
  # Post (_, Nat x) '.'? spot, Real (R.of1 x) # REWRITE_REAL
  
  Post a o? spot, Post (do_exp2 a) o
  
  Listy a? spot, Listy (do_exp2 a)

  Tree (_, Binary (_, Name 'List') '.' (_, Name 'adds_')),s?                                                             # TYPE_VARARG - List.adds_ a b c  ->  List.adds [a, b, c]
    do_exp2 (spot, Tree [(spot, Name2 'List' 'adds'), Exp.seq_row1 s+[(spot, Nat 0)]])

  Tree (_, Binary (_, Name 'Seq') '.' (_, Name 'adds_')),s?                                                             # TYPE_VARARG - Seq.adds_ a b c  ->  Seq.adds [a, b, c]
    do_exp2 (spot, Tree [(spot, Name2 'Seq' 'adds'), Exp.seq_row1 s+[(spot, Nat 0)]])
  
  Tree (_, Binary (_, Name 'B') '.' (_, Name 'or')),s?                                                             # TYPE_VARARG - B.or a b c  ->  a | (b | c)
   do_exp2 (Opt.get (Exp.binary_exps '|' s) $Fun)

  Tree [a, (_, Name '²')]? do_exp2 (spot, Binary a '^' (spot, Real 2.))                   # a²  ->  a^2
  Tree [a, (spot2, Name '√'), b]? do_exp2 (spot, Binary a '*' (spot, Tree [(spot2, Name2 'R' '√'), b])) # a√b  ->  a * (√b)
  Tree [a, (spot2, Name 'ϕ'), b]? do_exp2 (spot, Binary a '*' (spot, Tree [(spot2, Name2 'R' 'ϕ'), b])) # aϕb  ->  a * (ϕb)
  
  Tree s? Group.exps_exp (do_exps2 s)

  # cannot use [y] to represent the fractional part of a real due to leading zeros, else: 0.0016 becomes 0,016 -> 0.22
  # Binary (_, Nat x) '.' (_, Nat y)? spot, Real (R.of2 x y) # REWRITE_REAL2

  # unit fullname X . y  ->  X.y
  Binary (_, Name x) '.' (_, Name y) & S.is_capital x? spot, Name2 x y
  
  # REWRITE_UNIT_NAME long unit fullname a.X.y -> ((a . X) . y) -> X.y a
  Binary (_, Binary a '.' (_, Name x)) '.' (_, Name y) & S.is_capital x? Group.exps_exp (do_exps2 [(spot, Name2 x y), a])

  # REWRITE_INFIX
  # a .f b        -> (a (. f) b)       -> f a b
  # f a b . g d e -> (f a b (. g) d e) -> (g (f a b) d e)

  # reverse apply
  # x.f         -> f x
  # f a b . g d e -> (g d e (f a b))
  Binary a '.' b? Group.exps_exp (do_exps2 [b, a]) 

  # generated by Rule.tests_binds, but not user source code
  Binary (_, Binary a '&' b) '|' c?                                           # a & b | c  -->  if a b c
    Group.exps_exp (do_exps2 [(spot, Name 'op_if'), a, b, c])

  Binary a '|' b?                                                             # a | b  ->  x = a; if x x b
    # bind, c = Exp.bind_name a
    # exp (Rule.bind_exp bind (spot, Tree [(spot, Name 'op_if'), c, c, b]))
    do_exp2 (spot, Tree [(spot, Name 'op_if0'), a, b])

  Binary a '&' b?                                                             # a & b  -->  if a b 0
    Group.exps_exp (do_exps2 [((spot, Name 'op_if')), a, b, (spot, Nat 0)])

  Binary (spot2, Tree fun) '=' body?            # default nil return type - f x:t = a  ->  f x:t = a
    do_exp2 (spot, Binary (spot2, Binary (spot2, Tree fun) ':' (spot2, Name 'Z')) '=' body)

  # todo, _ in multi args - f x:t _ : u = a  ->  f x:t _:Z : u = a
  Binary (spot1, Binary (spot2, Tree [name, (spot3, Name '_')]) ':' return) '=' body?            # default nil argument type - f _ : t = a  ->  f _ : t = a
    do_exp2 (spot, Binary (spot1, Binary (spot2, Tree [name, (spot3, Binary spot3,Name'_' ':' spot3,Name'Z')]) ':' return) '=' body)
  
  # eta expand for match rule
  #   {f = (a? b)} ===  {f x = (a? b) x}
  #   {f = (a? b; c)} ===  {f x = (a? b; c) x}
  #   f : t?u = (a? b)  ->  f x:t : u = (a? b) x
  Binary (_, Binary fun ':' (_, Binary arg_type '?' return_type)) '=' body & Exp.is_fun body?
    arg = spot, Name 'x'.S.tick
    typed_arg = spot, Binary arg ':' arg_type
    fun2 = fun.Exp.tree .
      Tree name_args? Tree name_args+[typed_arg]                 # f y.. x:t
      Name name? Tree [fun, typed_arg]                                        # f x:t
      ? Exp.seq_error $Fun 'invalid fun' [(spot, term)]
    body2 = spot, Tree [body, arg]                                            # (a? b) x
    do_exp2 (spot, Binary (spot, Binary (spot, fun2) ':' return_type) '=' body2) # f y.. x:t : u = (a? b) x

  Binary (_, Binary (_, Tree (_, Name '_'),args) ':' type) '=' body?            # REWRITE_NAMELESS _ x:t : u = a  ->  f$n x:t : u = a
    name = spot, Name 'f'.S.tick
    free = free_vars (List.map_add args arg_vars) body
    all_args = (free & List.map free (_ x:Exp : Exp = spot, Binary x ':' (spot, Name 'Any'))) + args
    Ref.seq_add nameless_funs (spot, Binary (spot, Binary (spot, Tree name,all_args) ':' type) '=' body).do_exp2
    free & spot, Tree name,free | name                                          # f x:t y:u  @ free y
    
  # f x,y:t : u = a
  # f z:t   : u = (x,y = z; a)
  Binary (_, Binary (_, Tree name,params) ':' return) '=' body?                 # todo - skip if params = simple var  
    params2, bind_list = params Rule.binds . List.unzip
    body2 = Exp.binary_exps ';' bind_list.List.adds+[body]
    # todo - nto do_exp2 around the whole exp because the pattern is always applied (even without pair)
    spot, Binary (spot, Binary (spot, Tree name,params2).do_exp2 ':' return.do_exp2) '=' body2.do_exp2 

  Binary a o b? spot, Binary (do_exp2 a) o (do_exp2 b)                          # [a; b] and [x,.. = a] already handled in do_exp_exps2

  Row s? spot, Row_ (s do_exp2)

  # todo - Name -> Str or Real
  Name '½'? spot, Real 1./2.
  Name '⅓'? spot, Real 1./3.
  Name '¼'? spot, Real 1./4.
  # Name 'ℯ'? spot, Real (R.exp 1.)
  # Name 'π'? spot, Real 3.14159265358979323846264338327950288

  ? spot, term

Fact (1 . (1? 42) == 42)
Fact (41,1 . (x, 1? x + 2) == 43)
Fact (A . ((x = A)? x) == A)
Fact (A . ((x = A)? x; (x = B_)? x) == A)
Fact (B_ . ((x = A)? x; (x = B_)? x) == B_)

of x:S : S = x.Exp.str_exps.Group.exps.exps.0.Exp.str

Fact (of '42' == '42')

Fact (of '"foo"' == "'foo'")
Fact (of 'a' == 'a')

Fact (of 'a+b' == '(a + b)')
Fact (of 'a,b' == '(a,b)')
Fact (of 'f a,b' == '(f (a,b))')

Fact (of 'a,b' == '(a,b)')
Fact (of 'a,b,c' == '(a,b,c)')
Fact (of 'a,b, c,d' == '((a,b),(c,d))')
Fact (of 'a,(b,c)' == '(a,(b,c))')
Fact (of 'a, (f b, c)' == '(a,((f b),c))')
Fact (of 'x = a, b' == '(x = (a,b))')

Fact (of '[a,b]' == '[a, b]')
Fact (of '[a,b,c]' == '[a, b, c]')
Fact (of '[a,(b,c)]' == '[a, (b,c)]')
Fact (of '[a,b, c,d]' == '[(a,b), (c,d)]')
Fact (of '[0.a]' == '[(a 0)]')                                                  # rewrite after listy

Fact (of 'a+b' == '(a + b)')
Fact (of 'f a+b' == '(f (a + b))')
