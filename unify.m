# constraint resolve

  https://en.wikipedia.org/wiki/Unification_(computer_science)
  https://en.wikipedia.org/wiki/Subtyping

of_type spot:Spot note:S s:Exps x:Type y:Type : Equals, Type =
  of_type1_opt x y | of_type1_opt y x | Type.spot_exps_error spot,note,(x,(y,s))

of_types_opt r:Types s:Types : !(Equals, Exps) =
  unify = List.map2 r s of_type_opt 
  List.all unify Opt.bit &
    equals_seq, types = List.unzip unify
    List.adds equals_seq, types

of_type_opt x:Type y:Type : !(Equals, Exp) =
  of_type1_opt x y | of_type1_opt y x

of_type0 spot,note,exps:Spot,S,Exps x:Type y:Type : Equals, Exp =    
  of_type1_opt x y | of_type1_opt y x | Type.spot_exps_error (spot, note, x,(y,exps))

of_type2 error:Spot,S,Exps x:Type equals,y:Equals,Type : Equals, Type =
  equals2, type = of_type0 error x y
  of_equals error equals equals2, type

of_exp_type spot,note,exps:Spot,S,Exps a:Exp x:Type y:Type : Equals, Exp =
  of_type1_opt x y | of_type1_opt y x | Type.spot_exps_error (spot, note, a,(x,(y,exps)))

of_type1_opt x:Type y:Type : !(Equals, Exp) = of_type1 x y  

max : Term ? N = # todo - !N
  B? 1
  N0? 0ff
  N1? 0ffff
  N2? 0ffff_ffff
  C_? C.max
  I? 07fff_ffff_ffff_ffff
  N? 0ffff_ffff_ffff_ffff

of_type1 x:Type y:Type : !(Equals, Type) =
  spot = Exp.spot x
  x.Exp.tree,y.Exp.tree .
    # inlined Exp.eq (via Term.eq)
    Z_, Z_? 0, x
    B, B? 0, x
    C_, C_? 0, x
    N, N? 0, x
    N, I? 0, x
    I, N? 0, y
    I, I? 0, x
    R_, R_? 0, x
    S_, S_? 0, x
        
    Name x1, Name x2 & x1 == x2? 0, x
    Tnat x1, Tnat x2 & x1 == x2? 0, x
    Nat x1, Nat x2 & x1 == x2? 0, x
    Nat n, Nat m & n > m? [(m, x)], y                                           # else, type_apply will loop

    _, Pre '!' (_, Pre '!' t) & Exp.eq x t? 0, y                                # todo - simplify with case t <: t!
    
    Binary a '=' t, _?
      of_type_opt t y .
        equals, type? equals, (spot, Binary a '=' type)

    _, Binary a '=' t?
      of_type_opt x t .
        equals, type? equals, (spot, Binary a '=' type)

    Binary a ':' t, _?
      of_type_opt t y .
        equals, type? equals, (spot, Binary a ':' type)

    _, Binary a ':' t?
      of_type_opt x t .
        equals, type? equals, (spot, Binary a ':' type)

    # todo - Opt.nat coersion cast        
    _, Pre '!' t & Exp.eq x t? 0, y                                             # t <: t!, before n <: t NAT_OCCUR below. else, Unify.of_type1 invalid occur 0 (! 0)
                      
    Nat n, _?                                                                   # NAT_OCCUR
      Type.occur n y & Exp.seq_error $Fun 'invalid occur' [x, y]
      [(n, y)], y                                                    # i == y, polymorphic

    Name 'Any', _? 0, y                                                         # type cast
    Tnat m, Tnat n? 0, (spot, Tnat (N.max n m))                                 # else, unify #0 #1 N = unify (unify #0 #1) N = unify B N fails
    Binary _ ':' t, _? of_type1 t y
    _, Binary _ ':' t? of_type1 x t                                             # why needed?
    
    #B, N? 0, y   # do not unify B and N - since B.eq needs B
    C_, N? 0, y                                                                  # good idea?
    N0, N1? 0, y
    N0, N2? 0, y
    N1, N2? 0, y
    N0, N? 0, y
    N1, N? 0, y
    N2, N? 0, y
  
    Tnat 0, Z_? 0, y

    Tnat n, u & (m = max u; m > 0 & n <= m)? 0, y

    Tnat 0, Pre '*' _? 0, y                                                    # #0 <: *t
    
    Tnat 0, Pre '+' _? 0, y                                                    # #0 <: +t

    Tnat 0, Pre '!' _? 0, y                                                    # ZERO_OPT #0 ^ t! = t!

    Tnat 0, Row [t, u]?                                                     # u ^ t* = v  =>  #0 ^ t,u = v
      type = spot, Pre '*' t
      of_type_opt type u | 0, (spot, Pre '!' y)                                  # #0 ^ t,u = !(t,u)

    Pre o1 t1, Pre o2 t2 & o1 == o2?                                          # !t %t *t   t <: u  =>  op t <: op u
      of_type_opt t1 t2 .
        equals, type? equals, (spot, Pre o1 type)

    Post t1 o1, Post t2 o2 & o1 == o2?                                          
      of_type_opt t1 t2 .
        equals, type? equals, (spot, Post type o1)

    # todo - (_ x:Exp : B = (_,N? 1) x) -> (_,N? 1)
    # todo - Tnat -> unify with N
    Post _,N '^', Row s & List.all s (_ x:Exp : B = (_, Tnat _? 1) x)? 0, x

    Binary t1 o1 u1, Binary t2 o2 u2?                                           # t,t t-t t?t
      o1 == o2 &
        unify1 = of_type_opt t1 t2
        unify2 = of_type_opt u1 u2
        unify1 & unify2 &
          equals1, type1 = unify1
          equals2, type2 = unify2
          of_equals (spot, $Fun + ' type1 - op', [x,y]) equals1 equals2, (spot, Binary type1 o1 type2)
        
    Row [t, u], Pre '*' (_, Name 'Any')?                                        # *Any with (#42,(S,(#42,#0)))
      0, x
    
    # PAIR_LIST 2,(3,(5,0))  ==  *N
    Row [t, u], Pre '*' _?                                                      # t,u and y=*v
      unify0 = of_type_opt u y                                                  # u = *v   ->  p
      unify1 = unify0 & of_type_opt (spot, Pre '*' t) y                         # *t = *v  ->  q
      unify0 & unify1 &
        equals0, p = unify0                                                     
        equals1, q = unify1
        of_type_opt p q .
         equals2, r?
          of_equals_opt equals0 equals1 .                                         # t, t* = t*
            equals3, 1?
              of_equals_opt equals3 equals2 .
                equals4, 1? equals4, r
  
    Pre '!' t1, Pre '*' t2?                                                     # t! <: t*
      of_type_opt t1 t2 .
        equals, type? equals, (spot, Pre '*' type)                        # u ^ v = t  =>  u! ^ v* = t*
      
    Pre '!' _, Tnat 0? 0, x                                                     # else, !t .unify #0 == !!t 

    Pre '!' t, _ & Exp.eq t y? 0, x                                            # t! <: t
    
    Pre '!' t1, _?                                                             # t <: t!
      of_type_opt t1 y .
        equals, type? equals, (spot, Pre '!' type)                        # u <: v  -->  u <: v!
    
    Row r, Row s? of_types_opt r s .
      equals, types? equals, (spot, Row_ types)

    Tree r, Tree s? of_types_opt r s .
      equals, types? equals, (spot, Tree types)

    N, Name y0 & Kind.tag y0? 0, y                                              # N <: Term or reg..

    Name x0, _?                                                                 # NAME_DEF 
      type = Hash.get !Kind.name_types x0
      type & of_type_opt type y

    # S, #0  ->  !S
    # Name and Nat need reflexive rules above
    Tnat 0, _ & !((_, Name _? 1; _, Nat _? 1) y)?  0, (spot, Pre '!' y)                                           # #0 <: t!      

Fact (of_type1 (Kind.of '!"42"') (Kind.of '"42"') . (e, t? ! e.List.bit & Exp.eq t '!"42"'.Kind.of))
Fact (of_type1 (Kind.of '*"0"') (Kind.of '*1') . (e, t? e.List.bit & Exp.eq t '*"0"'.Kind.of))
Fact (of_type1 (Kind.of 'N') (Kind.of 'Term') . (_, t? Exp.eq t 'Term'.Kind.of))
#Fact (of_type1 (Kind.of 'Term') (Kind.of 'N') . (_, t? Exp.eq t 'Term'.Kind.of)) # not reflexive


# equality modulo name_types
term_eq x:Term y:Term : B = x,y .
  # inlined Exp.eq (via Term.eq)
  # todo - factor with Unify.of_type1
  Z_, Z_? 1
  B, B? 1
  C_, C_? 1
  N0, N0? 1
  N1, N1? 1
  N2, N2? 1
  N, N? 1  
  S_, S_? 1
  R_, R_? 1
  Nat m, Nat n? n == m  
  Pre o1 t1, Pre o2 t2? o1 == o2 & eq t1 t2
  Post t1 o1, Post t2 o2? o1 == o2 & eq t1 t2
  Binary _ '=' _,t, _? term_eq t y
  _, Binary _ '=' _,t? term_eq x t
  Binary _ ':' _,t, _? term_eq t y
  _, Binary _ ':' _,t? term_eq x t  
  Binary t1 o1 u1, Binary t2 o2 u2? o1 == o2 & eq t1 t2 & eq u1 u2
  Tree s1, Tree s2? List.all2 s1 s2 eq
  Row s1, Row s2? List.all2 s1 s2 eq
  Name 'Any', _? 1
  _, Name 'Any'? 1
  Name w, Name z & S.eq w z? 1
  Name z, _ & Hash.in !Kind.name_types z?
    term_eq (Opt.get (Hash.get !Kind.name_types z) $Fun . Exp.tree) y
  _, Name z & Hash.in !Kind.name_types z?
    term_eq (Opt.get (Hash.get !Kind.name_types z) $Fun . Exp.tree) x

eq _,x:Exp _,y:Exp : B = term_eq x y

eq1 _,x:Exp y:Term : B = term_eq x y

# fixme - match with opt type
of_str x:S y:S : S =
  unify = of_type_opt x.Kind.of y.Kind.of
  | unify & Exp.str unify.1
  | ''

str_eq x:S y:S z:S : B =
  z1 = of_str x y
  z2 = z.S.bit & z.Exp.type_of.Exp.str | ''
  z1 == z2 | (Log.fill "$s\. unify:\.  $s\.  $s\. got: $s\. want: $s" [$Fun, x, y, z1, z2]; 0) # fixme - extra output
  
# reflexive  All (x? str_eq x x == x)
# symmetric  All (x? y? str_eq x y == str_eq y x)
# transitive All (x? y? z? p:(str_eq x y == str_eq y z)? q:(str_eq x y == str_eq y z)? str_eq x z)
Fact (str_eq 'Z' 'Z' 'Z')
Fact (str_eq 'Z' 'B' '')
Fact (str_eq 'Z' 'C' '')
Fact (str_eq 'Z' 'N' '')
Fact (str_eq 'Z' 'S' '')
Fact (str_eq 'Z' '!N' '')
Fact (str_eq 'Z' '%N' '')
Fact (str_eq 'Z' 'B,N' '')
Fact (str_eq 'Z' 'B?N' '')
Fact (str_eq 'Z' '0' 'Z')
Fact (str_eq '0' 'Z' 'Z')
Fact (str_eq '"0"' 'Z' 'Z')
Fact (str_eq 'Z' '"0"' 'Z')
Fact (str_eq '"1"' 'Z' '')
Fact (str_eq 'Z' '"1"' '')

Fact (str_eq 'B' 'B' 'B')
Fact (str_eq 'B' 'C' '')
Fact (str_eq 'B' 'N' '')                                                            # do not unify B and N since B.str_eq != N.str_eq
Fact (str_eq 'B' 'S' '')
Fact (str_eq 'B' '!N' '')
Fact (str_eq 'B' '%N' '')
Fact (str_eq 'B' 'B,N' '')
Fact (str_eq 'B' 'B?N' '')
Fact (str_eq '"0"' 'B' 'B')
Fact (str_eq 'B' '"0"' 'B')
Fact (str_eq '"1"' 'B' 'B')
Fact (str_eq 'B' '"1"' 'B')
Fact (str_eq '"2"' 'B' '')
Fact (str_eq 'B' '"2"' '')

Fact (str_eq 'C' 'B' '')
Fact (str_eq 'C' 'C' 'C')
Fact (str_eq 'C' 'N' 'N')
Fact (str_eq 'C' 'S' '')
Fact (str_eq 'C' '!N' '!N')
Fact (str_eq 'C' '%N' '')
Fact (str_eq 'C' 'B,N' '')
Fact (str_eq 'C' 'B?N' '')
Fact (str_eq '"0"' 'C' 'C')
Fact (str_eq 'C' '"0"' 'C')
Fact (str_eq 'C' '"1"' 'C')
Fact (str_eq 'C' '"2"' 'C')

Fact (str_eq 'N' 'N' 'N')
Fact (str_eq 'N' 'S' '')
Fact (str_eq 'N' '!N' '!N')
Fact (str_eq 'N' '%N' '')
Fact (str_eq 'N' 'B,N' '')
Fact (str_eq 'N' 'B?N' '')
Fact (str_eq '"0"' 'N' 'N')
Fact (str_eq 'N' '"0"' 'N')
Fact (str_eq 'N' '"1"' 'N')
Fact (str_eq 'N' '"2"' 'N')

Fact (str_eq 'S' 'S' 'S')
Fact (str_eq 'S' '!N' '')
Fact (str_eq 'S' '%N' '')
Fact (str_eq 'S' 'B,N' '')
Fact (str_eq 'S' 'B?N' '')
Fact (str_eq '"0"' 'S' '!S')
Fact (str_eq 'S' '"0"' '!S')
Fact (str_eq 'S' '"1"' '')
Fact (str_eq 'S' '!S' '!S')
Fact (str_eq '!S' 'S' '!S')
Fact (str_eq '*S' '*!S' '*!S')
Fact (str_eq '*!S' '*S' '*!S')

Fact (str_eq '0' '!!0' '! !0')
Fact (str_eq '!0' '0' '!0')
Fact (str_eq '0' '!0' '!0')
Fact (str_eq '1' '!1' '!1')

Fact (str_eq '*"0"' '*1' '*"0"')
Fact (str_eq '*!0' '*0' '*!0')
Fact (str_eq '*0' '*!0' '*!0')
Fact (str_eq '*!0' '*!0' '*!0')
Fact (str_eq '*!1' '*!1' '*!1')

Fact (str_eq 'N' '!N' '!N')
Fact (str_eq '!N' '!N' '!N')
Fact (str_eq '!N' '%N' '')
Fact (str_eq '!N' 'B,N' '')
Fact (str_eq '!N' 'B?N' '')
Fact (str_eq '!N' '0' '!N')

Fact (str_eq '%N' '%N' '%N')
Fact (str_eq '%N' 'B,N' '')
Fact (str_eq '%N' 'B?N' '')
Fact (str_eq '%N' '0' '%N')

Fact (str_eq 'N' '*N' '')
Fact (str_eq 'N, *N' '*N' '*N')
Fact (str_eq '!N' '*N' '*N')
Fact (str_eq 'S' '*S' '')
Fact (str_eq '*S' '*S' '*S')
Fact (str_eq 'S, *S' '*S' '*S')
Fact (str_eq '*S' 'B,N' '')
Fact (str_eq '*S' 'B?N' '')
Fact (str_eq '*S' '0' '*S')

Fact (str_eq '*N' 'N, *N' '*N')
Fact (str_eq '*N' 'N, (N, *N)' '*N')
Fact (str_eq '*N' 'N, (N, (N, *N))' '*N')

Fact (str_eq 'N, *N' '*N' '*N')
Fact (str_eq 'N, "0"' '*N' '*N')
Fact (str_eq 'S, *N' '*N' '')                                         
Fact (str_eq '"0", (N, "0")' '*N' '*N')                                         # #0 is N, hence N,(N,#0) -> *N
Fact (str_eq '"0", (S, "0")' '*S' '*!S')
Fact (str_eq '("0", "0")' '(S, "0")' '!S,"0"')
Fact (str_eq '("0", "0")' '*S' '*!S')

Fact (str_eq '*(N,N)' '*(N,N)' '*(N,N)')
Fact (str_eq '*(N,N)' '(N,N), *(N,N)' '*(N,N)')
Fact (str_eq '*(N,N)' '(N,N), ((N,N), *(N,N))' '*(N,N)')

# [0,2, 1,3, 2,5] : *0  # needs max in Tnat

Fact (str_eq '*N' '**N' '')

Fact (str_eq '*N' '*S' '')

Fact (str_eq 'B,N' 'B,N' 'B,N')
Fact (str_eq 'B,N' 'B?N' '')
Fact (str_eq 'B,N' '0' 'B,N')

Fact (str_eq 'B?N' 'B?N' 'B?N')
Fact (str_eq 'B?N' '0' 'B?N')

exp_type exp:S type:S : B = of_type_opt exp.Type.of_str type.Kind.of . Opt.bit
Fact (exp_type '0' '"0"')
Fact (exp_type '0' 'N')
Fact (exp_type '0' 'S')                                                         # !S
Fact (exp_type '[0, "a"]' '*S')                                                 # !*S

exp_type_cast exp:S type:S : B =
  type2 = type.Kind.of
  unify = of_type_opt exp.Type.of_str type2
  unify & eq unify.1 type2
Fact !(exp_type_cast '0' 'S')
Fact !(exp_type_cast '[0, "a"]' '*S')
Fact (exp_type_cast '[0, "a"]' '*!S')
Fact (exp_type_cast '[0] + ["a"]' '*!S')
# Fact (str_eq 'terms' '*term' 'terms') # todo - init Kind

of_equal equal:Equal equals:Equals : Equals =
  var, type0 = equal
  type1 = Map.get N.eq equals var
  | type1 &
    of_type_opt type0 type1 .
     equals1, type2?
       equals2, unify2 = of_equals_opt equals1 equals
       unify2 & var,type2, equals2
  | equal, equals

of_equals1 error:Spot,S,Exps equal:Equal equals:Equals : Equals =
  var, type0 = equal
  type1 = Map.get N.eq equals var
  | type1 &
    unify = of_type0 error type0 type1
    unify &
      equals2, type2 = of_type0 error type0 type1
      var,type2, of_equals error equals2 equals
  | equal, equals

of_equals error:Spot,S,Exps x:Equals y:Equals : Equals =
  List.sum_bad x (of_equals1 error) y

of_equals_list error:Spot,S,Exps s:*Equals : Equals =
  List.sum_left s (of_equals error) 0

of_equals_opt x:Equals y:Equals : Equals, B =                   # equals! but fix [unify t*! t* in type.py]
  z = List.sum_right x of_equal y
  z, ((x.List.bit | List.bit y) == List.bit z) # right

partial x=y,z:S,S : B = List.any ['Row','init', 'Seq','tick', 'Seq','bit_and', 'Seq','bit_opt', 'Seq','not', 'Seq','pump', 'S','pump'] (Pair.eq_by S.eq S.eq x) | (y == 'Fun' & S.prefix z 'new') | y == 'Dl'
Fact (partial 'Seq','tick')
Fact !(partial 'Seq','foo')

# apply function type and get the return type
apply at:N spot:Spot exp:Exp fun:Exp args:Exps equals:Equals : fun_type:Type, arg_types:Types? Term, Equals, Type =
  # t, vs & (spot.Spot.unit == 'Thread' & (K 23; Exp.log exp; Exp.log t; Exp.seq_log vs); 0)? Fail.main $Fun
  (_, Binary (_, Binary x '=' (_, Binary a ':' t)) '?' u), 0?                   # default argument - x=a:t? u
    # todo - check if a is of type u in Kind
    apply at+1 spot exp fun args+[a] equals u,0
  (_, Binary t '?' u), 0?                                                       # t? u
    # todo - check how ocaml recognize partial functions
    # todo - change return type of at Dl.main, Fun.new*, Any.cast
    unit = Spot.unit spot
    | ((_, Tree (_, Name f),_ & partial unit,f? 1) exp | (_, Tree (_, Name2 unit2,f),_ & partial unit2,f? 1) exp | (_, Tree (_, Name 'Dl'),_? 1) exp | ((_, Tree (_, Name2 unit2,_),_) & (unit2 == 'Any')? 1) exp) & # UNIFY_APPLY - Row.init
      Tree fun,args, equals, (spot, Binary t '?' u)
    | Tree ((spot, Name (S.fill 'Fun.new$n_$n' [List.size args, 1 + Fun.arity u])), (fun, args)), equals, (spot, Binary t '?' u) # see Fun.new1_1, Fun.new2_1, ...
  t, 0? Tree fun,args, equals, t
  (_, Binary t '?' u), v,vs?                                                    # t? u
    # t = expected arg type from function type
    # v = actual arg type from application expression
    # exp = toplevel expression
    equals1, _ = of_type0 spot,(S.fill '$s: type mismatch at argument $n: formal type, actual type, expression' [$Fun, at]),[exp] t v
    equals2 = of_equals spot,(S.fill '$s: type mismatch at argument $n: last context, current context, expression' [$Fun, at]),[exp, (0, Nat at)] equals equals1
    apply at+1 spot exp fun args equals2 u,vs
  t, vs? Exp.seq_error $Fun 'invalid' exp,(t,vs)
  ? Fail $Fun # assert false

apply0 at:N spot:Spot exp:Exp fun:Exp args:Exps equals:Equals fun_type,arg_types:Type,Types : Equals, Exp, Type =
  app, equals2, return = apply 0 spot exp fun args equals fun_type,arg_types
  0, (spot, app), return
