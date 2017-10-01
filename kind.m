# class of type

  https://en.wikipedia.org/wiki/Kind_(type_theory)
  
_nat_seq = %0 : %*S                                                             # x = n
_real_seq = %0 : %*S                                                             # x = r
_tag_seq = %0 : %*S                                                             # X = n
_type_seq = %0 : %*S,Type                                                       # X = t
_exp_seq = %0 : %*S,Type                                                        # x = a : t
_type_names = % 1.Set : % S/Z                                                   # X = t, updated in Kind.main via _exp_defs and _type_seq

# todo - generalize to name-types
name_nats = % 1.Set : % S/Z                                                           # x = n
name_reals = % 1.Set : % S/Z                                                           # x = r

name_tags = % 1.Set : % S/Z                                                           # X = n
name_types = % 1.Hash : % S/Type                                                      # X = t
name_funs = % 1.Hash : % S/(return:Type, args:Types)                                  # f x0:t0 x1:t1 ... : t = a
name_exps = % 1.Hash : % S/Type                                                       # x, t for x = a : t

pre op:S x:Exp : Exp = x.Exp.spot, Pre op x

op type:Type : *S =
  type.Exp.tree .
    Op o? [o]
    Pre o t? o, op t
    Binary t o u? op t + (o, op u)
    ? Exp.seq_error $Fun 'invalid' [type]

unary x:S : B = List.in S.eq ['%', '!', '*'] x

predefined x:S : B = List.in S.eq ['Any', 'Mem', 'File'] x | tag x

tag x:S : B = List.in S.eq ['Term', 'Reg', 'Flag'] x                              # todo

name : S ? Term =
  'Z'? Z_
  'I'? I
  'B'? B
  'C'? C_
  'N0'? N0
  'N1'? N1
  'N2'? N2
  'N'? N  
  'S'? S_
  'R'? R_
  x? Name x  
Fact (name 'Z' . str == 'Z')
Fact (name 'foo' . str == 'foo')

# checking well-formedness of type def
#   !%t (! % t)          ->  (! (% t))
#   !%!%t ((! % !) % t)  ->  (! (% (! (% t))))
#   !!%t ((! !) % t)     ->  (! (! (% t)))
# todo - check if the return type, if polymorphic, is contrained by the input type, except Cast.*
of_type exp=spot,term:Type : Type = term .
  Name '_'? spot, Name 'Any'                                                    # diff? Any vs _
  Name 'Z'? spot, Z_
  Name 'I'? spot, I
  Name 'B'? spot, B
  Name 'C'? spot, C_
  Name 'N0'? spot, N0
  Name 'N1'? spot, N1
  Name 'N2'? spot, N2
  Name 'N'? spot, N    
  Name 'S'? spot, S_
  Name 'R'? spot, R_
  Name x & (predefined x | Set.in S.eq !_type_names x)? exp
  Tnat _? exp                                                             # for testing only?
  Nat _? exp
  Pre o t & List.in S.eq ['+', '*', '!', '%'] o? spot, Pre o t.of_type               # seq list opt ref
  Post t o & List.in S.eq ['^'] o? spot, Post t.of_type o                             # row
  Binary t o u & unary o? of_type (List.sum_right (t.op + [o]) pre u)     # % * 0  ->  (% (* 0))
  Binary t o u & List.in S.eq ['^', '?', '-', '/', '~'] o? spot, Binary t.of_type o u.of_type                        # row, fun, map, hash, tree
  Binary x ':' t? spot, Binary x ':' t.of_type                                # key
  Row s? spot, Row_ (s of_type)    
  Tree (_, Name 'Tag') s? spot, Name !Tag.name
  Tree s? spot, Tree (s of_type)                                                   # todo - check arity
  ? Exp.seq_error $Fun 'invalid' [exp]
Fact (Exp.eq1 (of_type (Exp.of '!!S')) (Pre '!' (Spot.nil, Pre '!' (Spot.nil, S_))))

_exp_defs : Exp? Z =
  _, Binary (spot, Name name) '=' (_, Binary body ':' type)?                    # x = a : t
    Ref.seq_add _exp_seq (Type.name_full spot name),type
  _, Binary (spot, Name name) '=' body? body.Exp.tree .                         # 
    Nat _? Ref.seq_add (S.is_capital name & _tag_seq | _nat_seq) (Type.name_full spot name)                  # x = n, X = n
    Real _? Ref.seq_add _real_seq (Type.name_full spot name)                  # x = r
    _ & S.is_capital name? Ref.seq_add _type_seq (name, body)              # X = t
    a? Exp.seq_error $Fun 'invalid' [(spot, a)]

arg_bind : Exp? S, Type =                                                      # x:t  or  x=a:t  ->  x:t
  _, Binary (_, Name x) ':' t? x, t.of_type
  _, Binary (_, Name x) '=' (_, Binary _ ':' t)? x, t.of_type
  a? Exp.seq_error $Fun 'invalid' [a]

_fun_arg_type : Exp? S, Type =
  spot, Binary (spot2, Name x) ':' t? x, (spot, Binary (spot2, Name x) ':' t.of_type)
  spot, Binary (spot2, Name x) '=' (spot3, Binary a ':' t)? x, (spot, Binary (spot2, Name x) '=' (spot3, Binary a ':' t.of_type))
  a? Exp.seq_error $Fun 'invalid' [a]
    
_fun_type : Exp? *(S, Type,Types) =                                         # return type, argument types
  spot, Binary (_, Binary (_, Tree (_, Name name),args) ':' return) '=' _?         # function definition - f x:t.. : t = a
    arg_types = List.map (List.map args _fun_arg_type) Row.at1    # Type.TODO_MAX_ARG
    [(Type.name_full spot name, (of_type return, arg_types))]

main exps:Exps =
  List.do exps _exp_defs
  name_nats (!_nat_seq).List.set                                                # x = n
  name_reals (!_real_seq).List.set                                              # x = r
  name_tags (!_tag_seq).List.set                                                # X = n
  _type_names (Map.key_set !_type_seq)
  name_types (Map.map1 of_type !_type_seq . List.hash)                          # after updating _type_names above
  name_funs (List.map_add exps _fun_type . List.hash)  
  name_exps (Map.map1 of_type !_exp_seq).List.hash

of x:S : Type = x.Exp.type_of.of_type
Fact (Exp.eq1 (of 'S') S_)
Fact (Exp.eq1 (of '"42"') (Tnat 42))
