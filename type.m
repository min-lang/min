# class of term

  https://en.wikipedia.org/wiki/Type_system
  https://www.cis.upenn.edu/~bcpierce/tapl/ Types and Programming Languages
  http://graydon2.dreamwidth.org/253769.html Next big step for compiled languages
  https://github.com/steshaw/plt A path to Programming Language Theory enlightenment 
   
Type = Exp
Types = *Type

eq x:Type y:Type : B = Exp.eq x y
str x:Exp : S = Exp.str x

Equal = N, Exp                                                               # type variable bindings
Equals = *Equal
Binds = *(S, Exp)                                                          # term variable bindings

binds_str s:Binds : S = Map.str_by Fun.id Exp.str s
binds_log s:Binds = s.binds_str.Log
    
#equals_str s:Equals : S = str s # Equal.str
equals_str s:Equals : S = Map.str_by N.str Exp.str s
equals_log s:Equals = s.equals_str.Log
binds_str s:Binds : S = Map.str_by Fun.id Exp.str s

clock = %0 : %N

# type variable occurs, not free, in the type
occur x:N : Type? B =
  _, Nat y? x == y
  _, Tree s? List.any s (occur x) 
  _, Row s? List.any s (occur x) 
  _, Pre _ t? occur x t 
  _, Post t _? occur x t
  _, Binary _ ':' t? occur x t
  _, Binary _ '=' t? occur x t
  _, Binary t _ u? occur x t | occur x u                                        
  # Char Str Name Name2 Op Level Tnat? 0
Fact (occur 0 '0'.Kind.of)
Fact !(occur 0 '"0"'.Kind.of)
Fact !(occur 0 'S'.Kind.of)

# apply equals to :Type variable Nat n
apply equals:Equals type:Type : Exp =
  spot = Exp.spot type
  type.Exp.tree .
    Nat n? Map.get_by N.eq equals n .
      0? type
      type2?
        occur n type2 & Exp.seq_error $Fun 'invalid' [type, type2]              # or, 0 -> S,0 -> S,S,0 ..
        apply equals type2
    Tree s? spot, Tree (s (apply equals))
    Row s? spot, Row_ (s (apply equals))
    Pre o t? spot, Pre o (apply equals t)
    Binary t o u? spot, Binary (apply equals t) o (apply equals u)
    ? type
Fact (Exp.eq1 (apply [] (Spot.nil, Nat 0)) (Nat 0))
Fact (Job.err (? apply [(0, (Spot.nil, Nat 0))] (Spot.nil, Nat 0) . Z) . Regex.search 'Type.apply invalid 0 0')

spot_exps_error spot,note,exps:(Spot,S,Exps) : 0 = Fail.main4 spot.Spot.str note 0a.C.str exps.Exp.seq_strs
  
exps_if_types_error exps:Exps types0:Exps types1:Exps error:Spot,S,Exps : Equals =
  !types0 == !types1 | (Log.fill 'sizes diff - $n vs $n' [types0.List.size, types1.List.size]; spot_exps_error error)
  Unify.of_equals_list error (List.map (List.map3 exps types0 types1 (Unify.of_exp_type error)) Row.at0) # TODO_MAX_ARG

binary_op_name exp:Exp op:S : S = op.Op.name | Exp.seq_error $Fun 'op name' [exp]

unary_op_name exp:Exp op:S : S = op.Op.name_unary | Exp.seq_error $Fun 'op name' [exp]

# e1:t1
# e2:t2
# t1 <: t3
# t2 <: t4
exps_if_types fun:S spot:Spot name:S type:Term equals:Equals binds:Binds exp1:Exp typed_exp1:Exp type1:Type exp2:Exp typed_exp2:Exp type2:Type type3:Type type4:Type : !(Equals, Exp, Type) =
  unify1 = Unify.of_type_opt type1 type3 # todo? equals
  unify1 &
    unify2 = Unify.of_type_opt type2 type4
    unify2 &
      equals2 = Unify.of_equals (spot, $Fun, [exp1]) unify1.0 unify2.0
      equals2, (spot, Tree [(spot, Name name), typed_exp1, typed_exp2]), (apply equals2 spot,type)

unary_exps_if_types fun:S spot:Spot name:S type:Term equals:Equals binds:Binds exp1:Exp typed_exp1:Exp type1:Type type3:Type : !(Equals, Exp, Type) =
  unify1 = Unify.of_type_opt type1 type3                                         # todo? equals
  unify1 &
    equals, (spot, Tree [(spot, Name name), typed_exp1]), (apply unify1.0 spot,type)

max_type_var = 10

# instantiate with new type variables, such that different applications don't get mixed up with the same type variables
# arg_new base:N _,type:Arg : Type = type_new base type
arg_new base:N type:Type : Type = type_new base type

type_new base:N type:Type : Type =
  spot = Exp.spot type
  type.Exp.tree .
    Nat n?
      n < max_type_var | Exp.seq_error $Fun 'type var >= max_type_var' [type]
      spot, Nat base+n
    Tree s? spot, Tree (s (type_new base))
    Row s? spot, Row_ (s (type_new base))
    Pre o t? spot, Pre o (type_new base t)
    Binary a ':' t? spot, Binary a ':' (type_new base t)                        # x:t  or  x:a=t
    Binary x '=' t? spot, Binary x '=' (type_new base t)
    Binary t o u? spot, Binary (type_new base t) o (type_new base u)
    ? type

type_var_tick = %0 : %N
type_var _ : N = max_type_var * type_var_tick.Ref.tick

unary_types fun:S binds:Binds exp0:Exp spot:Spot op:S exp1:Exp : !(Equals, Exp, Type) =
  equals0, typed_exp1, type1 = of_exp fun binds exp1
  | op == '-' & B.or
   unary_exps_if_types fun spot 'N.neg' N equals0 binds exp1 typed_exp1 type1 spot,N
   unary_exps_if_types fun spot 'R.neg' R_ equals0 binds exp1 typed_exp1 type1 spot,R_
   Exp.seq_error $Fun op [exp0, type1]

  | op == '!' & B.or
    # todo - Opt.bit
   unary_exps_if_types fun spot 'B.not' B equals0 binds exp1 typed_exp1 type1 spot,B 
   (t = Nat 0.type_var; u = spot, Pre '%' spot,t; unary_exps_if_types fun spot 'Ref.get' t equals0 binds exp1 typed_exp1 type1 u) # %0? 0 - apply equals return
   unary_exps_if_types fun spot 'S.size' N equals0 binds exp1 typed_exp1 type1 spot,S_ 
   (t = spot, Pre '*' (spot, Nat 0.type_var); unary_exps_if_types fun spot 'List.size' N equals0 binds exp1 typed_exp1 type1 t) # *0? N
   (t = spot, Pre '+' (spot, Nat 0.type_var); unary_exps_if_types fun spot 'Seq.size' N equals0 binds exp1 typed_exp1 type1 t) # +0? N
   (t = Nat 0.type_var; u = spot, Binary (spot, Z_) '?' spot,t; unary_exps_if_types fun spot 'Fun.do' t equals0 binds exp1 typed_exp1 type1 u) # Z?0? 0
   Exp.seq_error $Fun '! invalid' [exp0, type1]

  | 
    name = unary_op_name exp0 op
    Hash.get !Kind.name_funs name .
      return_type0, arg_types0?
        base = !type_var      
        return_type = type_new base return_type0
        arg_types = arg_types0 (arg_new base)
        !arg_types == 1 | Exp.seq_error $Fun 'invalid unary op' [exp0]
        type3, _ = arg_types 
        equals5, _ = Unify.of_type spot $Fun [exp1] type1 type3
        equals7 = Unify.of_equals (spot, $Fun, [exp0]) equals0 equals5
        typed_exp0 = spot, Tree ((spot, Name name), [typed_exp1])
        equals7, typed_exp0, apply equals7 return_type
      ? Exp.seq_error $Fun 'not defined' [exp0, type1]

binary_types fun:S binds:Binds exp0:Exp spot:Spot exp1:Exp op:S exp2:Exp : Equals, Exp, Type =  
  equals1, typed_exp1, type1 = of_exp fun binds exp1
  equals2, typed_exp2, type2 = of_exp fun binds exp2
  equals0 = Unify.of_equals (spot, $Fun, [exp0]) equals1 equals2
  name = binary_op_name exp0 op
  
  | op == '≈' & B.or
   exps_if_types fun spot 'R.sim' B equals0 binds exp1 typed_exp1 type1 exp2 typed_exp2 type2 spot,R_ spot,R_
   Exp.seq_error $Fun name [exp0, type1, type2]
        
  | op == '==' & B.or
   Unify.of_type_opt type1 type2 . (_,type? of_exp fun binds (spot, class2 exp0 'eq' exp1 exp2 type))
   Exp.seq_error $Fun name [exp0, type1, type2]
  
  | op == '!=' & B.or
   Unify.of_type_opt type1 type2 . (_,type? of_exp fun binds (spot, class2 exp0 'ne' exp1 exp2 type))
   Exp.seq_error $Fun name [exp0, type1, type2]

  | op == '+' & B.or  # List.add and Seq.add not higher order, hence not using class2
   exps_if_types fun spot 'N.add' N equals0 binds exp1 typed_exp1 type1 exp2 typed_exp2 type2 spot,N spot,N # N N N
   exps_if_types fun spot 'N.add' N equals0 binds exp1 typed_exp1 type1 exp2 typed_exp2 type2 spot,N spot,I # N I I
   exps_if_types fun spot 'N.add' I equals0 binds exp1 typed_exp1 type1 exp2 typed_exp2 type2 spot,I spot,I # I I I
   exps_if_types fun spot 'R.add' R_ equals0 binds exp1 typed_exp1 type1 exp2 typed_exp2 type2 spot,R_ spot,R_ # R R R
   exps_if_types fun spot 'N.add' S_ equals0 binds exp1 typed_exp1 type1 exp2 typed_exp2 type2 spot,S_ spot,N # S N S
   exps_if_types fun spot 'N.add' S_ equals0 binds exp1 typed_exp1 type1 exp2 typed_exp2 type2 spot,S_ spot,I # S I S
   exps_if_types fun spot 'S.add' S_ equals0 binds exp1 typed_exp1 type1 exp2 typed_exp2 type2 spot,S_ spot,S_ # S S S
   (t = Pre '*' (spot, Nat 0.type_var); exps_if_types fun spot 'List.add' t equals0 binds exp1 typed_exp1 type1 exp2 typed_exp2 type2 spot,t spot,t) # *0? *0? *0 - apply equals return
   (t = Pre '+' (spot, Nat 0.type_var); exps_if_types fun spot 'Seq.add' t equals0 binds exp1 typed_exp1 type1 exp2 typed_exp2 type2 spot,t spot,t) # +0? +0? +0 - apply equals return
   exps_if_types fun spot 'N.add' Name'Mem' equals0 binds exp1 typed_exp1 type1 exp2 typed_exp2 type2 spot,Name'Mem' spot,N 
   Exp.seq_error $Fun name [exp0, type1, type2]
   
  | op == '-' & B.or
   exps_if_types fun spot 'N.sub' N equals0 binds exp1 typed_exp1 type1 exp2 typed_exp2 type2 spot,N spot,N # N? N? N
   exps_if_types fun spot 'N.sub' N equals0 binds exp1 typed_exp1 type1 exp2 typed_exp2 type2 spot,S_ spot,S_ # S? S? N
   exps_if_types fun spot 'R.sub' R_ equals0 binds exp1 typed_exp1 type1 exp2 typed_exp2 type2 spot,R_ spot,R_ # R? R? R
   exps_if_types fun spot 'N.sub' Name'Mem' equals0 binds exp1 typed_exp1 type1 exp2 typed_exp2 type2 spot,Name'Mem' spot,N # Mem? N? Mem
   exps_if_types fun spot 'N.sub' N equals0 binds exp1 typed_exp1 type1 exp2 typed_exp2 type2 spot,Name'Mem' spot,Name'Mem' # Mem? Mem? N
   Exp.seq_error $Fun name [exp0, type1, type2]

  | op == '/' & B.or
   exps_if_types fun spot 'N.div' N equals0 binds exp1 typed_exp1 type1 exp2 typed_exp2 type2 spot,N spot,N # N? N? N
   exps_if_types fun spot 'R.div' R_ equals0 binds exp1 typed_exp1 type1 exp2 typed_exp2 type2 spot,R_ spot,R_ # R? R? R
   Exp.seq_error $Fun name [exp0, type1, type2]

  | op == '*' & B.or
   exps_if_types fun spot 'N.mul' N equals0 binds exp1 typed_exp1 type1 exp2 typed_exp2 type2 spot,N spot,N # N? N? N
   exps_if_types fun spot 'R.mul' R_ equals0 binds exp1 typed_exp1 type1 exp2 typed_exp2 type2 spot,R_ spot,R_ # R? R? R
   Exp.seq_error $Fun name [exp0, type1, type2]

  | op == '^' & B.or
   exps_if_types fun spot 'R.pow' R_ equals0 binds exp1 typed_exp1 type1 exp2 typed_exp2 type2 spot,R_ spot,R_ # R? R? R
   Exp.seq_error $Fun name [exp0, type1, type2]
          
  | op == '<' & B.or
   exps_if_types fun spot 'N.lt' B equals0 binds exp1 typed_exp1 type1 exp2 typed_exp2 type2 spot,N spot,N # N? N? B
   exps_if_types fun spot 'R.lt' B equals0 binds exp1 typed_exp1 type1 exp2 typed_exp2 type2 spot,R_ spot,R_ # R? R? B
   Exp.seq_error $Fun name [exp0, type1, type2]
      
  |
    name2 = 'N.' + name
    Hash.get !Kind.name_funs name2 .
      return_type0, arg_types0?
        base = !type_var      
        return_type = type_new base return_type0
        arg_types = arg_types0 (arg_new base)
        !arg_types == 2 | Exp.seq_error $Fun 'invalid binary op' [exp0]
        type3 = arg_types.0
        type4 = arg_types.1
        equals5, _ = Unify.of_type spot $Fun [exp1] type1 type3
        equals6, _ = Unify.of_type spot $Fun [exp2] type2 type4
        equals7 = Unify.of_equals (spot, $Fun, [exp0]) equals0 
         Unify.of_equals (spot, $Fun, [exp0]) equals5 equals6
        typed_exp0 = spot, Tree ((spot, Name name2), [typed_exp1, typed_exp2])
        equals7, typed_exp0, apply equals7 return_type
      ? Exp.seq_error $Fun 'not defined' [exp0]
  
# a | b    same as [a & 0 | b]
# ->  op_if0 a b
# ->  x = a; op_if x x b
op_if0_types fun:S binds:Binds spot:Spot exp0:Exp test:Exp body:Exp : Equals, Exp, Type =
  exp = spot, Name 'op_if0'
  equals0, typed_exp0, type0 = of_exp fun binds test
  equals2, typed_exp2, type2 = of_exp fun binds body 
  # t .in B, C, N, !t, *t   types that include the literal 0
  #   !t? t? t   but not *t; else, B | *Exp but 1 is not *Exp
  #   t? t? t
  #   t? _? Z
  type0.normal.Exp.tree . # for type names such as [Exps]; else, need to unify type0 and literal cases 
    Z_?
      equals3, type = Unify.of_type spot 'tree_types - op_if0' [exp0, type0] type0 type2
      equals4 = Unify.of_equals_list (spot, 'tree_types - op_if0 unify', [exp0, type0]) [equals0,equals2,equals3]
      equals4, (spot, Tree [exp, typed_exp0, typed_exp2]), type
    B?
      Unify.of_type_opt type0 type2 .
        equals3, type?                                                          
          equals4 = Unify.of_equals_list (spot, 'tree_types - op_if0 unify', [exp0, type0]) [equals0,equals2,equals3]
          equals4, (spot, Tree [exp, typed_exp0, typed_exp2]), type
        ?
          equals4 = Unify.of_equals_list (spot, 'tree_types - op_if0 unify', [exp0, type0]) [equals0,equals2]
          equals4, (spot, Tree [exp, typed_exp0, typed_exp2]), spot,Z_        
    N?
      equals3, type = Unify.of_type spot 'tree_types - op_if0' [exp0, type0] type0 type2
      equals4 = Unify.of_equals_list (spot, 'tree_types - op_if0 unify', [exp0, type0]) [equals0,equals2,equals3]
      equals4, (spot, Tree [exp, typed_exp0, typed_exp2]), type
    Pre '!' type01?
      equals3, type = Unify.of_type spot 'tree_types - op_if0' [exp0, type0] type01 type2
      equals4 = Unify.of_equals_list (spot, 'tree_types - op_if0', [exp0, type0]) [equals0,equals2,equals3]
      equals4, (spot, Tree [exp, typed_exp0, typed_exp2]), type
    Pre '*' type01?      
      Unify.of_type_opt type0 type2 .                                          
        equals3, type?                                                          # t? t? t, that is *u? *u? *u
          equals4 = Unify.of_equals_list (spot, 'tree_types - op_if0 unify', [exp0, type0]) [equals0,equals2,equals3]
          equals4, (spot, Tree [exp, typed_exp0, typed_exp2]), type
        ?                                                                       # t? _? Z
          equals4 = Unify.of_equals_list (spot, 'tree_types - op_if0 unify', [exp0, type0]) [equals0,equals2]
          equals4, (spot, Tree [exp, typed_exp0, typed_exp2]), spot,Z_
    ? Exp.seq_error $Fun 'invalid' [exp, type0, type2]
    
# https://www.cs.umd.edu/~jfoster/papers/pldi02.pdf Flow-Sensitive Type Qualifiers
op_if_types fun:S binds:Binds spot:Spot exp0:Exp test:Exp body1:Exp body2:Exp : Equals, Exp, Type =
  exp = spot, Name 'op_if'
  equals0, typed_exp0, type0 = of_exp fun binds test
  # G |- x : !t
  # x:t, G |- b : u
  # x:Z, G |- c : u
  # G |- if x b c : u
  # test must be a variable name, else it cannot not be added to binds

  # todo?
  # G |- x : *t
  # x:t,*t, G |- b : u
  # x:Z, G |- c : u
  # G |- if x b c : u
  type0.Exp.tree,test.Exp.tree .
    Pre '!' type01, Name name?                                                    # G |- x : !t    
      equals1, typed_exp1, type1 = of_exp fun ((name, type01), binds) body1 # x:t, G |- b : u1
      equals2, typed_exp2, type2 = of_exp fun ((name, spot,Z_), binds) body2 # x:Z, G |- c : u2
      equals3, type = Unify.of_type spot 'tree_types - op_if with ! branches' [exp0] type1 type2
      equals4 = Unify.of_equals_list (spot, 'tree_types - op_if type ! unify', [exp0]) [equals0, equals1, equals2, equals3]
      equals4, (spot, Tree [exp, typed_exp0, typed_exp1, typed_exp2]), type
    ?                                                                          # todo check if type0 is B or !t or *t
      equals1, typed_exp1, type1 = of_exp fun binds body1 
      equals2, typed_exp2, type2 = of_exp fun binds body2
      equals3, type = Unify.of_type spot ($Fun + ' tree_types - if branches exp types unify') [body1, body2] type1 type2
      equals4 = Unify.of_equals_list (spot, 'tree_types - op_if unify', [exp0]) [equals0, equals1, equals2, equals3]
      equals4, (spot, Tree [exp, typed_exp0, typed_exp1, typed_exp2]), type

# type_fun inverts Kind.arg_bind - todo, unify them
# curry t u -> t? u
type_fun spot:Spot t:Type u:Type : Type = spot, Binary t '?' u
# type_fun spot:Spot a,t:Type u:Type : Type = spot, Binary (spot, Binary a ':' t) '?' u

type_args_return args:Exps type:Type : Types,Type = type.Exp.tree . 
  Binary t '?' u? type_args_return t,args u
  ? args.List.rev, type

exp_types_top exp:Exp : Exp =
  # exp . Exp.log
  of_exp '' 0 exp . 1

of_exp fun:S binds:Binds exp:Exp : Equals, Exp, type:Type =
  equals2, typed_exp, type = of_exp_do fun binds exp
  # debug, verbose print
  equals2, typed_exp, type

name2 spot:Spot name:S : Exp = spot, Name2 spot.Spot.unit name

name_full spot:Spot name:S : S = Name.dot spot.Spot.unit name 

# curry: t u v --> t? u? v
global_function_curry spot:Spot name:S : !(S, Type) =
  Hash.pair !Kind.name_funs name .
   name2, return_type,arg_types ?                 # global function as variable
     # arg = List.sum_bad arg_types.List.rev (type_fun spot) 0,return_type    # curry: t u v --> t? u? v
     arg = List.sum_bad arg_types.List.rev (type_fun spot) return_type    # curry: a,t b,u v --> a:t? b:u? 0,v
     name2, type_new !type_var arg

global_function_curry1 spot:Spot name:S : !Type =
  Hash.get !Kind.name_funs name .                                              
    return_type, arg_types?                                                      # global function as variable
      arg = List.sum_bad arg_types.List.rev (type_fun spot) return_type    # curry: t u v --> t? u? v
      type_new !type_var arg
 
of_fact exp:Exp base:Exp : Exp =
  spot = Exp.spot exp
  fact0 = spot, Tree [(spot, Name2 'Pair' 'main'), (spot, Str spot.Spot.path_line), exp]
  log = spot, Tree [(spot, Name2 'Log' 'main'), (spot, Str spot.Spot.path_line)]
  fact = spot, Binary log ';' fact0
  spot, Tree [(spot, Name2 'Pair' 'main'), fact0, base]

of_pair exp:Exp base:Exp : Exp =
  spot = Exp.spot exp
  spot, Tree [(spot, Name2 'Pair' 'main'), exp, base]

# normalized, canonical
normal : Type? Type =
  spot, Name x?
    u = Hash.get !Kind.name_types x 
    u & u | spot, Name x
  spot, Tnat _? spot, N
  _, Binary _ ':' t? normal t
  _, Binary _ '=' t? normal t
  t? t

of_apply fun:S binds:Binds spot:Spot fun_exp:Exp fun_type:Type args:Exps args_types:Types : Equals, Exp, Type =
  # Row.at or List.at for [0 a], else: unify #0 *t = *t  or unify #0 %t = !%t
  nonnil = !((_, Nat 0? 1) fun_exp)
  | nonnil & Unify.of_type_opt fun_type (spot, Pre '*' (spot, Nat 0.type_var)) &
    of_exp fun binds (spot, Tree ((spot, Name2 'List' 'map'), (fun_exp, args)))     # s:*_ f  ->  List.map s f

  | nonnil & Unify.of_type_opt fun_type (spot, Pre '+' (spot, Nat 0.type_var)) &
    of_exp fun binds (spot, Tree ((spot, Name2 'Seq' 'map'), (fun_exp, args)))     # s:+_ f  ->  Seq.map s f

  | nonnil & Unify.of_type_opt fun_type (spot, Pre '%' (spot, Nat 0.type_var)) &
    of_exp fun binds (spot, Tree ((spot, Name2 'Ref' 'set'), (fun_exp, args)))     # s:%_ a  ->  s a

  | !args == 1 &
    arg_type = args_types . 0 . normal
    fun_exp.Exp.tree,fun_type.Exp.tree,arg_type.Exp.tree .
      # try *t first before ^t since *t is a subtype. ordered due to unbounded type var?
      _, N, Pre '*' _?                                                          # n:N s:*_  ->  List.at n s
        of_exp fun binds (spot, Tree ((spot, Name2 'List' 'at'), (fun_exp, args)))     

      _, N, Pre '+' _?                                                          # n:N s:+_  ->  Seq.at n s
        of_exp fun binds (spot, Tree ((spot, Name2 'Seq' 'at'), (fun_exp, args)))     

      Nat n, _, Row types?                                                      # n:#n s:^_  ->  Row.at n s
        of_exp fun binds (spot, Tree ((spot, Row.name !types n), args))     

      ? Exp.seq_error $Fun 'invalid nat' [fun_exp, fun_type, arg_type]+args
  
  | Exp.seq_error $Fun 'invalid' [fun_exp, fun_type]

_trace = %0 : %B

_trace2 = %0 : %B

proper_fun : Type? B =
  _, Binary _ '?' _? 1
  _, Binary _ ':' t? proper_fun t
  _, Binary _ '=' t? proper_fun t

_m2 = %0 : %B # see Tree [(_, Name 'M2'), a] below

# https://en.wikipedia.org/wiki/Type_class
# http://okmij.org/ftp/Computation/typeclass.html Implementing, and Understanding Type Classes
class exp0:Exp op:S exp:Exp type:Type : Exp = class1 exp0 op type .
  spot, Tree s? spot, Tree s+[exp]
  a=(spot, Name2 _)? spot, Tree [a, exp]
  ? Spot.fail2 exp.0 $Fun exp.Exp.str

class2 exp0=spot,_:Exp op:S exp1:Exp exp2:Exp _,type:Type : Term = type . 
  B? Tree [(spot, Name2 'B' op), exp1, exp2]
  B_? Tree [(spot, Name2 'B' op), exp1, exp2]
  C_? Tree [(spot, Name2 'C' op), exp1, exp2]
  C? Tree [(spot, Name2 'C' op), exp1, exp2]
  N? Tree [(spot, Name2 'N' op), exp1, exp2]
  R_? Tree [(spot, Name2 'R' op), exp1, exp2]
  S_? Tree [(spot, Name2 'S' op), exp1, exp2]
  Tnat _? Tree [(spot, Name2 'N' op), exp1, exp2]
  Name x & Kind.tag x? Tree [(spot, Name2 'N' op), exp1, exp2] # else, will crash at Term.eq compare integer tags
  Pre '*' t? Tree [(spot, Name2 'List' op+'_by'), class1 exp0 op t, exp1, exp2]
  Row [t, u, v, w, p, q]? Tree [(spot, Name2 'Row' op+'_by6'), class1 exp0 op t, class1 exp0 op u, class1 exp0 op v, class1 exp0 op w, class1 exp0 op p, class1 exp0 op q, exp1, exp2]
  Row [t, u, v, w, p]? Tree [(spot, Name2 'Row' op+'_by5'), class1 exp0 op t, class1 exp0 op u, class1 exp0 op v, class1 exp0 op w, class1 exp0 op p, exp1, exp2]
  Row [t, u, v, w]? Tree [(spot, Name2 'Row' op+'_by4'), class1 exp0 op t, class1 exp0 op u, class1 exp0 op v, class1 exp0 op w, exp1, exp2]
  Row [t, u, v]? Tree [(spot, Name2 'Row' op+'_by3'), class1 exp0 op t, class1 exp0 op u, class1 exp0 op v, exp1, exp2]
  Row [t, u]? Tree [(spot, Name2 'Pair' op+'_by'), class1 exp0 op t, class1 exp0 op u, exp1, exp2]
  Pre '!' t? Tree [(spot, Name2 'Opt' op+'_by'), class1 exp0 op t, exp1, exp2]
  #spot, Pre '+' t? spot, Tree [(spot, Name2 'Seq' op+'_by'), class1 exp0 op t, exp1, exp2] # FIXME
  Pre '+' t? Tree [(spot, Name2 'Seq' 'eq'), exp1, exp2]
  Binary _ ':' t? class2 exp0 op exp1 exp2 t
  ? Spot.fail4 exp0.0 $Fun exp1.Exp.str exp2.Exp.str type.Term.str

class_opt_nat _,type:Exp : B = type .
  Tnat _? 1
  Z_? 1
  B? 1
  N? 1
  C? 1
  C_? 1
  R_? 1
  ? 0

class1 exp0=(spot,_):Exp op:S _,type:Type : Exp = type .
  Tnat _? spot, Name2 'N' op
  Z_? spot, Name2 'Z' op
  B? spot, Name2 'B' op
  N? spot, Name2 'N' op
  C? spot, Name2 'C' op
  C_? spot, Name2 'C' op
  S_? spot, Name2 'S' op
  R_? spot, Name2 'R' op
  Nat _? spot, Name2 'N' op # literal 0 for Seq and Opt
  Name x? spot, Name2 x op # todo Equals.str in type.m
  Pre '*' t? spot, Tree [(spot, Name2 'List' op+'_by'), class1 exp0 op t] 
  #Pre '!' t? spot, Tree [(spot, Name2 'Opt' op+'_by'), class1 exp0 op t]
  Pre '!' t?
    | op == 'str' & spot, Tree [(spot, Name2 'Opt' op+'_by'), (spot, Name2 (class_opt_nat t & 'N' | 'Opt') 'must'), class1 exp0 op t]
    | spot, Tree [(spot, Name2 'Opt' op+'_by'), class1 exp0 op t]
  Pre '+' t? spot, Tree [(spot, Name2 'Seq' op+'_by'), class1 exp0 op t]
  Binary _ ':' t? class1 exp0 op t
  Row [t, u, v, w, p, q]? spot, Tree [(spot, Name2 'Row' op+'_by6'), class1 exp0 op t, class1 exp0 op u, class1 exp0 op v, class1 exp0 op w, class1 exp0 op p, class1 exp0 op q]
  Row [t, u, v, w, p]? spot, Tree [(spot, Name2 'Row' op+'_by5'), class1 exp0 op t, class1 exp0 op u, class1 exp0 op v, class1 exp0 op w, class1 exp0 op p]
  Row [t, u, v, w]? spot, Tree [(spot, Name2 'Row' op+'_by4'), class1 exp0 op t, class1 exp0 op u, class1 exp0 op v, class1 exp0 op w]
  Row [t, u, v]? spot, Tree [(spot, Name2 'Row' op+'_by3'), class1 exp0 op t, class1 exp0 op u, class1 exp0 op v]
  Row [t, u]?
    # prefer [2,3,5] over 2,(3,(5,0)) as in Unify.PAIR_LIST
    Unify.of_type_opt spot,type (spot, Pre '*' (spot, Nat 0.type_var)) .
      equals, type2? class1 exp0 op type2
      ? spot, Tree [(spot, Name2 'Pair' op+'_by'), class1 exp0 op t, class1 exp0 op u]
  ? (Spot.fail4 spot $Fun exp0.str type.Term.str type.Term.tag.str)

of_exp_do fun:S binds:Binds exp:Exp : Equals, Exp, Type =
  spot = Exp.spot exp
  exp.Exp.tree .
    Nat n? 0, exp, (spot, Tnat n)                                            # #n
  
    Char _? 0, exp, (spot, C_)                                                # c
    
    Real _? 0, exp, (spot, R_)                                                # r
  
    Str _? 0, exp, (spot, S_)                                                 # s         
    
    Name name & S.is_capital name?                                           # unit X.main or tag X = n or Def.X
      open = 'Tag.' + name
      open2 = 'Def.' + name
      unit = name + '.main'
      name2, type = B.or
       Set.in S.eq !Kind.name_tags open & open, (spot, N)
       global_function_curry spot unit 
       global_function_curry spot open 
       global_function_curry spot open2
       0, 0
      type & 0, (spot, Name name2), type | (binds Row.at0 . List.log; Exp.seq_error $Fun 'invalid unit/tag name' [exp])
      
    Name name?                                                                  # local x or f
      full = name_full spot name
      name2, type = B.or
       Map.pair S.eq binds name                                                # local variable
       t = Hash.get !Kind.name_exps full; t & full, t:Type                 # global exps, before name_nats
       Set.in S.eq !Kind.name_nats full & full, (spot, N)                    # global x = n
       Set.in S.eq !Kind.name_reals full & full, (spot, R_)                    # global x = r
       global_function_curry spot full
       0, 0
      type & 0, (spot, Name name2), type | (binds Row.at0 . List.log; Exp.seq_error $Fun 'invalid name' [exp])

    Name2 unit name?                                                            # X.x
      full = Name.dot unit name
      type =
       Hash.get !Kind.name_exps full |                                           # global exps, before name_nats
        (Set.in S.eq !Kind.name_nats full & spot, N) |                                # global constant, x = n
         (Set.in S.eq !Kind.name_reals full & spot, R_) |                                # x = r
          (Set.in S.eq !Kind.name_tags full & spot, N) |                                # X = n, Term.Row_tag from Rule
           global_function_curry1 spot full
      type & 0, (spot, Name full), type | (binds Row.at0 . List.log; Exp.seq_error $Fun 'invalid name2' [exp])
         
    Tree [(_, Name 'op_if0'), a, c]? op_if0_types fun binds spot exp a c
    
    Tree [(_, Name 'op_if'), a, b, c]? op_if_types fun binds spot exp a b c
    
    Row exps?
      equals_list, typed_exps, types = exps (of_exp fun binds) . List.unzip3
      0, Row.of_exps2 spot typed_exps types, (spot, Row_ types)      

    Listy exp0? of_exp_do fun binds exp0

    # unused
    Tree ((_, Name 'Box'), exps)?
      equals_list, typed_exps, types = exps (of_exp fun binds) . List.unzip3
      0, Box.of_exps spot typed_exps types, (spot, Row_ types)

    Tree [(_, Name 'Asm'), _]?                                                  # pass to [Step]
      0, exp, (spot, Name 'Any')
    
    Tree [(_, Name 'Fact'), a]?
      !fun == 0 | Fail.main2 $Fun 'Fact must be at toplevel'
      _, typed_exp, type  = of_exp 'Fact' 0 a                                   # force KEY_VAR below
      Unify.of_type spot ($Fun + ' Fact must be boolean') [exp] type 0,B
      Ref.seq_add Fact.exps typed_exp
      0, (spot, Nat 0), (spot, Z_)                                              # todo - nop

    Tree [(_, Name 'str'), exp1]? of_exp fun binds (class exp 'str' exp1 (of_exp fun binds exp1 . type))
    
    Tree [(_, Name 'T'), a]?
      _trace 1
      equals, typed, type = of_exp fun binds a     # local var, x = a
      _trace 0
      Exp.spot_log a
      Exp.log typed
      Exp.log type
      equals_log equals
      0, (spot, Nat 0), (spot, Z_)
    
    Tree (fun0, args)?                                                          # apply - f a..
      !args > 0 | Fail.main2 $Fun 'assert'                                      # Group.exps_exp
      args_equals_list, typed_args, args_types = args (of_exp fun binds) . List.unzip3
      exp .
        _, Tree [(_, Name key), _] & Key.in key args_types.0.normal?                # key label x x=a,y=b 
          _, typed, type = of_exp fun binds args.0
          base, field = Key.get exp key type.normal                                           # todo - static offset, inlined during code gen in Asm
          0, (spot, Tree [(spot, Name2 'Key' 'at'), (spot, Nat base), typed]), field
        ?
          equals0, typed_fun, fun_type = of_exp fun binds fun0
          | proper_fun fun_type &                             # t?u  or  x:t?u  or  x=a:t?u
            typed_app, fun_equals, return = Unify.apply 0 spot exp typed_fun typed_args 0 fun_type,args_types
            equals = Unify.of_equals_list (spot, $Fun + ' apply', [exp]) fun_equals,args_equals_list
            0, (spot, typed_app), apply equals return
          |                                                                     # N
            (_, Nat _? 1) fun_type & Exp.seq_error_log $Fun 'type var cannot resolve overloading' [fun0, fun_type] # todo - check if var in subtype, else: S,n unify with seq S,*S
            of_apply fun binds spot fun0 fun_type.normal args args_types
              
    Pre '$' (_, Name 'Fun')? 0, (spot, Str fun), (spot, S_)                       # meta Span
    
    Pre '$' (spot2, Name 'Spot')? 0, Row.of_exps3 spot spot2.Exp.of_spot, (spot, Name 'Spot') # todo - expand in Rewrite.do_exp_exp2 instead
    
    Pre '$' (_, Name 'Perf')? 0, (spot, Name 'Perf'), (spot, Nat 0)             

    # resolve in step.m after all Fact are processed by the current function [of_exp_do]
    Pre '$' (_, Name 'Fact')? 0, (spot, Name 'Fact'), (spot, Nat 0)          # meta Fact, todo - type = *(S, B)

    # Pre and $Pre for pack initialization
    Pre '$' (_, Name 'Def')? 0, (spot, Name 'Def.do'), (spot, Nat 0)          # meta Def, todo - type = *(S, B)
    
    Pre '$' (_, Name 'trap')? 0, (spot, Nat Trap.bit.B.nat), (spot, B) # Trap.was_bit, value of environment variable 'trap' at compiled time, not run time

    Pre o a? unary_types fun binds exp spot o a | Exp.seq_error $Fun 'invalid unary' [exp]

    Binary exp1 ':' type1?
      _, typed_exp, type0 = of_exp fun binds exp1
      type = type1.Kind.of_type
      equals, type2 = Unify.of_type spot ($Fun + ' type cast') [exp] type type0
      type3 = apply equals type
      Unify.eq type2 type3 | Exp.seq_error $Fun 'type cast diff' [exp, type0, type2, type3]
      0, typed_exp, type

    Binary (_, Name name) '=' (_, Binary body ':' type1)?                    # x = a : t
      _, typed_exp, type0  = of_exp 'Pre' 0 body                             # force KEY_VAR below
      type = type1.Kind.of_type
      equals, type2 = Unify.of_type spot ($Fun + ' type cast') [exp] type type0
      type3 = apply equals type
      Unify.eq type2 type3 | Exp.seq_error $Fun 'top type cast diff' [exp, type0, type2, type3]
      Ref.seq_add Def.exps (spot, Tree [(spot, Name 'Def.set'), (spot, Name (name_full spot name)), typed_exp])
      0, (spot, Binary (name2 spot name) '=' (spot, Nat 0)), (spot, Z_)      # placehodler value = 0    
    
    Binary (_, Name name) '=' body?   
      | !fun == 0 &                                                             # top level definition
        | S.is_capital name & (unit = spot.Spot.unit; unit != 'Tag' & unit != 'Term') & # type definition - ignored. Kind.tag?
          0, (spot, Nat 0), (spot, Z_)                                           # tag definition - todo
        | body .
          _, Nat n? 0, (spot, Binary (name2 spot name) '=' (spot, Nat n)), (spot, Z_)
          _, Real r? 0, (spot, Binary (name2 spot name) '=' (spot, Real r)), (spot, Z_)
          _, Pre '%' (_, Nat n)? 0, (spot, Binary (name2 spot name) '=' (spot, Nat n)), (spot, Z_)
          _, Tree (_, Name 'Tag'),_? 0, (spot, Nat 0), (spot, Z_)                               # Tag X Y ..
          ? Exp.seq_error $Fun 'invalid top exp without type' [exp]
      |
        _, typed_body, type = of_exp fun binds body     # see KEY_VAR above, Key.Fact (_test1 (foo=42, bar='car') == 42)
        0, typed_body, (spot, Binary (spot, Name name) ':' type)
      
    Binary (_, Binary (_, Tree (_, Name name),args) ':' return) '=' (body = _, Name '_')? # foreign function type declaration - f x:t.. : t = _   Name.native
      typed_exp = spot, Binary (spot, Binary (spot, Tree (name2 spot name),args) ':' return.Kind.of_type) '=' body
      0, typed_exp, (spot, Z_)

    # Binary (_, Binary (_, Tree (_, Name name),args) ':' return) '=' body?       # function definition - f x:t.. : t = a
    Binary (_, Binary (_, Tree (_, Name name),args) ':' return) '=' body?       # function definition - f x=a:t.. : t = a
      binds2 = args Kind.arg_bind
      full = name_full spot name
      equals1, typed_body, body_type = of_exp full binds2+binds body                # discard equals
      return0 = Kind.of_type return
      equals2, return2 = Unify.of_type spot 'tree_types - exp of type vs declared type in tree' [exp] body_type return0 
      arg_types1 = binds2 Row.at1
      Unify.eq return0 return2 | Exp.seq_error $Fun 'return types diff' [return, return2, exp]
      typed_fun = spot, Binary (spot, Binary (spot, Tree (name2 spot name),args) ':' return) '=' typed_body
      0, typed_fun, (spot, Z_)

    Binary (_, Binary (_, Name name) '=' body) ';' exp2?                        # local var def - x = a; b
      name == '_' | (type0 = Map.get S.eq binds name; type0 & Exp.seq_error $Fun 'name already defined' [exp,type0]) # Name.wild
      equals, typed_body, type = of_exp fun binds body     # local var, x = a
      equals2, typed_exp2, type2 = of_exp fun (name,type),binds exp2
      typed_exp = spot, Binary (spot, Binary (spot, Name name) '=' typed_body) ';' typed_exp2
      equals, typed_exp, type2
    
    Binary exp1 ';' exp2?
      equals1, typed_exp1, type1 = of_exp fun binds exp1                # todo: not function type = partially applied
      (_, Binary _ '?' _? 1) type1 & Exp.seq_error $Fun 'fun at exps, incomplete apply' [exp1,type1]
      equals2, typed_exp2, type2 = of_exp fun binds exp2
      equals = Unify.of_equals_list (spot, $Fun + ' steps ;', [exp]) [equals1, equals2] 
      typed_exp = spot, Binary typed_exp1 ';' typed_exp2
      equals, typed_exp, type2
    
    Binary a o b? binary_types fun binds exp spot a o b 
    
    ? Exp.seq_error $Fun 'invalid exp' [exp]

Fact (str 'a' == 'a')
Fact (str 42 == '42')
Fact (str 3.14 == '3.14')
Fact (Flag O . str == 'o')
#Fact (str Z_ == 'Z') # fixme Type.class
Fact (1 | Pair.at0 []) # FIXME Unify.of_type []:#0 with 0,1 should fail

of_str0 a:S = (of_exp $Fun 0 a.Exp.of; 0)

of_str a:S : Type = of_exp $Fun 0 a.Exp.of . type

exp_str a:S : S = Exp.str a.of_str

exp_eq a:S t:S : B =
  b = a.exp_str == t
  b | (Put.main2 t a.exp_str; Put t; 0)

Fact (exp_eq '0' '#0')
Fact (exp_eq '1' '#1')
Fact (exp_eq "\\a" 'C')
Fact (exp_eq '1 + 41' 'N')
Fact (Job.err (? of_str0 '1 + "a"') == "Exp.str_exps:1.3-1.4: error  Type.binary_types add (1 + 'a') #1 S\.")
Fact (exp_eq '"foo"' 'S')
Fact (exp_eq "1,'a'" '(#1,S)')
Fact (exp_eq "[2,3,5]" '(#2,(#3,(#5,#0)))')

of_exps_exp exps:Exps exp:Exp : Type =
  Kind exps
  of_exp '' 0 exp . type

of_str2 x:S : Type = x.Exp.of.Kind.of_type

Fact (Spot.path $Spot == 'type.m')
