# opcode, linear computation, flat execution
  
  http://en.wikipedia.org/wiki/Opcode

Step = Spot, Terms
Steps = +Step

at spot:Spot terms_seq:+Terms : Steps = Smap (Pair.main spot) terms_seq

# https://en.wikipedia.org/wiki/De_Bruijn_index
Stack = * !S

row_value_steps stack:Stack offset:N : Exp ? N, Steps =
  spot, Row [(_, Nat rank), value]?
    # pop a; [rank] mov r13 n a
    offset + N.bytes rank, exp_steps_one stack value + Slist[(spot, [Pop, Reg A]), (spot, [Nat rank, Mov, Reg R13, Nat offset, Reg A])]
  ? Fail $Fun

row_steps spot:Spot stack:Stack size:N values:Exps : Steps =
  #
    mov r11 size
    call Mem.main_reg
    push r11
    push r13 
    mov r13 r11
    [row expressions with r13]
    pop r13 # restore    
        
  Seq.adds_
   Sone (spot, [Mov, Reg R11, Nat size])
   Sone (spot, [Call, Name 'Mem.main_reg'])
   Sone (spot, [Push, Reg R11])
   Sone (spot, [Push, Reg R13])
   Sone (spot, [Mov, Reg R13, Reg R11])
   Seq.adds (List.map_with 0 values (row_value_steps 0,(0,stack))) # stack off by 2 values (r13 saved value, r11 as return)
   Sone (spot, [Pop, Reg R13])

exp_steps stack:Stack exp:Exp : Stack, Steps =
  spot = Exp.spot exp
  #exp . Exp.spot_log
  exp.Exp.tree .
    Char c? [0], Slist[(spot, [Push, Nat c])]                             # push n
   
    Nat n?                                                                      # n
      | I.rank n < 3 &                                                          # push is signed
        [0], Slist[(spot, [Push, Nat n])]                             # push n
      | 
        [0], Slist[(spot, [Mov, Reg A, Nat n]), (spot, [Push, Reg A])] # mov a n; push a
  
    Real n? [0], Slist[(spot, [Mov, Reg A, Nat n.Cast.any]), (spot, [Push, Reg A])] # mov a n; push a -- same as push n when n.rank == 3 above
    
    Str s?                                                                      # s
      [0], Slist[(spot, [Push, Str s])]
      
    Name 'Fact'? exp_steps 0 (List.sum_right (List.rev !Fact.exps) Type.of_fact (spot, Nat 0))
    
    Name 'Perf'? exp_steps 0 (List.sum_right (List.rev !Perf.names) Type.of_pair (spot, Nat 0))      

    Name 'Def.do'?                                                                 # DEF_STEPS
      [], exps_steps_top (!Def.exps).List.rev
    
    Name x?                                                                     # var - x
      # todo - add tag and index in Type for key and nat vs ref
      key = List.key (Opt.eq_by S.eq) stack x (N.opt 0)
      | key & [0], Sone (spot, [Push, Reg Sp, Nat (8 * N.must key)]) # local variables
      | (Set.in S.eq !Kind.name_nats x | Set.in S.eq !Kind.name_tags x | Set.in S.eq !Kind.name_reals x | Hash.in !Kind.name_exps x) & # pack, global variables - X = n, x = n, x = r
        [0], Slist[(spot, [Push, Name x.name_label]), (spot, [Pop, Reg A]), (spot, [Push, Reg A, Nat 0])] # natural constant on heap - push x, pop a, push *a 0
      | [0], Sone (spot, [Push, Name x.name_label])                    # global functions

    Tree [(_, Name 'op_if0'), test, body]?                                       # a | b  ==  x = a; if x x b
      else = Name '_Else'.S.tick
      done = Name '_Done'.S.tick    
      # s0; pop a; cmp a 0; j e Else; Push a; j Done; @Else; s2; @Done
      [0], Seq.adds_
       exp_steps_one stack test
       Sone (spot, [Pop, Reg A])
       Sone (spot, [Cmp, Reg A, Nat 0])
       Sone (spot, [J, Flag E, else])
       Sone (spot, [Push, Reg A])
       Sone (spot, [J, done])
       Sone (spot, [Label, else])
       exp_steps_one stack body
       Sone (spot, [Label, done])
            
    Tree [(_, Name 'op_if'), test, body1, body2]?                                       # if a b c 
      else = Name '_Else'.S.tick
      done = Name '_Done'.S.tick
      # s0; pop a; cmp a 0; j e Else; s1; j Done; @Else; s2; @Done
      [0], Seq.adds_
       exp_steps_one stack test
       Sone (spot, [Pop, Reg A])
       Sone (spot, [Cmp, Reg A, Nat 0])
       Sone (spot, [J, Flag E, else])
       exp_steps_one stack body1
       Sone (spot, [J, done])
       Sone (spot, [Label, else])
       exp_steps_one stack body2
       Sone (spot, [Label, done])
        
    Tree [(_, Name 'Asm'), a]? [0], of_exp a 
    
    Tree ((_, Name 'Row'), ((_, Nat size), values))? [0], row_steps spot stack size values

    Tree [(_, Name 'N.eq'), a, b]?                                               # [a]; [c]; pop a; pop c; mov d 0; cmp c a; set e d; push d
      [0], exp_steps_one stack a + exp_steps_one (0, stack) b + Slist[(spot, [Pop, Reg A]), (spot, [Pop, Reg C]), (spot, [Mov, Reg D, Nat 0]), (spot, [Cmp, Reg C, Reg A]), (spot, [Set_, Flag E, Reg D]), (spot, [Push, Reg D])]

    Tree [(_, Name 'N.ne'), a, b]?                                               
      [0], exp_steps_one stack a + exp_steps_one (0, stack) b + Slist[(spot, [Pop, Reg A]), (spot, [Pop, Reg C]), (spot, [Mov, Reg D, Nat 0]), (spot, [Cmp, Reg C, Reg A]), (spot, [Set_, Flag Ne, Reg D]), (spot, [Push, Reg D])]

    Tree [(_, Name 'N.gt'), a, b]?                                               
      [0], exp_steps_one stack a + exp_steps_one (0, stack) b + Slist[(spot, [Pop, Reg A]), (spot, [Pop, Reg C]), (spot, [Mov, Reg D, Nat 0]), (spot, [Cmp, Reg C, Reg A]), (spot, [Set_, Flag G, Reg D]), (spot, [Push, Reg D])]

    Tree [(_, Name 'N.ge'), a, b]?                                               
      [0], exp_steps_one stack a + exp_steps_one (0, stack) b + Slist[(spot, [Pop, Reg A]), (spot, [Pop, Reg C]), (spot, [Mov, Reg D, Nat 0]), (spot, [Cmp, Reg C, Reg A]), (spot, [Set_, Flag Ge, Reg D]), (spot, [Push, Reg D])]

    Tree [(_, Name 'N.lt'), a, b]?                                               
      [0], exp_steps_one stack a + exp_steps_one (0, stack) b + Slist[(spot, [Pop, Reg A]), (spot, [Pop, Reg C]), (spot, [Mov, Reg D, Nat 0]), (spot, [Cmp, Reg C, Reg A]), (spot, [Set_, Flag L, Reg D]), (spot, [Push, Reg D])]

    Tree [(_, Name 'N.le'), a, b]?                                               
      [0], exp_steps_one stack a + exp_steps_one (0, stack) b + Slist[(spot, [Pop, Reg A]), (spot, [Pop, Reg C]), (spot, [Mov, Reg D, Nat 0]), (spot, [Cmp, Reg C, Reg A]), (spot, [Set_, Flag Le, Reg D]), (spot, [Push, Reg D])]

    Tree [(_, Name 'N.add'), a, b]?                                           # [a]; [c]; pop a; pop c; add a c; push a
      [0], exp_steps_one stack a + exp_steps_one (0, stack) b + Slist[(spot, [Pop, Reg A]), (spot, [Pop, Reg C]), (spot, [Add, Reg A, Reg C]), (spot, [Push, Reg A])]

    Tree [(_, Name 'N.mul'), a, b]?                                           # [a]; [c]; pop a; pop c; mul c; push a
      [0], exp_steps_one stack a + exp_steps_one (0, stack) b + Slist[(spot, [Pop, Reg A]), (spot, [Pop, Reg C]), (spot, [Mul, Reg C]), (spot, [Push, Reg A])]

    Tree [(_, Name 'N.and'), a, b]?                                           # [a]; [c]; pop a; pop c; and a c; push a
      [0], exp_steps_one stack a + exp_steps_one (0, stack) b + Slist[(spot, [Pop, Reg A]), (spot, [Pop, Reg C]), (spot, [And, Reg A, Reg C]), (spot, [Push, Reg A])]

    Tree [(_, Name 'N.or'), a, b]?                                           # [a]; [c]; pop a; pop c; or a c; push a
      [0], exp_steps_one stack a + exp_steps_one (0, stack) b + Slist[(spot, [Pop, Reg A]), (spot, [Pop, Reg C]), (spot, [Or, Reg A, Reg C]), (spot, [Push, Reg A])]

    Tree [(_, Name 'Mem.main'), a]?                                           # [a]; pop r11; call Mem.main_reg; push r11
      [0], exp_steps_one stack a + Slist[(spot, [Pop, Reg R11]), (spot, [Call, Name 'Mem.main_reg']), (spot, [Push, Reg R11])]

    Tree [(_, Name 'S.new'), a]?                                           # [a]; pop r11; add r11 1; call Mem.main_reg; push r11
      [0], exp_steps_one stack a + Slist[(spot, [Pop, Reg R11]), (spot, [Add, Reg R11, Nat 1]), (spot, [Call, Name 'Mem.main_reg']), (spot, [Push, Reg R11])]

    Tree [(_, Name 'Mem.add'), s, a]?                                           # [a]; [c]; pop c; pop a; add a 0 c; push 0
      [0], exp_steps_one stack s + exp_steps_one (0, stack) a + Slist[(spot, [Pop, Reg C]), (spot, [Pop, Reg A]), (spot, [Add, Reg A, Nat 0, Reg C]), (spot, [Push, Nat 0])]

    Tree [(_, Name 'Flow.add'), s, a]?                                          # [a]; [c]; pop c; pop a; add a 8 c; push 0
      [0], exp_steps_one stack s + exp_steps_one (0, stack) a + Slist[(spot, [Pop, Reg C]), (spot, [Pop, Reg A]), (spot, [Add, Reg A, Nat 8, Reg C]), (spot, [Push, Nat 0])]

    Tree [(_, Name 'Mem.set1'), s, a]?                                             # [a]; [c]; pop c; pop a; mov d a 0; add d c; mov a 0 d; push 0
      [0], exp_steps_one stack s + exp_steps_one (0, stack) a + at spot Slist[[Pop, Reg C], [Pop, Reg A], [Nat 1, Mov, Reg A, Nat 0, Reg C], [Push, Nat 0]]

    Tree [(_, Name 'Mem.set2'), s, a]?                                             # [s]; [a]; pop c; pop a; 2 mov a 0 c; push 0
      [0], exp_steps_one stack s + exp_steps_one (0, stack) a + Slist[(spot, [Pop, Reg C]), (spot, [Pop, Reg A]), (spot, [Nat 2, Mov, Reg A, Nat 0, Reg C]), (spot, [Push, Nat 0])]

    Tree [(_, Name 'Mem.set'), s, a]?                                             # [s]; [a]; pop c; pop a; mov a 0 c; push 0
      [0], exp_steps_one stack s + exp_steps_one (0, stack) a + Slist[(spot, [Pop, Reg C]), (spot, [Pop, Reg A]), (spot, [Mov, Reg A, Nat 0, Reg C]), (spot, [Push, Nat 0])]

    Tree [(_, Name 'Ref.set'), s, a]?                                             # [s]; [a]; pop c; pop a; mov a 0 c; push 0
      [0], exp_steps_one stack s + exp_steps_one (0, stack) a + Slist[(spot, [Pop, Reg C]), (spot, [Pop, Reg A]), (spot, [Mov, Reg A, Nat 0, Reg C]), (spot, [Push, Nat 0])]
    
    Tree [(_, Name 'Mem.set0'), s, a]?                                             # [s]; [a]; pop c; pop a; 0 mov a 0 c; push 0
      [0], exp_steps_one stack s + exp_steps_one (0, stack) a + Slist[(spot, [Pop, Reg C]), (spot, [Pop, Reg A]), (spot, [Nat 0, Mov, Reg A, Nat 0, Reg C]), (spot, [Push, Nat 0])]
      
    Tree [(_, Name 'S.set'), s, a]?                                             
      [0], exp_steps_one stack s + exp_steps_one (0, stack) a + Slist[(spot, [Pop, Reg C]), (spot, [Pop, Reg A]), (spot, [Nat 0, Mov, Reg A, Nat 0, Reg C]), (spot, [Push, Nat 0])]
    
    Tree [(_, Name 'Mem.get'), a]?                                              # [Mem.get e]  ->  [e]; pop a; push a 0
     [0], exp_steps_one stack a + Slist[(spot, [Pop, Reg A]), (spot, [Push, Reg A, Nat 0])]

    Tree [(_, Name 'S.char'), a]?
      [0], exp_steps_one stack a + Slist[(spot, [Pop, Reg A]), (spot, [Mov, Reg C, Nat 0]), (spot, [Nat 0, Mov, Reg C, Reg A, Nat 0]), (spot, [Push, Reg C])] # [e]; pop a; mov c 0; 0 mov c a 0; push c
      
    Tree [(_, Name 'Mem.get0'), a]?
      [0], exp_steps_one stack a + Slist[(spot, [Pop, Reg A]), (spot, [Mov, Reg C, Nat 0]), (spot, [Nat 0, Mov, Reg C, Reg A, Nat 0]), (spot, [Push, Reg C])] # [e]; pop a; mov c 0; 0 mov c a 0; push c

    Tree [(_, Name x), a] & S.strstr _mem8 x?
      [0], exp_steps_one stack a + Slist[(spot, [Pop, Reg A]), (spot, [Push, Reg A, Nat 8])]

    Tree [(_, Name 'List.tail'), a]?                                              
      [0], exp_steps_one stack a + Slist[(spot, [Pop, Reg A]), (spot, [Push, Reg A, Nat 8])]

    Tree [(_, Name 'Ref.get'), a]?                                              
      [0], exp_steps_one stack a + Slist[(spot, [Pop, Reg A]), (spot, [Push, Reg A, Nat 0])]

    Tree [(_, Name 'List.head'), a]?                                              # [List.head e]  ->  [e]; pop a; push a 0
      [0], exp_steps_one stack a + Slist[(spot, [Pop, Reg A]), (spot, [Push, Reg A, Nat 0])]

    Tree [(_, Name 'List.at'), (_, Nat 0), a]? 
      [0], exp_steps_one stack a + Slist[(spot, [Pop, Reg A]), (spot, [Push, Reg A, Nat 0])]

    Tree [(_, Name 'Flow.head'), a]?
      [0], exp_steps_one stack a + Slist[(spot, [Pop, Reg A]), (spot, [Push, Reg A, Nat 0])]

    Tree [(_, Name 'Flow.last'), a]?
      [0], exp_steps_one stack a + Slist[(spot, [Pop, Reg A]), (spot, [Push, Reg A, Nat 8])]

    Tree [(_, Name 'Row.at0'), a]?                                              # [Row.at0 e]  ->  [e]; pop a; push a 0
      [0], exp_steps_one stack a + Slist[(spot, [Pop, Reg A]), (spot, [Push, Reg A, Nat 0])]

    Tree [(_, Name 'Row.at2_0'), a]?
      [0], exp_steps_one stack a + Slist[(spot, [Pop, Reg A]), (spot, [Push, Reg A, Nat 0])]

    Tree [(_, Name 'Row.at3_0'), a]?
      [0], exp_steps_one stack a + Slist[(spot, [Pop, Reg A]), (spot, [Push, Reg A, Nat 0])]

    Tree [(_, Name 'Row.at1'), a]?                                              
      [0], exp_steps_one stack a + Slist[(spot, [Pop, Reg A]), (spot, [Push, Reg A, Nat 8])]

    Tree [(_, Name 'Row.at2_1'), a]?                                              
      [0], exp_steps_one stack a + Slist[(spot, [Pop, Reg A]), (spot, [Push, Reg A, Nat 8])]

    Tree [(_, Name 'Row.at3_1'), a]?                                              
      [0], exp_steps_one stack a + Slist[(spot, [Pop, Reg A]), (spot, [Push, Reg A, Nat 8])]
      
    Tree [(_, Name 'Row.at2'), a]?                                              
      [0], exp_steps_one stack a + Slist[(spot, [Pop, Reg A]), (spot, [Push, Reg A, Nat 16])]

    Tree [(_, Name 'Row.at3_2'), a]?                                              
      [0], exp_steps_one stack a + Slist[(spot, [Pop, Reg A]), (spot, [Push, Reg A, Nat 16])]

    Tree [(_, Name 'Row.at3'), a]?                                              
      [0], exp_steps_one stack a + Slist[(spot, [Pop, Reg A]), (spot, [Push, Reg A, Nat 24])]
    
    Tree [(_, Name x), a] & (is_identity x | S.prefix x 'Cast.')?                                                      # type cast - f a  ->  a    
      exp_steps stack a

    Tree [(_, Name 'Def.set'), (_, Name name), body]?                            # Def_SET set top exp
      # exp; pop c; mov a x; mov a 0 c
      [], exp_steps_one stack body + Slist[spot,[Pop, Reg C], spot,[Mov, Reg A, Name name.name_label], spot,[Mov, Reg A, Nat 0, Reg C]]

    Tree ((_, Name x), exps)?                                                      # function application - f a..
      callee =    
        key = List.key (Opt.eq_by S.eq) stack x (N.opt 0)
        | key & [Reg Sp, Nat (8 * (N.must key + 1 + !exps))]                   # stack = return value, arguments
        | [Name x.name_label]                                                   # f a..
      call_steps stack spot callee exps

    Tree ((_, Name2 x y), exps)?                                                # function application - X.f a..
      call_steps stack spot [Name (Name.dot x y)] exps

    Binary (_, Name name) '=' body?                                             # local var - x = a
      [name], exp_steps_one stack body
      
    Binary (_, Name2 unit name) '=' (_, Nat n)?                                             # x = n
      0, Sone (spot, [New, Name (Name.dot unit name).name_label, Nat n])

    Binary (_, Name2 unit name) '=' (_, Real r)?                                             # x = r
      0, Sone (spot, [New, Name (Name.dot unit name).name_label, Real r])

    Binary a '=' (_, Name '_')? 0, 0                                            # function type declaration - f x:t.. : t = _
    
    Binary (_, Binary (_, Tree (_, Name2 unit name0),args) ':' return) '=' body?       # function definition - f x:t.. : t = a
      #
        @Name
        body
        pop a  # body's value
        add sp 8*!locals  # body's locals
        mov sp 8(1 + !args) a  # function return value
        ret
      name = Name.dot unit name0
      name_ticks = Name.ticks name . Name 
      name_calls = Name.calls name . Name
      pre1, pre2, post =
        | Perf.call &
          exps = [(spot, Str name), (spot, name_ticks), (spot, name_calls)]     # matching $Perf in Perf.main - x,t,n:S,%N,%N
          types = [(spot, S_), (spot, N), (spot, N)]
          unit == 'Fun' | Ref.seq_add Perf.names (Row.of_exps2 spot exps types)
          pre1 = unit == 'Fun' & [] | [(spot, [Push, name_calls]), (spot, [Pop, Reg R10]), (spot, [Add, Reg R10, Nat 0, Nat 1])] # push X.f.calls; pop r10; add r10 0 1

          | Perf.tick &
            pre2 = unit == 'Fun' & [] | [(spot, [Push, Reg A]), (spot, [Push, Reg D]), (spot, [Push, name_ticks]), (spot, [Pop, Reg R15]), (spot, [Rdtsc]), (spot, [Shl, Reg D, Nat 32]), (spot, [Or, Reg A, Reg D]), (spot, [Sub, Reg R15, Nat 0, Reg A]), (spot, [Pop, Reg D]), (spot, [Pop, Reg A])] 
            # cpuid - must save rax/rbx/rcx/rdx
            post = [(spot, [Rdtsc]), (spot, [Shl, Reg D, Nat 32]), (spot, [Or, Reg A, Reg D]), (spot, [Push, name_ticks]), (spot, [Pop, Reg R15]), (spot, [Add, Reg R15, Nat 0, Reg A])] # *cupid; rdtsc; shl d 32; or a d; push X.f.ticks; pop c; add c 0 a
            pre1, pre2, post
          | pre1, [], []
        | [], [], []
      args_stack = List.rev (args arg_name)
      stack2, steps = exp_steps (0, args_stack+stack) body                  # 1 for return address
      ! List.bit stack2 & Exp.seq_error $Fun 'fun def - empty exp' [exp]
      (B.not (Cast.any stack2.0) | ! stack2.0 == 0) | Exp.seq_error $Fun 'fun def - non-exp on stack' [exp]
      0, Seq.adds_       
       Perf.call & Sone (spot, [New, name_ticks, Nat 0])
       Perf.call & Sone (spot, [New, name_calls, Nat 0])
       Sone (spot, [Label, Name name.name_label]) # preserve global name_ticks and name_calls across calls
       Slist pre1
       Slist pre2
       steps
       Sone (spot, [Pop, Reg A])
       Sone (spot, [Add, Reg Sp, Nat (8 * ! stack2.List.tail)]) # pop local variables
       Sone (spot, [Mov, Reg Sp, Nat (8 * (1 + !args)), Reg A]) # return address, arguments
       Slist post
       Sone (spot, [Ret])
        
    Binary exp1 ';' exp2?                                                               # a; b
      stack0, steps0 = exp_steps stack exp1                                     # OP_SEMI
      | !stack0 == 0 &                                                          # inserted by PRE_STEPS above
        stack1, steps1 = exp_steps stack exp2
        stack1, steps0 + steps1
      | !stack0 == 1 & (B.not (Cast.any stack0.0) | ! stack0.0 == 0) &                           # unnamed expression 0 on stack
        stack1, steps1 = exp_steps stack exp2
        stack1, steps0 + Sone (spot, [Add, Reg Sp, Nat 8]) + steps1                            # pop _          
      |                                                                           # x = a; b
        stack1, steps1 = exp_steps stack0+stack exp2
        stack1 + stack0, steps0 + steps1

    ? Exp.seq_error $Fun 'invalid' [exp]

# upper names are fully qualified names with module prefix
# underscore-leading names are local names without module prefix
name_label name:S : S =
  | name.S.is_capital & name
  | '_' + name

arg_name : Exp ? S =
  _, Binary (_, Name x) ':' _? x
  _, Binary (_, Name x) '=' _? x # f x=a:t : u = b
  a? Exp.seq_error $Fun 'invalid' [a]

_mem8 = 'Term.Char_term Term.Nat_term Term.Tree_term Term.Binary_term Term.Name_term Term.Nat_term Term.Row_term Term.Op_term Term.Pre_term Term.Name2_term Term.Tnat_term Term.Str_term Term.Level_term Term.Terms_term Term.Post_term Term.Map_term Term.Key_term' : S 

is_identity x:S : B = List.in S.eq ['Mem.nat', 'Mem.of', 'Mem.str', 'Bit', 'S.mem', 'N.char', 'File.nat', 'File.of', 'Pair.cast', 'Fun.mem', 'Ref.mem', 'File.nat', 'List.bit', 'N.bit', 'Any.nat', 'Any.mem', 'Any.cast', 'Any.cast_fun3', 'Any.cast_fun3x', 'Any.cast_fun4', 'Any.cast_fun5', 'Any.cast_fun6', 'B.cast'] x # todo

call_steps stack:Stack spot:Spot callee:Terms exps:Exps : Stack, Steps =
  #
    push 0
    arguments
    call Name
    add sp 8*!args
  return = spot, [Push, Nat 0]                                                  # push 0
  arguments = exps_steps (0, stack) exps                                       # 1 for return value
  call = spot, (Call, callee)                                                   # call f
  restore = spot, [Add, Reg Sp, Nat (8 * !exps)]                                # add sp 8!args
  # [0], (return, arguments + [call, restore])
  [0], Sone return + arguments + Slist[call, restore]
     
# map with state, for arguments
exps_steps stack:Stack exps:Exps : Steps =
  exps & exp_steps_one stack exps.List.head + exps_steps 0,stack exps.List.tail

exp_steps_empty exp:Exp : Steps = exp_steps 0 exp . 1 # no need to restore, discard toplevel stack
  
exps_steps_top exps:Exps : Steps = exps exp_steps_empty . Seq.adds

exp_steps_one stack:Stack exp:Exp : Steps =
  stack2, steps = exp_steps stack exp
  | !stack2 == 1 &
    steps
  | !stack2 > 1 &
    spot = exp.Exp.spot
    Seq.adds_ steps
     Sone (spot, [Pop, Reg A])
     Sone (spot, [Add, Reg Sp, Nat (8 * (!stack2 - 1))])          # top expression already popped to rax, hence -1
     Sone (spot, [Push, Reg A])
  | Exp.seq_error $Fun 'invalid' [exp]

exps_binary_out exps:Exps =
  0 & exps.Exp.seq_logs # z0
  Kind exps
  typed_exps = exps Type.exp_types_top
  0 & typed_exps.Exp.seq_logs # z1
  steps0 = of_file 3.File.of # /min/main.ma
  time0 = !Clock.rdtsc
  steps1 = exps_steps_top typed_exps
  0 & steps1.seq_log # z2
  steps = steps0 + steps1
  Asm.steps_binary_out steps 1
  0

str step:Step : S = ((_, terms) = step; Term.seq_str terms)
#Fact (str [] == '')

put step:Step = step.str.Put
log step:Step = step.str.Log
seq_str steps:Steps : S = Seq.map_line steps str
seq_put x:Steps = x.seq_str.Put
seq_puts x:Steps = Seq.do put x
seq_log x:Steps = Seq.do log x

of_str path:S s:S line:N terms:Terms : Steps =
  s2, n, term = Term.of s line
  | term & of_str path s2 line+n term,terms
  | Slink ((path, line, 0, line + n, 0), List.rev terms) (s2 & of_str path s2 line+n 0)

of_file file:File : Steps = of_str 'main.ma' file.File.in 1 0                                    # emacs starts line from 1

Fact (exp_steps [] 'Row 10 1,13 3,42'.Exp.of . 1 . seq_str == "mov r11 10\.call Mem.main_reg\.push r11\.push r13\.mov r13 r11\.push 13\.pop a\.1 mov r13 0 a\.push 42\.pop a\.3 mov r13 2 a\.pop r13")

of_exp : Exp? Steps =
  spot, Binary a ';' b? of_exp a + of_exp b
  spot, Pre '@' a? Sone (spot, [Label, Term.of_exp a])
  spot, Tree s? Sone (spot, s Term.of_exp)
  e=spot,x? Sone (spot, [Term.of_exp e])
  _? Fail.main2 $Fun 'assert'                                                   # fixme in Rewrite - spot,x = Exp should always match

of_exp1 : Exp? Step =
  spot, Tree s? spot, s Term.of_exp
  e=spot,x? spot, [Term.of_exp e]
  _? Fail.main2 $Fun 'assert'    
