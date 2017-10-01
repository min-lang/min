# token, node, word, lexical form

  https://en.wikipedia.org/wiki/Term_(logic)

# tag for Term and Seq
tag term:0 : N =                                             # hack! do not use tag integers > Any.data_vmaddr
  term.Mem.of.Mem.nat >= Any.data_vmaddr & term.Pair.cast.Row.at0 | term.Mem.of.Mem.nat

item term:0 : 1 =                                             # hack!
  term.Mem.of.Mem.nat >= Any.data_vmaddr & term.Pair.cast.Row.at1 | Cast.any 0

eq x:Term y:Term : B = x,y .
  Z_, Z_? 1
  B, B? 1
  C_, C_? 1
  N, N? 1
  I, I? 1
  R_, R_? 1
  N, I? 1                                                                       # todo
  I, N? 1                                                                       # todo
  S_, S_? 1
  Str a, Str b? a == b                                                          # s-literal
  Real a, Real b? a == b                                                        # r-literal
  Tnat m, Tnat n? m == n                                                        # type of n-literals
  Nat m, Nat n? m == n                                                          # n-literal
  Name a, Name b? S.eq a b
  Tree r, Tree s? List.all2 r s Exp.eq 
  Row r, Row s? List.all2 r s Exp.eq 
  Pre _ t, Pre _ u? Exp.eq t u
  Post t _, Post u _? Exp.eq t u
  Binary p _ q, Binary t _ u? Exp.eq p t & Exp.eq q u
  # todo - Reg Flag
Fact (eq (Exp.str_term '"foo"') (Str 'foo'))
Fact (eq (Exp.str_term '1,2') (Exp.str_term '1,2'))
Fact !(eq (Exp.str_term '1,2') (Exp.str_term '3,4'))
Fact (eq (Exp.str_term 'Term') (Exp.str_term 'Term'))
  
put x:Term = x.str.Put
log x:Term = x.str.Log
seq_str x:Terms : S = List.map_str x str
seq_put x:Terms = List.map_put x str
seq_log x:Terms = List.map_log x str

flag_str : Flag? S =
  O? 'o'
  No? 'no'
  E? 'e'
  Ne? 'ne'
  S__? 's'
  Ns? 'ns'
  P? 'p'
  Np? 'np'
  L? 'l'
  Ge? 'ge'
  Le? 'le'
  G? 'g'
  x? Fail.main2 $Fun x.Cast.nat.N.str
Fact (flag_str S__ == 's')

reg_str : Reg? S = 
  A? 'a'
  Ah? 'ah'
  B_? 'b'
  Bh? 'bh'
  C? 'c'
  Ch? 'ch'
  D? 'd'
  Dh? 'dh'
  Sp? 'sp'
  Bp? 'bp'
  Si? 'si'
  Di? 'di'
  R8? 'r8'
  R9? 'r9'
  R10? 'r10'
  R11? 'r11'
  R12? 'r12'
  R13? 'r13'
  R14? 'r14'
  R15? 'r15'
  Xmm0? 'xmm0'
  Xmm1? 'xmm1'
  x? Fail.main2 $Fun x.Cast.nat.N.str
   
str : Term? S =
  Flag x? flag_str x
  Reg x? reg_str x
  Char x? C.code x
  Nat x? N.str x
  Tnat x? '#' + x.N.str
  Name x? x
  Name2 x y? Name.dot x y
  Str x? S.code x
  Real x? R.str x
  Mem n,x? Mem.hex x n
  Level x? '$' + x.N.str
  Tree s? '(' + s.Exp.seq_str + ')'
  Listx s? '[' + s.Exp.seq_str + ']'
  Listy s? '[' + s.Exp.row_seq.Exp.seq_str_seq + ']'
  Meta x? '[' + x + ']'
  Terms s? '(' + s.Term.seq_str + ')'
  Row s? '(' + s.Exp.seq_str_pair + ')'
  Key x y? x + ':' + str y
  Map s? '(' + Map.map_str s Fun.id str + ')'
  Pre o a? S.fill '($s $s)' [o, a.str]
  Post a o? S.fill '($s $s)' [a.str, o]
  Binary a o b? S.fill '($s$s$s$s$s)' [a.str, (o.Group.op_lean & '' | ' '), o, (o == ';' & 0a.C.str  | ' '), b.str]
  Op x? x
  Add? 'add'
  And? 'and'
  Xor? 'xor'
  Or? 'or'
  Sub? 'sub'
  Cmp? 'cmp'
  Shl? 'shl'
  Shr? 'shr'
  Mul? 'mul'
  Div? 'div'
  Mod? 'mod'
  Neg? 'neg'
  Call? 'call'
  Enter? 'enter'
  Leave? 'leave'
  J? 'j'
  Mov? 'mov'
  Movsx? 'movsx'
  Lea? 'lea'
  Test? 'test'
  Not? 'not'
  Push? 'push'
  Pop? 'pop'
  Ret? 'ret'
  Syscall? 'syscall'
  Rdtsc? 'rdtsc'
  Cpuid? 'cpuid'
  Set_? 'set'
  Pause? 'pause'
  Xchg? 'xchg'
  Cmpxchg? 'cmpxchg'
  Base? '+'
  Span? ','
  Label? "\.@"
  New? '$'
  A? 'a'
  Ah? 'ah'
  B_? 'b'
  Bh? 'bh'
  C? 'c'
  Ch? 'ch'
  D? 'd'
  Dh? 'dh'
  Sp? 'sp'
  Bp? 'bp'
  Si? 'si'
  Di? 'di'
  R8? 'r8'
  R9? 'r9'
  R10? 'r10'
  R11? 'r11'
  R12? 'r12'
  R13? 'r13'
  R14? 'r14'
  R15? 'r15'
  Xmm0? 'xmm0'
  Xmm1? 'xmm1'
  Z_? 'Z'  
  B? 'B'
  C_? 'C'
  N? 'N'
  I? 'I'
  N0? 'N0'
  N1? 'N1'
  N2? 'N2'
  S_? 'S'
  R_? 'R'
  x? Fail.main2 $Fun x.N.str
# Fact (str Z_ == 'Z') # fixme Type.class
Fact (Flag O . str == 'o')
  
lower : S? !Term =
  'o'? Flag O
  'no'? Flag No
  'e'? Flag E
  'ne'? Flag Ne
  's'? Flag S_
  'ns'? Flag Ns
  'p'? Flag P
  'np'? Flag Np
  
  'l'? Flag L
  'ge'? Flag Ge
  'le'? Flag Le
  'g'? Flag G
  'sl'? Flag Sl
  'sge'? Flag Sge
  'sle'? Flag Sle
  'sg'? Flag Sg

  'a'? Reg A
  'b'? Reg B_
  'c'? Reg C
  'd'? Reg D
  'ah'? Reg Ah
  'bh'? Reg Bh
  'ch'? Reg Ch
  'dh'? Reg Dh
  'sp'? Reg Sp
  'bp'? Reg Bp
  'si'? Reg Si
  'di'? Reg Di
  'r8'? Reg R8
  'r9'? Reg R9
  'r10'? Reg R10
  'r11'? Reg R11
  'r12'? Reg R12
  'r13'? Reg R13
  'r14'? Reg R14
  'r15'? Reg R15
  'xmm0'? Reg Xmm0
  'xmm1'? Reg Xmm1
  
  'add'? Add
  'or'? Or
  'and'? And
  'sub'? Sub
  'xor'? Xor
  'shl'? Shl
  'shr'? Shr
  
  'cmp'? Cmp
  'mul'? Mul
  'div'? Div
  'mod'? Mod
  'neg'? Neg
  'call'? Call
  'j'? J
  'mov'? Mov
  'movsx'? Movsx
  'lea'? Lea
  'test'? Test
  'push'? Push
  'pop'? Pop
  'ret'? Ret
  'syscall'? Syscall
  'rdtsc'? Rdtsc
  'cpuid'? Cpuid
  'set'? Set_  
  'pause'? Pause
  'xchg'? Xchg
  'cmpxchg'? Cmpxchg

# floating number - whole, fractional, exponent
# of_num nat:!N frac:!N s:S line:N : !S, N, !Term =
of_nat s:S : S, N =
  r = S.cut_by s+1 C.is_dec
  r, S.nat (S.span s r)  
Fact (x = '42foo'; of_nat x == x+2,42)

of_num s:S : Term, S =
  real, r = S.cut_num s
  (real & Real (R.of (S.span s r)) | Nat (S.nat (S.span s r))), r
Fact (x = '42foo'; y, s = of_num x; s == x+2 & eq y (Nat 42))
Fact (x = '3.1415 foo'; y, s = of_num x; s == x+6 & eq y (Real '3.1415'.R.of))

neg : Term? Term =
  x? x

# : in:S, line_increment:N, term
of s:S line:N : !S, N, !Term =
  x = s & s.S.char | 0
  | x == 0 & 0, 0, 0
  | x == \! & 0, 0, 0
  | x == \; & s + 1, 0, 0
  | x == 0a & s + 1, 1, 0
  | x == \  & of s+1 line
  # | x == \- & # neg literal numbers
  | x == \+ & s + 1, 0, Base
  | x == \, & s + 1, 0, Span
  | x == \@ & s + 1, 0, Label
  | x == \# & of (S.cut s+1 0a) line  
  | x == \' & (r, n = S.cut_line s+1 \' 0; r + 1, n, Str (S.span s+1 r))
  # | x == \0 & (r = S.cut_by s+1 C.is_hex; r, 0, Nat (S.hex (S.span s+1 r)))
  | x == \0 &
    | S.char s+1 == \' &
      r, n = S.cut_line s+2 \' 0
      r + 1, n, Mem_ (Mem.of_hex (S.span s+2 r))
    |
      r = S.cut_by s+1 C.is_hex
      r, 0, Nat (S.hex (S.span s+1 r))      
  # | C.is_digit x & (r = S.cut_by s+1 C.is_dec; r, 0, Nat (S.nat (S.span s r)))
  | C.is_digit x & (y, r = of_num s; r, 0, y)
  | C.is_lo_upper x & (r = S.cut_by s+1 C.is_name; r, 0, Name (S.span s r))
  | C.is_lower x &
    r = S.cut_by s+1 C.is_name
    r, 0, (lower (S.span s r) | Fail.main3 (N.str line) 'str_term invalid term lower' (S.span s r))
  | Fail.main3 line.N.str 'str_term' x.C.str

Fact (s, n, x = of '42' 0; eq x (Nat 42))
Fact (s, n, x = of '3.1415' 0; eq x (Real 3.1415))
Fact (s, n, x = of '02a' 0; eq x (Nat 42))
Fact (n, x = of "0'63616665'" 0 . 2 . Term.Mem_term; n == 4 & Mem.get0 x == 063 & Mem.get0 x+1 == 061 & Mem.get0 x+2 == 066 & Mem.get0 x+3 == 065)
Fact (s, n, x = of "'foo'" 0; eq x (Str 'foo')) 

of1 s:S : S = (_, _, x = of s 0; x & str x | '')
Fact (of1 '42' == '42')
Fact (of1 'a' == 'a')
Fact (of1 '+' == '+')
Fact (Binary (0, Nat 13) '+' (0, Nat 42) . str == '(13 + 42)')

of_exp spot,m:Exp : Term = m .
  Name x? S.is_capital x & Name x | (lower x | Exp.seq_error $Fun 'invalid name' [(spot,m)]) # labels from main.ma - Data_vmend, Code_vmaddr, Code_vmend
  Name2 x y? Name x+'.'+y
  x? x

Flag_term x:Term : N = x.Pair.cast.Row.at1.Cast.any                             
Reg_term x:Term : N = x.Pair.cast.Row.at1.Cast.any
Char_term x:Term : C = x.Pair.cast.Row.at1.Cast.any
Nat_term x:Term : N = x.Pair.cast.Row.at1.Cast.any
Real_term x:Term : R = x.Pair.cast.Row.at1.Cast.any
Mem_term x:Term : N, Mem = x.Pair.cast.Row.at1.Cast.any
Tnat_term x:Term : N = x.Pair.cast.Row.at1.Cast.any
Str_term x:Term : S = x.Pair.cast.Row.at1.Cast.any
Name_term x:Term : S = x.Pair.cast.Row.at1.Cast.any
Name2_term x:Term : S, S = x.Pair.cast.Row.at1.Cast.any
Op_term x:Term : S = x.Pair.cast.Row.at1.Cast.any
Level_term x:Term : N = x.Pair.cast.Row.at1.Cast.any
Tree_term x:Term : Exps = x.Pair.cast.Row.at1.Cast.any
Listx_term x:Term : Exps = x.Pair.cast.Row.at1.Cast.any
Listy_term x:Term : Exp = x.Pair.cast.Row.at1.Cast.any
Meta_term x:Term : S = x.Pair.cast.Row.at1.Cast.any
Pre_term x:Term : S, Exp = x.Pair.cast.Row.at1.Cast.any
Post_term x:Term : Exp, S = x.Pair.cast.Row.at1.Cast.any
Binary_term x:Term : Exp, S, Exp = x.Pair.cast.Row.at1.Cast.any
Row_term x:Term : Exps = x.Pair.cast.Row.at1.Cast.any
Key_term x:Term : S, Term = x.Pair.cast.Row.at1.Cast.any
Terms_term x:Term : Terms = x.Pair.cast.Row.at1.Cast.any
Map_term x:Term : *(S, Term) = x.Pair.cast.Row.at1.Cast.any

# do not use [X = 0] to reserve it for optional type
Flag_tag = 1
Reg_tag = 2
Char_tag = 3
Nat_tag = 4
Str_tag = 5
Name_tag = 6
Op_tag = 7
Level_tag = 8
Tree_tag = 9
Listx_tag = 10
Listy_tag = 11
Meta_tag = 12

Tnat_tag = 89
Next_tag = 90
Def_tag = 91

Type_tag = 92
At_tag = 93
Fun_tag = 94
Pair_tag = 95
By_tag = 96
Mod_tag = 97
Pow_tag = 98

Pre_tag = 110
Post_tag = 111
Binary_tag = 112
Row_tag = 113
Name2_tag = 114
Key_tag = 115
Terms_tag = 116
Map_tag = 117
Node_tag = 118

# Z_ = 120
# N0 = 130
Real_tag = 150
Mem_tag = 151

# sequence types
Sstr_tag = 200
Slist_tag = 201
Srow_tag = 202
Sfun_tag = 203
Slink_tag = 204
Smap_tag = 205
Sseq_tag = 206
Sskip_tag = 207
Stake_tag = 208
Skeep_tag = 209
Spair_tag = 210
Sadd_tag = 211
Sone_tag = 212

Snil_term x:+0 : Z = 0
Sskip_term x:+0 : N, +0 = x.Pair.cast.Row.at1.Cast.any
Stake_term x:+0 : N, +0 = x.Pair.cast.Row.at1.Cast.any
Slist_term x:+0 : *0 = x.Pair.cast.Row.at1.Cast.any
#Sstr_term x:+C : S, S = x.Pair.cast.Row.at1.Cast.any
Sstr_term x:+C : N, S = x.Pair.cast.Row.at1.Cast.any
#Srow_term x:+0 : Mem Mem = x.Pair.cast.Row.at1.Cast.any                          # 0^ 0^
Srow_term x:+0 : N, Mem = x.Pair.cast.Row.at1.Cast.any
Sfun_term x:+0 : !N, Z?!0 = x.Pair.cast.Row.at1.Cast.any
Slink_term x:+0 : 0, +0 = x.Pair.cast.Row.at1.Cast.any
Sone_term x:+0 : 0 = x.Pair.cast.Row.at1.Cast.any
Sadd_term x:+0 : +0, +0 = x.Pair.cast.Row.at1.Cast.any
Smap_term x:+1 : 0?1, +0 = x.Pair.cast.Row.at1.Cast.any
Skeep_term x:+1 : 0?B, +0 = x.Pair.cast.Row.at1.Cast.any
Sseq_term x:+0 : *+0 = x.Pair.cast.Row.at1.Cast.any
Spair_term x:+(0,1) : +0, +1 = x.Pair.cast.Row.at1.Cast.any
