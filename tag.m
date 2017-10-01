# tagged union, enum, algebraic data type

  https://en.wikipedia.org/wiki/Algebraic_data_type
  https://en.wikipedia.org/wiki/Tagged_union

# 1 - 210 in term.m
Add = 1010
And = 1011
Xor = 1012
Or = 1013
Sub = 1014
Cmp = 1015
Shl = 1016
Shr = 1017
Mul = 1018
Div = 1019
Mod = 1020
Neg = 10200

Call = 1021
Enter = 1022
Leave = 1023
J = 1024
Mov = 1025
Movsx = 10225
Lea = 1026
Test = 1027
Not = 1028
Push = 1029
Pop = 1030
Ret = 1031
Syscall = 1032
Rdtsc = 1033
Cpuid = 1034
Set_ = 1035
Pause = 1036
Xchg = 1037                                                                       # lock+inc lock+add dec xadd cmpxchg cmpxchg8b cmpxchg16b
Cmpxchg = 1038

Base = 1040
Span = 1041
Label = 1042
New = 1043

A = 1050
Ah = 1051
B_ = 1052
Bh = 1053
C = 1054
Ch = 1055
D = 1056
Dh = 1057
Sp = 1058
Bp = 1059
Si = 1060
Di = 1061
R8 = 1062
R9 = 1063
R10 = 1064
R11 = 1065
R12 = 1066
R13 = 1067
R14 = 1068
R15 = 1069
Xmm0 = 10300
Xmm1 = 10301

O = 1070
No = 1071

L = 1072
Sl = 1082
Ge = 1073
Sge = 1083

E = 1074
Ne = 1075

Le = 1076
Sle = 1086
G = 1077
Sg = 1087

S__ = 1078
Ns = 1079
P = 1080
Np = 1081

Z_ = 10120
B = 10121
C_ = 10122
S_ = 10123
R_ = 10124

N0 = 10130
N1 = 10131
N2 = 10132
N = 10133
I = 10134

# Next Def Type At Fun 
# Or And Pair By
# Eq Ne Lt Le Gt Ge
# Not Add Sub Mul Div Mod Pow 
# unary: !not !opt %ref +seq 

Flag x:N : Term = Cast.any (Term.Flag_tag, x)                                             # fixme with Tag def - Flag x:Flag
Reg x:N : Term = Cast.any (Term.Reg_tag, x)                                               # fixme with Tag def - Reg x:Reg
Char x:C : Term = Cast.any (Term.Char_tag, x)
Nat x:N : Term = Cast.any (Term.Nat_tag, x)                                     # binding, type variable
Tnat x:N : Term = Cast.any (Term.Tnat_tag, x)                                             # type for natural literals
Str x:S : Term = Cast.any (Term.Str_tag, x)
Real x:R : Term = Cast.any (Term.Real_tag, x)
Mem_ x:N,Mem : Term = Cast.any (Term.Mem_tag, x)
Name x:S : Term = Cast.any (Term.Name_tag, x)
Name2 x:S y:S : Term = Cast.any (Term.Name2_tag, (x, y))
Op x:S : Term = Cast.any (Term.Op_tag, x)
Level x:N : Term = Cast.any (Term.Level_tag, x)
Tree x:Exps : Term = Cast.any (Term.Tree_tag, x)
Listx x:Exps : Term = Cast.any (Term.Listx_tag, x)
Listy x:Exp : Term = Cast.any (Term.Listy_tag, x)
Meta x:S : Term = Cast.any (Term.Meta_tag, x)
Pre o:S x:Exp : Term = Cast.any (Term.Pre_tag, (o, x))
Post x:Exp o:S : Term = Cast.any (Term.Post_tag, (x, o))
Binary x:Exp o:S y:Exp : Term = Cast.any (Term.Binary_tag, (x, o, y))
Row_ s:Exps : Term = Cast.any (Term.Row_tag, s)

# Node a:0~1 hash:N x:0 y:1 b:0~1 : 0~1 = Cast.any (Term.Node_tag, (a, hash, x, y, b))

#Key x:S y:Term : Term = Cast.any (Term.Key_tag, (x, y))
Terms s:Terms : Term = Cast.any (Term.Terms_tag, s) # Json
Map s:*(S, Term) : Term = Cast.any (Term.Map_tag, s) # Json

#Snil = 0
Snil _ : +0 = Cast.any 0
Sone x:0 : +0 = Cast.any (Term.Sone_tag, x)                         # one, singleton
Slink x:0 s:+0 : +0 = Cast.any (Term.Slink_tag, (x, s))                         # cons, next
Sadd r:+0 s:+0 : +0 = Cast.any (Term.Sadd_tag, (r, s))                            # two, merge
Slist x:*0 : +0 = Cast.any (Term.Slist_tag, x)                                  # List
Sseq s:*+0 : +0 = Cast.any (Term.Sseq_tag, s)                                   # join, concat, merge

Sstr n:N s:S : +C = Cast.any (Term.Sstr_tag, (n, s))
Sfun n:!N f:Z?!0 : +0 = Cast.any (Term.Sfun_tag, (n, f))                        # unfold

Sskip n:N s:+0 : +0 = Cast.any (Term.Sskip_tag, (n, s))
Stake n:N s:+0 : +0 = Cast.any (Term.Stake_tag, (n, s))                         # 
Srow n:N s:Mem : +0 = Cast.any (Term.Srow_tag, (n, s))
Smap f:0?1 s:+0 : +1 = Cast.any (Term.Smap_tag, (f, s))
Skeep f:0?B s:+0 : +1 = Cast.any (Term.Skeep_tag, (f, s))                       # take_nat
Spair r:+0 s:+0 : +(0,1) = Cast.any (Term.Spair_tag, (r, s))                    # zip, with
# push - add to tail?

_tick = %0 : %N

name _ : S = Name.add 'Tag' _tick
