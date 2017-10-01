# expression, tree, phrase, parser form

  https://en.wikipedia.org/wiki/Expression_(mathematics)
  https://en.wikipedia.org/wiki/Expression_(computer_science)
      
Terms = *Term
Exp = Spot, Term
Exps = *Exp 

spot x:Exp : Spot = x.0
spot_new x:Exp : Spot = x & x.0 | Spot 0
tree x:Exp : Term = x.1
tag exp:Exp : N = exp.tree.Term.tag
item exp:Exp : 0 = exp.tree.Term.item

str x:Exp : S = Term.str x.tree
opt_str x:!Exp : S = x & Term.str x.tree | '!!'
strs x:Exp : S = x.str + 0a.C.str
put x:Exp = x.str.Put
opt_put x:Exp = x.opt_str.Put
log x:Exp = x.str.Log
err x:Exp = x.str.Err

opt_log x:Exp = x.opt_str.Log

seq_str x:Exps : S = List.map_str x str
seq_strs x:Exps : S = List.map_str x strs
seq_str_pair x:Exps : S = List.map_str_pair x str
seq_str_seq x:Exps : S = List.map_str_seq x str
seq_put x:Exps = x.seq_str.Put
seq_puts x:Exps = List.do x put
seq_spot_puts x:Exps = List.do x spot_put
seq_tee x:Exps : Exps = (List.map_log x str; x)
seq_out x:Exps = List.map_out x str
seq_log x:Exps = x.seq_str.Log

seq_logs x:Exps = List.do x log

spot_str spot,term:Exp : S = spot.Spot.str + ':' + term.str

spot_put x:Exp = x.spot_str.Put

spot_log x:Exp = x.spot_str.Log

spot_basic_str x:Exp : S = 
  spot, term = x
  spot.Spot.basic_str + ':' + term.Term.str

spot_basic_put x:Exp = x.spot_basic_str.Put
spot_basic_log x:Exp = x.spot_basic_str.Log
  
seq_spot_str x:Exps : S = List.map_str x spot_str
seq_spot_put x:Exps = List.do x spot_put
seq_spot_log x:Exps = x.seq_spot_str.Log
seq_spot_logs x:Exps = List.do x spot_log
seq_spot_basic_put x:Exps = List.do x spot_basic_put
  
# : Spot
spot2 x:Exp y:Exp : Spot =
  path, line1, column1, _ = spot x
  _, _, _, line2, column2 = spot y
  path, line1, column1, line2, column1

# e  ->  e  for e = n, s, x
# e  ->  x = e; x
bind_name exp:Exp : !Exp, Exp =
  | is_pure exp & 0, exp
  |
    spot = spot exp  
    name = spot, Name 'x'.S.tick
    (spot, Binary name '=' exp), name

# is atomic, cheap, effect-free
is_pure : Exp ? B = 
  _, Char _? 1
  _, Str _? 1
  _, Nat _? 1
  _, Name _? 1
  # mem alloc, but io-free? Constructor name.S.char.C.is_upper

_binary_exp op:S x:Exp y:Exp : Exp = x.spot, Binary x op y

binary_exps op:S s:Exps : !Exp = List.sum2 s (_binary_exp op)

binary_exps1 op:S s:Exp,Exps : Exp = List.sum2 s (_binary_exp op)

# long, multiline comment
comment_next path:S line:N level:N s:S : N, N, !Term, N, N, !S =
  r = S.cut_not s+1 \ 
  | r - s+1 > level & comment path line+1 level r
  | S.char r == 0a & comment_next path line+1 level r
  | str_tree path line 0 s

comment path:S line:N level:N s:S : N, N, !Term, N, N, !S =
  x = S.char s
  comment_next path line level (S.cut s 0a)

# long, multiline string
cut_str line:N column:N s:S : S, N =
  r = S.cut_not s \ 
  | (r - s > column | S.char r == 0a) & cut_str line+1 column (S.cut s 0a + 1)
  | s, line

term_str_eq s:S x:Term n:N : B =
  y, r = str_num s s
  Term.eq x y & r == s+n

# compare to Rewrite.REWRITE_REAL
  [0-9][0-9_]*\.[0-9][0-9_]*\.[0-9][0-9_]*

  num  3.(f x)  3.f     3.f^4   when followed immediately by an atomic term such as name or (exp) or [exp]
  real 3.+4.    3. + x  3.14    when followed by number or space or EOF or operators other than .  
str_num s0:S s:S : Term, S = s.S.char .
  \.?
    r = S.cut_by s+1 C.is_dec
    | (r == s + 1 & (x = S.char r; C.is_letter x | x == \(  | x == \[)) & Nat (S.nat (S.span s0 s)), s
    | S.char r == \. & C.is_dec (r+1).S.char &
      t = S.cut_by r+1 C.is_dec
      base = S.span s0 r
      exp = S.span r+1 t
      Real (R.of_exp base exp), t
    | Real (R.of (S.span s0 r)), r
  x & C.is_dec x? str_num s0 s+1 
  ? Nat (S.nat (S.span s0 s)), s
Fact (term_str_eq '42foo' (Nat 42) 2)
Fact (term_str_eq '42foo' (Nat 42) 2)
Fact (term_str_eq '42.foo' (Nat 42) 2)
Fact (term_str_eq '42. foo' (Real 42.) 3)
Fact (term_str_eq '42.3foo' (Real 42.3) 4)
Fact (term_str_eq '42.' (Real 42.) 3)
Fact (term_str_eq '3.f' (Nat 3) 1)
Fact (term_str_eq '3.(f x)' (Nat 3) 1)
Fact (term_str_eq '3.f^4' (Nat 3) 1)
Fact (term_str_eq '3.+4.' (Real 3.) 2)
Fact (term_str_eq '3. + x' (Real 3.) 2)
Fact (term_str_eq '3.14' (Real 3.14) 4)
Fact (term_str_eq '2.99.8 light' (Real 2.99.8) 6)
  

# glue_tree needs both the starting position (line1, column1) and the ending position (line2, column2)
#str_tree path:S line:N column:N s:S : line1:N, column1:N, tree:Term, line2;N, column2:N, S =
str_tree path:S line:N column:N s:S : N, N, !Term, N, N, !S =
  x = S.char s
  y = x & S.char s+1
  | x == 0 & 0, 0, 0, 0, 0, 0
  | x == \  & str_tree path line column+1 s+1
  | x == \# & comment path line column s+1

  # | x == \\ & line, column, Char y, line, column + 2, s + 2
  | x == \\ &
    c, r = Unicode.char s+1
    line, column, Char c, line, column + 2, r
  
  | x == 0a &
    r = S.cut_not s+1 \ 
    line, column, Level r-s-1, line + 1, r - s+1, r    
    
  | x == \' &
    r, line2, column2 = S.cut_quote s+1 line column
    | r & line, column, Str (S.quote (S.span s+1 r)), line2, column2, r + 1
    | Fail.fill '$s:$n:$n: $s missing closing quote' [path, line, column, $Fun]    

  | x == \" & y == \" &
    r, n = cut_str 0 column s+2
    line, column, Str (S.meta (S.span s+2 r)), line + n, column, r
  
  | x == \" &
    r, n = S.cut_line s+1 \" 0                                                  # fixme - cut_line returns columns as well
    line, column, Str (S.meta (S.span s+1 r)), line + n, column + r-s, r + 1
    
  | x == \0 & y != \. & 
    | y == \' &
      r, n = S.cut_line s+2 \' 0
      line, column, Mem_ (Mem.of_hex (S.span s+2 r)), line + n, column + r-s, r + 1
    |
      r = S.cut_by s+1 C.is_hex
      line, column, Nat (S.hex (S.span s+1 r)), line, column + r-s, r  

  | x == \_ & C.is_bin y &
    r = S.cut_by s+1 C.is_lo_bin
    line, column, Nat (S.bin (S.span s+1 r)), line, column + r-s, r
  
  # | x == \_ & C.is_hex y &
  #   r = S.cut_by s+1 C.is_hex
  #   line, column, Mem_ (Mem.of_hex (S.span s+1 r)), line, column + r-s, r
  
  | ((x == \= & y == \=) | (x == \! & y == \=) | (x == \< & y == \=) | (x == \> & y == \=)) & # == != <= >=
    line, column, Op (C.str2 x y), line, column + 2, s + 2

  # | C.is_digit x &
  #   r = S.cut_by s+1 C.is_dec
  #   line, column, Nat (S.nat (S.span s r)), line, column + r-s, r
           
  | C.is_digit x &   
    num, r = str_num s s
    line, column, num, line, column + r-s, r
   
  | S.has '~,!@$%^&*()-=+[{]}|;:,<.>/?' x &  # except \#'"0-9A-Za-z 
    line, column, Op (C.str x), line, column + 1, s + 1
    
  | C.is_alpha x &
    r = S.cut_by s+1 C.is_alpha
    line, column, Name (S.span s r), line, column + r-s, r

  |
    u, r = Unicode.char s
    | Unicode.is_name u & line, column, Name (S.span s r), line, column + 1, r
    | Unicode.is_op u & line, column, Op (S.span s r), line, column + 1, r
    | Fail.fill '$s:$n:$n: $s invalid character $c near$.$s' [path, line, column, $Fun, x, S.heads s 100]

str_term x:S : !Term = str_tree $Fun Spot.line_base Spot.col_base x . 2
Fact (Term.eq (str_term '3.1415') (Real 3.1415))
Fact (Term.eq (str_term '3.0015') (Real 3.0015))
Fact (Term.eq (str_term '0.1415') (Real 0.1415))
Fact (Term.eq (str_term '0.0015') (Real 0.0015))
Fact (Term.eq (str_term '_10_1010') (Nat 42))
    
str_exps_at path:S line:N column:N str:S : Exps =
  line1, column1, tree, line2, column2, str2 = str_tree path line column str
  tree & ((path, line1, column1, line2, column2), tree), str_exps_at path line2 column2 str2

str_exps_nil x:S : Exps = str_exps_at $Fun Spot.line_base Spot.col_base x                                         # useless, dummy debug value

str_exps x:S : Exps = str_exps_at $Fun Spot.line_base Spot.col_base x

str_exps2 path,line,col,_,_:Spot x:S : Exps = str_exps_at path line col x
  
of_nil x:S : Exp = x.str_exps.Group.exps.Rewrite.exps.List.at0                                                   # useless, dummy debug value

of x:S : Exp = x.str_exps.Group.exps.Rewrite.exps.List.at0

of2 spot,x:Spot,S : Exp = x.(str_exps2 spot).Group.exps.Rewrite.exps.List.at0

tnat : Type? Type =
  spot, Str n? spot, Tnat n.S.nat                                               # "0"  ->  #0
  spot, Tree s? spot, Tree tnat.s
  spot, Row s? spot, Row_ tnat.s
  spot, Pre o t? spot, Pre o t.tnat
  spot, Post t o? spot, Post t.tnat o
  spot, Binary t o u? spot, Binary t.tnat o u.tnat
  t? t
  
type_of x:S : Type = x.of.tnat
Fact (eq1 (type_of '"42"') (Tnat 42))
Fact (type_of 'N, "0"' . str == '(N,#0)')

path_exps path:S : Exps = str_exps_at path Spot.line_base 0 path.Path       # fixme - Spot.col_base

unit_exps units:*S : Exps =                                                     # todo - check units unique
  paths = units (_ x:S : S = S.add x '.m')  
  (List.map_add paths path_exps).Group.exps.Rewrite.exps

paths_exps paths:*S : Exps = (List.map_add paths path_exps).Group.exps.Rewrite.exps

file_exps file:File : Exps =
  file.File.in.str_exps.Group.exps

# [file_exps] joins two exps as fun app. [file_exps2] gives a pair of exp.
file_exps2 file:File : Exp, Exp =
  s = file.File.in.str_exps.Group.exps
  s.0.Rewrite.exp, s.1.Rewrite.exp

seq_error fun:S x:S exps:Exps : 0 = Fail.main4 exps.0.spot.Spot.str fun x exps.seq_str

seq_error_log fun:S x:S exps:Exps = Log.main4 exps.0.spot.Spot.str+':' fun x exps.seq_str 

is_fun : Exp ? B =
  _, Binary _ '?' _? 1
  _, Binary (_, Binary _ '?' _) ';' _? 1

at_spot spot:Spot terms:Terms : Exps = terms (Pair.main spot)

eq _,x:Exp _,y:Exp : B = Term.eq x y
Fact (eq (Kind.of '1,2') (Kind.of '1,2'))

eq1 _,x:Exp y:Term : B = Term.eq x y  
Fact (eq1 (Kind.of '"42"') (Tnat 42))

seq_row1 s:*Exp : Exp = List.sum2 s (_ a:Exp b:Exp : Exp = a.Exp.spot, Row_ [a, b])

seq_row s:*Exp : Exp = List.sum (_ a:Exp b:Exp : Exp = a.Exp.spot, Row_ [a, b]) (Spot.nil, Nat 0) s

row_seq : Exp? *Exp =
  _, Row [a, b]? a, row_seq b
  _, Nat 0? 0
  a? Fail.main2 $Fun a.str 

of_spot spot=path,line1,column1,line2,column2:Spot : *Exp = [(spot, Str path), (spot, Nat line1), (spot, Nat column1), (spot, Nat line2), (spot, Nat column2)] 

