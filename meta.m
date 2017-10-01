# reflection, string interpolation

  https://en.wikipedia.org/wiki/String_interpolation
  http://en.wikipedia.org/wiki/Reflection_%28computer_programming%29
  http://en.wikipedia.org/wiki/Homoiconicity

of_meta nest:N path:S line:N column:N in:S : N, N, S =
  S.char in .
    0? Fail.fill '$s:$n:$n: $s missing closing bracket ]' [path, line, column, $Fun]
    \[? of_meta nest+1 path line column+1 in+1
    \]? nest & of_meta nest-1 path line column+1 in+1 | line, column, in
    0a? of_meta nest+1 path line+1 0 in+1
    _? of_meta nest path line column+1 in+1

of_str path:S line:N column:N in:S : N, N, S =
  x = S.char in
  | x == 0a & of_str path line+1 0 in+1
    
  | (x == 0 | x == \[) & line, column, in
  
  | of_str path line column+1 in+1

of_path path:S line:N column:N in:S : *Exp =
  | in.S.char == \[ &
    line2, column2, in2 = of_meta 0 path line column+1 in+1
    spot = path, line, column, line2 + 1, column2 + 1
    Exp.of2 spot,(S.span in+1 in2), (in2+1 . S.char & of_path path line2 column2+1 in2+1)
  |
    line2, column2, in2 = of_str path line column+1 in+1
    spot = path, line, column, line2, column2
    (spot, Str (S.span in in2)), (in2.S.char & of_path path line2 column2 in2)

of_exp (path,line,column,_),in:Spot,S : *Exp = of_path path line column in
Fact (of_exp $'foo [x]' . Exp.seq_str == "'foo ' x")
Fact (of_exp $'[x] foo' . Exp.seq_str == "x ' foo'")
Fact (of_exp $'foo [x] bar' . Exp.seq_str == "'foo ' x ' bar'")
Fact (of_exp $'foo [x + 40] bar' . Exp.seq_str == "'foo ' (x + 40) ' bar'")
Fact (Regex 'meta.m:\d*:\d*: Exp.str_tree invalid character.*' (Job.err (? of_exp $'foo [x 太] bar' . Z))) # current unit = meta.m

#  Meta [x:N, y:R] 'foo [x] bar [y]'  ->  List.str0 ['foo ', N.str x, ' bar ', R.str y]
main x=spot,s:Spot,S : Exp = spot, Tree [(spot, Name 'List.str0'), (spot, Listy x.of_exp.Exp.seq_row)]
Fact (main $'foo [x] bar [y]' . str == "(List.str0 ['foo ', x, ' bar ', y])")
