# javascript object notation

  https://en.wikipedia.org/wiki/JSON

term line:N column:N s:S : !Term, line2:N, column2:N, !S =
  x = S.char s
  y = x & S.char s+1
  | x == 0 & 0:!Term, 0, 0, 0
  
  | x == \  & term line column+1 s+1

  | x == 0a & term line+1 column s+1

  | x == \" &                
    r, n = S.cut_line s+1 \" 0
    Str (S.span s+1 r), line + n, column + r-s, r + 1

  | x == \- &
    term, line2, column2, in2 = term line column+1 s+1
    Term.neg term, line2, column2, in2
  
  | C.is_digit x &
    z, r = Term.of_num s
    z, line, column + r-s, r

  | S.has '{}[]:,' x &  
    Op (C.str x), line, column + 1, s + 1

  | C.is_alpha x &
    r = S.cut_by s+1 C.is_alpha
    Name (S.span s r), line, column + r-s, r

  | Fail.fill ':$n:$n: $s invalid character $c' [line, column, $Fun, x]
  
str_terms line:N column:N in:S : Terms =
  term, line2, column2, in2 = term line column in
  term & term, str_terms line2 column2 in2

Fact (str_terms 0 0 '{"Item":{"range":{"S":"bar"},"hash":{"S":"foo"},"item":{"S":"42"}}}' . Term.seq_str == "{ 'Item' : { 'range' : { 'S' : 'bar' } , 'hash' : { 'S' : 'foo' } , 'item' : { 'S' : '42' } } }")
Fact (str_terms 0 0 '[1, 2, 3]' . Term.seq_str == '[ 1 , 2 , 3 ]')

terms_tree_seq pairs:*(S, Term) : Terms? *(S, Term), Terms =
  Op '}', terms? [], terms
  terms?
    pair, terms2 = terms_pair terms
    terms2 .
      Op ',', terms3? terms_tree_seq pair,pairs terms3
      Op '}', terms3? (pair, pairs).List.rev, terms3
      s? Fail.main2 $Fun s.Term.seq_str
  
terms_list_seq seq:Terms : Terms? Terms, Terms =
  Op ']', terms? [], terms
  terms?
    term, terms2 = terms_tree terms
    terms2 .
      Op ',', terms3? terms_list_seq term,seq terms3
      Op ']', terms3? (term, seq).List.rev, terms3
      s? Fail.main2 $Fun s.Term.seq_str
    
terms_pair : Terms ? S,Term, Terms =
  Str name, (Op ':', terms)?
    tree, terms2 = terms_tree terms
    name,tree, terms2
  s? Fail.main2 $Fun s.Term.seq_str
  
terms_tree : Terms ? Term, Terms =
  Op '{', terms?
    pairs, terms2 = terms_tree_seq [] terms
    Map pairs, terms2
  Op '[', terms?
    seqs, terms2 = terms_list_seq [] terms
    Terms seqs, terms2
  term, terms? term, terms
  ? Fail $Fun

str_tree in:S : Term = str_terms 0 0 in . terms_tree . 0

Fact (str_tree '{"Item":{"range":{"S":"bar"},"hash":{"S":"foo"},"item":{"S":"42"}}}' . str == "(Item,(range,(S,'bar') hash,(S,'foo') item,(S,'42')))")
Fact (str_tree '[1, 2, 3]' . str == '(1 2 3)')
Fact (str_tree '[{"x":1}]' . str == '((x,1))')
Fact (str_tree '{}' . str == '()')
Fact (str_tree '[{"x":[]}]' . str == '((x,()))')

at key:S : Term? Term =
  Map pairs? Map.get S.eq pairs key | Fail.main4 $Fun 'invalid key' key (Map pairs).str
  Terms terms? List.at_opt key.S.nat terms | Fail.main4 $Fun 'invalid key' key (Terms terms).str
  Str s & key == '+'? Nat (S.nat s)
  term? Fail.main4 $Fun 'invalid term' key term.str
Fact (at 'Item' (str_tree '{"Item":{"range":{"S":"bar"},"hash":{"S":"foo"},"item":{"S":"42"}}}') . str == "(range,(S,'bar') hash,(S,'foo') item,(S,'42'))")

at_key_seq term:Term : *S? Term =
  key, keys? at_key_seq (at key term) keys
  ? term
Fact (at_key_seq (str_tree '{"Item":{"range":{"S":"bar"},"hash":{"S":"foo"},"item":{"S":"42"}}}') ['Item','item','S','+'] . str == "42")
Fact (at_key_seq (str_tree '{"Item":{"range":{"S":"bar"},"hash":{"S":"foo"},"item":{"S":"42"}}}') 'Item item S +'.S.words . str == "42")

at_keys term:Term keys:S : S = at_key_seq term keys.S.words . str
Fact (at_keys (str_tree '{"Item":{"range":{"S":"bar"},"hash":{"S":"foo"},"item":{"S":"42"}}}') 'Item item S +' == '42')
Fact (at_keys (str_tree '{"foo":[1, 2, 3]}') 'foo 2' == '3')

get in:S path:S : S =  at_key_seq in.str_tree path.S.terms . str

main path:S = get !In path . Put
