# key row, named product, json, label

  https://en.wikipedia.org/wiki/Record_(computer_science)
  https://en.wikipedia.org/wiki/Struct_(C_programming_language)

get_at exp:Exp types:Types key:S base:N : Types ? N, Type =
  (_, Binary (_, Name x) ':' t), _ & x == key? base, t
  _, t? get_at exp types key base+8 t
  ? Exp.seq_error $Fun 'invalid '+key exp,types

get exp:Exp key:S : Type ? N, Type =
  _, Row t? get_at exp t key 0 t
  t? Exp.seq_error $Fun 'not row - '+key [t, exp]
    
# todo - key in tail
is : Type ? B =
  _, Row ((_, Binary (_, Name _) ':' _), _)? 1                                  

in x:S : Type ? B = _, Row s? List.any s (in_binary x)

in_binary x:S : Type ? B = _, Binary (_, Name y) ':' _? x == y

at base:N x:0 : 1 = Mem.get (x.Mem.of + base) . Cast.any

_test1 x:(foo:N, bar:S) : N = foo x
_test2 x:(foo:N, bar:S) : S = bar x
_test3 x:(foo:N, bar:S) : N = _test1 x
_test4 x:N,S : N = _test1 x
_test5 x:(foo:N, bar:S) : N = _test4 x
_test6 x:N : foo:N, bar:S = 42, 'car'

Fact (_test1 42,'car' == 42)
Fact (_test1 (foo=42, bar='car') == 42)
Fact (_test2 42,'car' == 'car')
