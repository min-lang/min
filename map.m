# finite map, association, dictionary

  https://en.wikipedia.org/wiki/Associative_array

in eq:0?0?B s:*(0,1) x:0 : B =
  s & 
    a, b = s.List.head
    | eq a x & 1
    # | a == x & 1
    | in eq s.List.tail x
Fact (in S.eq ['foo',41, 'bar',42] 'bar')
Fact !(in S.eq ['foo',41, 'bar',42] 'qux')

get eq:0?0?B s:*(0,1) x:0 : !1 =
  | s &
    a, b = s.List.head
    | eq a x & b
    | get eq s.List.tail x
Fact (get S.eq ['foo',41, 'bar',42] 'bar' == 42)
Fact !(get S.eq ['foo',41, 'bar',42] 'qux' . Opt.bit) 

get_by eq:0?0?B s:*(0,1) x:0 : !1 =
  | s &
    a, b = s.List.head
    | eq a x & b
    | get_by eq s.List.tail x
Fact (get_by S.eq ['foo',41, 'bar',42] 'bar' == 42)
Fact !(get_by S.eq ['foo',41, 'bar',42] 'qux' . Opt.bit) 

pair eq:0?0?B s:*(0,1) x:0 : !(0, 1) =
  | s &
    a, b = s.List.head
    # | a == x & a, b
    | eq a x & a, b
    | pair eq s.List.tail x
Fact (pair S.eq ['foo',41, 'bar',42] 'bar' == 'bar',42) 

get_nat str:0?S eq:0?0?B error:S s:*(0,N) x:0 : N =
  | s &
    a, b = s.List.head
    | eq a x & b
    | get_nat str eq error s.List.tail x
  | Fail.main3 error 'get_nat' x.str
Fact (get_nat S.str S.eq '' ['foo',41, 'bar',0] 'foo' == 41)
Fact (get_nat S.str S.eq '' ['foo',41, 'bar',42] 'bar' == 42)
#Fact (Job.err ?Z(get_nat N.str N.eq 'foo' [2,41, 3,42] N.max3) == "foo: error  get_nat 18446744073709551615\.") [make race] Job.err?
#Fact (Job.err ?Z(get_nat 'fum' ['foo',41, 'bar',0] 'qux') == "fum: error  get_nat qux\.") # [make race] Job.err?
    
str_by f:0?S g:1?S s:*(0,1) : S = List.map_str s (Pair.str_by f g)
Fact (str_by Fun.id R.str ['foo',3.14, 'bar',42.] == 'foo,3.14 bar,42')
Fact (str ['foo',3.14, 'bar',42] == 'foo,3.14,bar,42') # fixme: foo,3.14 bar,42
Fact (str [(2, 3), (5, 8)] == '2,3 5,8')
Fact (str ['foo',41, 'bar',42] == 'foo,41 bar,42')

map s:*(0,1) f:0?2 g:1?3 : *(2,3) = s & (x, y = s.List.head; (f x, g y), map s.List.tail f g)
Fact (map ['foo',41, 'bar',42] S.dup2 N.tick . str == 'foofoo,42 barbar,43')

keys_map s:*(0,1) f:0?1?2 : *2 = s & (x, y = s.List.head; f x y, keys_map s.List.tail f)
Fact (keys_map ['foo',41, 'bar',42] (_ x:S y:N : N, S = y, x) . str == '41,foo 42,bar')

keys s:*(0,1) : *0 = keys_map s (_ x:0 _:1 : 0 = x)
Fact (keys ['foo',41, 'bar',42] == ['foo', 'bar'])

key_set s:*(0,1) : 0/Z = keys s . List.set

map_str s:*(0,1) f:0?S g:1?S : S = map s f g . str
Fact (map_str ['foo',41, 'bar',42] S.dup2 N.str == 'foofoo,41 barbar,42')

map1_rev s:*(0,1) f:1?2 r:*(0,2) : *(0,2) = s & map1_rev s.List.tail f (x, y = s.List.head; (x, f y), r) | r

map1 f:1?2  s:*(0,1) : *(0,2) = List.rev (map1_rev s f 0)
Fact (map1 N.tick [1,2, 3,4] == [1,3, 3,5])
Fact (map1 N.tick ['foo',41, 'bar',42] . str == 'foo,42 bar,43')

map1_alt f:1?2 s:*(0,1) : *(0,2) = map s Fun.id f
Fact (map1_alt N.tick [1,2, 3,4] == [1,3, 3,5])

do s:*(0,1) f:0?1?Z = s & (x, y = s.List.head; f x y; do s.List.tail f)
