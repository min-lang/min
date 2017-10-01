# hashtable, mutable and unordered map

  https://en.wikipedia.org/wiki/Hash_table

  (0/1) = N, (0,1)^

# size > 0 or Hash.set fails
main size:N : 0/1 = Cast.any ((size | 1), Row (size | 1))

data s:0/1 : N, Mem = Cast.any s 

size s:0/1 : N = data s . 0

mem s:0/1 : Mem = data s . 1

in hash:S/0 x:S : B =
  size, mem = data hash
  i = S.hash x % size
  r = Cast.any (Row.at mem i)                                           
  List.any r (Pair.eq0 S.eq x)
Fact (in ['foo',13, 'bar',42].List.hash 'bar')
Fact !(in ['foo',13, 'bar',42].List.hash 'qux')
Fact !(in [].List.hash 'foo')

pair hash:S/0 x:S : !(S, 0) =
  size, mem = data hash
  i = S.hash x % size
  r = Cast.any (Row.at mem i)                                           
  List.get_by r (Pair.eq0 S.eq x)
Fact (pair ['foo',13, 'bar',42].List.hash 'bar' == 'bar',42)  
Fact !(pair [].List.hash 'foo' . Opt.bit)

get hash:S/0 x:S : !0 =
  y = pair hash x
  y & y.Row.at1                                                         
Fact (get ['foo',13, 'bar',42].List.hash 'bar' == 42)
Fact !(get [].List.hash 'foo')

set hash:S/0 x:S y:0 =  
  size, mem = data hash
  i = S.hash x % size
  r = Cast.any (Row.at mem i)                                           
  Row.set mem i (Cast.any (x,y),r)
Fact (s = ['foo',13, 'bar',42].List.hash; set s 'bar' 41; get s 'bar' == 41)
Fact (s = [].List.hash; set s 'bar' 41; get s 'bar' == 41)

get_set hash:S/0 x:S y:0 : B, 0 =
  a = get hash x
  a & 0, a | (set hash x y; 1, y) 
Fact (s = [].List.hash; get_set s 'bar' 41 == 1,41; get_set s 'bar' 42 == 0,41)

map1 hash:0/1 f:1?2 =
  size, mem = data hash
  Row.for (Map.map1 f) mem size
Fact (s = ['foo',13, 'bar',42].List.hash; map1 s N.tick; get s 'bar' == 43)
