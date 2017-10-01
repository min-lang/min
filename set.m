# mathematical set

  http://en.wikipedia.org/wiki/Set_%28mathematics%29

main size:N : 0/Z = Cast.any ((size | 1), Row (size | 1))

in eq:0?0?B set:0/Z x:0 : B =
  size, mem = Hash.data set # size > 0 by Set
  i = S.hash x % size
  r = Cast.any (Row.at mem i)                                           
  List.in eq r x
Fact (in S.eq ['foo', 'bar'].List.set 'bar')

add set:0/Z x:0 =  
  size, mem = Hash.data set # size > 0 by Set
  i = S.hash x % size
  r = Cast.any (Row.at mem i)
  Row.set mem i (Cast.any x,r)
Fact (s = ['foo', 'bar'].List.set; add s 'bar'; in S.eq s 'bar')
