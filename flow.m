# stream, buffer, port

 https://en.wikipedia.org/wiki/Stream_(computing)
  
Flow = head:S, last:S

main n:N : Flow = (s = S.new n; s, s) # FIXME check size

head s:Flow : S = s.0 # inlined

last s:Flow : S = s.1 # inlined

add s:Flow n:N = Mem.add s.Mem.of+8 n # inlined

size s:Flow : N = (s0, s1 = s; s1 - s0)

char s:Flow x:C = (S.set s.last x; add s 1)
Fact (s = main 1; char s \a; out_str s == 'a')

mem s:Flow n:N x:Mem = (Mem.copy x s.last.S.mem n; add s n) # racy

str s:Flow x:S = (S.copy0 x s.last; add s !x) # racy
Fact (s = main 3; str s 'foo'; size s == 3 & out_str s == 'foo')

str0 s:Flow x:S = (str s x; char s 0)   #  null terminated, do not assume zero buffer
Fact (s = main 4; str0 s 'foo'; size s == 4 & out_str s == 'foo')

str_pad s:Flow x:S n:N = (S.copy x s.last; add s n)
Fact (s = main 5; str_pad s 'foo' 5; size s == 5)

str_size_nil s:Flow x:S n:N = (S.copy_size_nil x s.last n; add s n+1)
Fact (s = main 5; str_size_nil s 'foo' 5; size s == 6)
Fact (s = main 5; str_size_nil s 'foobarqux' 5; size s == 6)

nat0 s:Flow x:N = char s x.N.char
Fact (s = main 1; nat0 s \a; out_str s == 'a')

nat1 s:Flow x:N = (nat0 s x; nat0 s (N.shr x 8))
Fact (s = main 2; nat1 s (N.of1 \a \c); out_str s == 'ca')

nat2 s:Flow x:N = (nat1 s x; nat1 s (N.shr x 16))
Fact (s = main 4; nat2 s (N.of2 \e \f \a \c); out_str s == 'cafe')

nat3 s:Flow x:N = (nat2 s x; nat2 s (N.shr x 32))
Fact (s = main 8; nat3 s (N.of3 \e \b \a \b \e \f \a \c); out_str s == 'cafebabe')

nat s:Flow x:N : N?Z =
  0? nat0 s x
  1? nat1 s x
  2? nat2 s x
  3? nat3 s x
Fact (s = main 8; nat s (N.of3 \e \b \a \b \e \f \a \c) 3; out_str s == 'cafebabe')

out s:Flow = Out.size s.head s.size

out_str s:Flow : S = S.sub s.head s.size
