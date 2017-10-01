# bit, bool, boolean, flag, truth, logic, 0 or 1
  
  0 false, f, no, n, null, nil, off, falsehood, contradiction, nay
  1 true, t, yes, y, some, on, truth, tautology, aye

  http://en.wikipedia.org/wiki/Boolean_data_type

or x:B y:B : B = x | y

and x:B y:B : B = x & y

all f:0?B x:B a:0 : B = x & f a          

any f:0?B x:B a:0 : B = f a | x

str x:B : S = x & '1' | '0'
Fact (0.str == '0')
Fact (1.str == '1')

of : S? B =
  '0'? 0
  '1'? 1
  x? Fail.fill "$s: bad '$s'" [$Fun, x]
Fact !(of '0')
Fact (of '1')
Fact (Job.err ?Z(of 'foo') == "B.of: bad 'foo'\.")

put x:B = x.B.str.Put

log x:B = x.B.str.Log

eq x:B y:B : B = nat x == nat y
Fact (eq 0 0)
Fact !(eq 0 1)
Fact !(eq 1 0)
Fact !(eq 42.cast 0)
Fact (eq 1 1)
Fact (eq 42.cast 1)

ne x:B y:B : B = nat x != nat y
Fact !(ne 0 0)
Fact (ne 0 1)
Fact (ne 1 0)
Fact (ne 42.cast 0)
Fact !(ne 1 1)
Fact !(ne 42.cast 1)

not x:B : B = Asm
  cmp sp 8 0
  j e B.not0
  mov sp 16 0
  ret
  @B.not0
  mov sp 16 1
  ret

# B.or, else N.or is inferred
Fact !(B.or 0 0 0)
Fact (B.or 0 0 1)
Fact (B.or 0 1 !Fail.nil)
Fact (Job.err ?(B.or 0 'foo'.Fail) == "foo: error \.")

cast x:0 : B = Cast.bit x

nat x:B : N = Cast.bit_nat (N.ne x.Cast.any 0)
Fact (nat 0 == 0)
Fact (nat 1 == 1)
Fact (nat 42.cast == 1)
