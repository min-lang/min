# nat, non-negative natural number, unsigned integer

  http://en.wikipedia.org/wiki/Natural_number
  https://en.wikipedia.org/wiki/Integer_(computer_science)#Long_long
  http://danluu.com/integer-overflow/# The Performance Cost of Integer Overflow Checking

add x:N y:N : N = Asm
  mov a sp 16
  mov c sp 8
  add a c
  mov sp 24 a
  ret

sub x:N y:N : N = Asm
  mov a sp 16
  mov c sp 8
  sub a c
  mov sp 24 a
  ret

mul x:N y:N : N = Asm
  mov a sp 16
  mul sp 8
  mov sp 24 a
  ret

div x:N y:N : N = Asm
  mov a sp 16
  mov d 0
  div sp 8
  mov sp 24 a
  ret

mod x:N y:N : N = Asm
  mov a sp 16
  mov d 0
  div sp 8
  mov sp 24 d
  ret

or x:N y:N : N = Asm 
  mov a sp 16
  mov c sp 8
  or a c
  mov sp 24 a
  ret

and x:N y:N : N = Asm
  mov a sp 16
  mov c sp 8
  and a c
  mov sp 24 a
  ret

shl x:N y:N : N = Asm
  mov a sp 16
  mov c sp 8
  shl a
  mov sp 24 a
  ret

shl32 x:N : N = Asm
  mov a sp 8
  shl a 32
  mov sp 16 a
  ret

shr x:N y:N : N = Asm
  mov a sp 16
  mov c sp 8
  shr a
  mov sp 24 a
  ret

eq x:N y:N : B = Asm
  mov a sp 16
  cmp a sp 8
  mov c 0
  set e c
  mov sp 24 c
  ret

ne x:N y:N : B = Asm
  mov a sp 16
  cmp a sp 8
  mov c 0
  set ne c
  mov sp 24 c
  ret

gt x:N y:N : B = Asm
  mov a sp 16
  cmp a sp 8
  mov c 0
  set g c
  mov sp 24 c
  ret

ge x:N y:N : B = Asm
  mov a sp 16
  cmp a sp 8
  mov c 0
  set ge c
  mov sp 24 c
  ret

lt x:N y:N : B = Asm
  mov a sp 16
  cmp a sp 8
  mov c 0
  set l c
  mov sp 24 c
  ret

le x:N y:N : B = Asm
  mov a sp 16
  cmp a sp 8
  mov c 0
  set le c
  mov sp 24 c
  ret

neg x:N : N = Asm
  mov a sp 8
  neg a
  mov sp 16 a
  ret
  
char x:N : C = Cast.nat_char x

bit x:N : B = Cast.bit x

str_rev x:N y:S = x & (S.set y (x % 10 + \0).char; str_rev x/10 y+1)
str x:N : S = (y = S.new 20; x & (str_rev x y; S.rev y) | (S.set y \0; y))
Fact (str 42 == '42')
Fact (str \a == 'a')
Fact (N.str \a == '97')
Fact (str 3141592653589793238 == '3141592653589793238')

str_pure x:N : S = (y = S.new 20; x & (str_rev x y; S.rev_pure y) | (S.set y \0; y))       
Fact (str_pure 42 == '42')
Fact (str_pure \a == '97')
Fact (str_pure 3141592653589793238 == '3141592653589793238')
 
str3 x:N : S = str x . S.div3
Fact (str3 3141592653589793238 == '3_141_592_653_589_793_238')

of1 a:N b:N : N = or (shl a 8) b
Fact (of1 0ca 0fe == 0cafe)

of2 a:N b:N c:N d:N : N = or (shl (of1 a b) 16) (of1 c d)
Fact (of2 0ca 0fe 0ba 0be == 0cafe_babe)

of3 a:N b:N c:N d:N e:N f:N g:N h:N : N = or (shl (of2 a b c d) 32) (of2 e f g h)
Fact (of3 0ca 0fe 0ba 0be 0de 0ad 0be 0ef == 0cafe_babe_dead_beef)

str5 x:N : S = (y = x.str; S.heads y+'     ' 5)

put x:N = x.str.Put
err x:N = x.str.Err
log x:N = x.str.Log
write file:File x:N = File.write file x.str
linef file:File x:N = File.line file x.str

between a:N x:N b:N : B = a <= x & x <= b
Fact (between 13 29 42)
Fact !(between 42 13 29)

min x:N y:N : N = x < y & x | y
Fact (min 0 42 == 0)
Fact (min 13 42 == 13)

max x:N y:N : N = x < y & y | x
Fact (max 0 42 == 42)
Fact (max 42 13 == 42)

rank x:N : N =
  | x <= 0ff & 0 
  | x <= 0ffff & 1 
  | x <= 0ffff_ffff & 2
  | 3
Fact (rank 42 == 0)
Fact (rank 0cafe == 1)
Fact (rank 0cafe_babe == 2)
Fact (rank 0cafe_babe_dead_beef == 3)

at x:N shift:N : N = and (shr x shift) 0ff 
Fact (at 0cafe_babe_dead_beef 16 == 0ad)

for n:N f:N?0 i=0:N = i < n & (f i; for n f i+1)
_fact_sum = %0 : %N
Fact (for 10 (_ x:N = Ref.add _fact_sum x); !_fact_sum == 45)

for2 n:N f:0?N?Z x:0 i=0:N = i < n & (f x i; for2 n f x i+1)
_fact_sum2 = %0 : %N
Fact (for2 10 (_ a:N x:N = Ref.add _fact_sum2 a+x) 1; !_fact_sum2 == 55)

any f:N?B n:N i=0:N : !N = i < n & (f i & opt i | any f n i+1)
Fact (any (_ x:N : B = 5*x > 42) 10 == opt 9)

do n:N f:Z?Z = n > 0 & (f 0; do n-1 f)  
_fact_do_sum = %0 : %N
Fact (do 10 (? Ref.tickz _fact_do_sum); !_fact_do_sum == 10)

add3 x:N y:N z:N : N = x + y + z

even x:N : B = x % 2 == 0

odd x:N : B = x % 2 == 1

mod2 x:N y:N : B = x % 2 == y % 2

mod2_ne x:N y:N : B = x % 2 != y % 2 # !mod2

tick x:N : N = x + 1

div0 x:N y:N : N = y & x / y

sub2 y:N x:N : N = x - y

map n:N f:N?0 : *0 = n & f n-1, map n-1 f
Fact (map 3 Fun.id == [2, 1, 0])

# https://developer.apple.com/library/mac/documentation/Darwin/Reference/ManPages/man3/rand.3.html int rand(void);
lib_rand = Dl'rand' : Z? N

rand _ : N = Fun.call0 lib_rand

pick n:N : N = 0.rand % n                                                       # RAND_MAX = 2147483647 = 0x7fffffff, 31-bit
Fact (pick 13 <= 13)

hex1 x:C : N = between \a x \f & x - \a + 10 | x - \0
Fact (hex1 \d == 13)

or3 x:N y:N z:N : N = or (or x y) z
or4 x:N y:N z:N w:N : N = or (or (or x y) z) w

bytes : N ? N =
  0? 1
  1? 2
  2? 4
  3? 8
  n? Fail.main2 $Fun n.N.str

max3 = 0ffff_ffff_ffff_ffff

ip x:N : S = S.fill '$n.$n.$n.$n' [N.at x 0, N.at x 8, N.at x 16, N.at x 24]

real x:N : R = Cast.bits_real x

str_size = 20                                                               # 2^64 = 18446744073709551616

opt x:N : !N = Cast.any (x + 1)

must x:!N : N = Cast.nat x - 1
