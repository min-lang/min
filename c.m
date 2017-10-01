# char, character, unicode code point

  https://en.wikipedia.org/wiki/Character_(computing)
  https://en.wikipedia.org/wiki/Unicode
  
add x:C y:N : C = Asm
  mov a sp 16
  mov c sp 8
  add a c
  mov sp 24 a
  ret

sub x:C y:N : C = Asm
  mov a sp 16
  mov c sp 8
  sub a c
  mov sp 24 a
  ret

Fact (\. == 46)
Fact (\a == 97)

eq x:C y:C : B = N.eq x y

ne x:C y:C : B = N.ne x y

bin x:C : N = x - \0
Fact (bin \0 == 0)
Fact (bin \1 == 1)

hex x:C : N = between \a x \f & x - \a + 10 | x - \0
Fact (hex \a == 0a)

hex2 x:C y:C : N = (16 * hex x) + hex y
Fact (hex2 \4 \2 == 042)

meta : C? C = (\.? 0a; \!? 0d; \'? \"; \"? \'; \\? \\) # printf format
Fact (meta \. == 0a)
Fact (meta \! == 0d)
Fact (meta \' == \")
Fact (meta \" == \')

code2 : C? S = (09? '\,'; 0a? '\.'; 0d? '\!'; x? str x) 
Fact (code2 0a == '\.')
Fact (code2 09 == '\,')
Fact (code2 0d == '\!')

out x:C = x.str.Out

put x:C = x.str.Put

err x:C = x.str.Err

log x:C = x.str.Log

str x:C : S = (s = S.new 1; S.set s x; s)
Fact (str \a == 'a')

str2 x:C y:C : S = (s = S.new 2; S.set s x; S.set s+1 y; s)
Fact (str2 \2 \a == '2a')

code x:C : S = (r = S.new 2; S.set r \\; S.set r+1 x; r)
Fact (code \a == "\\a")

between a:C x:C b:C : B = N.between a x b

is_bin x:C : B = x == \0 | x == \1
Fact (is_bin \0)
Fact (is_bin \1)
Fact !(is_bin \2)

is_lo_bin x:C : B = x == \0 | x == \1 | x == \_
Fact (is_lo_bin \_)
Fact (is_lo_bin \0)
Fact (is_lo_bin \1)
Fact !(is_lo_bin \2)

is_digit x:C : B = between \0 x \9
Fact (is_digit \7)
Fact !(is_digit \a)

is_dec x:C : B = x == \_ | is_digit x
Fact (is_dec \7)
Fact (is_dec \_)

is_hex x:C : B = is_dec x | between \a x \f 
Fact (is_hex \a)
Fact (is_hex \_)

upper x:C : C = add x (\A - \a)
Fact (upper \a == \A)

is_upper x:C : B = between \A x \Z
Fact (is_upper \A)
Fact !(is_upper \a)

is_lower x:C : B = between \a x \z
Fact (is_lower \a)
Fact !(is_lower \A)

is_lo_upper x:C : B = x == \_ | is_upper x

is_lo_lower x:C : B = x == \_ | is_lower x

is_letter x:C : B = is_upper x | is_lower x

is_alpha x:C : B = is_dec x | is_letter x
Fact (is_alpha \a)
Fact (is_alpha \_)

is_name x:C : B = x == \. | is_alpha x
Fact (is_name \A)
Fact (is_name \.)

is_nil x:C : B = x == 0 

is_any x:C : B = 1

nat x:C : N = Cast.char_nat x

max = 010_fffd

opt x:C : !C = Cast.any (x + 1)
