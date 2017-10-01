# hexadecimal number

  https://en.wikipedia.org/wiki/Hexadecimal
  leading with 0 instead of 0x: 0cafe_babe 0dead_beef  

str_rev x:N y:S = x & (S.set y (x % 16 < 10 & x % 16 + \0 | x % 16 - 10 + \a).N.char; str_rev x/16 y+1) | S.set y \0
str x:N : S = (y = S.new 17; str_rev x y; S.rev y)
Fact (str 02a == '42')
Fact (Hex.str 02a == '02a')
# 'cafebabe'.decode('hex'); import binascii; binascii.unhexlify('cafebabe')
Fact (Hex.str 0cafe_babe_dead_beef == '0cafebabedeadbeef')

# without leading 0
str_rev0 x:N y:S = x & (S.set y (x % 16 < 10 & x % 16 + \0 | x % 16 - 10 + \a).N.char; str_rev0 x/16 y+1)
str0 x:N : S = (y = S.new 17; str_rev0 x y; S.rev y)
Fact (str0 02a == '2a')

str4 x:N : S = '0' + x.str0.S.div4
Fact (str4 0cafe_babe_dead_beef == '0cafe_babe_dead_beef')

char x:N : C = (x % 16 < 10 & x % 16 + \0 | x % 16 - 10 + \a).N.char
Fact (char 1 == \1)
Fact (char 10 == \a)
Fact (char 0a == \a)
Fact (char 15 == \f)
Fact (char 0ab == \b)

# https://en.wikipedia.org/wiki/Nibble
at x:N shift:N : C = N.and (N.shr x shift) 0f . char

n0_str x:N : S = (y = S.new 2; S.set y (at x 4); S.set y+1 (at x 0); y)
Fact (n0_str 0cafe == 'fe')

n0_out x:N = x.n0_str.Out

# char_out x:C = x.n0_str.Out

out x:N = x.Hex.str.Out
Fact (Job.out ?(Hex.out 0cafebabe) == '0cafebabe')

out0 x:N = x.str0.Out

put x:N = x.str.Put

put0 x:N = x.str0.Put

line x:N = x.str.Put

log x:N = x.str.Log

str_size = 16 + 1 : N                                                           # 0ffff_ffff_ffff_ffff
