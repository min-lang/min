# universal character set

mask = _0011_1111

of2 a:N b:N : N = N.or (N.shl a 6) b
of3 a:N b:N c:N : N = N.or3 (N.shl a 12) (N.shl b 6) c
of4 a:N b:N c:N d:N : N = N.or4 (N.shl a 24) (N.shl b 12) (N.shl c 6) d

char2 s:S : C, S = 42, ''

#
  https://en.wikipedia.org/wiki/UTF-8
    7	  U+0000	U+007F	  0xxxxxxx                                       0000_0000
    11	U+0080	U+07FF	  110xxxxx	10xxxxxx                             1100_0000  
    16	U+0800	U+FFFF	  1110xxxx	10xxxxxx	10xxxxxx                   1110_0000  
    21	U+10000	U+1FFFFF	11110xxx	10xxxxxx	10xxxxxx	10xxxxxx         1111_0000  
char s:S : C, S =
  x = S.char s
  | x < _1100_0000 & x . N.char, s + 1                                          # hex(0b11000000) = 0xc0

  | x < _1110_0000 &                                                            # hex(0b11100000) = 0xe0
    y = S.char s+1  
    of2 (N.and x _0001_1111) (N.and y mask) . N.char, s + 2

  # https://en.wikipedia.org/wiki/Plane_(Unicode)#Basic_Multilingual_Plane
  | x < _1111_0000 &                                                            # hex(0b11110000) = 0xf0
    y = S.char s+1
    z = y & S.char s+2
    of3 (N.and x _0000_1111) (N.and y mask) (N.and z mask) . N.char, s + 3

  # https://en.wikipedia.org/wiki/Plane_(Unicode)#Supplementary_Multilingual_Plane
  |
    y = S.char s+1
    z = y & S.char s+2
    w = z & S.char s+3
    of4 (N.and x _0000_0111) (N.and y mask) (N.and z mask) (N.and w mask) . N.char, s + 4

Fact (s = 'foo'; char s == \f,s+1)

# u'\xbc\xbd'.encode('utf8') = '\xc2\xbc\xc2\xbd'
# '太極'.encode('utf8') = '\xc2\xbc\xc2\xbd'
# hex(((0xc2 & 0b00011111) << 6) + (0xbc & 0b00111111)) = 0xbc
Fact (s = "\c2\bc\c2\bd"; char s == 0bc,s+2) 

# u'太極' = u'\u592a\u6975'
# u'太極'.encode('utf8') = '\xe5\xa4\xaa\xe6\xa5\xb5'
Fact (s = "\e5\a4\aa\e6\a5\b5"; char s == 0592a,s+3)

# https://en.wikipedia.org/wiki/Emoticons_(Unicode_block) 😄
# print u'\U0001f604' # smiley face in Terminal
# u'\U0001f604'.encode('utf8') = '\xf0\x9f\x98\x84'
Fact (s = "\f0\9f\98\84"; char s == 01f604,s+4)

# https://en.wikipedia.org/wiki/Number_Forms vulgar fraction
# ¼ ½ ¾ ⅐ ⅑ ⅒ ⅓ ⅔ ⅕ ⅖ ⅗ ⅘ ⅙ ⅚ ⅛ ⅜ ⅝ ⅞ ↉
is_op x:C : B = List.in C.eq [\≈] x

is_name x:C : B = List.in C.eq [\σ, \ϕ, \π, \√, \², \ℯ, \₀, \₁, \₂, \½, \⅓, \¼, \⅕, \⅙, \⅐, \⅛, \⅑, \⅒] x
Fact (is_name \π)
Fact (is_name \²)
Fact (is_name \½)

# todo
  ⅈ ∞
  × ✕ ✖ ÷
  ∘ ∙ ⋅ ⋆
  ∅ ∈
  ∪ ∩ ≤ ≥ ⊂ ⊃ ⊆ ⊇
  ⋀ ⋁ ∫ ⌈ ⌉ ⌊ ⌋ ∀ ∃ ≈
