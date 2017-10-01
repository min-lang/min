# str, string, character array

  https://en.wikipedia.org/wiki/String_(computer_science)        

_time = %0 : %N
eq r:S s:S : B = Fun.call2 lib_strcmp r s == 0

eq_limit r:S s:S n:N : B = Fun.call3 lib_strncmp r s n == 0

mem s:S : Mem = Cast.str_mem s

nat s:S : N = s.mem.Mem.nat

id r:S s:S : B = Mem.id r.mem s.mem
eq0 r:S s:S : B = char r == char s & (! r.bit | eq0 r+1 s+1)
Fact (eq 'foo' 'foo')
Fact !(eq 'foo' 'foo-')
Fact !(eq 'foo' 'bar')
Fact ('foo' == 'foo')

# define r != s in Rewrite by !(r == s)
ne r:S s:S : B = !(r == s)           
Fact (ne 'foo' 'bar')
Fact ('foo' != 'bar')

size s:S : N = Fun.call1 lib_strlen s
Fact ('foo'.size == 3)

copy r:S s:S = (Fun.call2 lib_strcpy s r; 0)
Fact (x = 'foo42'.dup; copy 'bar' x; x == 'bar')

# mutate!
copy_size_nil r:S s:S n:N = (Fun.call3 lib_strncpy s r n; 0)   # same as copy_size but terminate early if 0 in string
Fact (x = 'foo42'.dup; copy_size_nil 'bar' x 3; x == 'bar42')
Fact (x = 'foo42'.dup; copy_size_nil 'bar' x 5; x == 'bar')

# mutate!
copy_size r:S s:S n:N = Mem.copy r.mem s.mem n
Fact (x = 'foo42'.dup; copy_size 'bar' x 3; x == 'bar42')

# http://linux.die.net/man/3/strtoul
#   unsigned long int strtoul(const char *nptr, char **endptr, int base);
nat0 s:S : N = Fun.call3 lib_strtoul s 0 10 # does not handle _ between characters

hex0 s:S : N = Fun.call3 lib_strtoul s 0 16 # does not handle _ between characters

# https://developer.apple.com/library/mac/documentation/Darwin/Reference/ManPages/man3/strrchr.3.html
get s:S x:C : S = Fun.call2 lib_strchr s x
Fact (get 'foobar' \o == 'oobar')

last s:S : C = char (s + !s-1)
Fact (last 'bar' == \r)

rget s:S x:C : S = Fun.call2 lib_strrchr s x
Fact (rget 'foobar' \b == 'bar')

has s:S x:C : B = Fun.call2 lib_strchr s x . Cast.any
Fact (has 'foo' \o)
Fact !(has 'foo' \a)

_tok s:S x:S : !S = Fun.call2 lib_strtok s x

_parts x:S : *S =
  y = _tok 0 x
  y & y, _parts x

parts s:S x:S : *S = (y = _tok s.dup x; y & y, _parts x | [])
Fact (parts '' ' ' == [])
Fact (parts 'foo 42 bar' ' ' == ['foo', '42', 'bar'])

# words  whitespace \ \n\v\t
# parts  ,.;
# terms  punctuators  ][!"#$%&'()*+,./:;<=>?@\^_`{|}~-
words s:S : *S = parts s ' '
Fact (words 'foo 42 bar' == ['foo', '42', 'bar'])

terms s:S : *S = parts s '.'
Fact (terms 'foo.42.bar' == ['foo', '42', 'bar'])

part s:S x:S : !S = _tok s.dup x
Fact (part 'foo,bar' ',' == 'foo')

part2 s:S x:S : !S = (_tok s.dup x; _tok 0 x)
Fact (part2 'foo,bar' ',' == 'bar')

new n:N : S = Mem n+1 . Mem.str # unused, inlined in Step.exp_steps

char s:S : C = Mem.get0 s.mem
Fact (char 'foo' == \f)
Fact (char '' == 0)

bit s:S : B = s.char != 0
Fact (bit 'foo')
Fact !(bit '')

# mutate!
set s:S c:C = Mem.set0 s.mem c
Fact (x = 'foo'.dup; set x \b; x == 'boo')

copy_size0 r:S s:S n:N = Mem.copy r.mem s.mem n

copy0 r:S s:S = copy_size r s r.size

# https://developer.apple.com/library/mac/documentation/Darwin/Reference/ManPages/man3/strstr.3.html
strstr r:S s:S : S = Fun.call2 lib_strstr r s
Fact (strstr 'foobar' 'ob' == 'obar')

size_pure x:S : N = char x & 1 + size_pure (x.mem+1).Mem.str
Fact (size_pure 'foo' == 3)

size0 x:S : N = char x & 1 + size0 (x.mem+1).Mem.str

rev x:S : S = (n = x.size; y = new n; Mem.rev x.mem y.mem n; y)
Fact (eq 'bar'.rev 'rab')

rev_pure x:S : S = (n = x.size_pure; y = new n; Mem.rev x.mem y.mem n; y)
Fact (eq 'bar'.rev_pure 'rab')

add r:S s:S : S = (m = size r; n = size s; x = new m+n; copy_size r x m; copy_size s (x+m) n; x)
Fact (eq (add 'foo' 'bar') 'foobar')

add3 q:S r:S s:S : S = add q (add r s)
add4 p:S q:S r:S s:S : S = add p (add3 q r s)
add5 o:S p:S q:S r:S s:S : S = add o (add4 p q r s)

code s:S : S = (n = size s; r = new n+2; set r \'; copy_size s (r+1) n; set r+n+1 \'; r)
Fact ('foo'.code == "'foo'")

chars_eq r:S s:S : B = char r == char s & (! r.bit | chars_eq r+1 s+1)

dup s:S : S = (n = size s; r = new n; copy_size s r n; r)
Fact (eq (dup 'foo') 'foo')

sub s:S n:N : S = (r = new n; copy_size s r n; r)
Fact (eq (sub 'quux' 2) 'qu')

span r:S s:S : S = sub r s-r # unsafe, out of bound

key n:N i:I : N = I.lt i 0 & n + i | i
Fact (key 5 0 == 0)
Fact (key 5 1 == 1)
Fact (key 5 -1 == 4)

span_i s:S n:N i:I j:I : S = span (s + key n i) (s + key n j + 1)
Fact (span_i 'foobar' 6 1 -1 == 'oobar')
Fact (span_i 'foobar' 6 -4 -2 == 'oba')

spanx s:S i:N j:N : S = span s+i s+(size s + j + 1)
Fact (spanx 'foobar' 1 -2 == 'ooba')

cut s:S x:C : S = (y = s.char; (y == 0 | y == x) & s | cut s+1 x)
Fact (cut 'foobar' \b == 'bar')
Fact (cut 'foo' \b == '')

cut_quote s:S line:N column:N : !S, N, N =
  x = s.char .
    0? 0, 0, 0
    \'?
      | char s+1 == \' & cut_quote s+2 line column+2
      | s, line, column
    0a? cut_quote s+1 line+1 1
    _? cut_quote s+1 line column+1
Fact (cut_quote 'foobar' 0 1 == 0,0,0)
Fact (cut_quote "fo\.o'bar" 0 1 == "'bar",1,2)
Fact (cut_quote "foo''b'ar" 0 1 == "'ar",0,7)

cut_line s:S x:C line:N : S, N =
  y = s.char
  | (y == 0 | y == x) & s, line
  | y == 0a & cut_line s+1 x line+1
  | cut_line s+1 x line
Fact (s, n = cut_line "foo\.bar" \b 1; s == 'bar' & n == 2)

cut_not s:S x:C : S = (y = s.char; (y == 0 | y != x) & s | cut_not s+1 x)
Fact (cut_not 'oobar' \o == 'bar')
Fact (cut_not 'oo' \o == '')

# remove matching predicate
cut_by s:S f:C?B : S = (x = s.char; (x != 0 & f x) & cut_by s+1 f | s)
Fact (cut_by 'FOObar' C.is_upper == 'bar')
Fact (cut_by 'FOO' C.is_any == '')

bin_add s:S x:N : N = s.char & bin_add s+1 (s.char == \_ & x | (2 * x) + C.bin s.char) | x
bin s:S : N = bin_add s 0
Fact (bin '10_1010' == 42)

hex s:S x=0:N : N = s.char & hex s+1 (s.char == \_ & x | (16 * x) + C.hex s.char) | x
Fact ('42'.hex == 042)
Fact ('cafe_babe'.hex == 0cafe_babe)
Fact ('0cafe_babe_dead_beef'.hex == 0cafe_babe_dead_beef)

nat s:S x=0:N : N = s.char & nat s+1 (s.char == \_ & x | (10 * x) + s.char - \0) | x
Fact ('42'.nat == 42)
Fact ('3141592653589793238'.nat == 3141592653589793238)

has0 s:S x:C : B = char s & (x == char s | has0 s+1 x)

heads s:S n:N : S = sub s (N.min n s.size)
Fact (heads 'foobar' 3 == 'foo')

tails s:S n:N : S = span s+n s+s.size
Fact (tails 'foobar' 3 == 'bar')

_tick = %0 : %N

tick prefix:S : S = add prefix (Ref.tick _tick).N.str

set_rank s:S x:N r:N = Mem.set_rank s.mem x r

upper s:S : S = (r = dup s; set r r.char.C.upper; r)
Fact (upper 'foo' == 'Foo')

is_lower s:S : B = s.char.C.is_lower
Fact (is_lower 'foo')
Fact !(is_lower 'FOO')
Fact !(is_lower 'Foo')

is_capital s:S : B = s.char.C.is_upper
Fact (is_capital 'Foo')
Fact (is_capital 'FOO')
Fact !(is_capital '_Foo')
Fact !(is_capital 'foo')

# https://docs.oracle.com/javase/8/docs/api/java/lang/String.html#hashCode
hash x:S : N = x.char & (31 * x.char) + hash x+1
Fact (hash 'foo' == 10044)

quote_to r:S s:S =
  x = char r
  | x == \' & char r+1 == \' &
    set s \'
    quote_to r+2 s+1
  | x &
    set s x
    quote_to r+1 s+1
quote s:S : S = (r = new s.size; quote_to s r; r)
Fact (quote 'foobar' == 'foobar')
Fact (quote "foo''b\\61ar" == "foo'b\\61ar")
  
meta_to r:S s:S =                                                               # printf format 
  x = char r
  | x == \\ & char r+1 &
    y = char r+1
    | C.is_hex y &
      set s (C.hex2 y (char r+2))
      meta_to r+3 s+1
    |
      set s (C.meta y)
      meta_to r+2 s+1
  | x &
    set s x
    meta_to r+1 s+1
  
meta s:S : S = (r = new s.size; meta_to s r; r)
Fact (meta '\\' == \\.C.str) # '
Fact (meta '\62\61\72' == 'bar')
Fact ("\62\61\72" == 'bar')
Fact (meta "\.'\\" == (0a.C.str + \'.C.str + \\.C.str))

#
 https://en.wikipedia.org/wiki/Printf_format_string
 %[parameter][flags][width][.precision][length]type

 parameter - n$ positional
 flags - - + \  0 #
 width - * 
 precision - * 
 length - hh h l ll L z j t I I32 I64 q
   N0 N1 N2 N3
   I0 I1 I2 I3

 type - % d i u f F e E g G x X o s c p a A n

 Bin Hex 
 [x, width, precision]

 https://golang.org/pkg/text/template/
 
# format, meta, escape
  http://en.wikipedia.org/wiki/String_literal#Escape_sequences
    \a	07	^G Alarm (Beep, Bell)
    \b	08	^H Backspace
    \n	0A	^J Newline (Line Feed); see notes below
    \f	0C	^L Formfeed
    \r	0D	^M Carriage Return
    \t	09	^I Horizontal Tab
    \v	0B	^J Vertical Tab
    \'	27	   Single quotation mark
    \"	22	   Double quotation mark
    \?	3F	   Question mark
    \\	5C	   Backslash
    \nnn	any	The character whose numerical value is given by nnn interpreted as an octal number
    \xhh	any	The character whose numerical value is given by hh interpreted as a hexadecimal number
fill_char x:Any : C? S =
  \b? C.code x
  \c? C.str x
  \h? Hex.str x
  \n? N.str x
  \r? code x
  \s? x
  \$? '$'
  \,? 09.C.str
  \.? 0a.C.str
  c? Fail.main2 $Fun c.C.str

fill_size1 x:Any : C? N =
  \b? 1
  \c? 4
  \h? Hex.str_size
  \n? N.str_size
  \r? S.size x + 2                                                              # quotes "foo"
  \s? S.size x
  \$? 1
  \,? 1
  \.? 1
  c? Fail.main2 $Fun c.C.str

fill_flow s:S items:*Any flow:Flow : S =
  x = char s
  | x &
    | x == \$ &
      items | Fail.main2 'fill_flow empty items' s
      y = char s+1      
      Flow.str flow (fill_char items.List.head y)
      fill_flow s+2 ((y == \, | y == \.) & items | items.List.tail) flow
    |
      Flow.char flow x
      fill_flow s+1 items flow
  |
    items & Fail.main3 (!items).N.str 'fill_flow unused items' s
    Flow.out_str flow

fill_size s:S items:*Any : N =
  x = char s
  | x &
    | x == \$ &
      items | Fail.main2 'fill_size empty items' s
      y = char s+1
      fill_size1 items.List.head y + fill_size s+2 ((y == \, | y == \.) & items | items.List.tail)
    | 1 + fill_size s+1 items 
  |
    items & Fail.main3 (!items).N.str 'fill_size unused items' s
    0

fill s:S items:*Any : S = fill_flow s items (fill_size s items).Flow # printf format
Fact (fill 'foo $n $s $h bar' [42, 'qux', 42] == 'foo 42 qux 02a bar')

dup2 x:S : S = x + x
Fact (dup2 'foo' == 'foofoo')

skip_to s:S x:C r:S =                                                           # todo - rename to cut
  y = char s
  y &
    | x == y & skip_to s+1 x r
    | (set r y; skip_to s+1 x r+1)
skip s:S x:C : S = (r = new s.size; skip_to s x r; r)
Fact (skip 'foobar' \o == 'fbar')

map_to s:S f:C?C = (x = char s; x & (set s x.f; map_to s+1 f))

map s:S f:C?C : S = (r = dup s; map_to r f; r) 
Fact (map 'foo' C.upper == 'FOO')

_char x:C y:C a:C : C = a == x & y | a

map_char s:S x:C y:C : S = map s (_char x y)                                    # swap subst replace
Fact (map_char 'foo' \o \r == 'frr')
Fact (map_char "foo\.bar" 0a \. == 'foo.bar')

drop s:S n:N : S = Mem.str (mem s + n) # op_add

div_to s:S n:N k:N a:C r:S : S = n <= k & (copy_size s r n; r) | (copy_size s r k; set r+k a; div_to s+k n-k k a r+k+1)

div s:S k:N a:C : S = (n = size s; r = new n+n/k; div_to s.rev n k a r; rev r)
Fact (div '1234567890' 3 \, == '1,234,567,890')

div3 s:S : S = div s 3 \_
Fact (div3 '1234567890' == '1_234_567_890')

div4 s:S : S = div s 4 \_
Fact (div4 '1234567890' == '12_3456_7890')

# is_prefix startswith
prefix s:S r:S : B = eq_limit s r r.size
Fact (prefix 'foo' 'foo')
Fact !(prefix 'bar' 'foo')
Fact !(prefix 'fo' 'foo')
Fact (prefix 'foobar' 'foo')

suffix s:S r:S : B = s.size >= r.size & eq (drop s r.size) r
Fact (prefix 'foo' 'foo')
Fact !(prefix 'bar' 'foo')
Fact !(prefix 'fo' 'foo')
Fact (prefix 'foobar' 'foo')

seq x:S : +C = Sstr x.size x

do_span f:C?0 s:S n:N i:I j:I =
  l = key n i
  m = key n j
  do f s+l m-l+1
Fact (x = %0; do_span (Ref.add x) 'foobar' 6 2 -3; !x == \o + \b)

do f:C?0 s:S n:N = n & (s.char.f; do f s+1 n-1)                                 
Fact (x = %0; do (Ref.add x) 'foo' 3; !x == \f + \o + \o)

fold f:0?1?1 a:1 s:S n:N : 1 = (x = f (char s+(n-1)) a; n > 1 & fold f x s n-1 | x)
Fact (fold List.main 0 'foo' 3 == [\f, \o, \o])

sum f:1?0?1 a:1 s:S n:N : 1 = n & sum f (f a (char s)) s+1 n-1 | a
Fact (sum N.add 0 'foo' 3 == \f + \o + \o)

sum_opt f:1?C?!1 a:1 s:S opt:1?!1 must:!1?1 : !1 = char s & (x = f a s.char : !1; x & sum_opt f x.must s+1 opt must) | a.opt
Fact (sum_opt (_ a:N x:C : !N = x != \b & N.add a x . N.opt) 0 'foo' N.opt N.must == N.opt \f+\o+\o)
Fact (sum_opt (_ a:N x:C : !N = x != \b & N.add a x . N.opt) 0 'foobar' N.opt N.must == 0)

pump s:S : Z? !C =
  r = %s
  (_ r_:%S _:Z : !C = (x = char !r_; x & (Ref.addc r_; C.opt x))) r
Fact (x = pump 'foo'; 0.x == N.opt \f & x 0 == N.opt \o & x 0 == N.opt \o) 

pop s:S : !(C, S) = (x = char s; x & x, s + 1)
Fact (pop '' == 0)
Fact (pop 'foo' == \f,'oo')

lib_printf = 'printf'.Dl : Z? Z

printf_format = "foo bar\." : S

printf f:0 x:S = Asm
  # mov di S.printf_format 
  mov di sp 8
  mov r11 sp 16
  mov bp sp
  and sp 0ffff_fff0
  mov a 0                                                                       # no parameters in xmms 
  #call S.lib_printf
  call r11
  mov sp bp
  ret
# Fact (printf lib_printf printf_format; 1)

lib_sprintf = 'sprintf'.Dl : Z? Z

sprintf1_raw f:0 out:S format:S x:1 = Asm
  mov r11 sp 32  
  mov di sp 24
  mov si sp 16
  mov d sp 8
  mov bp sp
  and sp 0ffff_fff0
  call r11
  mov sp bp
  ret

sprintf _ : S = (x = new 8; sprintf1_raw lib_sprintf x '%03d' 42; x)
Fact (sprintf 0 == '042')

gt r:S s:S : B = Mem.gt r.mem s.mem

cut_exp neg:B s:S : neg:B, exp:B, end:S = s.char .
  \+? cut_exp 0 s+1
  \-? cut_exp 1 s+1
  \.?
    r = cut_by s+1 C.is_dec
    (r == s + 1 & (x = char r; C.is_letter x | x == \(  | x == \[)) & neg,0,s | neg,1,r
  x & C.is_dec x? cut_exp neg s+1
  ? 0, 0, s
Fact (x = '3.f'; cut_exp 0 x == 0,0,x+1)
Fact (x = '3.(f x)'; cut_exp 0 x == 0,0,x+1)
Fact (x = '3.f^4'; cut_exp 0 x == 0,0,x+1)
Fact (x = '3.+4.'; cut_exp 0 x == 0,1,x+2)
Fact (x = '3. + x'; cut_exp 0 x == 0,1,x+2)
Fact (x = '3.14'; cut_exp 0 x == 0,1,x+4)

Fact (x = '-3.f'; cut_exp 0 x == 1,0,x+2)
Fact (x = '-3.f^4'; cut_exp 0 x == 1,0,x+2)
Fact (x = '-3.+4.'; cut_exp 0 x == 1,1,x+3)
Fact (x = '-3. + x'; cut_exp 0 x == 1,1,x+3)
Fact (x = '-3.14'; cut_exp 0 x == 1,1,x+5)
  
cut_num s:S : real:B, end:S = s.char .
  \.?
    r = cut_by s+1 C.is_dec
    | (r == s + 1 & (x = char r; C.is_letter x | x == \(  | x == \[)) & 0, s
    | char r+1 == \. & C.is_dec r.char &
      neg, exp, t = cut_exp 0 r+2
      1, r
    | 1, r
  x & C.is_dec x? cut_num s+1 
  ? 0, s    
Fact (x = '42foo'; cut_num x == 0,x+2)
Fact (x = '42.foo'; cut_num x == 0,x+2)
Fact (x = '42. foo'; cut_num x == 1,x+3)
Fact (x = '42.3foo'; cut_num x == 1,x+4)
Fact (x = '42.'; cut_num x == 1,x+3)

Fact (x = '3.f'; cut_num x == 0,x+1)
Fact (x = '3.(f x)'; cut_num x == 0,x+1)
Fact (x = '3.f^4'; cut_num x == 0,x+1)
Fact (x = '3.+4.'; cut_num x == 1,x+2)
Fact (x = '3. + x'; cut_num x == 1,x+2)
Fact (x = '3.14'; cut_num x == 1,x+4)

of_hex_to s:S r:S =
  x = char s
  y = char s+1
  x & y & (set r (16*x.C.hex + y.C.hex); of_hex_to s+2 r+1)

of_hex s:S : S = (r = new s.size/2; of_hex_to s r; r)
Fact (of_hex '63616665' == 'cafe')

of_mem s:Mem n:N : S = (r = new n; Mem.copy s r.mem n; r)
Fact (x = 'foobar'; of_mem x.mem 3 == 'foo' & x == 'foobar')

# https://developer.apple.com/library/mac/documentation/Darwin/Reference/ManPages/man3/strcpy.3.html
lib_strcmp = 'strcmp'.Dl : S? S? N
lib_strncmp = 'strncmp'.Dl : S? S? N? N
lib_strlen = 'strlen'.Dl : S? N
lib_strcpy = 'strcpy'.Dl : S? S? N
lib_strncpy = 'strncpy'.Dl : S? S? N? N
lib_strcat = 'strcat'.Dl : S? S? N
lib_strtoul = 'strtoul'.Dl : S? N? N? N
lib_strchr = 'strchr'.Dl : S? C? S
lib_strrchr = 'strrchr'.Dl : S? C? S
lib_strtok = 'strtok'.Dl : S? S? S
lib_strstr = 'strstr'.Dl : S? S? S

str s:S : S = s # Fun.id
