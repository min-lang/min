#
  https://en.wikipedia.org/wiki/Regular_expression#POSIX_basic_and_extended

lib_regcomp = Dl 'regcomp' : re:Mem? ex:S? flags:N? N

lib_regexec = Dl 'regexec' : re:Mem? S? size:N? match:Mem? flags:N? N

# full text
main ex:S x:S : B = search '^'+ex+'$' x
Fact (main 'fo\+bar' 'foobar')
Fact !(main 'foo' 'foobar')
Fact (main 'foo\d\d' 'foo42')
Fact (main 'foo[0-9][0-9]' 'foo42')
Fact !(main 'foo[0-9][0-9]' 'foob2')

# search match
search ex:S x:S : B =
  re = Mem 32
  Fun.call3 lib_regcomp re ex 0100 # REG_ENHANCED
  Fun.call5 lib_regexec re x 0 0.Mem.of 0 == 0
Fact (search 'foo' 'foobar')
Fact (search 'fo\+bar' 'foobarqux')
Fact (search 'foo\d\d' 'foo42bar')
