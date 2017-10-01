# file 1, standard output, with newline

main x:S = (Out x; Out.char 0a)

main2 x:S y:S = (Out x; Out.char \ ; Out y; Out.char 0a)

# no library call, for debugging Dl or $Pre in Main
pure x:S = (Out.size x x.S.size_pure; Out.char 0a . Z)

nat_pure x:N = x.N.str_pure.pure

id x:S : S = (main x; x)

fill x:S s:*Any = main (S.fill x s)
