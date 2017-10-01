# file 2, standard error, with newline

main x:S = (Err x; Err.char 0a)

main2 x:S y:S = (Err x; Err.char \ ; Err y; Err.char 0a)

main3 x:S y:S z:S = (Err x; Err.char \ ; Err y; Err.char \ ; Err z; Err.char 0a)

main4 x:S y:S z:S w:S = (Err x; Err.char \ ; Err y; Err.char \ ; Err z; Err.char \ ; Err w; Err.char 0a)

fill x:S s:*Any = main (S.fill x s)

id x:S : S = (main x; x)

# no library call, for debugging Dl or $Pre in Main
pure x:S = (Err.size x x.S.size_pure; Err.char 0a)

nat_pure x:N = x.N.str_pure.pure
