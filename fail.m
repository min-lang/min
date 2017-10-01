# fatal exit, abort, exception, error

 http://en.wikipedia.org/wiki/Exception_handling
 https://github.com/noether-lang/noether/raw/master/doc/presentations/StrangeLoop2014/handling.pdf How to Make Error Handling Less Error-Prone

exit_skip = %0 : %B

exit_nat = %0 : %N

_exit _ : 0 = Sys.exit 1

main x:S : 0 = (main0 x; Err.char 0a; _exit 0)

nil _ : 0 = _exit 0

main0 x:S = (Err x; Err ': error ')

main2 x:S y:S : 0 = (main0 x; C.err \ ; Err y; Err.char 0a; _exit 0)

force2 x:S y:S : 0 = (main0 x; C.err \ ; Err y; Err.char 0a; Sys.exit 1)

main3 x:S y:S z:S : 0 = (main0 x; C.err \ ; Err y; C.err \ ; Log z; _exit 0)

main4 x:S y:S z:S w:S : 0 = (main0 x; C.err \ ; Err y; C.err \ ; Err z; C.err \ ; Log w; _exit 0)

main5 x:S y:S z:S w:S u:S : 0 = (main0 x; C.err \ ; Err y; C.err \ ; Err z; C.err \ ; Err w; C.err \ ; Log u; _exit 0)

fill x:S s:*Any : 0 = (Log.fill x s; _exit 0)
