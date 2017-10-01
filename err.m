# file 2, standard error

size x:S n:N = Sys.write 2 x n . Z

char x:C = (Sys.write0 2 x . Z)

main x:S = size x !x

main2 x:S = (main x; char \ )

tee x:S : S = (Log x; x)
