# file 1, standard output

  https://en.wikipedia.org/wiki/Standard_streams#Standard_output_.28stdout.29

size x:S n:N = Sys.write 1 x n . Z.main

char x:C = (Sys.write0 1 x . Z.main)

main x:S = size x !x
