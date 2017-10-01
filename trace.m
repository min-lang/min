# file 5, performance time tracing

size x:S n:N = Sys.write 5 x n . Z

main0 x:C = (Sys.write0 5 x . Z)

main1 x:S = size x !x

main x:S = (main1 x; main0 0a)

main_space x:S = (main1 x; main0 \ )

main_hex x:N = main_space x.Hex.str

fill x:S s:*Any = main (S.fill x s)
