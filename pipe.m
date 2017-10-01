# unix pipeline, process input/output chain

do _ =
  r, w = Pair.map File.of 0.Sys.pipe 
  | Posix.fork 0 &
    File.in_size r 10 . Log
    0
  |
    File.out w 'foo'
  0
