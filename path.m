# file path, file name

# http://man7.org/linux/man-pages/man2/open.2.html
in x:S : File = Sys.callx 5 x.S.mem.Mem.nat 0 0 0 0 0 . File.of
  
main x:S : S = x.in.File.in
