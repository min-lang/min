# compression via gzip

  https://en.wikipedia.org/wiki/Zlib

uncompress x:S n:N : S =
  z = S.new 10240
  m = Ref 10240
  Fun.call4 'uncompress'.Dl z m x n
  z

_ = Dl.open '/System/Library/Frameworks/Security.framework/Versions/A/Security' : N # contains Zlib.compress
main x:S : S =
  y = S.new 1024
  m = Ref 1024
  Fun.call4 'compress'.Dl y m x x.S.size

  z = S.new 1024
  n = Ref 1024  
  Fun.call4 'uncompress'.Dl z n y m.Ref.get
  z
Fact (main 'hello' == 'hello')
