# unix job, process

  https://en.wikipedia.org/wiki/Process_(computing)

add x:N : N = x > 0ffff_ffff & x | add x+1

multi _ = Asm
  mov a Data_vmend
  add a 8 1
  ret

per i:N =  
  | Posix.fork 0 & 0 
  | 
    i+1 . Core.set_affinity 
    !Core.affinity . N.log
    add 0
    !Core.affinity . N.log    
    Sys.exit 0
    0

main2 _ =  
  x = Posix.fork 0
  | x & Fail 'a'
  | Fail 'b'

out f:Z?0 : S =
  r, w = Pair.map File.of !Sys.pipe
  | Posix.fork 0 &
    Posix.wait 0
    File.in_size r 2048
  |
    File.dup2 w 1.File.of
    f 0
    Sys.exit 0

err f:Z?0 : S =
  r, w = Pair.map File.of !Sys.pipe
  | Posix.fork 0 &
    Posix.wait 0
    File.in_size r 2048
  |
    File.dup2 w 2.File.of
    f 0
    Sys.exit 1

do f:Z?Z : S, S =
  r1, w1 = Pair.map File.of !Sys.pipe 
  r2, w2 = Pair.map File.of !Sys.pipe 
  | Posix.fork 0 &
    Posix.wait 0
    x = File.in_size r1 2048
    y = File.in_size r2 2048
    x, y                                # fixme - wait for child to exit
  |
    File.dup2 w1 1.File.of
    File.dup2 w2 2.File.of
    # must write some to w1/w2, or r1/r2 above block
    Out ' '                                                                
    Err ' '
    f 0
    Sys.exit 1

test _ : S, S =
  r1, w1 = Pair.map File.of !Sys.pipe 
  r2, w2 = Pair.map File.of !Sys.pipe 
  | Posix.fork 0 &
    x = File.in_size r1 2048
    y = File.in_size r2 2048
    Put x
    Put y
    x, y
  |
    File.dup2 w1 1.File.of
    File.dup2 w2 2.File.of
    Out 'ok'
    Sys.exit 0

all = %0 : %*(Z?_)
