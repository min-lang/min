# reference, mutable

  https://en.wikipedia.org/wiki/Reference_type
  https://wiki.haskell.org/Mutable_variable
  https://en.wikipedia.org/wiki/Const_(computer_programming)
  http://en.wikipedia.org/wiki/Assignment_%28computer_science%29#Notation

main x:0 : %0 = (y = Mem 8; Mem.set y x; Cast.any y)

cast x:0 : %1 = Cast.any x

mem x:%0 : Mem = Cast.any x

nat x:%0 : N = Cast.any x

get x:%0 : 0 = Mem.get x.mem . Cast.any
Fact (get (main 42) == 42)
Fact (! main 42 == 42)

set x:%0 a:0 = Mem.set x.mem a
Fact (x = main 13; set x 42; x.get == 42)

tickz x:%N = set x x.get+1

tick x:%N : N = (set x x.get+1; x.get)
Fact (x = main 13; tick x == 14 & x.get == 14)

tick0 x:%N : N = (y = x.get; set x y+1; y)
Fact (x = main 13; tick0 x == 13 & x.get == 14)

diff s:%N y:N : N = (x = s.get; set s y; y - x)
Fact (x = main 3; diff x 5 == 2 & get x == 5)

sub s:%N x:N = set s s.get-x
Fact (x = main 5; sub x 2; x.get == 3)

add s:%N x:N = set s s.get+x
Fact (x = main 3; add x 5; x.get == 8)

add1 s:%N = set s s.get+1
Fact (x = main 3; add1 x; x.get == 4)

addc s:%S = set s s.get+1
Fact (x = main 'foo'; addc x; x.get == 'oo')

seq_add s:%*0 x:0 = set s x,s.get
Fact (x = main [3, 5]; seq_add x 2; x.get == [2, 3, 5])


#
  https://en.wikipedia.org/wiki/Compare-and-swap
  !x == old & (x new; x) | !x
swap x:%0 old:0 new:0 : 0 = Asm         # cmpxchg
  mov c sp 24
  mov a sp 16                           # old
  mov di sp 8                           # new
  0f0                                   # lock
  cmpxchg c 0 di                        # cmpxchg x new
  mov sp 32 a
  ret
Fact (x = %13; swap x 13 42 == 13 & !x == 42)
Fact (x = %21; swap x 13 42 == 21 & !x == 21)

#
  https://gcc.gnu.org/onlinedocs/gcc-4.2.1/gcc/Atomic-Builtins.html
    bool __sync_bool_compare_and_swap (type *ptr, type oldval type newval, ...)
swap0 x:%0 old:0 new:0 : B = Asm # cmpxchg, swap0 x:%0 old:0 new:0 : B = !x == old & (x new; 1) | 0
  mov c sp 24
  mov a sp 16                                                                   # old
  mov di sp 8                                                                   # new
  0f0                                                                           # lock
  cmpxchg c 0 di                                                                # cmpxchg x new
  mov a 0                                                                       # [set] sets/clears only the lower 8-bit
  set e a
  mov sp 32 a
  ret
Fact (x = %13; swap0 x 13 42 & !x == 42)
Fact (x = %21; swap0 x 13 42 . B.not & !x == 21)

# parallel add by 1
padd1 s:%N = (swap0 s !s !s+1 | padd1 s)                                      # no need to [r = !s]
Fact (s = %1; padd1 s; !s == 2)
Fact (s = %0; f = (_ _:N = N.for 10_000 (_ _:N = padd1 s)); f 0; f 0; !s == 20_000) # serial run 
Fact (s = %0; f = (_ _:N = N.for 10_000 (_ _:N = padd1 s)); Thread.two f f; 1) # fixme - Mem.make too small in Thread.two - Bus error: 10

# https://en.wikipedia.org/wiki/Fetch-and-add
# parallel add 
padd s:%N x:N = (swap0 s !s !s+x | padd s x)                                      # no need to [r = !s]
Fact (s = %1; padd s 2; !s == 3)
Fact (s = %0; f = (_ _:N = N.for 10_000 (_ _:N = padd s 2)); f 0; f 0; !s == 40_000) # serial run
Fact (s = %0; f = (_ _:N = N.for 10_000 (_ _:N = padd s 2)); Thread.two f f; !s == 40_000)

#
  http://www.ibm.com/developerworks/aix/library/au-multithreaded_structures2/
  https://www.kernel.org/doc/Documentation/trace/ring-buffer-design.txt
  http://www.hpl.hp.com/techreports/2004/HPL-2004-105.pdf
ppair x:0 s:%*0 = ! swap0 s !s x,!s & ppair x s
Fact (s = %[13]; ppair 42 s; !s == [42, 13])
Fact (s = %[]; N.for 10 (_ i:N = ppair i s); !s == [9, 8, 7, 6, 5, 4, 3, 2, 1, 0])

Fact
  s = %[]
  f = (_ _:N = (N.for 10000 ((_ s:%*N i:N = (Sys.cpuid 0; ppair i s)) s))) # Sys.cpuid for slowing to yield
  Thread.two_ready f f
  !s != List.add 10000.List.nat 10000.List.nat # should interleave, if start at the same time and scheduling is fair

pop opt:0?!0 s:%*0 : !0 = (u = !s; u . (x,r? (swap0 s u r & opt x | pop opt s)))
Fact (s = %[13]; pop N.opt s == N.opt 13 & pop N.opt s == 0)
Fact
  r = 10000.List.nat
  s = %r; r1 = %[]; r2 = %[]
  # s = %r; r1 = %[] : %*N; r2 = %[] : %*N
  f = (_ s:%*N r:%*N _:N = (N.for 10000 ((_ s:%*N r:%*N _:N = (Sys.cpuid 0; x = pop N.opt s; x & r x.N.must,!r)) s r))) # cpuid to slow down for fair scheduling
  Thread.two_ready (f s r1) (f s r2)
  List.bit !r1 & List.bit !r2 & List.sole_by N.eq !r1 & List.sole_by N.eq !r2 & List.fuse !r1 !r2 == r.List.rev # in very rare (1/100k), scheduler may block one core, and this test fails

do f:0?_ s:%*0 opt:0?!0 must:!0?0 = (x = pop opt s; x & (f x.must; do f s opt must))
Fact (s = %[2, 3]; r = %0; do (padd r) s N.opt N.must; !r == 5)

lock x:%B = Asm                         # use pause/cpuid with jmp in assembly
  mov r8 sp 8                           # cpuid overwrites a b c d 
  mov a 0                               # old
  mov di 1                              # new
  @Ref.lock_0                           
  0f0                                   # lock
  cmpxchg r8 0 di                       # cmpxchg x new
  j e Ref.lock_1                        
  mov a 0                               #  cmpxchg overwrites rax
  pause
  j Ref.lock_0
  @Ref.lock_1
  ret
Fact (x = %0; lock x; !x)

open x:%B = x 0
Fact (x = %0; lock x; open x; !(!x))
