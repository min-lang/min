# user-mode thread, coroutine, fiber

  https://en.wikipedia.org/wiki/Coroutine
  https://en.wikipedia.org/wiki/Fiber_(computer_science)

fun = %0 : %!(Z?Z)
do_raw x:N = Asm                                                                # callback with c-calling convention
  push b; push bp; push r12; push r13; push r14; push r15                       # callee-saved registers (only rbx is needed to be restored here?)
  push 0
  push di
  call Task.do
  add sp 16                                                                     # pop return and first arg di
  pop r15; pop r14; pop r13; pop r12; pop bp; pop b
  ret                                                                           # or, Sys.bsdthread_terminate 0

do x:N =
  Core.set_affinity x                                                           # necessary?
  Spin fun
  f = !fun; f 0 # todo - !fun 0
  0

test _ =
  N.for 4 (Sys.bsdthread_create do_raw)                                        # [do_raw] must use c-calling convention
  Posix.usleep 10
  fun (? N.log 42)
  Posix.usleep 100
  # todo - Thread.join
