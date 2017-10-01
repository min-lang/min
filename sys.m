# system call, kernel call

# http://www.opensource.apple.com/source/xnu/xnu-2782.20.48/bsd/kern/syscalls.master
#   user - rdi, rsi, rdx, rcx, r8 and r9
#   sys  - rdi, rsi, rdx, r10, r8 and r9
#   returns - rax, rdx
call g:N a:N b:N c:N d:N e:N f:N : N = Asm
  mov a sp 56
  add a 02000000
  mov di sp 48
  mov si sp 40
  mov d sp 32
  mov r10 sp 24
  mov r8 sp 16
  mov r9 sp 8
  syscall
  j ge Sys.call0
  neg a
  @Sys.call0
  mov sp 64 a
  ret

# return a pair, first component is negative if any error
# call2 g:N a:N b:N c:N d:N e:N f:N : N, N = Asm
call2 g:N a:N b:N c:N d:N e:N f:N : N = Asm
  mov a sp 56
  add a 02000000
  mov di sp 48
  mov si sp 40
  mov d sp 32
  mov r10 sp 24
  mov r8 sp 16
  mov r9 sp 8
  syscall
  j ge Sys.call2_0
  neg a
  @Sys.call2_0

  mov r11 16
  call Mem.main_reg
  mov sp 64 r11
  mov r11 0 a
  mov r11 8 d
  ret

write file:N x:S size:N : N = Asm
  mov a 02000004
  mov di sp 24                                                                 # output file
  mov si sp 16                                                                 # buffer address
  mov d sp 8                                                                   # buffer size
  syscall
  mov sp 32 a                                                                  # bytes written
  ret

write0 file:N x:C : N = Asm
  mov a 02000004
  mov di sp 16                                                                 # output file
  lea si sp 8                                                                  # buffer address 
  mov d 1                                                                       # buffer size
  syscall
  mov sp 24 a                                                                  # bytes written
  ret

exit x:N : 0 = Asm
  mov a 02000001
  mov di sp 8
  syscall

read file:N x:S size:N : N = Asm
  mov a 02000003
  mov di sp 24                                                                 # input file
  mov si sp 16                                                                 # buffer address
  mov d sp 8                                                                   # buffer size
  syscall
  mov sp 32 a                                                                  # bytes written
  ret

stat path:S : N =
  s = Mem 144
  callx 190 path.S.nat s.Mem.nat 0 0 0 0 # lstat, stat = 188
  (s + 72).Mem.get

fstat file:File : N =
  s = Mem 144
  callx 189 file.File.to s.Mem.nat 0 0 0 0
  (s + 72).Mem.get

fork _ : N = callx 2 0 0 0 0 0 0
vfork _ : N = callx 66 0 0 0 0 0 0

callx g:N a:N b:N c:N d:N e:N f:N : N =
  x = call g a b c d e f
  I.lt x 0 & Fail.main2 (-x).error (-x).N.str | x

callx2 g:N a:N b:N c:N d:N e:N f:N : N, N =
  x = call2 g a b c d e f
  I.lt x 0 & Fail.main2 (-x).error (-x).N.str | Mem.get x.Cast.mem, Mem.get (x+8).Cast.mem

# 7	AUE_WAIT4	ALL	{ int wait4(int pid, user_addr_t status, int options, user_addr_t rusage) NO_SYSCALL_STUB; } 
# wait pid:N : N = callx 84 pid 0 0 0 0 0 # Bad system call: 12

# 20	AUE_GETPID	ALL	{ int getpid(void); }
getpid _ : N = callx 20 0 0 0 0 0 0

# char * strerror(int errnum);
lib_errno = Dl 'errno' . Cast.any : %N

lib_strerror = Dl 'strerror' : error:N? S

error x:N : S = Fun.call1 lib_strerror x

# int pipe(int fildes[2]);
pipe _ : N, N = callx2 42 0 0 0 0 0 0  # __pipe.s returns multiple arguments - %eax, %edx

dup2 old:N new:N : N = callx 90 old new 0 0 0 0  # __pipe.s returns multiple arguments - %eax, %edx

# int setitimer(int which, const struct itimerval *restrict value, struct itimerval *restrict ovalue); 
sigaction kind:N do:N?Z : N =           # NO_SYSCALL_STUB, probably changed params. use Posix for now
  s = do, 0, 0
  callx 46 kind s.Cast.nat 0 0 0 0 # kill -11 `pgrep min`

# updated by Asm.steps_binary_out, used by Call.main
call_head _ : N = Asm
  mov a Call_head
  mov sp 16 a
  ret

# updated by Asm.steps_binary_out, used by Call.main
call_size _ : N = Asm
  mov a Call_size
  mov sp 16 a
  ret

# see Thread.m
# 360	AUE_NULL	ALL	{ user_addr_t bsdthread_create(user_addr_t func, user_addr_t func_arg, user_addr_t stack, user_addr_t pthread, uint32_t flags) NO_SYSCALL_STUB; }
# [fun] must use c-calling convention
bsdthread_create fun:0?1 x:0 : N = callx 360 fun.Cast.any x (Mem 10_000_000).Mem.nat 0 0 0 # 10MB stack

#361	AUE_NULL	ALL	{ int bsdthread_terminate(user_addr_t stackaddr, size_t freesize, uint32_t port, uint32_t sem) NO_SYSCALL_STUB; }
bsdthread_terminate _ : N = callx 361 0 0 0 0 0 0

cpuid _ = Asm # serializing, flush pipeline, ~200 cycles http://www.agner.org/optimize/instruction_tables.pdf
  cpuid
  ret

mfence _ = Asm
  0f 0ae 0f0
  ret

pause _ = Asm
  pause
  ret

di _ : N = Asm                          # hack! first parameter for callback with c-calling convention, for Thread.create
  mov sp 16 di
  ret

set_di x:N = Asm                        # for Thread.create0
  mov di sp 8
  ret
