# signal, interrupt, fault

  https://en.wikipedia.org/wiki/Trap_(computing)

bit_not = Env.bit 'Trap_no' : B 

bit = !bit_not : B

was_bit = $trap : B

do_stack sp:N =
  # N.for2, not N.for, since Fun.new* takes only 32-bit integers (not 64-bit)
  N.for2 50 (_ x:N i:N = Call.main (Mem.base x i*8)) sp # fixme - Call tag vs Call.main

# void handler(int, siginfo_t *info, ucontext_t *uap);
do kind:N info:N context:N =
  # 48 = _STRUCT_MCONTEXT        *uc_mcontext
  # 9 = 2 = _STRUCT_X86_EXCEPTION_STATE64	__es, 7 = rsp in _STRUCT_X86_THREAD_STATE64	__ss
  Log.fill '$s signal $n' [$Fun, kind]
  do_stack (Mem.base2 context 48 9*8)
  Sys.exit 1

# void    (*__sa_sigaction)(int, struct __siginfo *, void *);
do_raw kind:N = Asm                                                             # callback with c-calling convention
  push b; push bp; push r12; push r13; push r14; push r15                       # callee-saved registers (only rbx is needed to be restored here?)
  push 0
  push di
  push si
  push d
  call Trap.do
  add sp 32
  pop r15; pop r14; pop r13; pop r12; pop bp; pop b
  ret

sigsegv = 11                                                                    # SIGSEGV - Segmentation fault: 11

sigusr1 = 30

main _ = bit & Posix.sigaction sigsegv do_raw . Z

#
  Trap.do signal 11
  s.m:103.18:	S.size	Fun.call1
  trap.m:30.19:	Trap.f77	S.size
  trap.m:30.10:	Fact.check	Job.err
Fact (bit & Regex "Trap.do signal 11\.s.m:\\d\\+.\\d\\+:	S.size	Fun.call1\.trap.m:\\d\\+.\\d\\+:	Trap.f\\d\\+	S.size\.trap.m:\\d\\+.\\d\\+:	Fact.check	Job.err\." (Job.err (? S.size 0 . Z)))

# http://man7.org/linux/man-pages/man2/sigaltstack.2.html stack overflow
over _ = 0.over

