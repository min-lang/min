# portable operating system interface

  https://en.wikipedia.org/wiki/POSIX

# pid_t fork(void);
lib_fork = Dl 'fork' : Z? pid:N

# int pipe(int fildes[2]);
lib_pipe = Dl 'pipe' : files:Mem? N

lib_sysconf = Dl 'sysconf' : name:N? N

# fork _ : N = Fun.call0 lib_fork
fork _ : N = (!Job.multi; Fun.call0 lib_fork)

pipe ids:N,N : N =
  s = Mem 16
  Fun.call1 lib_pipe s . Hex.log
  #N.log !(!(s.Any.cast + 32).Any.cast)
  0

# #define	_SC_NPROCESSORS_ONLN		58
cores _ : N = Fun.call1 lib_sysconf 58

# https://developer.apple.com/library/mac/documentation/Darwin/Reference/ManPages/man3/sleep.3.html
#   unsigned int sleep(unsigned int seconds);
sleep seconds:N = Fun.call1 'sleep'.Dl seconds

# http://linux.die.net/man/3/usleep 1.0.-6
usleep seconds:N = Fun.call1 'usleep'.Dl seconds # [0,1000000]

# http://linux.die.net/man/2/nanosleep
nanosleep seconds:N = Fun.call1 'nanosleep'.Dl seconds

sigaction kind:N do:N?Z : N =                                                   # [do] must use c-calling convention
  #s = do, 0, 0
  sa_siginfo = 040
  s = do, sa_siginfo, 0 # __sigaction_u, sa_flags, sa_mask
  Fun.call3 'sigaction'.Dl kind s 0

# https://developer.apple.com/library/ios/documentation/System/Conceptual/ManPages_iPhoneOS/man2/wait.2.html
wait _ = Fun.call1 'wait'.Dl 0
