# system-mode parallelism

  https://en.wikipedia.org/wiki/Thread_(computing)

self _ = Fun.call0 'mach_thread_self'.Dl

# https://developer.apple.com/library/mac/documentation/Darwin/Reference/ManPages/man3/pthread_exit.3.html#//apple_ref/doc/man/3/pthread_exit
exit _ = Fun.call1 Dl'pthread_exit' 0

# int pthread_create(pthread_t *thread, const pthread_attr_t *attr, void *(*start_routine)(void *), void *arg)
lib_create = Dl'pthread_create' : %N? Z? N?_? N? Z

create f:N?_ x:N : N = (!Job.multi; y = %0; Fun.call4 lib_create y 0 f x; !y)

create0 f:N?_ x:N : N = (Sys.set_di x; f 0)

join x:N = Fun.call2 Dl'pthread_join' x 0

lock = %0 : %B

# todo - pass [n] to the new process without [Sys.di]
test n:N = all (_ x:N = (y = 0.Sys.di; Ref.lock Thread.lock; Put y.N.str; Posix.usleep 100.N.pick; Ref.open Thread.lock))

# wait until both threads are ready to execute code so they have the same amount of scheduled time for competiting the same resources
two_ready f:N?_ g:N?_ =
  Core.set_affinity 0
  ready = %0
  x = create ((_ ready:%N f:N?_ _:N = (Core.set_affinity 1; ready 1; f 0; exit 0)) ready f) 1
  Spin ready
  g 1
  join x

two f:N?_ g:N?_ =
  Core.set_affinity 0
  x = create ((_ f:N?_ _:N = (Core.set_affinity 1; f 0; exit 0)) f) 1 # REWRITE_FREE_VARS_FUN
  g 1
  join x

all f:N?_ =
  s = N.map 0.Core.size-1 ((_ f:N?_ i:N : N = create ((_ f:N?_ i:N = (f i; exit 0)) f) i+1) f) # REWRITE_FREE_VARS_FUN
  create0 f 0
  List.do s join 
