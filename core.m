# cpu, multi processor, hyperthread

  https://en.wikipedia.org/wiki/Multi-core_processor
  https://en.wikipedia.org/wiki/Hyper-threading  
  https://en.wikipedia.org/wiki/Fork%E2%80%93join_model
    
size _ : N = !Posix.cores

do _ =
  !Posix.cores . N.log
  0

set_affinity i:N =
  thread = Fun.call0 'mach_thread_self'.Dl
  Fun.call4 'thread_policy_set'.Dl thread 4 %i 1 

affinity _ : N =
  thread = Thread.self 0
  get_default = %0
  policy = %2
  count = %1
  Fun.call5 'thread_policy_get'.Dl thread 4 policy count get_default 
  !policy
