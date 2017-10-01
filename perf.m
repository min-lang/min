# performance, profile, monitor

  https://en.wikipedia.org/wiki/Profiling_(computer_programming)
      
names = %0 : %Exps

call = Env.bit 'perf_call' : B

tick = Env.bit 'perf_tick' : B

main _ =
  List.do $Perf (_ x,t,n:S,%N,%N = (Trace.main_space x; Trace.main_space (!t).N.str; Trace.main_hex !t; Trace (!n).N.str)) # see Perf.names in Step.exp_steps
  0
