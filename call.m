# call stacks, stack trace

  https://en.wikipedia.org/wiki/Stack_trace

rows = %0 : %*(N,S)

row_size = 96

name_size = row_size - 1 - 8 : N

add spot:Spot mem:N fun:S call:S =
  # todo - string pool, strings of variable length
  Trap.bit & Ref.seq_add Call.rows (mem, S.fill '$s:$,$s$,$s' [spot.Spot.str1, fun, call])

if mem:N base:0 : B =
  n = Mem.base base 0
  # todo - print non-call addresses as local variables on stack
  mem == n &
    Log.main (Mem.str (base + 8).Mem.of)
    1
  
main mem:N =
  n = !Sys.call_size
  N.any (_ i:N : B = if mem (!Sys.call_head + i*Call.row_size)) n . Z

add_flow_at flow:Flow base,call:N,S =
  Flow.nat3 flow base
  Flow.str_size_nil flow call name_size

add_flow flow:Flow = Trap.bit & List.do !rows (add_flow_at flow)
