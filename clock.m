# timer, frequency tick

  https://en.wikipedia.org/wiki/Time_Stamp_Counter

rdtsc _ : N = Asm
  rdtsc # edx:eax
  shl d 32
  or a d  
  mov sp 16 a
  ret

lib_clock = Dl 'clock' : Z? N

last = %0 : %N

main _ : N = Fun.call0 lib_clock

tick _ : N = Ref.diff last 0.main / 1000

sub x:%N = Ref.sub x 0.rdtsc

add x:%N = Ref.add x 0.rdtsc
