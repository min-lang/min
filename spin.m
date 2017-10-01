# concurrency synchronization lock
  
  https://en.wikipedia.org/wiki/Spinlock

main x:%!0 = Asm
  mov a sp 8
  @Spin.main_0
  pause                                                                         # yield
  cmp a 0 0
  j e Spin.main_0
  ret
