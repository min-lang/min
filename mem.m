# memory address, pointer
  
get s:Mem : N = Asm # inlined in Step.exp_steps
  mov a sp 8
  mov c a 0
  mov sp 16 c
  ret

get0 s:Mem : C = Asm
  mov a sp 8
  mov c 0
  0 mov c a 0
  mov sp 16 c
  ret

set s:Mem x:0 = Asm
  mov a sp 16
  mov c sp 8
  mov a 0 c
  mov sp 24 0
  ret

set0 s:Mem x:C = Asm
  mov a sp 16
  mov c sp 8
  0 mov a 0 c
  mov sp 24 0
  ret
Fact (eq (x = 'bafe'.of; set0 x \c; x) 'cafe'.of 4)

# https://en.wikipedia.org/wiki/C_dynamic_memory_allocation
main size:N : Mem = Asm
  mov r11 sp 8
  call Mem.main_reg # todo - thread local memory pages to avoid contention in xadd
  mov sp 16 r11
  ret

_main_hack _ : N =  1 + 1 # hack! align for main_reg below

# use [r10], arg/ret = [r11]
  todo - thread-local pages for memory allocation without lock  
  fixme - random 100x slower when lock on unaligned. currently, put unused instructions in _main_hack above to force align

  http://www.agner.org/optimize/instruction_tables.pdf  
    Instructions with a LOCK prefix have a long latency that depends on cache organization and possibly RAM speed. If there
    are multiple processors or cores or direct memory access (DMA) devices then all locked instructions will lock a cache
    line for exclusive access, which may involve RAM access. A LOCK prefix typically costs more than a hundred clock cycles,
    even on single-processor systems. This also applies to the XCHG instruction with a memory operand.
main_reg size:N : Mem = Asm 
  mov r10 Data_vmend
  cmp r10 8 0 # see main.ma for Job.multi
  j ne Mem.main_reg_1  
  0'4d0fc11a' # xadd r10 0 r11, 20% faster
  ret

  @Mem.main_reg_1
  0'f04d0fc11a' # lock; xadd r10 0 r11
  ret

main2 size:N : Mem = _

nat s:Mem : N = Cast.mem_nat s

id r:Mem s:Mem : B = nat r == nat s

# https://developer.apple.com/library/mac/documentation/Darwin/Reference/ManPages/man3/memcmp.3.html
# int memcmp(const void *s1, const void *s2, size_t n);
lib_memcmp = Dl 'memcmp' : Mem? Mem? size:N? N
eq r:Mem s:Mem n:N : B = Fun.call3 lib_memcmp r s n == 0

of x:0 : Mem = Cast.mem x

at s:Mem : Mem = s.get.of

off s:Mem index:N : Mem = Mem.of (s + index) # todo - rename to add?
Fact (s = 13,42 . of; off s 8 . get == 42)

# https://developer.apple.com/library/mac/documentation/Darwin/Reference/ManPages/man3/memcpy.3.html
#   void * memcpy(void *restrict dst, const void *restrict src, size_t n); 
lib_memcpy = Dl 'memcpy' : to:Mem? from:Mem? size:N? dst:Mem
copy r:Mem s:Mem n:N = (Fun.call3 lib_memcpy s r n; 0)

rev x:Mem y:Mem n:N = n & (set0 y (get0 x+n-1); rev x y+1 n-1)

copy0 r:Mem s:Mem n:N = n & (set0 s (get0 r); copy r+1 s+1 n-1)                        # from r to s. return 0

dup s:Mem n:N : Mem = (r = n.main; copy s r n; r)

span r:Mem s:Mem : Mem = dup r s-r

add x:Mem n:N = set x x.get+n

set1x s:Mem x:N = Asm
  mov a sp 16
  mov c sp 8
  1 mov a 0 c
  mov sp 24 0
  ret

set1 s:Mem x:N = (set0 s x.N.char; set0 s+1 (N.shr x 8).N.char)
Fact (eq (x = '--fe'.of; set1 x (N.of1 \a \c); x) 'cafe'.of 4) 

# network order
net_set1 s:Mem x:N = (set0 s+1 x.N.char; set0 s (N.shr x 8).N.char)

set2x s:Mem x:N = Asm
  mov a sp 16
  mov c sp 8
  2 mov a 0 c
  mov sp 24 0
  ret

set2 s:Mem x:N = (set1 s x; set1 s+2 (N.shr x 16))
Fact (eq (x = '----babe'.of; set2 x (N.of2 \e \f \a \c); x) 'cafebabe'.of 8)

set3 s:Mem x:N = (set2 s x; set2 s+4 (N.shr x 32))
Fact (eq (x = '--------deadbeef'.of; set3 x (N.of3 \e \b \a \b \e \f \a \c); x) 'cafebabedeadbeef'.of 16)

set_rank s:Mem x:N : N?Z = 
  0? set0 s x.N.char
  1? set1 s x
  2? set2 s x
  3? set3 s x

str x:Mem : S = Cast.mem_str x

log x:0 = x.Hex.str.Log

put x:0 = x.Hex.str.Put

line0 s:Mem i:N size:N = (Hex.n0_out (Mem.off s i).get0.C.nat; i % 2 == 1 & i != size - 1 & C.out \ )

do s:Mem index:N size:N f:0?N?N?Z = index < size & (f s index size; do s index+1 size f) # per 1 byte

line s:Mem size:N = (do s 0 size line0; C.out 0a)

next s:Mem size:N : Mem = s + size

hex0 r:S s:Mem i:N =
  x = get s+i
  S.set (r + 2*i) (x / 16).Hex.char
  S.set (r + 2*i + 1) (x % 16).Hex.char

hex s:Mem n:N : S =
  r = S.new 2*n
  N.for n (hex0 r s)
  r
Fact (hex 'cafe'.of 4 == '63616665')

seq s:Mem : *0 = (x = at s; x & Cast.any x, seq (s + 8)) # must be null-terminated
Fact (13,42,0 . of . seq == [13, 42])
Fact (Row.of [13,42,0] . of . seq == [13, 42])
Fact (3,13,42,0 . of . seq == [3, 13, 42])

base s:0 n:N : 1 = get (s + n).of . Cast.any

base2 s:0 m:N n:N : 1 = base (base s m) n

base3 s:0 m:N n:N p:N : 1 = base (base (base s m) n) p

gt r:Mem s:Mem : B = r.nat > s.nat
 
of_hex_to s:S n:N r:Mem : N =
  x = S.char s
  | C.is_hex x &  
    y = S.char s+1
    | y &
      set0 r (16*x.C.hex + y.C.hex)
      of_hex_to s+2 n+1 r+1
    | n
  | x & of_hex_to s+1 n r | n
  
of_hex s:S : N, Mem = (r = Mem s.S.size/2; of_hex_to s 0 r, r)
Fact (n, x = of_hex '63616665'; n == 4 & get0 x == 063 & get0 x+1 == 061 & get0 x+2 == 066 & get0 x+3 == 065)
Fact (n, x = of_hex '63.61 66.65'; n == 4 & get0 x == 063 & get0 x+1 == 061 & get0 x+2 == 066 & get0 x+3 == 065)
