# function, procedure, routine

  https://en.wikipedia.org/wiki/Function_type  
  https://en.wikipedia.org/wiki/Abstraction_(computer_science)
  https://en.wikipedia.org/wiki/Parameter_(computer_programming)#Parameters_and_arguments
  
# http://x86-64.org/documentation/abi.pdf 
  p20 For calls that may call functions that use varargs or stdargs (prototype-less calls or calls to functions
  containing ellipsis (. . . ) in the declaration) %al16 is used as hidden argument to specify the number of vector
  registers used. Note that the rest of %rax is undefined, only the contents of %al is defined.  The content of %al do
  not need to match exactly the number of registers, but must be an upper bound on the number of vector registers used
  and is in the range 0-8 inclusive. [al] does not seem to have effect on, for example, printf.

call0 fun:Z?0 : 0 = Asm
  mov b sp 8
  mov bp sp
  and sp 0ffff_fff0                                                             # align stack to 16-byte, see Align
  call b  
  mov sp bp  
  mov sp 16 a
  ret

call1 fun:0?1 x:0 : 1 = Asm
  mov b sp 16
  mov di sp 8
  mov bp sp
  and sp 0ffff_fff0
  call b
  mov sp bp  
  mov sp 24 a
  ret

call_nr fun:0?R x:0 : R = Asm
  mov b sp 16
  mov di sp 8
  mov bp sp
  and sp 0ffff_fff0
  call b  
  mov sp bp
  mov a xmm0
  mov sp 24 a
  ret

call_rr fun:R?R x:R : R = Asm
  mov b sp 16
  mov a sp 8
  mov xmm0 a
  mov bp sp
  and sp 0ffff_fff0
  call b  
  mov sp bp
  mov a xmm0
  mov sp 24 a
  ret

call_rrr fun:R?R?R x:R y:R : R = Asm
  mov b sp 24
  mov a sp 16
  mov xmm0 a
  mov a sp 8
  mov xmm1 a
  mov bp sp
  and sp 0ffff_fff0
  call b  
  mov sp bp
  mov a xmm0
  mov sp 32 a
  ret

call2 fun:0?1?2 x:0 y:1 : 2 = Asm
  mov b sp 24
  mov di sp 16
  mov si sp 8
  mov bp sp
  and sp 0ffff_fff0
  call b  
  mov sp bp  
  mov sp 32 a
  ret

call3 fun:0?1?2?3 x:0 y:1 z:2 : 3 = Asm
  mov b sp 32
  mov di sp 24
  mov si sp 16
  mov d sp 8
  mov bp sp
  and sp 0ffff_fff0
  call b  
  mov sp bp  
  mov sp 40 a
  ret

# so far, only used by Dbm.fetch. run [./min2 dbm]
call3_r2 fun:0?1?2?3,4 x:0 y:1 z:2 : 3,4 = Asm
  mov b sp 32
  mov di sp 24
  mov si sp 16
  mov d sp 8
  mov bp sp
  and sp 0ffff_fff0
  call b  
  mov sp bp

  mov r11 16
  call Mem.main_reg
  mov r11 0 a
  mov r11 8 d
  mov sp 40 r11
  ret

call4 fun:0?1?2?3?4 x:0 y:1 z:2 w:3 : 4 = Asm
  mov b sp 40
  mov di sp 32
  mov si sp 24
  mov d sp 16
  mov c sp 8
  mov bp sp
  and sp 0ffff_fff0
  call b  
  mov sp bp  
  mov sp 48 a
  ret

call5 fun:0?1?2?3?4?5 x:0 y:1 z:2 w:3 v:4 : 5 = Asm
  mov b sp 48
  mov di sp 40
  mov si sp 32
  mov d sp 24
  mov c sp 16
  mov r8 sp 8
  mov bp sp
  and sp 0ffff_fff0
  call b  
  mov sp bp  
  mov sp 56 a
  ret

call6 fun:0?1?2?3?4?5?6 x:0 y:1 z:2 w:3 u:4 v:5 : 6 = Asm
  mov b sp 56
  mov di sp 48
  mov si sp 40
  mov d sp 32
  mov c sp 24
  mov r8 sp 16
  mov r9 sp 8
  mov bp sp
  and sp 0ffff_fff0
  call b  
  mov sp bp  
  mov sp 64 a
  ret

#call5x fun:0?1?2?3?4?5 x:0 y:1 z:2 w:3 v:4 u:5 : 6 = Asm
# first arg = struct CGRect 0 0 a a, which is passed in stack 
call5x a:5 fun:0?1?2?3?4?5 x:0 y:1 z:2 w:3 v:4 : 5 = Asm # a as struct, special param passing
  mov a sp 56
  mov b sp 48
  mov di sp 40
  mov si sp 32
  mov d sp 24
  mov c sp 16
  mov r8 sp 8

  mov bp sp
  and sp 0ffff_fff0
  
  push a                                # first arg = struct CGRect 0 0 a a
  push a
  push 0
  push 0

  call b  
  mov sp bp  
  mov sp 56 a
  ret

call6x fun:0?1?2?3?4?5?6 x:0 y:1 z:2 w:3 v:4 u:5 : 6 = Asm # fixme - last argument not passed in stack, see main.ma
  # same as call6
  mov b sp 56
  mov di sp 48
  mov si sp 40
  mov d sp 32
  mov c sp 24
  mov r8 sp 16
  mov r9 sp 8
  mov bp sp
  and sp 0ffff_fff0
  call b  
  mov sp bp  
  mov sp 64 a
  ret

# https://en.wikipedia.org/wiki/%CE%9C-recursive_function
mem x:0?1 : Mem = Cast.mem x

id x:0 : 0 = x

# https://en.wikipedia.org/wiki/Currying#Partial_application
# https://en.wikipedia.org/wiki/Closure_(computer_programming)
# support only 32-bit address/data, due to [push n]
# use function variable, not direct call; otherwise, wrong relative rip for call
#   0000005A  68E2120000        push qword 0x12e2
#   0000005F  6800000000        push qword 0x0
#   00000064  682A000000        push qword 0x2a
#   00000069  48FFB42420000000  push qword [rsp+0x20]
#   00000071  48FF942418000000  call qword [rsp+0x18]
#   00000079  4881C410000000    add rsp,0x10
#   00000080  4858              pop rax
#   00000082  4881C408000000    add rsp,0x8
#   00000089  4889842410000000  mov [rsp+0x10],rax
#   00000091  C3                ret
#   00000092
mold1 x:0 : 1 = (f = Any.cast_fun3 0; f 0 x)
mold1_end _:N : N = 0

# Used in Unify.apply
# Need maxprot/initprot = 7 = xwr for __DATA in main.ma
# (f x) y
new1_1 f:0?1?2 x:0 : 1?2 =
  g = Mem.span mold1.mem mold1_end.mem                              # 092-05a = 56
  Mem.set2 g+!base+1 f.Cast.nat # skip 0x68
  Mem.set2 g+!base+11 x # 0x64 - 0x5a + 1 - skip 0x68, 00000064 push qword 0x2a, 0000005A push qword 0x12e2
  Cast.any g
Fact (f = new1_1 N.add 40; f 2 == 42)
#Fact ((new1_1 N.add 40) 2 == 42) # unsupported
Fact (f = N.add 40; f 2 == 42)
Fact ((N.add 40) 2 == 42)

# (f x) y z = f x y z
mold1_2 y:0 z:1 : 2 = (f = Any.cast_fun4 0; f 0 y z)
mold1_2_end _:N : N = 0

# same as 1 (1 f)
new1_2 f:0?1?2?3 x:0 : 1?2?3 =
  g = Mem.span mold1_2.mem mold1_2_end.mem
  Mem.set2 g+!base+1 f.Cast.nat # skip 0x68
  Mem.set2 g+!base+11 x # 0x64 - 0x5a + 1 - skip 0x68, 00000064 push qword 0x2a, 0000005A push qword 0x12e2
  Cast.any g

# (f x) y z w = f x y z w
mold1_3 y:0 z:1 w:2 : 3 = (f = Any.cast_fun5 0; f 0 y z w)
mold1_3_end _:N : N = 0

new1_3 f:0?1?2?3?4 x:0 : 1?2?3?4 =
  g = Mem.span mold1_3.mem mold1_3_end.mem                              # 092-05a = 56
  Mem.set2 g+!base+1 f.Cast.nat # skip 0x68
  Mem.set2 g+!base+11 x # 0x64 - 0x5a + 1 - skip 0x68, 00000064 push qword 0x2a, 0000005A push qword 0x12e2
  Cast.any g

# (f x y) z
mold2 x:0 : 1 = (f = Any.cast_fun4 0; f 0 0 x)
mold2_end _:N : N = 0
new2_1 f:0?1?2?3 x:0 y:1 : 2?3 =
  g = Mem.span mold2.mem mold2_end.mem
  Mem.set2 g+!base+1 f.Cast.nat # 0 + 1
  Mem.set2 g+!base+11 x # 0x64 - 0x5a + 1
  Mem.set2 g+!base+16 y # 0x69 - 0x5a + 1
  Cast.any g
Fact (Pair.str_by N.str N.str 13,42 == '13,42')
Fact (Pair.str_by (Pair.str_by N.str N.str) N.str (3,13),42 == '3,13,42') # (3,13),42
Fact ((Pair.str_by N.str N.str) 13,42 == '13,42')
#Fact ((Fun.new2_1 Pair.str_by N.str N.str) 13,42 == '13,42') # unsupported
Fact (f = Fun.new2_1 Pair.str_by N.str N.str; f 13,42 == '13,42')
Fact (f = Fun.new2_1 Pair.str_by N.str N.str; g = Fun.new2_1 Pair.str_by f N.str; g (3,13),42 == '3,13,42')
#Fact (f = Fun.new2_1 Pair.str_by N.str N.str; Fun.new2_1 Pair.str_by f N.str (3,13),42 == '3,13,42') # unsupported

# Fun.new* skips Step.exp_steps for function pre steps - STEP_FUN_PRE
base = %0 : %N
Fact (f = new2_1 (_ x:N y:N z:N : N = x + y + z) 2 3; f 5 == 10)

mold2_2 z:0 w:1 : 2 = (f = Any.cast_fun5 0; f 0 0 z w)
mold2_2_end _:N : N = 0

new2_2 f:0?1?2?3?4 x:0 y:1 : 2?3?4 =
  g = Mem.span mold2_2.mem mold2_2_end.mem
  Mem.set2 g+!base+1 f.Cast.nat # skip 0x68
  Mem.set2 g+!base+11 x # 0x64 - 0x5a + 1 - skip 0x68, 00000064 push qword 0x2a, 0000005A push qword 0x12e2
  Mem.set2 g+!base+16 y
  Cast.any g
Fact (f = new2_2 (_ x:N y:N z:N w:N : N = x + y + z + w) 2 3; f 5 8 == 18)

mold2_3 z:0 p:1 q:2 : 3 = (f = Any.cast_fun6 0; f 0 0 z p q)
mold2_3_end _:N : N = 0

new2_3 f:0?1?2?3?4?5 x:0 y:1 : 2?3?4?5 =
  g = Mem.span mold2_3.mem mold2_3_end.mem
  Mem.set2 g+!base+1 f.Cast.nat # skip 0x68
  Mem.set2 g+!base+11 x # 0x64 - 0x5a + 1 - skip 0x68, 00000064 push qword 0x2a, 0000005A push qword 0x12e2
  Mem.set2 g+!base+16 y
  Cast.any g
Fact (f = new2_3 (_ x:N y:N z:N p:N q:N : N = x + y + z + p + q) 2 3; f 5 8 13 == 31)

# (f x y z) w
mold3 x:0 : 1 = (f = Any.cast_fun5 0; f 0 0 0 x)
mold3_end _:N : N = 0
new3_1 f:0?1?2?3?4 x:0 y:1 z:2 : 3?4 =
  g = Mem.span mold3.mem mold3_end.mem
  Mem.set2 g+!base+1 f.Cast.nat # 0 + 1
  Mem.set2 g+!base+11 x # 0x64 - 0x5a + 1
  Mem.set2 g+!base+16 y # 0x69 - 0x5a + 1
  Mem.set2 g+!base+21 z # 16+5
  Cast.any g
Fact (f = new3_1 (_ x:N y:N z:N w:N : N = x + y + z + w) 2 3 5; f 8 == 18)

# (f x y z) w u
mold3_2 z:0 w:1 : 2 = (f = Any.cast_fun6 0; f 0 0 0 z w)
mold3_2_end _:N : N = 0
new3_2 f:0?1?2?3?4?5 x:0 y:1 z:2 : 3?4?5 =
  g = Mem.span mold3_2.mem mold3_2_end.mem
  Mem.set2 g+!base+1 f.Cast.nat # 0 + 1
  Mem.set2 g+!base+11 x # 0x64 - 0x5a + 1
  Mem.set2 g+!base+16 y # 0x69 - 0x5a + 1
  Mem.set2 g+!base+21 z # 16+5
  Cast.any g
Fact (f = new3_2 (_ x:N y:N z:N w:N u:N : N = x + y + z + w + u) 2 3 5; f 8 13 == 31)

# (f x y z w) u
mold4 x:0 : 1 = (f = Any.cast_fun6 0; f 0 0 0 0 x)
mold4_end _:N : N = 0
new4_1 f:0?1?2?3?4?5 x:0 y:1 z:2 w:3 : 4?5 =
  g = Mem.span mold4.mem mold4_end.mem
  Mem.set2 g+!base+1 f.Cast.nat # 0 + 1
  Mem.set2 g+!base+11 x # 0x64 - 0x5a + 1
  Mem.set2 g+!base+16 y # 0x69 - 0x5a + 1
  Mem.set2 g+!base+21 z # 16+5
  Mem.set2 g+!base+26 w # 21+5
  Cast.any g
Fact (f = new4_1 (_ x:N y:N z:N w:N u:N : N = x + y + z + w + u) 2 3 5 8; f 13 == 31)

loop f:Z?Z = (f 0; loop f)

arity : Type ? N =
  _, Binary _ '?' type? 1 + arity type
  ? 0

# https://en.wikipedia.org/wiki/Function_composition compose then
of g:1?2 f:0?1 x:0 : 2 = g (f x)
Fact (of S.size List.head ['fooo', 'bar'] == 4)
# Fact ((List.head . of S.size) ['fooo', 'bar'] == 4) # todo - two-step apply
Fact (f = List.head . of S.size; f ['fooo', 'bar'] == 4)
Fact (f = of S.size List.head; f ['fooo', 'bar'] == 4)

do f:Z?0 : 0 = f 0

callx f:Z?0 : 0 = f 0
