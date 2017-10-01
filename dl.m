# dynamic linking loader, dynamic library

  https://developer.apple.com/library/mac/documentation/Darwin/Reference/ManPages/man3/dlopen.3.html#//apple_ref/doc/man/3/dlopen
    
# http://linux.die.net/man/3/dlopen
# https://developer.apple.com/library/mac/documentation/Darwin/Reference/ManPages/man3/dlopen.3.html
lib_dlopen = Dl 'dlopen' : path:S? mode:N? !0
lib_dlerror = Dl 'dlerror' : Z? S

sym0 name:S : !(1?2) = Asm                                        
  mov di 0                              # /ref/dyld/include/dlfcn.h #define	RTLD_DEFAULT	((void *) -2)	/* Use default search algorithm. */
  sub di 2                              # must use RTLD_DEFAULT (not RTLD_NEXT) for 'extern id NSApp'
  mov si sp 8  
  mov a Code_vmend                      # see @Bind BIND_OPCODE_SET_SEGMENT_AND_OFFSET_ULEB(0x01, 0x00000000) in main.ma
  call a 0
  mov sp 16 a
  ret

main name:S : 0?1 =
  f = sym0 name
  f | Fail.main2 $Fun name
Fact (N.between 1 (Dl 'dlopen' . Cast.any) I.max3) # 07fffca5a47f7

open path:S : N =
  lib = Fun.call2 lib_dlopen path 0
  lib | (Put (Fun.call0 lib_dlerror); 0)

path_sym path:S name:S =
  open path . Hex.put
  Dl name . Mem.put
  0
