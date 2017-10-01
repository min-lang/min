# basic linear algebra subprograms

  http://www.netlib.org/blas

lib = Dl.open 'libblas.dylib' : N

# https://developer.apple.com/library/mac/documentation/Accelerate/Reference/BLAS_Ref/#//apple_ref/c/func/cblas_dscal
lib_dscal = Dl'cblas_dscal' : size:N? a:R? x:*R? dx:N? Z # I? R? R^? I? Z

# args - di si d c r8 r9 / a
dscal f:0 a:R x:Mem = Asm                                                           # x <- a x
  mov b sp 24
  mov di 2                                                                      # size
  mov a sp 16                                                                   # a
  mov xmm0 a  
  mov si sp 8                                                                   # x
  mov d 1                                                                       # dx
  push bp  
  mov bp sp  
  and sp 0ffff_fff0
  call b  
  mov sp bp
  pop bp
  ret  

main _ =
  x = 3,5 . Cast.mem
  dscal lib_dscal 2. x
  Fact.do $Fun (Mem.hex x 16 == '06000000000000000a00000000000000')
  0
