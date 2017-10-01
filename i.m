# int, natural number, signed integer

  http://en.wikipedia.org/wiki/Integer
  https://en.wikipedia.org/wiki/Signedness
  
le x:N y:N : B = Asm
  mov a sp 16
  cmp a sp 8
  mov c 0
  set sle c
  mov sp 24 c
  ret

le x:I y:N : B = Asm
  mov a sp 16
  cmp a sp 8
  mov c 0
  set sl c
  mov sp 24 c
  ret

lt x:I y:N : B = Asm
  mov a sp 16
  cmp a sp 8
  mov c 0
  set sl c
  mov sp 24 c
  ret

gt x:N y:N : B = Asm
  mov a sp 16
  cmp a sp 8
  mov c 0
  set sg c
  mov sp 24 c
  ret

ge x:N y:N : B = Asm
  mov a sp 16
  cmp a sp 8
  mov c 0
  set sge c
  mov sp 24 c
  ret
    
rank x:N : N =
  | x <= 07f & 0 
  | x <= 07fff & 1 
  | x <= 07fff_ffff & 2                                                         
  | 3

Fact (rank 42 == 0)
Fact (rank 0ca == 1)
Fact (rank 0cafe == 2)
Fact (rank 0cafe_babe == 3)
Fact (rank 0cafe_babe_dead_beef == 3)

max2 = 07fff_ffff

max3 = 07fff_ffff_ffff_ffff
