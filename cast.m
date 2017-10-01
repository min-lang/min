# type cast, coercion

  See Step.is_identity.

any x:0 : 1 = x

bit x:0 : B = any x

nat x:0 : N = any x

mem x:0 : Mem = any x

bits_real x:N : R = any x

real_bits x:R : N = any x

bit_nat x:B : N = any x

nat_char x:N : C = any x

char_nat x:C : N = any x

str_mem x:S : Mem = any x

mem_str x:Mem : S = any x

mem_nat x:Mem : N = any x

file_nat x:File : N = any x

nat_file x:N : File = any x

socket_nat x:Socket : N = any x

nat_socket x:N : Socket = any x

opt_nat x:!N : N = any x
