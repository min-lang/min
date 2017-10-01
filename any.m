# abstract data

# getconf PAGE_SIZE # 4096
code_vmaddr = 01000                     # after 4096 __PAGEZERO

data_vmaddr = 01000000                  # after 16MB __TEXT code

# See Fun.mold1.
_cast x:0 : 1 = x
cast_fun3x x:0 : 1 ? 2 ? 3 = _cast x
cast_fun3 x:0 : 1 ? 2 ? 3 = _cast x
cast_fun4 x:0 : 1 ? 2 ? 3 ? 4 = _cast x
cast_fun5 x:0 : 1 ? 2 ? 3 ? 4 ? 5 = _cast x
cast_fun6 x:0 : 1 ? 2 ? 3 ? 4 ? 5 ? 6 = _cast x
