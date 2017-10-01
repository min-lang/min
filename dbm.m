# unix simple database

 https://en.wikipedia.org/wiki/Dbm

lib_open = Dl'dbm_open' : path:S? flags:N? mode:N? N

lib_close = Dl'dbm_close' : db:N? Z

lib_fetch = Dl'dbm_fetch' : db:N? key:S? key_size:N? Mem,N

fetch db:N key:S : S =
  s, n = Fun.call3_r2 lib_fetch db key !key
  S.of_mem s n

lib_store = Dl'dbm_store' : db:N? key:0? key_size:1? term:2? term_size:3? mode:N? N

make path:S : N = Fun.call3 lib_open path 0202 01b0 # 0202=O_CREAT|O_RDWR, 01b0 = 0660 rw_rw_

replace db:N key:S term:S : N = Fun.call6 lib_store db key !key term !term 1 # DBM_REPLACE

close db:N = Fun.call1 lib_close db

test _ =
  db = make '/tmp/min-dbm' # expands to [path].db
  replace db 'foo' 'yoo' # invalid argument if not dbm_open with O_RDWR
  Fact.do $Fun (fetch db 'foo' == 'yoo')
  close db
  0
