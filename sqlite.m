# sql database engine

  https://www.sqlite.org/capi3ref.html

lib = Dl.open 'libsqlite3.dylib' : N

lib_open = Dl'sqlite3_open' : path:!S? db:%N? flag:N

# https://www.sqlite.org/capi3ref.html#sqlite3_exec
lib_exec = Dl'sqlite3_exec' : db:N? sql:S? callback:0? arg:0? error:%S? flag:N

# const char *sqlite3_errmsg(sqlite3*);
lib_errmsg = Dl'sqlite3_errmsg' : db:N? error:S

do_raw x:N y:N z:N w:N : N = Asm                                                                # callback with c-calling convention
  push b; push bp; push r12; push r13; push r14; push r15                       # callee-saved registers (only rbx is needed to be restored here?)
  push 0
  push di
  push si
  push d
  push c
  call Sqlite.do
  add sp 32                                                                     # pop 4 args 
  pop a                                                                         # pop 1 return value
  pop r15; pop r14; pop r13; pop r12; pop bp; pop b
  ret                                                                           # or, Sys.bsdthread_terminate 0

# sqlite3 '' 'select 40+2'
do arg:Mem size:N cols:S^ names:S^ : N =
  N.for size (_ i:N = (Log.main2 (Row.get names i) (Row.get cols i)))
  0

# https://www.sqlite.org/capi3ref.html#sqlite3_prepare
  int sqlite3_prepare_v2(
    sqlite3 *db,            /* Database handle */
    const char *zSql,       /* SQL statement, UTF-8 encoded */
    int nByte,              /* Maximum length of zSql in bytes. */
    sqlite3_stmt **ppStmt,  /* OUT: Statement handle */
    const char **pzTail     /* OUT: Pointer to unused portion of zSql */
  );
lib_prepare = Dl'sqlite3_prepare_v2' : db:N? sql:S? size:N? stmt:%N? tail:N? flag:N

# https://www.sqlite.org/capi3ref.html#sqlite3_step
  int sqlite3_step(sqlite3_stmt*);
lib_step = Dl'sqlite3_step' : stmt:N? flag:N

# https://www.sqlite.org/capi3ref.html#sqlite3_finalize
  int sqlite3_finalize(sqlite3_stmt *pStmt);
lib_finalize = Dl'sqlite3_finalize' : stmt:N? flag:N
  
#
 sqlite3 main.db 'create table users (id key, name)'
 sqlite3 main.db 'create table tasks (id key, user, time, summary)'
   # sqlite3 main.db 'drop table tasks'
 sqlite3 main.db 'select * from users'
 sqlite3 main.db 'select * from tasks'
 sqlite3 main.db 'select sql from sqlite_master'
 <<< '0|laker' sqlite3 main.db '.import /dev/stdin users'
 <<< '1|warrior' sqlite3 main.db '.import /dev/stdin users'
 <<< '0|0|0|foo' sqlite3 main.db '.import /dev/stdin tasks'
 <<< '1|0|5|bar' sqlite3 main.db '.import /dev/stdin tasks'
 <<< '2|1|7|qux' sqlite3 main.db '.import /dev/stdin tasks'
test _ =
  db = %0
  Fun.call2 lib_open '/tmp/main-sqlite' db
  stmt = %0
  Fun.call5 lib_prepare !db 'select summary from tasks where user="0"' -1 stmt 0
  for !stmt
  0

# https://www.sqlite.org/c3ref/column_blob.html
lib_column_text = Dl'sqlite3_column_text' : stmt:N? key:N? S

# https://www.sqlite.org/c3ref/column_count.html
lib_column_count = Dl'sqlite3_column_count' : stmt:N? N

flag_row = 100
for stmt:N =
  | Fun.call1 lib_step stmt == flag_row &
    Fact.do $Fun (Fun.call2 lib_column_text stmt 0 == 'foo')
    0
  0
