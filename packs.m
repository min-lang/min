# machine data
z                                       # zero, void, nil, null, unit
b                                       # bit, bool, boolean, flag, truth, logic
c                                       # char, character, unicode code point
n                                       # nat, number, non-negative, unsigned
i                                       # int, integer, signed, natural number
r                                       # real, floating-point number

# interpreted data
any                                     # abstract data
hex                                     # hexadecimal number
mem                                     # memory address, pointer
unicode                                 # universal character set
fun                                     # function, procedure, routine

# structured data
opt                                     # optional, nullable, some, pointed
pair                                    # two data, product, cons
ref                                     # reference, mutable
row                                     # array, tuple, vector, product
s                                       # str, string, character array
list                                    # singly linked list
seq                                     # sequence, container, collection, generator 
box                                     # packed data, inlined
key                                     # named, label, struct, record
map                                     # finite map, association, dictionary, finite function
hash                                    # hashtable, mutable and unordered map
set                                     # mathematical set
flow                                    # stream, buffer, port
regex                                   # regular expression, character pattern

# hardware
core                                    # cpu, multi processor, hyperthread
spin                                    # concurrency synchronization lock
clock                                   # timer, frequency tick

# operating system
sys                                     # system call, kernel call
posix                                   # portable operating system interface
dl                                      # dynamic linking loader, dynamic library
job                                     # unix job, process
thread                                  # system-mode parallelism
task                                    # user-mode parallelism, coroutine
time                                    # calendar, date and time, epoch
env                                     # environment, context

# langauge
cast                                    # type cast, coercion
fail                                    # fatal exit, abort, exception, error
fact                                    # assert, check, test
trap                                    # signal, interrupt, fault
call                                    # call stack, stack trace
perf                                    # performance, profile, monitor
main                                    # top level, entry point, program start

# file system
path                                    # unix file path, file name
file                                    # unix file description / number / handler
pipe                                    # unix pipeline, process input/output chain
in                                      # file 0, standard input
out                                     # file 1, standard output
put                                     # file 1, standard output, with newline
err                                     # file 2, standard error
log                                     # file 2, standard error, with newline
info                                    # file 4, informational output
trace                                   # file 5, performance time tracing
debug                                   # file 6, verbose debugging diagnostic

# network
socket                                  # network file
net                                     # network address, ip address, host identification
openssl                                 # secure sockets layer
common_crypto                           # common crypto in mac os x
http                                    # hypertext transfer protocol
httpd                                   # hypertext transfer protocol daemon, web server

# library
json                                    # javascript object notation
zlib                                    # compression via gzip
blas                                    # basic linear algebra subprograms
dbm                                     # unix simple database
sqlite                                  # sql database engine
cocoa                                   # cocoa ui in mac os x
quant                                   # quantitative analysis
dynamodb                                # amazon cloud key-value database

# compiler
spot                                    # file position, path and line and column
tag                                     # tagged union, enum, algebraic data type
name                                    # identifier, unique string, naming convention
op                                      # symbolic operator, prefix/infix/suffix function
meta                                    # reflection, string interpolation
term                                    # token, node, word, lexical form
exp                                     # expression, tree, phrase, parser form
group                                   # delimited, lexical sub-term by line / limit / glue / associate
rule                                    # rewrite rule, pattern matching
rewrite                                 # tree rewrite
kind                                    # class of type
unify                                   # constraint resolve
def                                     # definition, equality
type                                    # class of term
step                                    # opcode, linear computation, flat execution
asm                                     # assembly, machine code
