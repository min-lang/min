# Min: Crypto Token for Beautiful and Secure Code

Min is a new programming language for beautiful and secure code. We issue crypto tokens to investors and developers for bootstrapping the network in __open source and governance__. 

Token networks align participants toward a common goal. Our mission is to build a __profitable and sustainable ecosystem__ of good software.

Below are [an introduction](#charm-and-delight) to Min the language and [a walkthrough](#programming-and-rules) of our source code.


# Consensus and Incentives

Contributors earn Min coins, denoted by the [infimum](https://en.wikipedia.org/wiki/Join_and_meet) symbol ∧, through technical work, community building, or business development. Examples include

- ∧100: Write blogs, documentation, crash reports;
- ∧1,000: Port libraries, hunt bounties, moderate Slack; and,
- ∧10,000: Port to iOS / Android / Ethereal VM, launch token sales.

Min solves the most pressing problems of large-scale software development: __hiring and collaboration__. With Min tokens, decentralized work is rewarded with _smart contracts_. With Min language, code evolution is guided by _strong types_.

Our first product is a cross-platform framework for native mobile applications. Soon we will also optimize for machine learning and decentralized applications. Sign up for news of our [token launch](http://min-lang.com/sale)! 


# 100x and Roadmap

Currently Min compiles to x86-64 machine code without any external tools. Self-contained for cross compilation and
consistent on any platform, Min does not use any C backends, assembly, or linker.

- [x] Self-compile without any tools on Mac OS X
- [ ] Port to Linux, iOS, Android, Javascript, Windows
- [ ] Generalized sequences, memory management
- [ ] Coding guide, language specification

```
$ make
./min binary `cat packs` 3< main.ma > min1
chmod +x min1
./min1 binary `cat packs` 3< main.ma > min2
[[ `md5 < min1` == `md5 < min2` ]]
```

# Charm and Delight

Min is the most innovative programming language designed for beautiful code. To create it, we have started from scratch with machine code, then re-thought every syntax and idiom.

Beautiful code, like mathematics, is pleasurable to learn and to write. With Min, immutability by default simplifies stateful computations. Rich, advanced types eliminate mistakes and guide optimizations.

The art of programming — with the right syntax.

| Minimalist syntax | Immutable data | Advanced types
|:-:|:-:|:-:
| orthogonal yet intuitive | think in mathematics | automatically bug-free


## Philosophy. Yearn for the vast and endless Bits.

```
hex1 x:C : N = \a <= x <= \f & x - \a + 10 | x - \0
Fact (hex1 \d == 13)

hex s:S n=0 : N = s.0 & hex s+1 16n+s.0.hex1 | n
Fact (hex 'cafebabe' == 3405691582)
```

To code, don't drum up the men to use frameworks and design patterns. Instead, teach them to yearn for elegant algorithms in beautiful syntax. Min's novel parser uses horizontal spacing and vertical layout to free programming from clutters of delimiters and LALR(1) grammars.
Here, zero keywords and all operators are of a single keyboard character except the four relational operators.

| builtin keywords | delimiters with layout | composite operators|
|:-:|:-:|:-:
| 0 | 0 | 4 |


## Purpose. Fun for Thinkers and Tinkers.

Everyone can be taught to code but thinkers dream of abstractions and tinkers obsess with implementations. Min's design
emphasizes the unifying foundation of higher-order functions and formal types. This means flow controls and generic
sequences are naturally user-definable. You can think in terms of mathematical logic, and write as such.

```
hash_get rows:0/1 x:0 : 1 = rows 
 . hash x % size rows
 / y? x == y
 . head
Fact (hash_get ['foo'?13, 'bar'?42] 'bar' == 42)
```

All the while, you can peek behind every piece of Min's code — no dragons of macros or generated C code ahead. Tinker
and master the intricate clockwork of our compiler in a unified language, from machine registers as well as database
backends, all the way to web frontends and decentralized applications.

```
items = Sql 'rds.amazonaws.com:3306/tasks'
 . join users on=(x? u? x.user == u.id)
 / x? x.status != Done
 . top 5

done id:N = Xhr async=1 '/done?[id]'
Html
  Title Top [items.size] TODO
  items * id,summary,time,name?
    Li onclick=done(id) [summary], [time] by [name]
```

| Infinite model | Unified web 
|:-:|:-:
| strings, files, tables as lazy sequence | SQL, HTML, Javascript in one syntax


## Technology. Need for Speed and Security.

In “[Computer Scientists Close In On Perfect, Hack-Proof Code](https://www.wired.com/2016/09/computer-scientists-close-perfect-hack-proof-code/),” Kevin Hartnett at Quanta Magazine writes:

> _Key parts of Little Bird’s computer system were unhackable with existing technology, its code as __trustworthy as a mathematical proof__... That results made all of Darpa stand up and say, oh my goodness, we can actually use this technology in systems we care about._
>
> _Previously, when computers were isolated in homes and offices, programming bugs were merely inconvenient. Now those same small coding errors open __massive security vulnerabilities__ on networked machines that allow anyone with the know-how free rein inside a computer system._

Memory management costs enormous development effort or it dominates runtime cycles. Min's innovative type inference automates ownership annotations in a region-based memory model, so code remains at a high-level abstraction without the complexity of a garbage collector.

```
Term = Tag
 Nil
 Apply fun:Term arg:Term
 If test:Term pos:Term neg:Term
 Binary left:Term op:S right:Term

rewrite : Term? Term =
  Binary (Binary a '&' b) '|' c? If a b c    
  Binary a '&' b? If a b Nil
  Binary a '.' b? Apply b a
  Binary a '@' b? Binary b ';' a
```

Min's precise types also guarantee correctness before execution and optimize for machine performance. Scaling to a million page requests or intensive scientific computations won't need delegating to foreign functions. With Min, you won't have to worry about null pointers in critical services, or stealing and tampering of your digital assets in decentralized applications.

```
black_scholes
 s : ℝ # stock price
 x : ℝ # strike price
 t : ℝ # expiration time in years
 r : ℝ # risk-free interest rate
 σ : ℝ # volatility
 : ℝ
 = s ϕ(d1) - x e^(-r t)ϕ(d2) @ 
  ϕ = Normal.cdf
  d0 = log s/x + (r + σ²/2)t
  d1 = d0 / σ√t
  d2 = d1 - σ√t
```

# Programming and Rules

Here's the directory of Min's source code with description. We're making steps toward [our mission](#min-crypto-token-for-beautiful-and-secure-code) and [our language](#charm-and-delight).

| | |
| - | - 
| __machine data__
| [z.m](z.m)                            | zero, void, nil, null, unit 
| [b.m](b.m)                            | bit, bool, boolean, flag, truth, logic
| [c.m](c.m)                            | char, character, unicode code point
| [n.m](n.m)                            | nat, number, non-negative, unsigned
| [i.m](i.m)                            | int, integer, signed, natural number
| [r.m](r.m)                            | real, floating-point number
||
| __interpreted data__
| [any.m](any.m)                        | abstract data
| [hex.m](hex.m)                        | hexadecimal number
| [mem.m](mem.m)                        | memory address, pointer
| [unicode.m](unicode.m)                | universal character set
| [fun.m](fun.m)                        | function, procedure, routine
||
| __structured data__
| [opt.m](opt.m)                        | optional, nullable, some, pointed
| [pair.m](pair.m)                      | two data, product, cons
| [ref.m](ref.m)                        | reference, mutable
| [row.m](row.m)                        | array, tuple, vector, product
| [s.m](s.m)                            | str, string, character array
| [list.m](list.m)                      | singly linked list
| [seq.m](seq.m)                        | sequence, container, collection, generator 
| [box.m](box.m)                        | packed data, inlined
| [key.m](key.m)                        | named, label, struct, record
| [map.m](map.m)                        | finite map, association, dictionary, finite function
| [hash.m](hash.m)                      | hashtable, mutable and unordered map
| [set.m](set.m)                        | mathematical set
| [flow.m](flow.m)                      | stream, buffer, port
| [regex.m](regex.m)                    | regular expression, character pattern
| [json.m](json.m)                      | javascript object notation
||
| __hardware__
| [core.m](core.m)                      | cpu, multi processor, hyperthread
| [spin.m](spin.m)                      | concurrency synchronization lock
| [clock.m](clock.m)                    | timer, frequency tick
||
| __operating system__
| [sys.m](sys.m)                        | system call, kernel call
| [posix.m](posix.m)                    | portable operating system interface
| [dl.m](dl.m)                          | dynamic linking loader, dynamic library
| [job.m](job.m)                        | unix job, process
| [thread.m](thread.m)                  | system-mode parallelism
| [task.m](task.m)                      | user-mode parallelism, coroutine
| [time.m](time.m)                      | calendar, date and time, epoch
| [env.m](env.m)                        | environment, context
||
| __langauge__
| [cast.m](cast.m)                      | type cast, coercion
| [fail.m](fail.m)                      | fatal exit, abort, exception, error
| [fact.m](fact.m)                      | assert, check, test
| [trap.m](trap.m)                      | signal, interrupt, fault
| [call.m](call.m)                      | call stack, stack trace
| [perf.m](perf.m)                      | performance, profile, monitor
| [main.m](main.m)                      | top level, entry point, program start
||
| __file system__
| [path.m](path.m)                      | unix file path, file name
| [file.m](file.m)                      | unix file description / number / handler
| [pipe.m](pipe.m)                      | unix pipeline, process input/output chain
| [in.m](in.m)                          | file 0, standard input
| [out.m](out.m)                        | file 1, standard output
| [put.m](put.m)                        | file 1, standard output, with newline
| [err.m](err.m)                        | file 2, standard error
| [log.m](log.m)                        | file 2, standard error, with newline
| [info.m](info.m)                      | file 4, informational output
| [trace.m](trace.m)                    | file 5, performance time tracing
| [debug.m](debug.m)                    | file 6, verbose debugging diagnostic
||
| __network__
| [socket.m](socket.m)                  | network file
| [net.m](net.m)                        | network address, ip address, host identification
| [openssl.m](openssl.m)                | secure sockets layer
| [common_crypto.m](common_crypto.m)    | common crypto in mac os x
| [http.m](http.m)                      | hypertext transfer protocol
| [httpd.m](httpd.m)                    | hypertext transfer protocol daemon, web server
||
| __library__
| [zlib.m](zlib.m)                      | compression via gzip
| [blas.m](blas.m)                      | basic linear algebra subprograms
| [dbm.m](dbm.m)                        | unix simple database
| [sqlite.m](sqlite.m)                  | sql database engine
| [cocoa.m](cocoa.m)                    | cocoa ui in mac os x
| [quant.m](quant.m)                    | quantitative analysis
| [dynamodb.m](dynamodb.m)              | amazon cloud key-value database
||
| __compiler__ 
| [main.ma](main.ma)                    | mach object file format for mac executables
| [spot.m](spot.m)                      | file position, path and line and column
| [tag.m](tag.m)                        | tagged union, enum, algebraic data type
| [name.m](name.m)                      | identifier, unique string, naming convention
| [op.m](op.m)                          | symbolic operator, prefix/infix/suffix function
| [meta.m](meta.m)                      | reflection, string interpolation
| [term.m](term.m)                      | token, node, word, lexical form
| [exp.m](exp.m)                        | expression, tree, phrase, parser form
| [group.m](group.m)                    | delimited, lexical sub-term, glue / associate
| [rule.m](rule.m)                      | rewrite rule, pattern matching
| [rewrite.m](rewrite.m)                | tree rewrite
| [kind.m](kind.m)                      | class of type
| [unify.m](unify.m)                    | constraint resolve
| [def.m](def.m)                        | definition, equality
| [type.m](type.m)                      | class of term
| [step.m](step.m)                      | opcode, linear computation, flat execution
| [asm.m](asm.m)                        | assembly, machine code


# Minimal and Infimum

What is the minimal set of equations for programming? How do we derive the equivalence principle among types with finite symbols? 

| operator |  name | equivalence  |
| - | - | -
  x,y    |  Pair x y     | |
  %x     |  Ref x        |  Z, x
  !x     |  Opt x        |  B, x
  a=x    |  Key a x      |  x
  a:x?y  |  Fun a:x y    |  *(x, y)
  x+y    |  Tag x y      |  N, (x, y)
| | |
  x^n    |  Row x n      |  x, x, ..., x
  *x     |  List x       |  x, *x
  +x     |  Seq x        |  !x + *x + x^
  <x     |  Flow x       |  +x, +x
  x/Z    |  Set x        |  N, x^
| | |
  x-y    |  Map x y      |  *(x, y)
  x/y    |  Hash x y     |  N, (x, y)^

```
  head,tail %ref !opt name=term arg:type?val tag+tag
  row^size *list +seq <flow set-Z bag-N 
  key-term path~node hash/term
```

| code |  equivalence  |
| - | - |
a .f b                |  f a b
[a, b, c]             |  a, (b, (c, 0))
f a+b -c / d          |  (f (a + b) (- c)) / d
a & b \| c & d \| e   |  if a b (if c d e)
f x,y=a:t : u = b     |  f = ((z = (a : t))? (x, y = z; b : u))
a . (A x & b? c; ?d)  |  (tag a == A & b) & (x = item a; c) \| d
f a<br>&nbsp;g b<br>&nbsp;h c  |  f a (g b) (h c)
\| a & f d<br>\| b & g e<br>\| c  |  if a (f c) (if b (g e) c)


# Hungry and Foolish

Join our [mailing list and Slack](http://min-lang.com/signup) to build the future! 

> _I learned about serif and sans serif typefaces, about varying the amount of space between different letter
> combinations, about what makes great typography great. It was beautiful, historical, artistically subtle in a way
> that science can't capture, and I found it fascinating... It was the first computer with beautiful typography._

Stephen Tse <[s@min-lang.com](mailto:Stephen%20Tse%20<s@min-lang.com>)>.