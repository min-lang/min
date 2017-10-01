# environment, context

  http://en.wikipedia.org/wiki/Environment_variable

lib_getenv = Dl 'getenv' : S? !S

get name:S : !S = Fun.call1 lib_getenv name

any name:S : B = Opt.bit name.get

bit name:S : B = Env name . B.of

main name:S : S = get name | '0'

must name:S : S = get name | Fail.fill "$s: missing environment variable '$s'" [$Fun, name]
