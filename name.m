# identifier, unique string, naming convention

  “Short words are best and the old words when short are best of all.” - Winston Churchill

  http://en.wikipedia.org/wiki/Identifier_(computer_science)#In_computer_languages
  https://en.wikipedia.org/wiki/Naming_convention_(programming)
  https://en.wikipedia.org/wiki/Nomenclature

  a b c d e    term, coefficient, expression
  f g h        function, operator, routine, hex
  i j k        key, index, offset
  n m l        size, length, count
  p q o        rule, pattern  pointer, binding, predicate
  s r          sequence, string, vector, reference
  t u v        type, class, time
  w x y z      variable, parameter

dot x:S y:S : S = x + '.' + y

ticks x:S : S = x + '.ticks'

calls x:S : S = x + '.calls'

add prefix:S n:%N : S = prefix + n.Ref.tick.N.str
