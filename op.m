# symbolic operator, prefix/infix/suffix function

  ! + - * / % ^      bang add neg/sub mul div mod pow
  < > == != <= >=    lt gt eq ne le ge
  : ~ $ @            type sim meta at
  | &                or and
  , ; []             row step list  
  '' "" ``           str quote re


rank : S?N =
  ';'? 1                                                                        # command step, statement, instruction sequence
  
  '='? 2                                                                        # definition, equation
  ':'? 3                                                                        # type annotation
  
  '@'? 5                                                                        # at, scope, where
  
  '?'? 6                                                                        # function, map, domain/codomain
  '$'? 7                                                                        # meta, evaluation
  '*'? 8                                                                        # linked list

  '|'? 9                                                                        # or
  '&'? 10                                                                       # and
  ','? 11                                                                       # binary pair, tuple, list separator
  '~'? 12                                                                       # tree type

  '≈'? 14                                                                       # close, similar
  '=='? 14                                                                      # equal to 
  '!='? 14                                                                      # not equal to
  '<'? 14                                                                       # less than
  '<='? 14                                                                      # less than or equal to
  '>'? 14                                                                       # great than
  '>='? 14                                                                      # great than or equal to

  '+'? 20                                                                       # add
  '-'? 20                                                                       # subtract
  '/'? 21                                                                       # div, module token, tokenize
  '%'? 21                                                                       # ref, modulus, filter, membership

  '!'? 30                                                                       # nil/not/empty, fun neg, ref get, size
  '^'? 31                                                                       # power, exponential, reverse, transpose
  '.'? 32                                                                       # member, reverse apply

right name:S : B = List.in S.eq [';', ',', '?'] name

name_unary : S ? !S =
  '!'? 'N.not'
  '-'? 'N.neg'
  '%'? 'Ref.main'
  
name : S ? !S =
  '+'? 'add'
  '-'? 'sub'
  '*'? 'mul'
  '/'? 'div'
  '%'? 'mod'
  '^'? 'pow'  
  '=='? 'eq'
  '!='? 'ne'
  '<'? 'lt'
  '<='? 'le'
  '>'? 'gt'
  '>='? 'ge'
  ','? 'row'
  '≈'? 'sim'
