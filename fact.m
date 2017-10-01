# assert, check, test

  https://en.wikipedia.org/wiki/QuickCheck

exps = %0 : %Exps

bit = Env.bit 'fact' : B

do spot:S x:B = (x | Fail.force2 spot $Fun) . Z

check1 spot,fact:S,B = (bit & Log spot; fact | Fail.force2 spot $Fun) . Z

check _ = List.do $Fact check1
