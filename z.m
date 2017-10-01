# zero, void, nil, null, unit

 https://en.wikipedia.org/wiki/Unit_type
 https://en.wikipedia.org/wiki/Void_type

# ignore, skip, pass, no-op
main _:0 = 0                                                                 

eq _:Z _:Z : B = 1

opt _:Z : !Z = Cast.any 1

must _:!Z = 0
