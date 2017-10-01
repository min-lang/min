# delimited, lexical sub-term, glue / associate

  http://en.wikipedia.org/wiki/Indent_style

rev_exps_trees spot:!Spot rev_exps:Exps trees:Exps : Exps =
  | rev_exps &
    | rev_exps.List.tail &
      exps = List.rev rev_exps
      ((spot | Exp.spot2 exps.List.head rev_exps.List.head), Tree exps), trees
    |
      x = rev_exps.List.head
      (spot & (spot, x.Exp.tree) | x), trees                                    # singleton tree    
  | trees                                                                       # empty tree

# f [] = 0
# f [a] = a
# f [b, a] s = Tree (;, a, b)
# f [c, b, a] = Tree (;, a, (;, b, c))
# : Term
rev_exps_op_semi rev_exps:Exps : !Exp =
  | rev_exps &
    | rev_exps.List.tail &
      spot, tree = rev_exps.List.head
      spot, Tree [(spot, tree), (spot, Op ';'), rev_exps_op_semi rev_exps.List.tail]
    | rev_exps.List.head

# add rev seq of exps as a sequence of steps to trees of exps
# f [] s = s
# f [a] s = a, s
# f [b, a] s = Tree (;, a, b), s
# f [c, b, a] s = Tree (;, a, (;, b, c)), s
# : Exp
rev_exps_steps rev_exps:Exps trees:Exps : Exps =
  exp = rev_exps_op_semi rev_exps.List.rev
  | exp & exp, trees
  | trees                                                                       # empty tree

exps_trees_at space:N line_exps:Exps block_trees:Exps : Exps ? Exps, Exps =
  (spot, Level space0), exps? 
    | (_, Level _? 1) exps.List.opt0 &                                                     # skip consecutive newlines
      exps_trees_at space line_exps block_trees exps

    | space0 < space &                                                          # pop, keep exps.head to keep popping
      #Type.log ((rev_exps_trees 0 line_exps block_trees).List.rev, ((spot, Level space0), exps))
      #Type.log ((spot, Level space0), exps)
      (rev_exps_trees 0 line_exps block_trees).List.rev, ((spot, Level space0), exps)

    | space0 > space &                                                        # sub-block
      block, exps2 = exps_trees_at space0 0 0 exps
      | space0 == space + 1 &                                                 # arguments        
        exps_trees_at space block.List.rev+line_exps block_trees exps2
      | # space0 == space + 2                                                 # steps
        exps_trees_at space (rev_exps_steps block.List.rev line_exps) block_trees exps2

    | # space0 == space &
      exps_trees_at space0 0 (rev_exps_trees 0 line_exps block_trees) exps # same line

  exp, exps? exps_trees_at space (exp, line_exps) block_trees exps

  ? (rev_exps_trees 0 line_exps block_trees).List.rev, []                            # line_exps == 0 if there's a trailing newline

# linear terms to tree terms
#   a$. b c$. d e -->  a (b c) (d e)
#   a$.  b c$.  d e -->  a (; (b c) (d e))
# : inner-block:*exp, remaining-exps:Terms
exps_trees_at space:N line_exps:Exps block_trees:Exps : Exps ? Exps, Exps =
  (spot, Level space0), exps? 
    | (_, Level _? 1) exps.List.opt0 &                                                     # skip consecutive newlines
      exps_trees_at space line_exps block_trees exps

    | space0 < space &                                                          # pop, keep exps.head to keep popping
      (rev_exps_trees 0 line_exps block_trees).List.rev, ((spot, Level space0), exps)

    | space0 > space &                                                        # sub-block
      block, exps2 = exps_trees_at space0 0 0 exps
      | space0 == space + 1 &                                                 # arguments        
        exps_trees_at space block.List.rev+line_exps block_trees exps2
      | # space0 == space + 2                                                 # steps
        exps_trees_at space (rev_exps_steps block.List.rev line_exps) block_trees exps2

    | # space0 == space &
      exps_trees_at space0 0 (rev_exps_trees 0 line_exps block_trees) exps # same line

  exp, exps? exps_trees_at space (exp, line_exps) block_trees exps

  ? (rev_exps_trees 0 line_exps block_trees).List.rev, []                            # line_exps == 0 if there's a trailing newline

exps_trees x:Exps : Exps = exps_trees_at 0 0 0 x . 0

# limit:  a '(' b c' )' d  -->  a (b c) d
# : inner-groups:*exp, end-exp:Exp remaining-exp:*exp
limit_exps_to groups:Exps end_char:!S : Exps ? Exps, !Spot, Exps =
  (spot, Op '('), exps?
    groups2, end_spot, exps2 = limit_exps_to 0 ')' exps                              # sub-group
    end_spot | Exp.seq_error $Fun 'missing )' groups2
    # must use end-exp with exp2_spot to calculate the largest span of positions for [glue_exp] below, e.g. x+(y + z)
    spot2 = Spot.spot2 spot end_spot
    limit_exps_to (rev_exps_trees spot2 groups2 groups) end_char exps2

  (spot, Op '['), exps?
    groups2, end_spot, exps2 = limit_exps_to 0 ']' exps
    end_spot | Exp.seq_error $Fun 'missing ]' groups2
    # [a,b] vs [a, b] vs [f x], hence invalid to append ,0 since a,b,0 but f x,0 vs (f x), 0 - fix glue_exps
    # [a, (b, c)] vs [a, b, c], hence invalid to rewrite as (list (a, (b, c))) which is the same as (list (a, b, c)) - fix associate_exps
    # [a, b] vs [(a, b)], hence list vs list1 - fix List.size groups2
    list =
      | groups2 & 
        glued = groups2.List.rev.glue_exps
        spot1 = groups2.List.head.Exp.spot.Spot.end                             # list's last element
        spot2 = Spot.spot2 spot1 end_spot                                       # list's end marker
        spot0 = Spot.spot2 spot end_spot                                        # the whole list
        spot3 = !groups2 > 1 & !glued > 1 & spot2 | spot1                       # [f a] or [(a, b)]
        #exps_spot_exp spot0 ((spot2, Nat 0), (spot3, Op ','), groups2).List.rev
        spot0, Tree [(spot2, Name 'List'), (spot2, Tree ((spot2, Nat 0), ((spot3, Op ','), groups2)).List.rev)]
        # spot0, Tree [(spot2, Name 'List'), (spot2, Tree groups2.List.rev)]
      | end_spot, Nat 0
    limit_exps_to list,groups end_char exps2 # [a,b]  =>  list (a,b)

  (spot, Op o), exps & end_char & o == end_char? groups, spot, exps

  (_, Tree s), exps?
    limit_exps_to (exps_exp (limit_exps_to 0 end_char s).0, groups) end_char exps

  exp, exps? limit_exps_to exp,groups end_char exps

  ? List.rev groups, 0, 0

limit_exps exps:Exps : Exps = limit_exps_to 0 0 exps . 0

exps_exp exps:Exps : Exp = exps.List.tail & Exp.spot_new exps.List.head, Tree exps | exps.List.head
exps_spot_exp spot:Spot exps:Exps : Exp = exps.List.tail & spot, Tree exps | exps.List.head

# left-leaning: a, b  -->  (, a b)  not  (, a) b
# right-associative: a, b, c  -->  a, (b, c)  not  (a, b), c
op_lean name:S : B = List.in S.eq [';', ',', '?'] name

# glue tight adjucent-column exps:  a b+c d  -->  a (b + c) d
# [glue] comes after [limit], else f (x + y) becomes f [(x] + [y)]
glue_exps_to groups:Exps : Exps? Exps =
  exp, exps?
    _, _, _, line0, column0 = exp.Exp.spot
    _, line11, column11, line12, column12 = exps.List.opt0.Exp.spot_new
    _, line2, column2, _ = exps.List.opt1.Exp.spot_new
    exp .      
      _ & line11 == line0 & column11 == column0 & (!((_, Op o? op_lean o) exps.0) | line2 == line12 & column2 == column12)?
        glue_exps_to (glue_exp exp, groups) exps
      _, Tree s?
        exps_exp (List.rev (exps_exp (glue_exps s), groups)), glue_exps exps
      ? exps_exp (List.rev (exp, groups)), glue_exps exps
  ? groups

glue_exps exps:Exps : Exps = glue_exps_to 0 exps

glue_exp : Exp? Exp = 
  _, Tree s? exps_exp (glue_exps s)
  a? a
  
# split a + b ^ c = [a], +, [b ^ c]  where + has a lower rank/precedence than ^
#split_exps left:Exp op:Exp rank:N right:Exp exps:Exps : left:Exps, op:Exp, right:Exps =
split_exps left:Exps op:!Exp rank:N right:Exps exps0:Exps : Exps = exps0,op .
  exp,exps, _? 
    rank2 = (_, Op o? Op.rank o) exp
    same = (_, Op o? Op.right o) exp
    | rank2 & (same & rank2 < rank | rank2 <= rank) &
      # given f x + g y = h z
      # at reading op=, x f, +, y g
      # change left to y g + x f for f x + g y reversed
      right2 = op & (op, right.List.rev) | right.List.rev
      split_exps (left.List.rev + right2).List.rev exp rank2 0 exps
    |
      split_exps left op rank exp,right exps

  _, (spot, Op op2)?
    left2 = left & exps_exp (associate_exps left.List.rev)
    right0 = right & associate_exps right.List.rev
    #right2 = right & exps_exp (associate_exps right.List.rev)
    right2 = right,right0 .
      [(_, Tree _)], [(_, Binary _ ',' _)] & op2 == ','? spot, Tree right0
      ? right & exps_exp right0
    | left & right & op2 == '|' & left2.Exp.tree .
      Binary a '&' b & !left > 1? [(spot, Tree [(spot, Name 'op_if'), a, b, right2])] # a & b | c  ->  op_if a b c
      ? [(spot, Tree [(spot, Name 'op_if0'), left2, right2])]                  # a | b  ->  op_if0 a b
    | left & right & [(spot, Binary left2 op2 right2)]                           # (a & b) | c  ->  (a & b) | c
    | left & [(spot, Post left2 op2)]
    | right & [(spot, Pre op2 right2)]

# associate by operator precedence:  a + b ^ c  -->  a + (b ^ c)
associate_exps exps:Exps : Exps = exps & (split_exps 0 0 0ffff 0 exps | exps associate_exp) # 0ffff = max precedence


associate_exp : Exp? Exp = 
  _, Tree s? exps_exp (associate_exps s)
  a? a

exps s:Exps : Exps = s.exps_trees.limit_exps.glue_exps.associate_exps

of x:S : S = x.Exp.str_exps.exps.0.Exp.str
#of x:S : S = x.Exp.str_exps.exps.0.Exp.str.Log.id
Fact (of 'a' == 'a')

Fact (of 'a+b' == '(a + b)')
Fact (of 'f a+b' == '(f (a + b))')

Fact (of 'a,b' == '(a, b)')
Fact (of 'a,b,c' == '(a, (b, c))')
Fact (of 'a,(b,c)' == '(a, ((b, c)))')
Fact (of 'x = a, b' == '(x = (a, b))')

Fact (of 'a+[b]' == '(a + (List (b, 0)))')
Fact (of '[a,b]' == '(List (a, (b, 0)))')
Fact (of '[a,b,c]' == '(List (a, (b, (c, 0))))')
Fact (of '[a,(b,c)]' == '(List (a, ((b, c), 0)))')
