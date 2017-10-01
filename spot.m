# file position, path and line and column

Spot = path:S, line1:N, column1:N, line2:N, column2:N

nil = '', 0, 0, 0, 0 : Spot

line_base = 1                                                                   # emacs starts line at 1

col_base = 1                                                                    # emacs starts column at 0 but compilation-mode moves requires +1

new path:S : Spot = path, line_base, col_base, line_base, col_base

eq path1,line11,column11,line12,column12:Spot path2,line21,column21,line22,column22:Spot : B =
  path1 == path2 & line11 == line21 & column11 == column21 & line12 == line22 & column12 == column22

end path,_,_,line,column:Spot : Spot = path, line, column, line, column
Fact (eq (end 'foo',2,3,5,8) 'foo',5,8,5,8)
  
str path,line1,column1,line2,column2:Spot : S =  
  # http://www.gnu.org/prep/standards/standards.html#index-formatting-error-messages
  # https://github.com/emacs-mirror/emacs/blob/master/etc/compilation.txt
  S.fill '$s:$n.$n-$n.$n' [path, line1, column1, line2, column2]
Fact (Spot.str 'foo',2,3,5,8 == 'foo:2.3-5.8')                                  # todo - overload Spot.str in Type

str1 path,line,column,_:Spot : S = S.fill '$s:$n.$n' [path, line, column]
Fact (str1 'foo',2,3,5,8 == 'foo:2.3')

path_line path,line,_:Spot : S = S.fill '$s:$n' [path, line]
Fact (path_line 'foo',2,3,5,8 == 'foo:2')

basic_str x:Spot : S =
  _, line1, column1, line2, column2 = x
  S.fill '$n.$n-$n.$n' [line1, column1, line2, column2]
Fact (basic_str 'foo',2,3,5,8 == '2.3-5.8')

fun _,line,_:Spot fun:S : S = S.fill '$s:$n' [fun, line]
Fact (fun 'foo',2,3,5,8 'bar' == 'bar:2')

spot2 path,line1,column1,_:Spot _,_,_,line2,column2:Spot : Spot = path, line1, column1, line2, column2
Fact (eq (spot2 'foo',2,3,5,8 'bar',13,21,34,55) 'foo',2,3,34,55)

main x:N : Spot = '__Spot.new', x, x, x, x

path path,_:Spot : S = path

unit path,_:Spot : S = S.upper (S.part path '.' | Fail.main2 'spot_unit' path)
Fact (unit 'foo',2,3,5,8 == 'Foo')

fail2 a:Spot x:S y:S : 0 = Fail.main3 a.str x y

fail3 a:Spot x:S y:S z:S : 0 = Fail.main4 a.str x y z

fail4 a:Spot x:S y:S z:S w:S : 0 = Fail.main5 a.str x y z w
