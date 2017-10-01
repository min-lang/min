# real, floating-point number

  https://en.wikipedia.org/wiki/IEEE_floating_point
  https://en.wikipedia.org/wiki/Scientific_notation  
  http://docs.oracle.com/cd/E19957-01/806-3568/ncg_goldberg.html What Every Computer Scientist Should Know About Floating-Point Arithmetic

of x:S : R = Fun.call_nr Dl'atof' x
Fact (of '3.1415' == 04009_21ca_c083_126f.N.real)
Fact (of '3.1415' . Cast.real_bits == 04009_21ca_c083_126f)
Fact (of '3.14' == 3.14)

of3 x:S y:S z:S : R = S.fill '$s.$se$s' [x, y, z] . of

of_exp x:S y:S : R = S.fill '$se$s' [x, y] . of

of2 x:N y:N : R = of (S.add3 x.N.str '.' y.N.str)
Fact (of2 3 14 == 3.14)

# http://www.cplusplus.com/reference/cstdlib/strtod/
strtod x:S : R = Fun.call1 Dl'strtod' x

floor x:R : N = Fun.call1 Dl'floor' x

epsilon = 0.00001 : R

mod x:R y:R : R = Fun.call_rrr Dl'fmod' x y
Fact (mod 5. 2. == 1.)

abs x:R : R = Fun.call_rr Dl'fabs' x 
Fact (abs 2. == 2.)

sub x:R y:R : R = Asm
  0'f20f10442410 f20f5c442408 f20f11442418'
  ret
Fact (5. - 2. == 3.)

add x:R y:R : R = Asm
  0'f20f10442410 f20f58442408 f20f11442418'
  ret
Fact (5. + 2. == 7.)

neg x:R : R = Asm
  0'b800000000 66480f6ec0 f20f5c442408 f20f11442410'
  ret
Fact (neg 5. == 0. - 5.)

mul x:R y:R : R = Asm
  0'f20f10442410 f20f59442408 f20f11442418'
  ret
Fact (5.*2. == 10.)

div x:R y:R : R = Asm
  0'f20f10442410 f20f5e442408 f20f11442418'
  ret
Fact (5. / 2. == 2.5)

lt x:R y:R = Asm
  0'f20f10442410 f20fc244240801 f20f11442418'
  ret
Fact (2. < 5.)
Fact !(5. < 2.)

# https://docs.python.org/3/library/math.html#math.isclose
sim x:R y:R : B = abs (x - y) < epsilon
close x:R y:R : B = abs (x - y) < epsilon
Fact (close 3.141592 3.141593) # 3.141592653589793
Fact (close 3.141592 _1000_0000_0001_0010_0100_0011_1111_0101_1111_1001_0001_0110_0000_0000_1111_010.N.real)
Fact !(close 3.14159 3.14)
Fact !(close 4. 2.)
Fact !(close 2. 4.)
Fact (3.141592 ≈ 3.141593)

log x:R : R = Fun.call_rr Dl'log' x
Fact (close (log 2.) 0.6931471805599453)

# https://software.intel.com/en-us/node/522659 Exponential Functions
exp x:R : R = Fun.call_rr Dl'exp' x
Fact (exp 1. . str == '2.71828') # import math; '%g' % math.exp(1)

ℯ = exp 1. : R
Fact (close ℯ 2.71828)
Fact (close ℯ^2. 7.38906)
  
cos x:R : R = Fun.call_rr Dl'cos' x
Fact (cos 0 == 03ff0_0000_0000_0000.N.real) # 1.0
Fact (cos 3.14 == 0bfef_fffd_5719_f5d7.N.real) # -0.9999987317275395

nat x:R : N = Cast.real_bits x

lib_printf = 'printf'.Dl : Z? Z

sprintf1f_raw f:0 out:S format:S x:1 = Asm
  mov r11 sp 32  
  mov di sp 24
  mov si sp 16
  mov a sp 8
  mov xmm0 a
  mov bp sp 
  and sp 0ffff_fff0
  mov a 1                               # num of parameters in xmms 
  call r11
  mov sp bp 
  ret

str9 x:R : S = (y = S.new 10; sprintf1f_raw S.lib_sprintf y '%.9g' x; y)        # 9 significant digits + dot
Fact (3.141592653589793.str9 == '3.14159265') # import math; '%.g' % math.pi

str x:R : S = (y = S.new 7; sprintf1f_raw S.lib_sprintf y '%g' x; y) # default 6 significant digits + dot
Fact (str 3.141592653589793 == '3.14159') # import math; '%g' % math.pi
Fact ('3.1415'.of.str == '3.1415')
Fact (3.1415.str == '3.1415')
  
# https://en.wikipedia.org/wiki/Error_function error
erf x:R : R = Fun.call_rr Dl'erf' x # import math; math.erf(1) == 0.842700792949715
Fact(close (erf 1.) 0.842700793) # 03fea_f767_a741_088a

erfc x:R : R = Fun.call_rr Dl'erfc' x # import math; math.erf(1) == 0.842700792949715

#
  import struct; hex(struct.unpack('>Q', struct.pack('>d', math.pi))[0]) # 0x400921fb54442d18
  import struct; hex(struct.unpack('>Q', struct.pack('>d', 3.1415))[0]) # 0x400921cac083126f
    # 1000_0000_0001_0010_0100_0011_1111_0101_1111_1001_0001_0110_0000_0000_1111_010
    import struct; '_'.join(map(''.join, re.findall('....?', bin(struct.unpack('>Q', struct.pack('>d', 3.141592))[0])[2:]))) 
  import struct; hex(struct.unpack('>I', struct.pack('>f', 3.1415))[0]) # 0x40490e56
  import struct; hex(struct.unpack('>I', struct.pack('>f', math.pi))[0]) # 0x40490fdb
  import struct; hex(struct.unpack('>I', struct.pack('>f', 1))[0]) # 0x3f800000
π = 3.14159265358979323846264338327950288 # 04009_21fb_5444_2d18
Fact (π ≈ 3.14159) # pi

pow x:R y:R : R = Fun.call_rrr Dl'pow' x y
Fact (close (pow 3.14 0.5) 1.772)
Fact (close 3.14^0.5 1.772)

#
  https://en.wikipedia.org/wiki/NaN
  non = 0_111_1111
  +inf  07ff0_0000_0000_0000
  -inf  0fff0_0000_0000_0000
  nan   07ff0_ffff_ffff_ffff 

√ x:R : R = Fun.call_rr Dl'sqrt' x
Fact (close √3.14 1.772)
Fact (close 2.√π 3.5449077018110318)    # 2*math.sqrt(math.pi)

# https://en.wikipedia.org/wiki/Cumulative_distribution_function cumulative normal distribution
cdf x:R : R = ½ * erfc(-√½ * x)
ϕ x:R : R = ½ * erfc(-√½ * x)
Fact (close (ϕ 1.) 0.84134474606854293) # from scipy.stats import norm; norm.cdf(1)

# http://www.cygnus-software.com/papers/comparingfloats/Comparing%20floating%20point%20numbers.htm
# https://docs.oracle.com/javase/8/docs/api/java/lang/Double.html#equals-java.lang.Object-
# https://en.wikipedia.org/wiki/Machine_epsilon
# http://floating-point-gui.de/errors/comparison/
eq x:R y:R : B = N.eq x.nat y.nat
