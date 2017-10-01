# assembly language, machine instruction, binary code
 
 https://en.wikipedia.org/wiki/X86-64

# a c d b sp bp si di
# rax rcx rdx rbx rsp rbp rsi rdi
register_byte : Reg ? N =
  A? 0
  C? 1
  D? 2
  B_? 3
  Sp? 4
  Bp? 5
  Si? 6
  Di? 7

  Ah? 4
  Ch? 5
  Dh? 6
  Bh? 7
    
  R8? 0
  R9? 1
  R10? 2
  R11? 3
  R12? 4
  R13? 5
  R14? 6
  R15? 7

# p486 Table A-5. rFLAGS Condition Codes for CMOVcc, Jcc, and SETcc
flag_byte : Flag ? N =
  O? 00                                                                         # int, of=1 - O (overflow)
  No? 01                                                                        # int, of=0 - No (not overflow)
  L? 02                                                                         # nat, cf=1 - B (below), C (carry), Nae (not above or equal)
  Ge? 03                                                                        # nat, cf=0 - Nb (not below), Nc (not carry), Ae (above or equal)
  E? 04                                                                         # nat, zf=1 - Z (zero), E (equal)
  Ne? 05                                                                        # nat, zf=0 Nz (not zero), Ne (not equal)
  Le? 06                                                                        # nat, (sf xor of)=1 or zf=1 - Le (less than or equal to), Ng (not greater than)
  G? 07                                                                         # nat, (sf xor of)=0 and zf=0 - Nle (not less than or equal to), G (greater than)
  S__? 08                                                                       # int, sf=1 signed
  Ns? 09                                                                        # int, sf=0 not signed
  P? 0a                                                                         # pf=1 parity, parity even
  Np? 0b                                                                        # pf=0 not parity, parity odd
  Sl? 0c                                                                        # int, (sf xor of)=1 - Le (less than), Nge (not greater than or equal to)
  Sge? 0d                                                                       # int, (sf xor of)=0 - Nle (not less than), Ge (greater than or equal to)
  Sle? 0e                                                                       # int, cf=1 | zf=1 - Be (below or equal), Na (not above)
  Sg? 0f                                                                        # int, cf=0 | cf=1 - Nbe (not below or equal), A (above)

# extended set of registers in 64-bit
register_extended : Reg?B = (R8? 1; R9? 1; R10? 1; R11? 1; R12? 1; R13? 1; R14? 1; R15? 1; R15? 1)

register_extension_prefix0 binary:Flow register1:Reg register2:Reg =
  register_extension_prefix binary 0 (register_extended register1) 0 (register_extended register2) 0

# same as register_extension_prefix0 but extend operand to 64-bit
register_extension_prefix1 binary:Flow register1:Reg register2:Reg =
  register_extension_prefix binary 1 (register_extended register1) 0 (register_extended register2) 0

register_extension_prefix binary:Flow operand:B register:B index:B base:B uniform:B =
  x = N.or (N.or (N.or (operand & 8) (register & 4)) (index & 2)) (base & 1).B.nat
  (uniform.B.nat | x) & Flow.nat0 binary (N.or 040 x)

mode_register_memory mode:N register:N memory:N : N = N.or (N.shl mode 6) (N.or (N.shl register 3) memory)

op_register operand:N register:Reg : N = mode_register_memory 3 operand (register_byte register) # file:///ref/amd64-vol3/503.pdf - mode = 0011 = 3

scale_byte : N?N = (1? 0; 2? 1; 4? 2; 8? 3)

scale_index_base scale:N index:N base:N : N = N.or (N.shl scale.scale_byte 6) (N.or (N.shl index.register_byte 3) (register_byte base))

# op:N0
op_memory_register0 code:Flow op:N register:Reg base:Reg offset:N = # f r r n, 8-bit register
  register_extension_prefix0 code register base
  op_memory code op (register_byte register) base offset

# op:N0
op_memory_register code:Flow op:N register:Reg base:Reg offset:N = # f r r n
  register_extension_prefix1 code register base
  op_memory code op (register_byte register) base offset

# op:N1
op_memory_register1 code:Flow op:N register:Reg base:Reg offset:N = # f r r n
  register_extension_prefix1 code register base
  op_memory1 code op (register_byte register) base offset

# /0 or /7 are the immediates
#   ADD reg/mem64, imm32 81 /0
#   CMP reg/mem64, imm32 81 /7
# fixme - op:N0
op_memory_immediate code:Flow op:N immediate:N base:Reg offset:N = # f r n
  register_extension_prefix1 code A base
  op_memory code op immediate base offset

# fixme - op:N0
op_memory code:Flow op:N operand:N base:Reg offset:N = # f x r n
  # Table 1-12. SIB.index and .base Field Encodings
  # Register specification is null. The scale*index portion of the indexed register-indirect effective address is set to 0. - rSP = 0b100
  scale = 1
  index = Sp # none
  mode = 2
  memory = register_byte Sp             # memory = register sp means use scale-index-base  
  sib = scale_index_base scale index base
  Flow.nat0 code op
  Flow.nat0 code (mode_register_memory mode operand memory)  
  Flow.nat0 code sib
  Flow.nat2 code offset

# fixme - op:N1
op_memory1 code:Flow op:N operand:N base:Reg offset:N = # same as [op_memory] but op:N1
  scale = 1
  index = Sp # none
  mode = 2
  memory = register_byte Sp             # memory = register sp means use scale-index-base  
  sib = scale_index_base scale index base
  Flow.nat1 code op
  Flow.nat0 code (mode_register_memory mode operand memory)  
  Flow.nat0 code sib
  Flow.nat2 code offset

# p423 - Table A-1. Primary Opcode Map (One-byte Opcodes), Low Nibble 0–7h
group1_code : Term?N = (Add? 000; And? 020; Xor? 030; Or? 008; Sub? 028; Cmp? 038) # add adc and xor or sbb sub cmp
group1_tag : Term?B = (Add? 1; And? 1; Xor? 1; Or? 1; Sub? 1; Cmp? 1)
group1_byte : Term?N = (Add? 0; Or? 1; And? 4; Sub? 5; Xor? 6; Cmp? 7) 
group2_byte : Term?N = (Shl? 4; Shr? 5)

symbols = 0100_000.Hash : name:S / offset:N

labels = 0100_000.Hash : name:S / offset:N
label_bases = %0 : %*(Spot, rank:N, base:N, name:S, offset:N)
label_spans = %0 : %*(Spot, rank:N, name1:S, name2:S, offset:N)
label_relatives = %0 : %*(Spot, name:S, offset:N)

# terms to binary machine code
terms_binary terms:Terms spot:Spot opt_wide:!N code:Flow data:Flow = terms .
  Nat n, x & x & x.0 != Base?                                     # wide/rank
    terms_binary x spot n.N.opt code data
  ? !terms .
    0? 0
    1? term1_binary terms.0 spot opt_wide code data
    2? term2_binary terms.0 terms.1 spot opt_wide code data  
    3? term3_binary terms spot opt_wide code data  
    4? term4_binary terms spot opt_wide code data  
    ? Fail.main3 (Spot.str spot) $Fun terms.Term.seq_str

term1_binary term:Term spot:Spot opt_wide:!N code:Flow data:Flow = term .
  Ret? Flow.nat0 code 0c3                                                       
  Syscall? Flow.nat1 code 050f  
  Rdtsc? Flow.nat1 code 0310f  
  Cpuid? Flow.nat1 code 0a20f

  # Improves the performance of spin loops, by providing a hint to the processor that the current code is in a spin loop. The processor may use this to optimize power consumption while in the spin loop.
    Architecturally, this instruction behaves like a NOP instruction.
    Processors that do not support PAUSE treat this opcode as a NOP instruction.
  Pause? Flow.nat1 code 090f3
  
  Nat n? Flow.nat code n (opt_wide & N.must opt_wide | N.rank n)             # n
  
  Mem n,s? Flow.mem code n s                                                    
  
  Str s? Flow.str_pad code s (opt_wide & N.must opt_wide | !s)         # s, todo - check if s is longer than opt_wide

  Name x?                                                                       # X
    rank = Opt.or opt_wide 3                                                    # 64-bit by default
    # base = 0 because only used for labels in main.m - File, Code_vmaddr, Data_vmaddr, Data_size, Code_end, Bind
    Ref.seq_add label_bases spot,rank,0,x,code.Flow.size
    Flow.nat code 0 rank                                                        # patched by label_fix_base
    
  ? Fail.main4 (Spot.str spot) $Fun term.str term.Term.tag.N.str

last_label = %'' : %S

count = %0 : %N

count2 = %0 : %N

_debug = Env.bit 'asm' : B

term2_binary term1:Term term2:Term spot:Spot opt_wide:!N code:Flow data:Flow = term1,term2 .
  Label, Name x?                                                            # @X    
    Hash.set labels x code.Flow.size                                           # see CODE_DATA_OFFSET
    n = Any.code_vmaddr+code.Flow.size
    S.char x != \_ &                                                            # skip _Else* and _Done*
      Trap.bit & last_label x
      _debug & Debug.fill '$s$,$h$,$n' [x, n, n]
  
  Push, Reg r?                                                                  # push r - PUSH reg64 50 +rq
    register_extension_prefix1 code A r                                     
    Flow.nat0 code (050 + register_byte r)

  Pop, Reg r?                                                                   # pop r - POP reg64 58 +rq 
    register_extension_prefix1 code A r                                     
    Flow.nat0 code (058 + register_byte r)

  Push, Nat n?                                                                  # push n2 - PUSH imm64 68 id
    | opt_wide == 0 &
      I.rank n <= 2 | Fail.main4 (Spot.str spot) $Fun 'push n2' n.Hex.str
      Flow.nat0 code 068
      Flow.nat2 code n
    | opt_wide == 1 &
      Flow.nat0 code 06a                                                        # push n0 - PUSH imm8 6A ib 
      Flow.nat0 code n
    | Fail.main4 (Spot.str spot) $Fun 'push n' opt_wide.N.str
  
  Push, Str s?                                                                  # push s - PUSH imm64 68 id
    Flow.nat0 code 068
    # Asm.UNIQUE_STRING_LITERAL
    # 49% = 1099 / (1099+1136.) of all symbols
    # 99.1% 517752/522517., or 99.6% 1143864/1148629. with trap - min binary sie
    new, offset = Hash.get_set symbols s Any.data_vmaddr+data.Flow.size          # need code_vmaddr offset? see CODE_DATA_OFFSET
    new & Ref.tick count | Ref.tick count2
    Flow.nat2 code offset
    new & Flow.str0 data s

  Neg, Reg r?                                                                   # neg r - NEG reg/mem64, F7/3
    register_extension_prefix1 code A r
    Flow.nat0 code 0f7
    Flow.nat0 code (op_register 3 r)

  Mul, Reg r?                                                                   # mul r - MUL reg/mem64 F7 /4
    register_extension_prefix1 code A r
    Flow.nat0 code 0f7
    Flow.nat0 code (op_register 4 r)

  _, Reg r & group2_byte term1.Term.tag?                                        # shl r - shl reg/mem64, CL D3 /4
    register_extension_prefix1 code A r
    Flow.nat0 code 0d3
    Flow.nat0 code (op_register (group2_byte term1.Term.tag) r)

  J, Name x?                                                                    # j X - JMP rel32off E9 cd
    Flow.nat0 code 0e9
    Ref.seq_add label_relatives spot,x,code.Flow.size
    Flow.nat2 code 0

  Call, Name x?                                                                 # call X - CALL rel32off E8 id
    Flow.nat0 code 0e8
    Ref.seq_add label_relatives spot,x,code.Flow.size
    Flow.nat2 code 0
    n = Any.code_vmaddr + code.Flow.size
    Call.add spot n !last_label x
    _debug & Info.fill '$s$,$s$,$s$,$h$,$n' [Spot.str1 spot, !last_label, x, n, n] # todo - out x's address

  Call, Reg r?                                                                  # call r - CALL reg/mem64 FF /2
    register_extension_prefix1 code A r
    Flow.nat0 code 0ff
    Flow.nat0 code (op_register 2 r)

  Push, Name x?                                                                 # push X - PUSH imm64 68 id
    Flow.nat0 code 068
    # rank = 2: Push a sign-extended 32-bit immediate value onto the stack.
    # todo - use move for 64-bit immediates
    Ref.seq_add label_bases spot,2,Any.code_vmaddr,x,code.Flow.size             # PUSH_NAME - see CODE_DATA_OFFSET
    Flow.nat2 code 0

  ? Fail.main5 (Spot.str spot) $Fun term1.str term2.str term2.Term.tag.N.str
      
term3_binary terms:Terms spot:Spot opt_wide:!N code:Flow data:Flow = terms.0,terms.1,terms.2 .
  # x=`/usr/bin/mktemp -t ''`; { echo bits 64; echo 'movq rax, xmm0'; } > $x; nasm -f bin -o /dev/stdout $x | ndisasm -b 64 -
  Mov, Reg A, Reg Xmm0?                                                            # 66480F7EC0  movq rax,xmm0
    Flow.nat0 code 066
    Flow.nat0 code 048
    Flow.nat0 code 00f
    Flow.nat0 code 07e
    Flow.nat0 code 0c0

  # x=`/usr/bin/mktemp -t ''`; { echo bits 64; echo 'movq xmm1, rax'; } > $x; nasm -f bin -o /dev/stdout $x | ndisasm -b 64 -
  Mov, Reg Xmm1, Reg A?                                                            # 00000000  66480F6EC8        movq xmm1,rax
    Flow.nat0 code 066
    Flow.nat0 code 048
    Flow.nat0 code 00f
    Flow.nat0 code 06e
    Flow.nat0 code 0c8

  # x=`/usr/bin/mktemp -t ''`; { echo bits 64; echo 'movq xmm0, rax'; } > $x; nasm -f bin -o /dev/stdout $x | ndisasm -b 64 -
  Mov, Reg Xmm0, Reg A?                                                            # 66480F6EC0        movq xmm0,rax  
    # Flow.mem code 0_66480f6ec0
    Flow.nat0 code 066
    Flow.nat0 code 048
    Flow.nat0 code 00f
    Flow.nat0 code 06e
    Flow.nat0 code 0c0
    
  Mov, Reg r, Nat n?                                                            # mov r n - MOV reg64, imm64
    register_extension_prefix1 code A r
    Flow.nat0 code (0b8 + register_byte r)
    Flow.nat3 code n                                                            # 64-bit immediate, only to register, not memory

  # [set] sets/clears only the lower 8-bit
  # Checks the status flags in the rFLAGS register and, if the flags meet the condition specified in the mnemonic (cc),
  # sets the value in the specified 8-bit memory location or register to 1. If the flags do not meet the specified condition, SETcc clears the memory location or register to 0.
  Set_, Flag f, Reg r?                                                                   # sete r - 0F94/0 - SETE reg/mem8 - Set byte if equal (ZF = 1).
    Flow.nat0 code 0f
    Flow.nat0 code (090 + flag_byte f)
    Flow.nat0 code (op_register 0 r)
    
  _, Reg r, Nat n & group1_tag terms.0.Term.tag?                                         # add r n - ADD reg/mem64, imm32 81 /0 id Add sign-extended imm32 to reg/mem64
    register_extension_prefix1 code A r
    Flow.nat0 code 081
    Flow.nat0 code (op_register terms.0.Term.tag.group1_byte r)
    Flow.nat2 code n

  _, Reg r, Reg s & group1_tag terms.0.Term.tag? # add r r - ADD reg/mem64, reg64 01 /r
    register_extension_prefix1 code s r
    Flow.nat0 code (terms.0.Term.tag.group1_code + 01)
    Flow.nat0 code (op_register (register_byte s) r)
    
  Nat n, Base, Name x?                                                         # n + X, main.ma - 01000+Main0
    rank = Opt.or opt_wide 3                                                    # 64-bit by default
    Ref.seq_add label_bases spot,rank,n,x,code.Flow.size
    Flow.nat code 0 rank                                                        # patched by label_fix_base

  Name x, Span, Name y?                          # X, Y
    rank = Opt.or opt_wide 3                                                    # 64-bit by default
    Ref.seq_add label_spans spot,rank,x,y,code.Flow.size
    Flow.nat code 0 rank                                                        # patched by label_fix_span

  Push, Reg r, Nat n?                                                          # push r n - PUSH reg/mem64 FF /6
    op_memory_immediate code 0ff 6 r n
    
  Mul, Reg r, Nat n?                                                            # mul r n - MUL reg/mem64 F7 /4
    op_memory_immediate code 0f7 4 r n                                          

  Div, Reg r, Nat n?                                                            # div r n - DIV reg/mem64 F7 /6 (unsigned), signed div IDIV reg/mem64 F7 /7
    op_memory_immediate code 0f7 6 r n                                          

  Shl, Reg r, Nat n?                                                            # shl r n - SHL reg/mem64, imm8 C1 /4 ib
    register_extension_prefix1 code A r
    Flow.nat0 code 0c1
    Flow.nat0 code (op_register 4 r)
    Flow.nat0 code n

  J, Nat n, Name x?                          # j n X - JO rel32off  0F 80 cd
    Flow.nat0 code 0f
    Flow.nat0 code (080 + n)
    Ref.seq_add label_relatives spot,x,code.Flow.size 
    Flow.nat2 code 0

  J, Flag f, Name x?                         # j flag X - JO rel32off  0F 80 cd
    Flow.nat0 code 0f
    Flow.nat0 code (080 + flag_byte f)
    Ref.seq_add label_relatives spot,x,code.Flow.size 
    Flow.nat2 code 0

  Call, Reg r, Nat n?                        # call r n - CALL reg/mem64 FF /2
    op_memory_immediate code 0ff 2 r n

  Mov, Reg r, Name x?                        # mov r X - MOV reg64, imm64 B8 +rq iq 
    register_extension_prefix1 code A r
    Flow.nat0 code (0b8 + register_byte r)    
    base = S.has x \. & Any.code_vmaddr | 0 # hack - main.ma has no unit - Code_vmaddr, Data_vmend
    Ref.seq_add label_bases spot,3,base,x,code.Flow.size                        # MOVE_NAME - see CODE_DATA_OFFSET
    Flow.nat3 code 0

  Mov, Reg r, Reg s?                         # mov r r - MOV reg64, reg/mem64 8B /r
    register_extension_prefix1 code r s
    Flow.nat0 code 08b
    Flow.nat0 code (op_register (register_byte r) s)

  Movsx, Reg r, Reg s?                         # movsx r r - MOVSX reg64, reg/mem8 0F BE/r
    register_extension_prefix1 code r s
    Flow.nat1 code 0be0f
    Flow.nat0 code (op_register (register_byte r) s)

  New, Name x, Nat n?                        # $X n - same as push s below
    # CODE_DATA_OFFSET - 
    # - labels in main.ma are absolute
    # - code labels by step.m are off by code_vmaddr, due to PAGE_ZERO
    # - data labels by step.m are absolute from data_vmaddr
    # hence, -code_vmaddr here and base=code_vmaddr in PUSH_NAME and MOVE_NAME above
    Hash.set labels x (Any.data_vmaddr - Any.code_vmaddr + data.Flow.size)
    Flow.nat3 data n        

  New, Name x, Real r?                        # $X r - same as $X n above
    Hash.set labels x (Any.data_vmaddr - Any.code_vmaddr + data.Flow.size)
    Flow.nat3 data r.R.nat
      
  ? Fail.main3 (Spot.str spot) $Fun terms.Term.seq_str

# 1.2.2 Operand-Size Override Prefix
# The operand-size override prefix (66h) selects the non-default operand size.
operand_size_override code:Flow = Flow.nat0 code 066

term4_binary terms:Terms spot:Spot opt_wide:!N code:Flow data:Flow = terms.0,terms.1,terms.2,terms.3 .
  Mov, Reg r, Reg s, Nat n?      # mov r r n - MOV reg64, reg/mem64 8B /r
    | N.must opt_wide == 0 &
      op_memory_register0 code 08a r s n                            # 0 mov r r n - MOV reg8, reg/mem8 8A /r
    | op_memory_register code 08b r s n 

  Lea, Reg r, Reg s, Nat n?                                                     # lea r r n - LEA reg64, mem 8D /r
    op_memory_register code 08d r s n
    
  _, Reg r, Reg s, Nat n & group1_tag terms.0.Term.tag?                         # add r r n - ADD reg64, reg/mem64 03 /r
    op_memory_register code (group1_code terms.0.Term.tag + 03) r s n

  Mov, Reg r, Nat m, Nat n?                                                     # mov r n n - MOV reg/mem64, imm32 C7 /0 id
    op_memory_immediate code 0c7 0 r m
    Flow.nat2 code n

  # 0 mov r n r - MOV reg/mem8, reg8 88 /r
  # mov r n r - MOV reg/mem16, reg16 89 /r 
  # mov r n r - MOV reg/mem32, reg32 89 /r 
  # mov r n r - MOV reg/mem64, reg64 89 /r 
  Mov, Reg r, Nat n, Reg s? Opt.or opt_wide 3 .
    0? op_memory_register0 code 088 s r n
    1? (operand_size_override code; op_memory_register0 code 089 s r n)
    2? op_memory_register0 code 089 s r n
    3? op_memory_register code 089 s r n
    m? Fail.main3 (Spot.str spot) ($Fun + ' invalid wide ' + m.N.str) terms.Term.seq_str

  # XCHG reg/mem64, reg64, 87 /r
  # Exchange the contents of a 64-bit register with the contents of a 64-bit register or memory operand.
  # If either operand references memory, the processor locks automatically, whether or not the LOCK prefix is used and independently of the value of IOPL.
  Xchg, Reg r, Nat n, Reg s?                                                    # xchg r n r
    op_memory_register code 087 s r n

  # CMPXCHG reg/mem64, reg64 - 0F B1 /r
  # Compare RAX register with a 64-bit register or memory location. If equal, copy the second operand to the first operand. Otherwise, copy the first operand to RAX.
  Cmpxchg, Reg r, Nat n, Reg s?                                                    # xchg r n r
    op_memory_register1 code 0b10f s r n
  
  _, Reg r, Nat m, Nat n & group1_tag terms.0.Term.tag?  # add r n n - ADD reg/mem64, imm32 81 /0 id - Add sign-extended imm32 to reg/mem64.
    op_memory_immediate code 081 (group1_byte terms.0.Term.tag) r m                 # CMP reg/mem64, imm32 81 /7 id 
    Flow.nat2 code n

  # add r n r
  #   ADD reg/mem64, reg64 01 /r - Add reg64 to reg/mem64.
  #   SUB reg/mem64, reg64 - 29 /r - Subtract the contents of a 64-bit register from a 64-bit destination register or memory location. 
  _, Reg r, Nat n, Reg s & group1_tag terms.0.Term.tag?
    op_memory_register code 1+(group1_code terms.0.Term.tag) s r n
        
  ? Fail.main3 (Spot.str spot) $Fun terms.Term.seq_str

step_binary code:Flow data:Flow step:Step =
  spot, terms = step
  terms_binary terms spot 0 code data

terms_binary_out terms:Terms =
  code = Flow 010000
  data = Flow 010000
  terms_binary terms (Spot 0) 0 code data
  Flow.out code
  Flow.out data

label_get spot:Spot label:S : N =
  s = Hash.pair labels label
  s & s.Row.at2_1 | Fail.main3 spot.Spot.str $Fun label                 # fixme - hash type for s.1

Base = Spot, N, N, S, N # spot, wide, base, name, key
label_fix_base code:S label_base:Base =
  spot, wide, base, name, key = label_base
  S.set_rank code+key base+(label_get spot name) wide

Span = Spot, N, S, S, N
label_fix_span code:S label_span:Span =
  spot, wide, name1, name2, key = label_span
  S.set_rank code+key (label_get spot name2)-(label_get spot name1) wide

Relative = Spot, S, N
label_fix_relative code:S label_relative:Relative =
  spot, name, key = label_relative
  Mem.set2 (code + key).S.mem (label_get spot name)-key-4

steps_binary_out steps:Steps pad:B =
  code = Flow 01000000 # Code,Code_end 16MB
  data = Flow 01000000 # Data,Data_end 16MB
  Seq.do (step_binary code data) steps
  Hash.set labels 'Call_head' Any.data_vmaddr+data.Flow.size
  Call.add_flow data
  # https://en.wikipedia.org/wiki/Data_structure_alignment#Computing_padding
  pad & Flow.add code (N.and -code.Flow.size 0fff)                             # align 4096-byte for page
  Hash.set labels 'Code_vmaddr' Any.code_vmaddr
  Hash.set labels 'Code_end' code.Flow.size
  Hash.set labels 'Code_vmend' Any.code_vmaddr+code.Flow.size
  Hash.set labels 'Data_vmaddr' Any.data_vmaddr
  Hash.set labels 'Data_size' data.Flow.size
  Hash.set labels 'Data_vmend' Any.data_vmaddr+data.Flow.size
  Hash.set labels 'Call_size' (List.size !Call.rows)
  _debug & Debug.fill '$s$,$h$,$n' ['Code_vmend', Any.code_vmaddr+code.Flow.size, Any.code_vmaddr+code.Flow.size]
  _debug & Debug.fill '$s$,$h$,$n' ['Data_vmend', Any.data_vmaddr+data.Flow.size, Any.data_vmaddr+data.Flow.size]
  List.do !label_bases (label_fix_base code.Flow.head)
  List.do !label_spans (label_fix_span code.Flow.head)
  List.do !label_relatives (label_fix_relative code.Flow.head)
  Flow.out code
  Flow.out data

file_steps_binary_out file:File pad:B = steps_binary_out file.Step.of_file pad
