# mach object file format for mac executables
# https://en.wikipedia.org/wiki/Mach-O

@File
0feedfacf                               # uint32_t magic, mach magic number identifier = MH_CIGAM_64 0xCFFAEDFE, Constant for the magic field of the mach_header_64 (64-bit architectures)
2 01000007                              # cpu_type_t cputype = CPU_TYPE_X86_64 = CPU_TYPE_X86 | CPU_ARCH_ABI64
2 080000003                             # cpu_subtype_t cpusubtype = CPU_SUBTYPE_X86_64_ALL | CPU_SUBTYPE_LIB64 0x80000000
2 2                                     # uint32_t filetype = MH_EXECUTE, demand paged executable file
2 9                                     # uint32_t ncmds, number of load commands HARDCODED - @Seg_zero @Seg_code @Thread @Seg_data @Dyld_info @Linker @Lib @Dysymtab (todo @Symtab)
2 Command,Command_end                   # uint32_t sizeofcmds, the size of all the load commands
2 085                                     # NOUNDEFS DYLDLINK TWOLEVEL # no PIE, otool -htdVflvIG /usr/bin/true | head
2 0                                     # uint32_t reserved

@Command
@Seg_zero                               # required by OSX 10.10 enforce_hard_pagezero = TRUE in xnu-2782.1.97/bsd/kern/mach_loader.c
2 019                                   # uint32_t cmd, LC_SEGMENT_64	0x19, 64-bit segment of this file to be mapped
2 Seg_zero,Seg_zero_end                 # uint32_t cmdsize, includes sizeof section_64 structs, 048
16 '__PAGEZERO'                         # char segname[16], segment name, /ref/xnu-2050.18.24/bsd/kern/mach_loader.c - vm_map_has_hard_pagezero(map, 0x1000) == FALSE
3 0                                     # uint64_t vmaddr, memory address of this segment
3 01000                                 # uint64_t vmsize, memory size of this segment. always one page = 01000
3 0                                     # uint64_t fileoff, file offset of this segment, page-aligned
3 0                                     # uint64_t filesize, amount to map from the file
2 0                                     # vm_prot_t maxprot, none
2 0                                     # vm_prot_t initprot, none
2 0                                     # uint32_t nsects, number of sections in segment
2 0                                     # uint32_t flags, flags
@Seg_zero_end

# since mac os x 10.12 sierra, /ref/dyld-433.5/src/ImageLoaderMachO.cpp checks dyld - malformed mach-o image: __LINKEDIT has fileoff==0 which overlaps mach_header
# LC_COMMAND index=1 must be __LINKEDIT for @Bind below: BIND_OPCODE_SET_SEGMENT_AND_OFFSET_ULEB(0x01, 0x00000000)
@Seg_link                               # required by OSX 10.10 enforce_hard_pagezero = TRUE in xnu-2782.1.97/bsd/kern/mach_loader.c
2 019                                   # uint32_t cmd, LC_SEGMENT_64	0x19, 64-bit segment of this file to be mapped
2 Seg_link,Seg_link_end                 # uint32_t cmdsize, includes sizeof section_64 structs, 048
16 '__LINKEDIT'                         # char segname[16], segment name, /ref/xnu-2050.18.24/bsd/kern/mach_loader.c - vm_map_has_hard_pagezero(map, 0x1000) == FALSE
3 Code_vmend                            # uint64_t vmaddr, memory address of this segment
3 01000                                 # uint64_t vmsize, memory size of this segment. always one page = 01000
3 Code_end                              # uint64_t fileoff, file offset of this segment, page-aligned
3 010                                   # uint64_t filesize, amount to map from the file. # 16 bytes per nlist_64 in /ref/xnu/EXTERNAL_HEADERS/mach-o/nlist.h
2 7                                     # vm_prot_t maxprot, none
2 7                                     # vm_prot_t initprot, none
2 0                                     # uint32_t nsects, number of sections in segment
2 0                                     # uint32_t flags, flags
@Seg_link_end

@Seg_code
2 019                                   # uint32_t cmd, LC_SEGMENT_64	0x19, 64-bit segment of this file to be mapped
2 Seg_code,Seg_code_end                 # uint32_t cmdsize, includes sizeof section_64 structs, 098
16 '__TEXT'                             # usually __TEXT, char segname[16], segment name

3 01000                                 # uint64_t vmaddr, memory address of this segment, after Seg_zero = 0x1000
3 File,Code_end                         # uint64_t vmsize, memory size of this segment - see Code_end in Asm.steps_binary_out
3 File                                  # uint64_t fileoff, file offset of this segment, page-aligned, 0
3 File,Code_end                         # uint64_t filesize, amount to map from the file

2 7                                     # vm_prot_t maxprot, maximum VM protection = x_r, w for dldy updating @Dl_sym
2 7                                     # vm_prot_t initprot, initial VM protection = x_r
2 1                                     # uint32_t nsects, number of sections in segment
2 0                                     # uint32_t flags, flags

16 ''                                   # usually __text, char sectname[16], name of this section
16 ''                                   # usually __TEXT, char segname[16], segment this section goes in
3 0                                     # uint64_t addr, memory address of this section
3 0                                     # uint64_t size, size in bytes of this section
2 0                                     # uint32_t offset, file offset of this section
2 0                                     # uint32_t align, section alignment (power of 2)
2 0                                     # uint32_t reloff, file offset of relocation entries
2 0                                     # uint32_t nreloc, number of relocation entries
2 0                                     # optional, can be 0 - uint32_t flags, flags (section type and attributes), S_ATTR_PURE_INSTRUCTIONS
2 0                                     # uint32_t reserved1, reserved (for offset or index)
2 0                                     # uint32_t reserved2, reserved (for count or sizeof)
2 0                                     # uint32_t reserved3, reserved
@Seg_code_end

@Thread
2 5                                     # uint32_t cmd, LC_UNIXTHREAD, todo for Mountain Lion: LC_MAIN
2 Thread,Thread_end                     # uint32_t cmdsize, 184
2 4                                     # /ref/xnu/osfmk/mach/i386/thread_status.h x86_THREAD_STATE64
2 42                                    # sizeof _STRUCT_X86_THREAD_STATE64 / sizeof uint32_t
3 0                                     # # /ref/xnu/osfmk/mach/i386/_structs.h rax eax ax ah al
# dyld seems to ignore registers other than rip: /ref/dyld/src/ImageLoaderMachO.cpp void* entry = (void*)(registers->rip + fSlide);
3 0                                     # rbx
3 0                                     # rcx
3 0                                     # rdx
3 0                                     # rdi
3 0                                     # rsi
3 0                                     # rbp
3 0                                     # rsp
3 0                                     # r8
3 0                                     # r9
3 0                                     # r10
3 0                                     # r11
3 0                                     # r12
3 0                                     # r13
3 0                                     # r14
3 0                                     # r15
3 01000+Code                            # rip Code_vmaddr+Code
3 0                                     # rflags
3 0                                     # cs
3 0                                     # fs
3 0                                     # gs
@Thread_end

@Seg_data
2 019                                   # uint32_t cmd, LC_SEGMENT_64	0x19, 64-bit segment of this file to be mapped
2 Seg_data,Seg_data_end                 # uint32_t cmdsize, includes sizeof section_64 structs
16 '__DATA'                             # usually __data, char segname[16], segment name
3 Data_vmaddr                           # uint64_t vmaddr, memory address of this segment, 02000 in post-min.m
3 0400000000                            # uint64_t vmsize, memory size of this segment, 16GB - FIXME - small data model allows only +/-2GB for mov reg/mem
3 Code_end                              # uint64_t fileoff, file offset of this segment
3 Data_size                             # uint64_t filesize, amount to map from the file
2 7                                     # vm_prot_t maxprot, maximum VM protection = xwr for Fun_1/Fun_2, else: Bus error: 10
2 7                                     # vm_prot_t initprot, initial VM protection = xwr
2 1                                     # uint32_t nsects, number of sections in segment
2 0                                     # uint32_t flags, flags

16 ''                                   # usually __data, char sectname[16], name of this section
16 ''                                   # usually __Data, char segname[16], segment this section goes in
3 0                                     # uint64_t addr, memory address of this section
3 0                                     # uint64_t size, size in bytes of this section, 1GB
2 0                                     # uint32_t offset, file offset of this section
2 0                                     # uint32_t align, section alignment (power of 2)
2 0                                     # uint32_t reloff, file offset of relocation entries
2 0                                     # uint32_t nreloc, number of relocation entries
2 0                                     # uint32_t flags, flags (section type and attributes), S_REGULAR
2 0                                     # uint32_t reserved1, reserved (for offset or index)
2 0                                     # uint32_t reserved2, reserved (for count or sizeof)
2 0                                     # uint32_t reserved3, reserved
@Seg_data_end

@Dyld_info
2 022                                                                           #define	LC_DYLD_INFO 	0x22	/* compressed dyld information */
2 Dyld_info,Dyld_info_end                                                       # cmdsize
2 0
2 0
2 Bind                                                                          # bind_off relative to _LINKEDIT
2 Bind,Bind_end                                                                 # bind_size
2 0
2 0
2 0
2 0
2 0
2 0
@Dyld_info_end

@Linker                                 
2 0e                                    # /ref/xnu/EXTERNAL_HEADERS/mach-o/loader.h #define LC_LOAD_DYLINKER 0xe	/* load a dynamic linker */
2 Linker,Linker_end                     # uint32_t cmdsize, includes sizeof section_64 structs
2 Linker,Linker_name
@Linker_name
'/usr/lib/dyld'; 0
6 ''  # otool -l min: objdump: 'min': truncated or malformed object (load command 6 cmdsize not a multiple of 8)
@Linker_end

# /usr/include/mach-o/loader.h: struct dylib 
@Lib
2 0c                                    # #define	LC_LOAD_DYLIB	0xc	/* load a dynamically linked shared library */
2 Lib,Lib_end                           # uint32_t cmdsize, includes sizeof section_64 structs, 048
2 Lib,Lib_name
2 0                                     # timestamp, time stamp 0 Wed Dec 31 16:00:02 1969
2 0                                     # current_version
2 0                                     # compatibility_version

@Lib_name
'/usr/lib/libSystem.B.dylib'; 0         
5 ''
@Lib_end

# else, /ref/dyld-433.5/src/ImageLoaderMachO.cpp dyld - malformed mach-o image: missing LC_DYSYMTAB
@Dysymtab
2 0b                                    # #define	LC_DYSYMTAB	0xb	/* dynamic link-edit symbol table info */
2 80
72 ''
@Dysymtab_end

# todo: else, otool -l min: objdump: 'min': truncated or malformed object (contains LC_DYSYMTAB load command without a LC_SYMTAB load command)
# /ref/xnu/EXTERNAL_HEADERS/mach-o/nlist.h

@Command_end

# @Bind before @Code or @Data since the latter two are appended outside this file. Use a fixed location for the vm
# address 0x1000 (0x00000000 of segment index 01 = Seg_code) for dlsym's function address. See Dl.sym.
@Bind
# $ dyldinfo -bind -opcodes min
# bind information:
# segment section          address        type    addend dylib            symbol
# __LINKEDIT ??               0x000C0000    pointer      0 libSystem        _dlsym
# no compressed rebase info
# binding opcodes:
# 0x0000 BIND_OPCODE_SET_DYLIB_ORDINAL_IMM(1)  dylib 1 = /usr/lib/libSystem.B.dylib
# 0x0001 BIND_OPCODE_SET_SYMBOL_TRAILING_FLAGS_IMM(0x00, _dlsym)
# 0x0009 BIND_OPCODE_SET_TYPE_IMM(1)           segment 1 = Seg_link
# 0x000A BIND_OPCODE_SET_SEGMENT_AND_OFFSET_ULEB(0x01, 0x00000000)
# 0x000C BIND_OPCODE_DO_BIND()

# otool -l min | grep ' bind_off'
#   bind_off 876
# tail -c +876 min | hexdump | head -1
#   0000000 00 11 40 5f 64 6c 73 79 6d 00 51 71 00 90 48 b8
0'11 40 5f 64 6c 73 79 6d 00 51 71 00 90'
@Bind_end

# http://x86-64.org/documentation/abi.pdf System V Application Binary Interface AMD64 Architecture Processor Supplement
# 3.4.1 Initial Stack and Register State - Stack State
#   extern int main ( int argc , char *argv[ ] , char* envp[ ] );
#   Figure 3.9: Initial Process Stack
@Code
  mov a Data_vmend
  mov a 0 a 
  add a 0 16                            # 8 = Mem.last, 8 = Job.multi

  push sp
  call Main.main

# Asm.steps_binary_out appends the rest of @Code segment and the @Data segment.
