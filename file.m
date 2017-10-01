# unix file description, file number

  https://en.wikipedia.org/wiki/Handle_(computing)

to x:File : N = Cast.file_nat x

of x:N : File = Cast.nat_file x

read file:File x:S size:N : N = Sys.read file.to x size

in_to file:File x:S : S = read file x 1 & in_to file x+1 | x

# THREAD_UNSAFE reallocate with the accurate size y-x+1 immediately
in_read file:File : S = (x = Mem 0 . Mem.str; y = in_to file x; S.new y-x; x)                                       

page_size = 1024

in_size file:File size:N : S = (x = Mem size . Mem.str; read file x size; x)                                       

# only for regular file with known size (not socket)
in file:File : S = (n = Sys.fstat file; x = Mem n+1 . Mem.str; m = read file x n; x) # todo - check m

# no memory allocation due to in_text THREAD_UNSAFE [Mem 0]
in_text_at x:S file:File : S =                                     
  n = read file x page_size             # check -1
  y = x + n
  (n == 0 | S.bit x+(n-1)) & in_text_at y file | y # until \0

# read until \0
in_text file:File : S =
  # THREAD_UNSAFE reallocate with the accurate size y-x+1 immediately
  x = Mem 0 . Mem.str                    
  y = in_text_at x file
  S.new y-x
  x

in_last file:File : S, C =
  x = Mem page_size . Mem.str
  n = read file x page_size
  x, S.char x+(n-1)

write_size file:File x:S n:N = Sys.write file.to x n . Z

write file:File x:S = write_size file x !x

write_char file:File x:C = Sys.write0 file.to x . Z

write_space file:File x:S = (write file x; write_char file \ )

line file:File x:S = (write file x; write_char file 0a)

out file:File x:S = write file x

# http://man7.org/linux/man-pages/man2/close.2.html
close x:File = Sys.callx 6 x.to 0 0 0 0 0 . Z

# http://linux.die.net/man/2/dup2
dup2 old:File new:File : N = Sys.dup2 old.to new.to
