# network file

Socket = N

nat x:Socket : N = Cast.socket_nat x

# http://man7.org/linux/man-pages/man2/socket.2.html
main _ : Socket = Cast.any (Sys.callx 97 2 1 6 0 0 0) # PF_INET/AF_INET SOCK_STREAM IPPROTO_TCP

inet = 2                                #  AF_INET - sa_family_t	sin_family;

# size=0, family=inet, port=port, address=(a, b, c, d), pad=0
address0 a:N b:N c:N d:N port:N : Mem =
  s = Mem 16
  Mem.set0 s 0                          # unused - sin_len
  Mem.set0 s+1 0                        # unused - AF_INET - sa_family_t	sin_family;
  Mem.net_set1 s+2 port                 # in_port_t	sin_port;
  Mem.set0 s+4 a                        # struct	in_addr sin_addr;
  Mem.set0 s+5 b
  Mem.set0 s+6 c
  Mem.set0 s+7 d
  s

address1 ip:N port:N : Mem =  
  s = Mem 16
  Mem.net_set1 s+2 port                                                         # in_port_t	sin_port;
  Mem.set s+4 ip                                                                        # struct	in_addr sin_addr;
  s

address host:S port:N : Mem = address1 host.Net.host port

# https://developer.apple.com/library/mac/documentation/Darwin/Reference/ManPages/man2/connect.2.html
connect1 x:Socket address:Mem = Sys.callx 98 x.nat address.Mem.nat 16 0 0 0 . Z
connect2 x:Socket address:N = Sys.callx 98 x.nat address 16 0 0 0 . Z
connect x:Socket host:S port:N = connect1 x (address host port)

test _ =
  s = main 0
  connect s 'google.com' 80
  File.out s.File.of "GET / HTTP/1.0\.Host: www.google.com\.\."
  #
    HTTP/1.0 200 OK
    Content-Type: text/html; charset=ISO-8859-1    
  Fact.do $Fun (Regex.search 'HTTP/1.. 200 OK' (File.in_read s.File.of))

# https://developer.apple.com/library/mac/documentation/Darwin/Reference/ManPages/man2/setsockopt.2.html
  #define	SOL_SOCKET	0xffff		/* options for socket level */  
opt x:Socket mask:N = Sys.callx 105 x.nat 0ffff mask (Ref 1).Ref.mem.Mem.nat 8 0 . Z

# http://man7.org/linux/man-pages/man2/bind.2.html
bind1 x:Socket address:Mem = Sys.callx 104 x.nat address.Mem.nat 16 0 0 0 . Z
bind x:Socket host:S port:N = bind1 x (address host port)

# http://man7.org/linux/man-pages/man2/listen.2.html
listen x:Socket = Sys.callx 106 x.nat 0 0 0 0 0 . Z

# http://man7.org/linux/man-pages/man2/accept.2.html
accept x:Socket : N = Sys.callx 30 x.nat (Mem 16).Mem.nat (Mem 8).Mem.nat 0 0 0
