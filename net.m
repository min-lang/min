# network address, ip address, host identification

#  https://developer.apple.com/library/mac/documentation/Darwin/Reference/ManPages/man3/getaddrinfo.3.html
lib_getaddrinfo = Dl 'getaddrinfo' : host:S? service:S? hints:Mem? out:%N? N

# [[ $(curl -s `./min net dynamodb.us-west-1.amazonaws.com`) = $(curl -s dynamodb.us-west-1.amazonaws.com) ]]
host name:S : N =
  hints = Mem 48
  Mem.set2 hints+4 2                                                            # ai_family = PF_INET
  Mem.set2 hints+8 1                                                            # ai_socktype = SOCK_STREAM
  info = Ref 0
  Fun.call4 lib_getaddrinfo name 0 hints info
  # 32 = addrinfo.ai_addr, 4 = sockaddr.sa_data = sockaddr_in.sin_addr
  (Mem.next (Mem.get (Mem.next info.Ref.get.Cast.any 32)).Cast.any 4).Mem.get

str x:N : S = N.ip x

# host google.com # google.com has address 216.58.194.174
test _ = (x = "google.com"; Put.fill '$s: ip address of $s = $s' [$Fun, x, Net.str (host x)])
