# hypertext transfer protocol

test _ =
  sock = Socket 0
  Socket.connect sock 'jigsaw.w3.org' 80
  request = S.fill 'GET / HTTP/1.1
Host: jigsaw.w3.org

' []
  File.out sock.File.of request
  #
    HTTP/1.1 200 OK
    Content-Type: text/plain
    Date: Sun, 08 May 2016 14:39:55 GMT
    Server: Google Frontend
    Content-Length: 15
    
    24.130.149.219      
  Fact.do $Fun (Regex.search 'HTTP/1.. 200 OK' (File.in_size sock.File.of 1000))
  0

# ?chunk_size is broken - http://httpbin.org/range/1024?chunk_size=10
test2 _ =
  sock = Socket 0
  Socket.connect sock 'jigsaw.w3.org' 80
  request = S.fill 'GET /HTTP/ChunkedScript HTTP/1.1
Host: httpbin.org

' []
  # request . Log
  File.out sock.File.of request
  # 2000...
  File.in_size sock.File.of 40 . Log
  0

# https://tools.ietf.org/html/rfc7230#section-4.2 # 4.2.  Compression Codings
test3 _ =
  sock = Socket 0
  Socket.connect sock 'httpbin.org' 80
  # curl httpbin.org/deflate
  request = S.fill 'GET /deflate HTTP/1.1
Host: httpbin.org

' []
  File.out sock.File.of request
  b = File.in_size sock.File.of 10000
  # {"deflated": true, "headers": {"Host": "httpbin.org"}, "method": "GET", "origin": "108.245.44.219"}
  #
    {
      "deflated": true, 
      "headers": {
        "Host": "httpbin.org"
      }, 
      "method": "GET", 
      "origin": "24.130.149.219"
    }
  # fixme - httpbin.org now only accepts https (not http)
  #Fact.do $Fun (Regex.search '"deflated": true,' (uncompress (S.drop (S.str b "\!\.\!\.") 4) 1000))
  0
