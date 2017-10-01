# hypertext transfer protocol daemon, web server

  https://en.wikipedia.org/wiki/Httpd

do x:File = 
  S.map_char (S.skip (File.in_size x 1000) 0a) 0d 31 . Put
  File.write x "HTTP/1.0 200\.\.hello\."
  File.close x

main port:N =
  sock0 = Socket 0
  #define	SO_REUSEADDR	0x0004		/* allow local address reuse */
  Socket.opt sock0 4
  Socket.bind sock0 "localhost" port
  Socket.listen sock0
  Fun.loop ?(Socket.accept sock0 . File.of . Httpd.do)
  # curl -v localhost:8080
