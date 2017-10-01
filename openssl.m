# secure sockets layer

test _ =
  dlopen = Dl 'dlopen'
  Dl.open '/usr/lib/libssl.0.9.7.dylib' # loading again with path prefix is ok
  Fun.call0 'SSL_load_error_strings'.Dl 
  Fun.call0 'SSL_library_init'.Dl 
  context = Fun.call1 'SSL_CTX_new'.Dl (Fun.call0 'SSLv23_client_method'.Dl) # Negotiate highest available SSL/TLS version
  bio = Fun.call1 'BIO_new_ssl_connect'.Dl context
  Fun.call4 'BIO_ctrl'.Dl bio 100 0 'dynamodb.us-west-1.amazonaws.com:443'  
  Fun.call4 'BIO_ctrl'.Dl bio 101 0 0 # BIO_C_DO_STATE_MACHINE   
  Fact.do $Fun (Fun.call2 'ERR_error_string'.Dl (Fun.call0 'ERR_get_error'.Dl) 0 == 'error:00000000:lib(0):func(0):reason(0)')
  request = 'GET / HTTP/1.1
Host: dynamodb.us-west-1.amazonaws.com

'
  Fun.call2 'BIO_puts'.Dl bio request
  reply = S.new 1024
  Fun.call3 'BIO_read'.Dl bio reply 1024 # healthy: dynamodb.us-west-1.amazonaws.com

  #
    HTTP/1.1 200 OK
    x-amzn-RequestId: I1N01FEFBLQDBO2FIA8QVKBKJJVV4KQNSO5AEMVJF66Q9ASUAAJG
    x-amz-crc32: 1538475103
    Content-Length: 42
    Date: Sun, 08 May 2016 14:31:49 GMT
    
    healthy: dynamodb.us-west-1.amazonaws.com     
  Fact.do $Fun (Regex.search 'healthy: dynamodb.us-west-1.amazonaws.com' reply)
