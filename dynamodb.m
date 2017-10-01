# amazon cloud key-value database

  http://docs.aws.amazon.com/amazondynamodb/latest/APIReference/API.CreateTable.html
  
sign data:S key:Mem : Mem = Common_crypto.hmac_key key data

#
  date
    . Common_crypto.hmac_str 'AWS4'+key
    . sign region
    . sign service 
    . sign 'aws4_request' 

  date . Common_crypto.hmac_str 'AWS4'+key . sign region . sign service . sign 'aws4_request' 
             
signature_key key:S date:S region:S service:S : Mem =
  sign 'aws4_request' 
   sign service 
    sign region
     Common_crypto.hmac_str 'AWS4'+key date 

do action:S body:S : S =
  now = !Time.now
  datetime = Time.datetime_iso now.Time.gmtime
  date = Time.date_iso now.Time.gmtime # 20151103T230739Z
  region = 'us-west-1'
  service = 'dynamodb'

  access_key_id = Env.must 'AWS_ACCESS_KEY_ID'
  secret_access_key = Env.must 'AWS_SECRET_ACCESS_KEY'
  
  key = signature_key secret_access_key date region service  
  method = 'POST'
  canonical_uri = '/'
  canonical_querystring = ''
  version = 'DynamoDB_20120810'
  target = version + '.' + action
  body_hash = Common_crypto.sha256_hex body
  content_type = 'application/x-amz-json-1.0'
  # Content-Length:
  host = 'dynamodb.us-west-1.amazonaws.com'
  canonical_headers = 'content-type:' + content_type + "\." + 'host:' + host + "\." + 'x-amz-date:' + datetime + "\." + 'x-amz-target:' + target + "\."
  signed_headers = 'content-type;host;x-amz-date;x-amz-target'
  canonical_request = method + "\." + canonical_uri + "\." + canonical_querystring + "\." + canonical_headers + "\." + signed_headers + "\." + body_hash
  algorithm = 'AWS4-HMAC-SHA256'
  credential_scope = date + '/' + region + '/' + service + '/' + 'aws4_request'
  string_to_sign = algorithm + "\." +  datetime + "\." +  credential_scope + "\." +  Common_crypto.sha256_hex canonical_request
  signature = Common_crypto.hmac_key_hex key string_to_sign 
  
  sock = Socket 0
  Socket.connect sock 'dynamodb.us-west-1.amazonaws.com' 80

  request = S.fill 'POST / HTTP/1.1
Content-Length: $n
Connection: close
X-Amz-Target: $s
Host: dynamodb.us-west-1.amazonaws.com
X-Amz-Date: $s
Content-Type: application/x-amz-json-1.0
Authorization: AWS4-HMAC-SHA256 Credential=AKIAJEG264NCS4QOTZMQ/$s/us-west-1/dynamodb/aws4_request,SignedHeaders=content-type;host;x-amz-date;x-amz-target,Signature=$s

$s' [body.S.size, target, datetime, date, signature, body]
  File.out sock.File.of request
  File.in_read sock.File.of

  # {"__type":"com.amazon.coral.service#UnknownOperationException"}
  # {"__type":"com.amazon.coral.service#InvalidSignatureException","message":".."}

# http://docs.aws.amazon.com/amazondynamodb/latest/APIReference/API_PutItem.html
put2 hash:S range:S item:S : S = do 'PutItem' (S.fill '{"TableName": "000", "Item": {"hash": {"S": "$s"}, "range": {"S": "$s"}, "item": {"S": "$s"}}}' [hash, range, item]) . reply

put hash:S item:S : S = put2 hash '_' item . reply

reply x:S : S = S.rget x 0a + 1

# len('{"Item":{"range":{"S":""},"hash":{"S":""},"item":{"S":"') = 55
# len('"}}}') = 4
item x:S hash:S range:S : S = S.spanx x (55 + hash.S.size + range.S.size) -5

# http://docs.aws.amazon.com/amazondynamodb/latest/APIReference/API_GetItem.html
# {"Item":{"range":{"S":"bar"},"hash":{"S":"foo"},"item":{"S":"42"}}}
get2 hash:S range:S : S = item (do 'GetItem' (S.fill '{"TableName": "000", "Key": {"hash": {"S": "$s"}, "range": {"S": "$s"}}}' [hash, range]) . reply) hash range

get hash:S : S = get2 hash '_'

#
  sudo easy_install boto
  import boto.dynamodb
  s = boto.dynamodb.connect_to_region('us-west-1', aws_access_key_id='???', aws_secret_access_key='???')
  s.create_table('000', s.create_schema('hash', '', 'range', ''), 1, 1)
test _ =
  Fact.do $Fun (do 'ListTables' '{}' . reply == '{"TableNames":["000"]}')
  put 'foo' '13'
  Fact.do $Fun (get 'foo' == '13')

  put2 'foo' 'bar' '42'
  Fact.do $Fun (get2 'foo' 'bar' == '42')
  Fact.do $Fun (get 'foo' == '13')
  0
