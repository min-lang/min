# common crypto in mac os x

  https://developer.apple.com/library/mac/documentation/Darwin/Reference/ManPages/man3/Common%20Crypto.3cc.html

lib_CCHmac = Dl 'CCHmac' : algo:N? key:Mem? key_size:N? data:Mem? data_size:N? out:Mem? Mem
lib_CC_SHA256 = Dl 'CC_SHA256' : data:Mem? data_size:N? out:Mem? Mem
_CC_SHA256_DIGEST_LENGTH = 32
    
hmac_str key:S data:S : Mem = hmac key.S.mem key.S.size data.S.mem !data
# f932 0baf 0249 169e 7385 0cd6 156d ed01 06e2 bb6a d8ca b01b 7bbb ebe6 d106 5317$
Fact (Mem.hex (hmac_str 'foo' 'bar') 32 == 'f9320baf0249169e73850cd6156ded0106e2bb6ad8cab01b7bbbebe6d1065317') 

hmac_key key:Mem data:S : Mem = hmac key _CC_SHA256_DIGEST_LENGTH data.S.mem !data

hmac_key_hex key:Mem data:S : S = Mem.hex (hmac_key key data) _CC_SHA256_DIGEST_LENGTH

hmac key:Mem key_size:N data:Mem data_size:N : Mem =
  kCCHmacAlgSHA256 = 2  
  out = Mem _CC_SHA256_DIGEST_LENGTH
  Fun.call6x lib_CCHmac kCCHmacAlgSHA256 key key_size data data_size out
  out

sha256 data:S : Mem =
  out = Mem _CC_SHA256_DIGEST_LENGTH
  Fun.call3 lib_CC_SHA256 data.S.mem !data out
  out

sha256_hex data:S : S = Mem.hex (sha256 data) _CC_SHA256_DIGEST_LENGTH
