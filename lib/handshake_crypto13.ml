open Nocrypto

let (<+>) = Utils.Cs.(<+>)

let trace tag cs = Tracing.cs ~tag:("crypto " ^ tag) cs

let expand_label hash prk label hashvalue length =
  let info =
    let len = Cstruct.create 2 in
    Cstruct.BE.set_uint16 len 0 length ;
    let label = Cstruct.of_string ("tls13 " ^ label) in
    let llen = Cstruct.create 1 in
    Cstruct.set_uint8 llen 0 (Cstruct.len label) ;
    let hashlen = Cstruct.create 1 in
    Cstruct.set_uint8 hashlen 0 (Cstruct.len hashvalue) ;
    len <+> llen <+> label <+> hashlen <+> hashvalue
  in
  let key = Hkdf.expand ~hash ~prk ~info length in
  trace label key ;
  key

let pp_hash_k_n ciphersuite =
  let open Ciphersuite in
  let pp = privprot13 ciphersuite
  and hash = hash13 ciphersuite
  in
  let k, n = kn pp in
  (pp, hash, k, n)

type t = {
  secret : Cstruct.t ;
  cipher : Ciphersuite.ciphersuite13 ;
  hash : Nocrypto.Hash.hash ;
}

let hkdflabel label context length =
  let len =
    let b = Cstruct.create 2 in
    Cstruct.BE.set_uint16 b 0 length ;
    b
  and label =
    let lbl = Cstruct.of_string ("tls13 " ^ label) in
    let l = Cstruct.create 1 in
    Cstruct.set_uint8 l 0 (Cstruct.len lbl) ;
    l <+> lbl
  and context =
    let l = Cstruct.create 1 in
    Cstruct.set_uint8 l 0 (Cstruct.len context) ;
    l <+> context
  in
  len <+> label <+> context

let derive_secret_no_hash hash prk ?(ctx = Cstruct.empty) label =
  let length = Nocrypto.Hash.digest_size hash in
  let info = hkdflabel label ctx length in
  let key = Hkdf.expand ~hash ~prk ~info length in
  trace ("derive_secret: " ^ label) key ;
  key

let derive_secret t label log =
  let ctx = Nocrypto.Hash.digest t.hash log in
  derive_secret_no_hash t.hash t.secret ~ctx label

let empty cipher = {
  secret = Cstruct.empty ;
  cipher ;
  hash = Ciphersuite.hash13 cipher
}

let derive t secret_ikm =
  let salt =
    if Cstruct.equal t.secret Cstruct.empty then
      Cstruct.empty
    else
      derive_secret t "derived" Cstruct.empty
  in
  let secret = Hkdf.extract ~hash:t.hash ~salt secret_ikm in
  trace "derive (extracted secret)" secret ;
  { t with secret }

let traffic_key cipher prk =
  let _, hash, key_len, iv_len = pp_hash_k_n cipher in
  let key_info = hkdflabel "key" Cstruct.empty key_len in
  let key = Hkdf.expand ~hash ~prk ~info:key_info key_len in
  let iv_info = hkdflabel "iv" Cstruct.empty iv_len in
  let iv = Hkdf.expand ~hash ~prk ~info:iv_info iv_len in
  (key, iv)

let ctx t label secret =
  let secret, nonce = traffic_key t.cipher secret in
  trace (label ^ " secret") secret ;
  trace (label ^ " nonce") nonce ;
  let pp = Ciphersuite.privprot13 t.cipher in
  { State.sequence = 0L ; cipher_st = Crypto.Ciphers.get_aead ~secret ~nonce pp }

let hs_ctx t log =
  let server_handshake_traffic_secret = derive_secret t "s hs traffic" log
  and client_handshake_traffic_secret = derive_secret t "c hs traffic" log
  in
  (server_handshake_traffic_secret,
   ctx t "server handshake traffic" server_handshake_traffic_secret,
   client_handshake_traffic_secret,
   ctx t "client handshake traffic" client_handshake_traffic_secret)

let app_ctx t log =
  let server_application_traffic_secret = derive_secret t "s ap traffic" log
  and client_application_traffic_secret = derive_secret t "c ap traffic" log
  in
  (server_application_traffic_secret,
   ctx t "server application traffic" server_application_traffic_secret,
   client_application_traffic_secret,
   ctx t "client application traffic" client_application_traffic_secret)

let finished hash secret data =
  let key = derive_secret_no_hash hash secret "finished" in
  Hash.mac hash ~key (Hash.digest hash data)
