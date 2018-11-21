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
  secret : Cstruct.t option ;
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

let derive_secret t label log =
  match t.secret with
  | None -> assert false
  | Some prk ->
    let ctx = Nocrypto.Hash.digest t.hash log in
    let length = Nocrypto.Hash.digest_size t.hash in
    let info = hkdflabel label ctx length in
    let key = Hkdf.expand ~hash:t.hash ~prk ~info length in
    trace ("derive_secret: " ^ label) key ;
    key

let empty cipher = {
  secret = None ;
  cipher ;
  hash = Ciphersuite.hash13 cipher
}

let derive t secret =
  let salt =
    match t.secret with
    | None -> Cstruct.empty
    | Some _ -> derive_secret t "derived" Cstruct.empty
  in
  let secret = Hkdf.extract ~hash:t.hash ~salt secret in
  trace "derive (extracted secret)" secret ;
  { t with secret = Some secret }

let traffic_key cipher prk =
  let _, hash, key_len, iv_len = pp_hash_k_n cipher in
  let key_info = hkdflabel "key" Cstruct.empty key_len in
  let key = Hkdf.expand ~hash ~prk ~info:key_info key_len in
  let iv_info = hkdflabel "iv" Cstruct.empty iv_len in
  let iv = Hkdf.expand ~hash ~prk ~info:iv_info iv_len in
  (key, iv)

let ctx t label log =
  let secret = derive_secret t label log in
  let secret, nonce = traffic_key t.cipher secret in
  trace (label ^ " secret") secret ;
  trace (label ^ " nonce") nonce ;
  let pp = Ciphersuite.privprot13 t.cipher in
  { State.sequence = 0L ; cipher_st = Crypto.Ciphers.get_aead ~secret ~nonce pp }

let hs_ctx t log =
  ctx t "s hs traffic" log,
  ctx t "c hs traffic" log

let app_ctx t log =
  ctx t "s ap traffic" log,
  ctx t "c ap traffic" log

(*
let finished cs master_secret server data =
  let hash = Ciphersuite.hash13 cs in
  let label = if server then "server finished" else "client finished" in
  let key = expand_label hash master_secret label (Cstruct.create 0) (Hash.digest_size hash) in
  Hash.mac hash ~key (Hash.digest hash data)
*)
