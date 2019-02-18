open Nocrypto

let (<+>) = Utils.Cs.(<+>)

let left_pad_dh group msg =
  let bytes = Nocrypto.Uncommon.cdiv (Nocrypto.Dh.modulus_size group) 8 in
  let padding = Cstruct.create (bytes - Cstruct.len msg) in
  padding <+> msg

let dh_shared group secret share =
  (* RFC 8556, Section 7.4.1 - we need zero-padding on the left *)
  match Core.group_to_impl group, secret with
  | `Nocrypto nc_group, `Nocrypto secret ->
    begin match Nocrypto.Dh.shared nc_group secret share with
      | None -> None
      | Some shared -> Some (left_pad_dh nc_group shared)
    end
  | `Hacl `X25519, `Hacl priv ->
    Logs.debug (fun m -> m "kex with X25519 key secret %a (share %a)!"
                   Cstruct.hexdump_pp (Hacl_x25519.to_cstruct priv)
                   Cstruct.hexdump_pp share) ;
    begin match Hacl_x25519.of_cstruct share with
      | Error _ -> None
      | Ok public -> Some (Hacl_x25519.key_exchange ~pub:public ~priv)
    end
  | _ -> assert false

let dh_gen_key group =
  (* RFC 8556, Section 4.2.8.1 - we need zero-padding on the left *)
  match Core.group_to_impl group with
  | `Nocrypto nc_group ->
    let sec, shared = Nocrypto.Dh.gen_key nc_group in
    `Nocrypto sec, left_pad_dh nc_group shared
  | `Hacl `X25519 ->
    Logs.debug (fun m -> m "generating X25519 key!") ;
    let random = Nocrypto.Rng.generate Hacl_x25519.key_length_bytes in
    Logs.debug (fun m -> m "secrete %a" Cstruct.hexdump_pp random) ;
    let secret =
      match Hacl_x25519.of_cstruct random with
      | Ok s -> s
      | Error msg -> invalid_arg msg
    in
    let public = Hacl_x25519.(to_cstruct (public secret)) in
    Logs.debug (fun m -> m "public is %a" Cstruct.hexdump_pp public) ;
    (`Hacl secret, public)

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
  Logs.info (fun m -> m "label info %a" Cstruct.hexdump_pp info) ;
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
  let lbl = len <+> label <+> context in
  trace "hkdflabel" lbl ;
  lbl


let derive_secret_no_hash hash prk ?(ctx = Cstruct.empty) label =
  let length = Nocrypto.Hash.digest_size hash in
  let info = hkdflabel label ctx length in
  trace "prk" prk ;
  let key = Hkdf.expand ~hash ~prk ~info length in
  trace ("derive_secret: " ^ label) key ;
  key

let derive_secret t label log =
  let ctx = Nocrypto.Hash.digest t.State.hash log in
  trace "derive secret ctx" ctx ;
  derive_secret_no_hash t.State.hash t.State.secret ~ctx label

let empty cipher = {
  State.secret = Cstruct.empty ;
  cipher ;
  hash = Ciphersuite.hash13 cipher
}

let derive t secret_ikm =
  let salt =
    if Cstruct.equal t.State.secret Cstruct.empty then
      Cstruct.empty
    else
      derive_secret t "derived" Cstruct.empty
  in
  trace "derive: secret_ikm" secret_ikm ;
  trace "derive: salt" salt ;
  let secret = Hkdf.extract ~hash:t.State.hash ~salt secret_ikm in
  trace "derive (extracted secret)" secret ;
  { t with State.secret }

let traffic_key cipher prk =
  let _, hash, key_len, iv_len = pp_hash_k_n cipher in
  let key_info = hkdflabel "key" Cstruct.empty key_len in
  let key = Hkdf.expand ~hash ~prk ~info:key_info key_len in
  let iv_info = hkdflabel "iv" Cstruct.empty iv_len in
  let iv = Hkdf.expand ~hash ~prk ~info:iv_info iv_len in
  (key, iv)

let ctx t label secret =
  let secret, nonce = traffic_key t.State.cipher secret in
  trace (label ^ " secret") secret ;
  trace (label ^ " nonce") nonce ;
  let pp = Ciphersuite.privprot13 t.State.cipher in
  { State.sequence = 0L ; cipher_st = Crypto.Ciphers.get_aead ~secret ~nonce pp }

let hs_ctx t log =
  Tracing.cs ~tag:"hs ctx with sec" t.State.secret ;
  Tracing.cs ~tag:"log is" log ;
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

let exporter t log = derive_secret t "exp master" log
let resumption t log = derive_secret t "res master" log

let res_secret hash secret nonce =
  derive_secret_no_hash hash secret ~ctx:nonce "resumption"

let finished hash secret data =
  let key = derive_secret_no_hash hash secret "finished" in
  Hash.mac hash ~key (Hash.digest hash data)
