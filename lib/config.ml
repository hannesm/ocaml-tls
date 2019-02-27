open Nocrypto

open Utils
open Core

open Sexplib.Std

type certchain = X509.t list * Rsa.priv [@@deriving sexp]

type own_cert = [
  | `None
  | `Single of certchain
  | `Multiple of certchain list
  | `Multiple_default of certchain * certchain list
] [@@deriving sexp]

type session_cache = SessionID.t -> epoch_data option
let session_cache_of_sexp _ = fun _ -> None
let sexp_of_session_cache _ = Sexplib.Sexp.Atom "SESSION_CACHE"

type ticket_cache = {
  lookup : Cstruct.t -> (psk13 * epoch_data) option ;
  ticket_granted : psk13 -> epoch_data -> unit ;
  lifetime : int32 ;
  timestamp : unit -> Ptime.t
}

type ticket_cache_opt = ticket_cache option
let ticket_cache_opt_of_sexp _ = None
let sexp_of_ticket_cache_opt _ = Sexplib.Sexp.Atom "TICKET_CACHE"

type config = {
  ciphers : Ciphersuite.ciphersuite list ;
  ciphers13 : Ciphersuite.ciphersuite13 list ;
  protocol_versions : tls_version * tls_version ;
  signature_algorithms : signature_algorithm list ;
  use_reneg : bool ;
  authenticator : X509.Authenticator.a option ;
  peer_name : string option ;
  own_certificates : own_cert ;
  acceptable_cas : X509.distinguished_name list ;
  session_cache : session_cache ;
  ticket_cache : ticket_cache_opt ;
  cached_session : epoch_data option ;
  cached_ticket : (psk13 * epoch_data) option ;
  alpn_protocols : string list ;
  groups : group list ;
  zero_rtt : int32 ;
} [@@deriving sexp]

module Ciphers = struct

  (* A good place for various pre-baked cipher lists and helper functions to
   * slice and groom those lists. *)

  let psk = [
    `TLS_DHE_PSK_WITH_AES_128_GCM_SHA256 ;
    `TLS_DHE_PSK_WITH_AES_256_GCM_SHA384 ;
    `TLS_DHE_PSK_WITH_AES_128_CCM ;
    `TLS_DHE_PSK_WITH_AES_256_CCM ;

    `TLS_PSK_WITH_AES_256_GCM_SHA384 ;
    `TLS_PSK_WITH_AES_128_GCM_SHA256 ;
    `TLS_PSK_WITH_AES_128_CCM ;
    `TLS_PSK_WITH_AES_256_CCM ;
  ]

  let default = psk @ [
    `TLS_DHE_RSA_WITH_AES_256_GCM_SHA384 ;
    `TLS_DHE_RSA_WITH_AES_128_GCM_SHA256 ;
    `TLS_DHE_RSA_WITH_AES_256_CCM ;
    `TLS_DHE_RSA_WITH_AES_128_CCM ;
    `TLS_DHE_RSA_WITH_AES_256_CBC_SHA256 ;
    `TLS_DHE_RSA_WITH_AES_128_CBC_SHA256 ;
    `TLS_DHE_RSA_WITH_AES_256_CBC_SHA ;
    `TLS_DHE_RSA_WITH_AES_128_CBC_SHA ;
    `TLS_RSA_WITH_AES_256_CCM ;
    `TLS_RSA_WITH_AES_128_CCM ;
    `TLS_RSA_WITH_AES_256_CBC_SHA256 ;
    `TLS_RSA_WITH_AES_128_CBC_SHA256 ;
    `TLS_RSA_WITH_AES_256_CBC_SHA ;
    `TLS_RSA_WITH_AES_128_CBC_SHA ;
    ]

  let supported = default @ [
    `TLS_RSA_WITH_AES_256_GCM_SHA384 ;
    `TLS_RSA_WITH_AES_128_GCM_SHA256 ;
    `TLS_DHE_RSA_WITH_3DES_EDE_CBC_SHA ;
    `TLS_RSA_WITH_3DES_EDE_CBC_SHA ;
    `TLS_RSA_WITH_RC4_128_SHA ;
    `TLS_RSA_WITH_RC4_128_MD5
    ]

  let fs_of = List.filter Ciphersuite.ciphersuite_fs

  let fs = fs_of default

  let psk_of = List.filter Ciphersuite.ciphersuite_psk

  let default13 = [
    `TLS_AES_128_GCM_SHA256 ;
    `TLS_AES_256_GCM_SHA384 ;
    (* `TLS_CHACHA20_POLY1305_SHA256 ; *)
    `TLS_AES_128_CCM_SHA256 ;
    (* `TLS_AES_128_CCM_8_SHA256 *)
  ]

  let supported13 = default13

end

let default_signature_algorithms =
  [ `RSA_PSS_RSAENC_SHA256 ;
    `RSA_PSS_RSAENC_SHA384 ;
    `RSA_PSS_RSAENC_SHA512 ;
    `RSA_PKCS1_SHA256 ;
    `RSA_PKCS1_SHA384 ;
    `RSA_PKCS1_SHA512 ;
    `RSA_PKCS1_SHA1 ]

let supported_signature_algorithms =
  default_signature_algorithms @ [ `RSA_PKCS1_MD5 ]

let min_dh_size = 1024

let min_rsa_key_size = 1024

let dh_group = `FFDHE2048 (* ff-dhe draft 2048-bit group *)

let supported_groups =
  [ `X25519 ; `P256 ; `FFDHE2048 ; `FFDHE3072 ; `FFDHE4096 ; `FFDHE6144 ; `FFDHE8192 ]

let default_config = {
  ciphers = Ciphers.default ;
  ciphers13 = Ciphers.default13 ;
  protocol_versions = (TLS_1_0, TLS_1_3) ;
  signature_algorithms = default_signature_algorithms ;
  use_reneg = false ;
  authenticator = None ;
  peer_name = None ;
  own_certificates = `None ;
  acceptable_cas = [] ;
  session_cache = (fun _ -> None) ;
  cached_session = None ;
  cached_ticket = None ;
  alpn_protocols = [] ;
  groups = supported_groups ;
  ticket_cache = None ;
  zero_rtt = 0l ;
}

let invalid msg = invalid_arg ("Tls.Config: invalid configuration: " ^ msg)

let validate_common config =
  let (v_min, v_max) = config.protocol_versions in
  if v_max < v_min then invalid "bad version range" ;
  ( match config.signature_algorithms with
    | [] when v_max >= TLS_1_2 ->
       invalid "TLS 1.2 configured but no signature algorithms provided"
    | hs when not (List_set.subset hs supported_signature_algorithms) ->
       invalid "Some signature algorithms are not supported"
    | _ -> () ) ;
  if not (List_set.is_proper_set config.ciphers) then
    invalid "set of ciphers is not a proper set" ;
  if List.length config.ciphers = 0 then
    invalid "set of ciphers is empty" ;
  if List.exists (fun proto -> let len = String.length proto in len = 0 || len > 255) config.alpn_protocols then
    invalid "invalid alpn protocol" ;
  if List.length config.alpn_protocols > 0xffff then
    invalid "alpn protocols list too large"

module CertTypeUsageOrdered = struct
  type t = X509.key_type * X509.Extension.key_usage
  let compare = compare
end
module CertTypeUsageSet = Set.Make(CertTypeUsageOrdered)

let validate_certificate_chain = function
  | (s::chain, priv) ->
     let pub = Rsa.pub_of_priv priv in
     if Rsa.pub_bits pub < min_rsa_key_size then
       invalid "RSA key too short!" ;
     ( match X509.public_key s with
       | `RSA pub' when pub = pub' -> ()
       | _ -> invalid "public / private key combination" ) ;
     ( match init_and_last chain with
       | Some (ch, trust) ->
         (* TODO: verify that certificates are x509 v3 if TLS_1_2 *)
         ( match X509.Validation.verify_chain_of_trust ~anchors:[trust] (s :: ch) with
           | `Ok _   -> ()
           | `Fail x -> invalid ("certificate chain does not validate: " ^
                                 (X509.Validation.validation_error_to_string x)) )
       | None -> () )
  | _ -> invalid "certificate"

let validate_client config =
  match config.own_certificates with
  | `None -> ()
  | `Single c -> validate_certificate_chain c
  | _ -> invalid_arg "multiple client certificates not supported in client config"

module StringSet = Set.Make(String)

let non_overlapping cs =
  let namessets =
    let nameslists =
      filter_map cs ~f:(function
          | (s :: _, _) -> Some s
          | _           -> None)
      |> List.map X509.hostnames
    in
    List.map (fun xs -> List.fold_right StringSet.add xs StringSet.empty) nameslists
  in
  let rec check = function
    | []    -> ()
    | s::ss -> if not (List.for_all
                         (fun ss' -> StringSet.is_empty (StringSet.inter s ss'))
                         ss)
               then
                 invalid_arg "overlapping names in certificates"
               else
                 check ss
  in
  check namessets

let validate_server config =
  let open Ciphersuite in
  let typeusage =
    let tylist =
      List.map ciphersuite_kex config.ciphers |>
        List.filter needs_certificate |>
        List.map required_keytype_and_usage
    in
    List.fold_right CertTypeUsageSet.add tylist CertTypeUsageSet.empty
  and certificate_chains =
    match config.own_certificates with
    | `Single c                 -> [c]
    | `Multiple cs              -> cs
    | `Multiple_default (c, cs) -> c :: cs
    | `None                     -> []
  in
  let server_certs =
    List.map (function
        | (s::_,_) -> s
        | _ -> invalid "empty certificate chain")
      certificate_chains
  in
  if
    not (CertTypeUsageSet.for_all
           (fun (t, u) ->
              List.exists (fun c ->
                  X509.supports_keytype c t &&
                  X509.Extension.supports_usage ~not_present:true c u)
                server_certs)
           typeusage)
  then
    invalid "certificate type or usage does not match" ;
  List.iter validate_certificate_chain certificate_chains ;
  ( match config.own_certificates with
    | `Multiple cs              -> non_overlapping cs
    | `Multiple_default (_, cs) -> non_overlapping cs
    | _                         -> () )
  (* TODO: verify that certificates are x509 v3 if TLS_1_2 *)


type client = config [@@deriving sexp]
type server = config [@@deriving sexp]

let of_server conf = conf
and of_client conf = conf

let peer conf name = { conf with peer_name = Some name }

let with_authenticator conf auth = { conf with authenticator = Some auth }

let with_own_certificates conf own_certificates = { conf with own_certificates }

let with_acceptable_cas conf acceptable_cas = { conf with acceptable_cas }

let (<?>) ma b = match ma with None -> b | Some a -> a

let client
  ~authenticator ?peer_name ?ciphers ?ciphers13 ?version ?signature_algorithms ?reneg ?certificates ?cached_session ?cached_ticket ?ticket_cache ?alpn_protocols ?groups () =
  let config =
    { default_config with
        authenticator = Some authenticator ;
        ciphers = ciphers <?> default_config.ciphers ;
        ciphers13 = ciphers13 <?> default_config.ciphers13 ;
        protocol_versions = version <?> default_config.protocol_versions ;
        signature_algorithms = signature_algorithms <?> default_config.signature_algorithms ;
        use_reneg = reneg <?> default_config.use_reneg ;
        own_certificates  = certificates <?> default_config.own_certificates ;
        peer_name = peer_name ;
        cached_session = cached_session ;
        alpn_protocols = alpn_protocols <?> default_config.alpn_protocols ;
        ticket_cache = ticket_cache ;
        cached_ticket = cached_ticket ;
        groups = groups <?> default_config.groups ;
    } in
  ( validate_common config ; validate_client config ; config )

let server
    ?ciphers ?ciphers13 ?version ?signature_algorithms ?reneg ?certificates ?acceptable_cas ?authenticator ?session_cache ?ticket_cache ?alpn_protocols ?groups ?zero_rtt () =
  let config =
    { default_config with
        ciphers = ciphers <?> default_config.ciphers ;
        ciphers13 = ciphers13 <?> default_config.ciphers13 ;
        protocol_versions = version <?> default_config.protocol_versions ;
        signature_algorithms = signature_algorithms <?> default_config.signature_algorithms ;
        use_reneg = reneg <?> default_config.use_reneg ;
        own_certificates = certificates <?> default_config.own_certificates ;
        acceptable_cas = acceptable_cas <?> default_config.acceptable_cas ;
        authenticator = authenticator ;
        session_cache = session_cache  <?> default_config.session_cache ;
        alpn_protocols = alpn_protocols <?> default_config.alpn_protocols ;
        ticket_cache = ticket_cache ;
        groups = groups <?> default_config.groups ;
        zero_rtt = zero_rtt <?> default_config.zero_rtt ;
    } in
  ( validate_common config ; validate_server config ; config )
