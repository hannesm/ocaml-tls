open Utils
open Core
open State

open Nocrypto

let src = Logs.Src.create "handshake" ~doc:"TLS handshake"
module Log = (val Logs.src_log src : Logs.LOG)

let trace_cipher cipher =
  let kex, papr = Ciphersuite.get_kex_privprot cipher in
  let sexp = lazy (Sexplib.Sexp.(List Ciphersuite.(
      [ sexp_of_key_exchange_algorithm kex ;
        sexp_of_payload_protection papr ])))
  in
  Tracing.sexp ~tag:"cipher" sexp

let empty = function [] -> true | _ -> false

let change_cipher_spec =
  (Packet.CHANGE_CIPHER_SPEC, Writer.assemble_change_cipher_spec)

let hostname (h : client_hello) : string option =
  map_find ~f:(function `Hostname s -> Some s | _ -> None) h.extensions

let rec find_matching host certs =
  match certs with
  | (s::_, _) as chain ::xs ->
    if X509.supports_hostname s host then
      Some chain
    else
      find_matching host xs
  | _::xs -> find_matching host xs (* this should never happen! *)
  | [] -> None

let agreed_cert certs hostname =
  let match_host ?default host certs =
     let host = String.lowercase host in
     match find_matching (`Strict host) certs with
     | Some x -> return x
     | None   -> match find_matching (`Wildcard host) certs with
                 | Some x -> return x
                 | None   -> match default with
                             | Some c -> return c
                             | None   -> fail (`Error (`NoMatchingCertificateFound host))
  in
  match certs, hostname with
  | `None                    , _      -> fail (`Error `NoCertificateConfigured)
  | `Single c                , _      -> return c
  | `Multiple_default (c, _) , None   -> return c
  | `Multiple cs             , Some h -> match_host h cs
  | `Multiple_default (c, cs), Some h -> match_host h cs ~default:c
  | _                                 -> fail (`Error `CouldntSelectCertificate)

let get_secure_renegotiation exts =
  map_find
    exts
    ~f:(function `SecureRenegotiation data -> Some data | _ -> None)

let get_alpn_protocols (ch : client_hello) =
  map_find ~f:(function `ALPN protocols -> Some protocols | _ -> None) ch.extensions

let alpn_protocol config ch =
  match config.Config.alpn_protocols, get_alpn_protocols ch with
  | _, None | [], _ -> return None
  | configured, Some client -> match first_match client configured with
    | Some proto -> return (Some proto)
    | None ->
      (* RFC7301 Section 3.2:
         In the event that the server supports no protocols that the client
         advertises, then the server SHALL respond with a fatal
         "no_application_protocol" alert. *)
      fail (`Fatal `NoApplicationProtocol)

let get_alpn_protocol (sh : server_hello) =
  map_find ~f:(function `ALPN protocol -> Some protocol | _ -> None) sh.extensions

let empty_common_session_data = {
  server_random          = Cstruct.create 0 ;
  client_random          = Cstruct.create 0 ;
  peer_certificate_chain = [] ;
  peer_certificate       = None ;
  trust_anchor           = None ;
  received_certificates  = [] ;
  own_certificate        = [] ;
  own_private_key        = None ;
  own_name               = None ;
  client_auth            = false ;
  master_secret          = Cstruct.empty ;
  alpn_protocol          = None ;
}

let empty_session = {
  common_session_data = empty_common_session_data ;
  client_version      = Supported TLS_1_2 ;
  ciphersuite         = `TLS_DHE_RSA_WITH_AES_256_CBC_SHA ;
  renegotiation       = Cstruct.(empty, empty) ;
  session_id          = Cstruct.empty ;
  extended_ms         = false ;
}

let empty_session13 cipher = {
  common_session_data13 = empty_common_session_data ;
  ciphersuite13         = cipher ;
  kex13                 = `DHE_RSA ;
  resumption_secret     = Cstruct.empty ;
  exporter_secret       = Cstruct.empty ;
  psk                   = None ;
  master_secret         = Handshake_crypto13.empty cipher
}

let session_of_epoch (epoch : epoch_data) : session_data =
  let empty = empty_session in
  let common_session_data = {
    empty_session.common_session_data with
    peer_certificate = epoch.peer_certificate ;
    trust_anchor = epoch.trust_anchor ;
    own_certificate = epoch.own_certificate ;
    own_private_key = epoch.own_private_key ;
    received_certificates = epoch.received_certificates ;
    peer_certificate_chain = epoch.peer_certificate_chain ;
    master_secret = epoch.master_secret ;
    own_name = epoch.own_name ;
    alpn_protocol = epoch.alpn_protocol ;
  } in
  { empty with
    common_session_data ;
    ciphersuite = epoch.ciphersuite ;
    session_id = epoch.session_id ;
    extended_ms = epoch.extended_ms ;
  }

let supported_protocol_version (min, max) v =
  if compare_tls_version min v > 0 then
    None
  else if compare_tls_version v max > 0 then
    None
  else
    Some v

let to_client_ext_type = function
  | `Hostname _            -> `Hostname
  | `MaxFragmentLength _   -> `MaxFragmentLength
  | `SupportedGroups _     -> `SupportedGroups
  | `ECPointFormats _      -> `ECPointFormats
  | `SecureRenegotiation _ -> `SecureRenegotiation
  | `Padding _             -> `Padding
  | `SignatureAlgorithms _ -> `SignatureAlgorithms
  | `UnknownExtension _    -> `UnknownExtension
  | `ExtendedMasterSecret  -> `ExtendedMasterSecret
  | `ALPN _                -> `ALPN
  | `KeyShare _            -> `KeyShare
  | `EarlyDataIndication   -> `EarlyDataIndication
  | `PreSharedKeys _       -> `PreSharedKey
  | `Draft _               -> `Draft
  | `SupportedVersions _   -> `SupportedVersion
  | `PostHandshakeAuthentication -> `PostHandshakeAuthentication
  | `Cookie _              -> `Cookie
  | `PskKeyExchangeModes _ -> `PskKeyExchangeMode

let to_server_ext_type = function
  | `Hostname              -> `Hostname
  | `MaxFragmentLength _   -> `MaxFragmentLength
  | `ECPointFormats _      -> `ECPointFormats
  | `SecureRenegotiation _ -> `SecureRenegotiation
  | `UnknownExtension _    -> `UnknownExtension
  | `ExtendedMasterSecret  -> `ExtendedMasterSecret
  | `ALPN _                -> `ALPN
  | `KeyShare _            -> `KeyShare
  | `EarlyDataIndication   -> `EarlyDataIndication
  | `PreSharedKey _        -> `PreSharedKey
  | `Draft _               -> `Draft
  | `SelectedVersion _     -> `SupportedVersion

let extension_types t exts = List.(
  exts |> map t
       |> filter @@ function `UnknownExtension -> false | _ -> true
  )

(* a server hello may only contain extensions which are also in the client hello *)
(*  RFC5246, 7.4.7.1
   An extension type MUST NOT appear in the ServerHello unless the same
   extension type appeared in the corresponding ClientHello.  If a
   client receives an extension type in ServerHello that it did not
   request in the associated ClientHello, it MUST abort the handshake
   with an unsupported_extension fatal alert. *)
let server_exts_subset_of_client sexts cexts =
  let (sexts', cexts') =
    (extension_types to_server_ext_type sexts, extension_types to_client_ext_type cexts) in
  List_set.subset sexts' (`Cookie :: cexts')

module Group = struct
  type t = Packet.named_group
  let compare = Pervasives.compare
end

module GroupSet = Set.Make(Group)

(* Set.of_list appeared only in 4.02, for 4.01 compatibility *)
let of_list xs = List.fold_right GroupSet.add xs GroupSet.empty

let client_hello_valid (ch : client_hello) =
  let open Ciphersuite in
  (* match ch.version with
    | TLS_1_0 ->
       if List.mem TLS_DHE_DSS_WITH_3DES_EDE_CBC_SHA ch.ciphersuites then
         return ()
       else
         fail HANDSHAKE_FAILURE
    | TLS_1_1 ->
       if List.mem TLS_RSA_WITH_3DES_EDE_CBC_SHA ch.ciphersuites then
         return ()
       else
         fail HANDSHAKE_FAILURE
    | TLS_1_2 ->
       if List.mem TLS_RSA_WITH_AES_128_CBC_SHA ch.ciphersuites then
         return ()
       else
         fail HANDSHAKE_FAILURE *)
  let sig_alg =
    map_find
      ~f:(function `SignatureAlgorithms sa -> Some sa | _ -> None)
      ch.extensions
  and key_share =
    map_find
      ~f:(function `KeyShare ks -> Some ks | _ -> None)
      ch.extensions
  and groups =
    map_find
      ~f:(function `SupportedGroups gs -> Some gs | _ -> None)
      ch.extensions
  in

  let version_good = function
    | Supported TLS_1_2 | TLS_1_X _ -> `Ok
    | Supported TLS_1_3 ->
      (* TODO needs to be fixed, this will never happen (client_version is TLS_1_2 (or something else) in a 1.3 hello) *)
      ( let good_sig_alg =
          List.exists (fun sa -> List.mem sa Config.supported_signature_algorithms)
        in
        match sig_alg with
        | None -> `Error `NoSignatureAlgorithmsExtension
        | Some sig_alg when good_sig_alg sig_alg ->
          ( match key_share, groups with
            | None, _ -> `Error `NoKeyShareExtension
            | _, None -> `Error `NoSupportedGroupExtension
            | Some ks, Some gs ->
              match
                List_set.is_proper_set gs,
                List_set.is_proper_set (List.map fst ks),
                GroupSet.subset (of_list (List.map fst ks)) (of_list gs)
              with
              | true, true, true -> `Ok
              | false, _, _ -> `Error (`NotSetSupportedGroup gs)
              | _, false, _ -> `Error (`NotSetKeyShare ks)
              | _, _, false -> `Error (`NotSubsetKeyShareSupportedGroup (gs, ks)) )
        | Some x -> `Error (`NoGoodSignatureAlgorithms x)
      )
    | SSL_3 | Supported TLS_1_0 | Supported TLS_1_1 ->
      Utils.option
        `Ok
        (fun _ -> `Error `HasSignatureAlgorithmsExtension)
        sig_alg
  in

  let share_ciphers =
    match
      first_match (filter_map ~f:any_ciphersuite_to_ciphersuite ch.ciphersuites) Config.Ciphers.supported,
      first_match (filter_map ~f:any_ciphersuite_to_ciphersuite13 ch.ciphersuites) Config.Ciphers.supported13
    with
    | None, None -> false
    | _ -> true
  in
  match
    not (empty ch.ciphersuites),
    List_set.is_proper_set ch.ciphersuites,
    share_ciphers,
    List_set.is_proper_set (extension_types to_client_ext_type ch.extensions)
  with
  | true, _, true, true -> version_good ch.client_version
  | false, _ , _, _ -> `Error `EmptyCiphersuites
  (*  | _, false, _, _ -> `Error (`NotSetCiphersuites ch.ciphersuites) *)
  | _, _, false, _ -> `Error (`NoSupportedCiphersuite ch.ciphersuites)
  | _, _, _, false -> `Error (`NotSetExtension ch.extensions)


let server_hello_valid (sh : server_hello) =
  let open Ciphersuite in
  List_set.is_proper_set (extension_types to_server_ext_type sh.extensions)
  (* TODO:
      - EC stuff must be present if EC ciphersuite chosen
   *)

let (<+>) = Cs.(<+>)

let to_sign_1_3 context_string =
  (* input is prepended by 64 * 0x20 (to avoid cross-version attacks) *)
  (* input for signature now contains also a context string *)
  let prefix = Cstruct.create 64 in
  Cstruct.memset prefix 0x20 ;
  let ctx =
    let stop = Cstruct.create 1 (* trailing 0 byte *) in
    match context_string with
    | None -> stop
    | Some x -> Cstruct.of_string x <+> stop
  in
  prefix <+> ctx

let signature version ?context_string data client_sig_algs signature_algorithms private_key =
  match version with
  | TLS_1_0 | TLS_1_1 ->
    let data = Hash.MD5.digest data <+> Hash.SHA1.digest data in
    let signed = Rsa.PKCS1.sig_encode ~key:private_key data in
    return (Writer.assemble_digitally_signed signed)
  | TLS_1_2 ->
    (* if no signature_algorithms extension is sent by the client,
       support for md5 and sha1 can be safely assumed! *)
    ( match client_sig_algs with
      | None              -> return `RSA_PKCS1_SHA1
      | Some client_algos ->
        match first_match client_algos signature_algorithms with
        | None      -> fail (`Error (`NoConfiguredSignatureAlgorithm client_algos))
        | Some sig_alg -> return sig_alg ) >|= fun sig_alg ->
    let hash_alg = Core.hash_of_signature_algorithm sig_alg in
    let hash = Hash.digest hash_alg data in
    let cs = X509.Encoding.pkcs1_digest_info_to_cstruct (hash_alg, hash) in
    let sign = Rsa.PKCS1.sig_encode ~key:private_key cs in
    Writer.assemble_digitally_signed_1_2 sig_alg sign
  | TLS_1_3 ->
    (* RSA-PSS is used *)
    let prefix = to_sign_1_3 context_string in
    ( match client_sig_algs with
      | None              -> return `RSA_PSS_RSAENC_SHA256
      | Some client_algos ->
        match first_match client_algos signature_algorithms with
        | None -> fail (`Error (`NoConfiguredSignatureAlgorithm client_algos))
        | Some sig_alg -> return sig_alg ) >>= fun sig_alg ->
    let hash_algo = hash_of_signature_algorithm sig_alg in
    match signature_scheme_of_signature_algorithm sig_alg with
    | `PSS ->
      let module H = (val (Hash.module_of hash_algo)) in
      let module PSS = Rsa.PSS(H) in
      let data = H.digest data in
      let to_sign = prefix <+> data in
      let signature = PSS.sign ~key:private_key to_sign in
      return (Writer.assemble_digitally_signed_1_2 sig_alg signature)
    | _ -> fail (`Error (`NoConfiguredSignatureAlgorithm [])) (*TODO different warning, types *)

let peer_rsa_key = function
  | None -> fail (`Fatal `NoCertificateReceived)
  | Some cert ->
    match X509.public_key cert with
    | `RSA key -> return key
    | _        -> fail (`Fatal `NotRSACertificate)

let verify_digitally_signed version ?context_string sig_algs data signature_data certificate =
  peer_rsa_key certificate >>= fun pubkey ->

  let decode_pkcs1_signature raw_signature =
    match Rsa.PKCS1.sig_decode ~key:pubkey raw_signature with
    | Some signature -> return signature
    | None -> fail (`Fatal `RSASignatureVerificationFailed)
  in

  match version with
  | TLS_1_0 | TLS_1_1 ->
    ( match Reader.parse_digitally_signed data with
      | Ok signature ->
         let compare_hashes should data =
           let computed_sig = Hash.MD5.digest data <+> Hash.SHA1.digest data in
           guard (Cs.equal should computed_sig) (`Fatal `RSASignatureMismatch)
         in
         decode_pkcs1_signature signature >>= fun raw ->
         compare_hashes raw signature_data
      | Error re -> fail (`Fatal (`ReaderError re)) )
  | TLS_1_2 ->
     ( match Reader.parse_digitally_signed_1_2 data with
       | Ok (sig_alg, signature) ->
         guard (List.mem sig_alg sig_algs) (`Error (`NoConfiguredSignatureAlgorithm sig_algs)) >>= fun () ->
         let hash_algo = hash_of_signature_algorithm sig_alg in
         let compare_hashes should data =
           match X509.Encoding.pkcs1_digest_info_of_cstruct should with
           | Some (hash_algo', target) when hash_algo = hash_algo' ->
             guard (Crypto.digest_eq hash_algo ~target data) (`Fatal `RSASignatureMismatch)
           | _ -> fail (`Fatal `HashAlgorithmMismatch)
         in
         decode_pkcs1_signature signature >>= fun raw ->
         compare_hashes raw signature_data
       | Error re -> fail (`Fatal (`ReaderError re)) )
  | TLS_1_3 ->
    ( match Reader.parse_digitally_signed_1_2 data with
      | Ok (sig_alg, signature) ->
        guard (List.mem sig_alg sig_algs) (`Error (`NoConfiguredSignatureAlgorithm sig_algs)) >>= fun () ->
        let hash_algo = hash_of_signature_algorithm sig_alg in
        begin match signature_scheme_of_signature_algorithm sig_alg with
          | `PSS ->
            let module H = (val (Hash.module_of hash_algo)) in
            let module PSS = Rsa.PSS(H) in
            let data =
              let prefix = to_sign_1_3 context_string
              and data = H.digest signature_data
              in
              prefix <+> data
            in
            guard (PSS.verify ~key:pubkey ~signature data) (`Fatal `RSASignatureMismatch)
          | `PKCS1 ->
            fail (`Fatal `UnsupportedSignatureScheme)
        end
      | Error re -> fail (`Fatal (`ReaderError re)))

let validate_chain authenticator certificates hostname =
  let authenticate authenticator host certificates =
    match authenticator ?host certificates with
    | `Fail err  -> fail (`Error (`AuthenticationFailure err))
    | `Ok anchor -> return anchor

  and key_size min cs =
    let check c =
      match X509.public_key c with
      | `RSA key when Rsa.pub_bits key >= min -> true
      | _                                     -> false
    in
    guard (List.for_all check cs) (`Fatal `KeyTooSmall)

  and parse_certificates certs =
    let certificates = filter_map ~f:X509.Encoding.parse certs in
    guard (List.length certs = List.length certificates) (`Fatal `BadCertificateChain) >|= fun () ->
    certificates

  in

  (* RFC5246: must be x509v3, take signaturealgorithms into account! *)
  (* RFC2246/4346: is generally x509v3, signing algorithm for certificate _must_ be same as algorithm for certificate key *)
  parse_certificates certificates >>= fun certs ->
  let server = match certs with
    | s::_ -> Some s
    | [] -> None
  in
  match authenticator with
  | None -> return (server, certs, [], None)
  | Some authenticator ->
    authenticate authenticator hostname certs >>= fun anchor ->
    key_size Config.min_rsa_key_size certs >|= fun () ->
    Utils.option
      (server, certs, [], None)
      (fun (chain, anchor) -> (server, certs, chain, Some anchor))
      anchor
