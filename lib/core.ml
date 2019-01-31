(** Core type definitions *)

open Sexplib.Conv
open Nocrypto

open Packet
open Ciphersuite

type tls_version =
  | TLS_1_0
  | TLS_1_1
  | TLS_1_2
  | TLS_1_3
  [@@deriving sexp]

let pair_of_tls_version = function
  | TLS_1_0   -> (3, 1)
  | TLS_1_1   -> (3, 2)
  | TLS_1_2   -> (3, 3)
  | TLS_1_3   -> (3, 4)

let compare_tls_version a b = match a, b with
  | TLS_1_0, TLS_1_0 -> 0 | TLS_1_0, _ -> -1 | _, TLS_1_0 -> 1
  | TLS_1_1, TLS_1_1 -> 0 | TLS_1_1, _ -> -1 | _, TLS_1_1 -> 1
  | TLS_1_2, TLS_1_2 -> 0 | TLS_1_2, _ -> -1 | _, TLS_1_2 -> 1
  | TLS_1_3, TLS_1_3 -> 0

let tls_version_of_pair = function
  | (3, 1) -> Some TLS_1_0
  | (3, 2) -> Some TLS_1_1
  | (3, 3) -> Some TLS_1_2
  | (3, 4) -> Some TLS_1_3
  | _      -> None

let draft = 0x000c

type tls_any_version =
  | SSL_3
  | Supported of tls_version
  | TLS_1_X of int
  [@@deriving sexp]

let any_version_to_version = function
  | Supported v -> Some v
  | _           -> None

let version_eq a b =
  match a with
  | Supported x -> compare_tls_version x b = 0
  | _           -> false

let version_ge a b =
  match a with
  | Supported x -> compare_tls_version x b = 1
  | SSL_3       -> false
  | TLS_1_X _   -> true

let tls_any_version_of_pair x =
  match tls_version_of_pair x with
  | Some v -> Some (Supported v)
  | None ->
     match x with
     | (3, 0) -> Some SSL_3
     | (3, x) -> Some (TLS_1_X x)
     | _      -> None

let pair_of_tls_any_version = function
  | Supported x -> pair_of_tls_version x
  | SSL_3       -> (3, 0)
  | TLS_1_X m   -> (3, m)

let max_protocol_version (_, hi) = hi
let min_protocol_version (lo, _) = lo

type tls_hdr = {
  content_type : content_type;
  version      : tls_any_version;
} [@@deriving sexp]

module SessionID = struct
  type t = Cstruct_sexp.t [@@deriving sexp]
  let compare = Cstruct.compare
  let hash t = Hashtbl.hash (Cstruct.to_bigarray t)
  let equal = Cstruct.equal
end

(* TODO needs to be updated in respect to psk13 *)
module PreSharedKeyID = struct
  type t = Cstruct.t [@@deriving sexp]
  let compare = Cstruct.compare
  let hash t = Hashtbl.hash (Cstruct.to_bigarray t)
  let equal = Cstruct.equal
end

type early_data = {
  configuration_id : Cstruct.t ;
  ciphersuite : ciphersuite ;
  extensions : Cstruct.t ; (* XXX: extensions! *)
  context : Cstruct.t ;
} [@@deriving sexp]

type psk_identity = (Cstruct.t * int32) * Cstruct.t [@@deriving sexp]

let binders_len psks =
  let binder_len (_, binder) =
    Cstruct.len binder + 1 (* binder len *)
  in
  2 (* binder len *) + List.fold_left (+) 0 (List.map binder_len psks)

type group = Nocrypto.Dh.group [@@deriving sexp] (* for now *)

type signature_algorithm = [
  | `RSA_PKCS1_MD5
  | `RSA_PKCS1_SHA1
  | `RSA_PKCS1_SHA224
  | `RSA_PKCS1_SHA256
  | `RSA_PKCS1_SHA384
  | `RSA_PKCS1_SHA512
(*  | `ECDSA_SECP256R1_SHA1
  | `ECDSA_SECP256R1_SHA256
  | `ECDSA_SECP256R1_SHA384
    | `ECDSA_SECP256R1_SHA512 *)
  | `RSA_PSS_RSAENC_SHA256
  | `RSA_PSS_RSAENC_SHA384
  | `RSA_PSS_RSAENC_SHA512
(*  | `ED25519
  | `ED448
  | `RSA_PSS_PSS_SHA256
  | `RSA_PSS_PSS_SHA384
    | `RSA_PSS_PSS_SHA512 *)
] [@@deriving sexp]

let hash_of_signature_algorithm = function
  | `RSA_PKCS1_MD5 -> `MD5
  | `RSA_PKCS1_SHA1 -> `SHA1
  | `RSA_PKCS1_SHA224 -> `SHA224
  | `RSA_PKCS1_SHA256 -> `SHA256
  | `RSA_PKCS1_SHA384 -> `SHA384
  | `RSA_PKCS1_SHA512 -> `SHA512
  | `RSA_PSS_RSAENC_SHA256 -> `SHA256
  | `RSA_PSS_RSAENC_SHA384 -> `SHA384
  | `RSA_PSS_RSAENC_SHA512 -> `SHA512

let signature_scheme_of_signature_algorithm = function
  | `RSA_PKCS1_MD5 -> `PKCS1
  | `RSA_PKCS1_SHA1 -> `PKCS1
  | `RSA_PKCS1_SHA224 -> `PKCS1
  | `RSA_PKCS1_SHA256 -> `PKCS1
  | `RSA_PKCS1_SHA384 -> `PKCS1
  | `RSA_PKCS1_SHA512 -> `PKCS1
  | `RSA_PSS_RSAENC_SHA256 -> `PSS
  | `RSA_PSS_RSAENC_SHA384 -> `PSS
  | `RSA_PSS_RSAENC_SHA512 -> `PSS

type client_extension = [
  | `Hostname of string
  | `MaxFragmentLength of max_fragment_length
  | `SupportedGroups of named_group list
  | `ECPointFormats of ec_point_format list
  | `SecureRenegotiation of Cstruct_sexp.t
  | `Padding of int
  | `SignatureAlgorithms of signature_algorithm list
  | `ExtendedMasterSecret
  | `ALPN of string list
  | `KeyShare of (named_group * Cstruct_sexp.t) list
  | `EarlyDataIndication of early_data
  | `PreSharedKeys of psk_identity list
  | `Draft of int
  | `SupportedVersions of tls_any_version list
  | `PostHandshakeAuthentication
  | `Cookie of Cstruct_sexp.t
  | `PskKeyExchangeModes of psk_key_exchange_mode list
  | `UnknownExtension of (int * Cstruct_sexp.t)
] [@@deriving sexp]

type server13_extension = [
  | `KeyShare of (group * Cstruct_sexp.t)
  | `PreSharedKey of int
  | `SelectedVersion of tls_version (* only used internally in writer!! *)
] [@@deriving sexp]

type server_extension = [
  server13_extension
  | `Hostname
  | `MaxFragmentLength of max_fragment_length
  | `ECPointFormats of ec_point_format list
  | `SecureRenegotiation of Cstruct_sexp.t
  | `ExtendedMasterSecret
  | `ALPN of string
  | `EarlyDataIndication
  | `Draft of int
  | `UnknownExtension of (int * Cstruct_sexp.t)
] [@@deriving sexp]

type encrypted_extension = [
  | `Hostname
  | `MaxFragmentLength of max_fragment_length
  | `SupportedGroups of named_group list
  | `ALPN of string
  | `UnknownExtension of (int * Cstruct_sexp.t)
] [@@deriving sexp]

type hello_retry_extension = [
  | `SelectedGroup of group (* only used internally in writer!! *)
  | `Cookie of Cstruct_sexp.t
  | `SelectedVersion of tls_version (* only used internally in writer!! *)
  | `UnknownExtension of (int * Cstruct_sexp.t)
] [@@deriving sexp]

type client_hello = {
  client_version : tls_any_version;
  client_random  : Cstruct_sexp.t;
  sessionid      : SessionID.t option;
  ciphersuites   : any_ciphersuite list;
  extensions     : client_extension list
} [@@deriving sexp]

type server_hello = {
  server_version : tls_version;
  server_random  : Cstruct_sexp.t;
  sessionid      : SessionID.t option;
  ciphersuite    : ciphersuite;
  extensions     : server_extension list
} [@@deriving sexp]

type dh_parameters = {
  dh_p  : Cstruct_sexp.t;
  dh_g  : Cstruct_sexp.t;
  dh_Ys : Cstruct_sexp.t;
} [@@deriving sexp]

type ec_curve = {
  a : Cstruct_sexp.t;
  b : Cstruct_sexp.t
} [@@deriving sexp]

type ec_prime_parameters = {
  prime    : Cstruct_sexp.t;
  curve    : ec_curve;
  base     : Cstruct_sexp.t;
  order    : Cstruct_sexp.t;
  cofactor : Cstruct_sexp.t;
  public   : Cstruct_sexp.t
} [@@deriving sexp]

type ec_char_parameters = {
  m        : int;
  basis    : ec_basis_type;
  ks       : Cstruct_sexp.t list;
  curve    : ec_curve;
  base     : Cstruct_sexp.t;
  order    : Cstruct_sexp.t;
  cofactor : Cstruct_sexp.t;
  public   : Cstruct_sexp.t
} [@@deriving sexp]

type ec_parameters =
  | ExplicitPrimeParameters of ec_prime_parameters
  | ExplicitCharParameters of ec_char_parameters
  | NamedGroupParameters of (group * Cstruct_sexp.t)
  [@@deriving sexp]

type hello_retry = {
  retry_version : tls_version ;
  ciphersuite : ciphersuite13 ;
  sessionid : SessionID.t option ;
  selected_group : group ;
  extensions : hello_retry_extension list
} [@@deriving sexp]

type session_ticket = {
  lifetime : int32 ;
  age_add : int32 ;
  nonce : int ;
  ticket : Cstruct.t ;
  (* TODO extensions *)
} [@@deriving sexp]

type certificate_request_extension = [
  (*  | `StatusRequest *)
  | `SignatureAlgorithms of signature_algorithm list
  (* | `SignedCertificateTimestamp *)
  | `CertificateAuthorities of X509.distinguished_name list
  (* | `OidFilters *)
  (* | `SignatureAlgorithmsCert *)
  | `UnknownExtension of (int * Cstruct.t)
]

type tls_handshake =
  | HelloRequest
  | HelloRetryRequest of hello_retry
  | EncryptedExtensions of encrypted_extension list
  | ServerHelloDone
  | ClientHello of client_hello
  | ServerHello of server_hello
  | Certificate of Cstruct_sexp.t
  | ServerKeyExchange of Cstruct_sexp.t
  | CertificateRequest of Cstruct_sexp.t
  | ClientKeyExchange of Cstruct_sexp.t
  | CertificateVerify of Cstruct_sexp.t
  | Finished of Cstruct_sexp.t
  | SessionTicket of session_ticket
  | KeyUpdate
  [@@deriving sexp]

type tls_alert = alert_level * alert_type [@@deriving sexp]

(** the master secret of a TLS connection *)
type master_secret = Cstruct_sexp.t [@@deriving sexp]

module Cert = struct
  include X509.Certificate
  let t_of_sexp _ = failwith "can't convert certificate from S-expression"
  let sexp_of_t _ = Sexplib.Sexp.Atom "certificate"
end

type psk13 = {
  identifier : Cstruct.t ;
  obfuscation : int32 ;
  nonce : int ; (* 0..255 *)
  (* origin : [ `Resumption | `External ] (* using different labels for binder_key *) *)
} [@@deriving sexp]

(** information about an open session *)
type epoch_data = {
  protocol_version       : tls_version ;
  ciphersuite            : Ciphersuite.ciphersuite ;
  peer_random            : Cstruct_sexp.t ;
  peer_certificate_chain : Cert.t list ;
  peer_certificate       : Cert.t option ;
  peer_name              : string option ;
  trust_anchor           : Cert.t option ;
  received_certificates  : Cert.t list ;
  own_random             : Cstruct_sexp.t ;
  own_certificate        : Cert.t list ;
  own_private_key        : Nocrypto.Rsa.priv option ;
  own_name               : string option ;
  master_secret          : master_secret ;
  session_id             : SessionID.t ;
  extended_ms            : bool ;
  alpn_protocol          : string option ;
  resumption_secret      : Cstruct.t ;
  exporter_secret        : Cstruct.t ;
  psk                    : psk13 option ;
} [@@deriving sexp]

let supports_key_usage ?(not_present = false) cert usage =
  match X509.Extension.(find Key_usage (X509.Certificate.extensions cert)) with
  | None -> not_present
  | Some (_, kus) -> List.mem usage kus

let supports_extended_key_usage ?(not_present = false) cert usage =
  match X509.Extension.(find Ext_key_usage (X509.Certificate.extensions cert)) with
  | None -> not_present
  | Some (_, kus) -> List.mem usage kus
