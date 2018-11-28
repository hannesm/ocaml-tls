open Utils

open State
open Core
open Handshake_common

open Handshake_crypto13

let answer_client_hello state ch raw log =
  (match client_hello_valid ch with
   | `Error e -> fail (`Fatal (`InvalidClientHello e))
   | `Ok -> return () ) >>= fun () ->

  (* TODO: if early_data 0RTT *)
  let ciphers =
    filter_map ~f:Ciphersuite.any_ciphersuite_to_ciphersuite13 ch.ciphersuites
  in

  ( match map_find ~f:(function `SignatureAlgorithms sa -> Some sa | _ -> None) ch.extensions with
    | None -> fail (`Fatal (`InvalidClientHello `NoSignatureAlgorithmsExtension))
    | Some sa -> return sa ) >>= fun sigalgs ->

  ( match map_find ~f:(function `SupportedGroups gs -> Some gs | _ -> None) ch.extensions with
    | None -> fail (`Fatal (`InvalidClientHello `NoSupportedGroupExtension))
    | Some gs -> return (filter_map ~f:Ciphersuite.any_group_to_group gs )) >>= fun groups ->

  ( match map_find ~f:(function `KeyShare ks -> Some ks | _ -> None) ch.extensions with
    | None -> fail (`Fatal (`InvalidClientHello `NoKeyShareExtension))
    | Some ks ->
       let f (g, ks) = match Ciphersuite.any_group_to_group g with
         | None -> None
         | Some g -> Some (g, ks)
       in
       return (filter_map ~f ks) ) >>= fun keyshares ->

  let base_server_hello ?epoch kex cipher extensions =
    let ciphersuite = (cipher :> Ciphersuite.ciphersuite) in
    let sh =
      { server_version = TLS_1_3 ;
        server_random = Nocrypto.Rng.generate 32 ;
        sessionid = None ;
        ciphersuite ;
        extensions }
    in
    let session : session_data13 =
      (* let s = match epoch with None -> empty_session13 | Some e -> session_of_epoch13 e in *)
      { server_random = sh.server_random ;
        client_random = ch.client_random ;
        ciphersuite = cipher ;
        kex ;
        peer_certificate_chain = [] ;
        peer_certificate = None ;
        trust_anchor = None ;
        received_certificates = [] ;
        own_certificate = [] ;
        own_private_key = None ;
        master_secret = Cstruct.create 0 ;
        own_name = None ;
        client_auth = false ;
        alpn_protocol = None ;
        resumption_secret = Cstruct.create 0 ;
        psk_id = Cstruct.create 0 }
    in
    (sh, session)
  and resumed_session =
    match map_find ~f:(function `PreSharedKey ids -> Some ids | _ -> None) ch.extensions with
    | None -> None
    | Some ids ->
      match
        List.filter (function None -> false | Some _ -> true)
          (List.map state.config.Config.psk_cache ids)
      with
      | x::_ -> x
      | [] -> None
  and keyshare group =
    snd (List.find (fun (g, _) -> g = group) keyshares)
  in

  Tracing.sexpf ~tag:"version" ~f:sexp_of_tls_version TLS_1_3 ;

  (* KEX to use:
    - if client has keyshare (+supportedgroup) ext, we can use (EC)DHE (if we have the same)
    - if client has presharedkey ext, plus PSK is in our databse, we can use PSK!
    - if client has keyshare (+supportedgroup) + presharedkey, we can use (EC)DHE-PSK

     error conditions:
      - no KS found that meets our demands -> HRR
      - TODO: what if KS found, but not part of supportedgroup?
      - what is PSK + KS + SG found, but PSK does not match --> (EC)DHE *)
  match
    resumed_session,
    first_match (List.map fst keyshares) state.config.Config.groups,
    first_match ciphers state.config.Config.ciphers13
  with
  | Some epoch, Some group, _ -> invalid_arg "NYI"
(*    (* DHE_PSK *)
    (* trace_cipher dhe_psk_cipher ; *)
    let keyshare = keyshare group in
    let secret, my_share = Nocrypto.Dh.gen_key group in

    let sh, session = base_server_hello ~epoch `DHE_PSK dhe_psk_cipher [`PreSharedKey epoch.psk_id ; `KeyShare (group, my_share)] in
    let sh_raw = Writer.assemble_handshake (ServerHello sh) in

    Tracing.sexpf ~tag:"handshake-out" ~f:sexp_of_tls_handshake (ServerHello sh) ;

    let ss = epoch.resumption_secret in
    ( match Nocrypto.Dh.shared group secret keyshare with
      | None -> fail (`Fatal `InvalidDH)
      | Some shared -> return shared ) >>= fun es ->

    let log = log <+> raw <+> sh_raw in
    let server_ctx, client_ctx = hs_ctx dhe_psk_cipher log es in

    let ee = EncryptedExtensions [`Hostname] in
    let ee_raw = Writer.assemble_handshake ee in

    Tracing.sexpf ~tag:"handshake-out" ~f:sexp_of_tls_handshake ee ;

    let log = log <+> ee_raw in
    let master_secret = master_secret dhe_psk_cipher es ss log in
    Tracing.cs ~tag:"master-secret" master_secret ;

    let traffic_secret = traffic_secret dhe_psk_cipher master_secret log in

    let f_data = finished dhe_psk_cipher master_secret true log in
    let fin = Finished f_data in
    let fin_raw = Writer.assemble_handshake fin in

    Tracing.sexpf ~tag:"handshake-out" ~f:sexp_of_tls_handshake fin ;

    let log = log <+> fin_raw in
    let server_app_ctx, client_app_ctx = app_ctx dhe_psk_cipher log traffic_secret in

    guard (Cs.null state.hs_fragment) (`Fatal `HandshakeFragmentsNotEmpty) >|= fun () ->

    let session = { session with master_secret } in
    let st = AwaitClientFinished13 (session, Some client_app_ctx, log) in
    ({ state with machina = Server13 st },
     [ `Record (Packet.HANDSHAKE, sh_raw) ;
       `Change_enc (Some server_ctx) ;
       `Change_dec (Some client_ctx) ;
       `Record (Packet.HANDSHAKE, ee_raw) ;
       `Record (Packet.HANDSHAKE, fin_raw) ;
       `Change_enc (Some server_app_ctx) ] ) *)

  | Some epoch, None, _ -> invalid_arg "NYI"
(*    (* PSK *)
    trace_cipher psk_cipher ;
    let sh, session = base_server_hello ~epoch `PSK psk_cipher [`PreSharedKey epoch.psk_id] in
    let sh_raw = Writer.assemble_handshake (ServerHello sh) in

    Tracing.sexpf ~tag:"handshake-out" ~f:sexp_of_tls_handshake (ServerHello sh) ;

    let es = epoch.resumption_secret in
    let ss = es in

    let log = log <+> raw <+> sh_raw in
    let server_ctx, client_ctx = hs_ctx psk_cipher log es in

    let ee = EncryptedExtensions [`Hostname] in
    let ee_raw = Writer.assemble_handshake ee in

    Tracing.sexpf ~tag:"handshake-out" ~f:sexp_of_tls_handshake ee ;

    let log = log <+> ee_raw in
    let master_secret = master_secret psk_cipher es ss log in
    Tracing.cs ~tag:"master-secret" master_secret ;

    let traffic_secret = traffic_secret psk_cipher master_secret log in

    let f_data = finished psk_cipher master_secret true log in
    let fin = Finished f_data in
    let fin_raw = Writer.assemble_handshake fin in

    Tracing.sexpf ~tag:"handshake-out" ~f:sexp_of_tls_handshake fin ;

    let log = log <+> fin_raw in
    let server_app_ctx, client_app_ctx = app_ctx psk_cipher log traffic_secret in

    guard (Cs.null state.hs_fragment) (`Fatal `HandshakeFragmentsNotEmpty) >|= fun () ->

    let session = { session with master_secret } in
    let st = AwaitClientFinished13 (session, Some client_app_ctx, log) in
    ({ state with machina = Server13 st },
     [ `Record (Packet.HANDSHAKE, sh_raw) ;
       `Change_enc (Some server_ctx) ;
       `Change_dec (Some client_ctx) ;
       `Record (Packet.HANDSHAKE, ee_raw) ;
       `Record (Packet.HANDSHAKE, fin_raw) ;
       `Change_enc (Some server_app_ctx) ] ) *)

  | None, Some group, Some cipher ->
    (* DHE - full handshake *)
    (* trace_cipher cipher ; *)
    let keyshare = keyshare group in
    (* XXX: for-each ciphers there should be a suitable group (skipping for now since we only have DHE) *)
    (* XXX: check sig_algs for signatures in certificate chain *)

    let early_secret = Handshake_crypto13.(derive (empty cipher) (Cstruct.create 32)) in

(* if acceptable, do server hello *)
    let secret, public = Nocrypto.Dh.gen_key group in
    (match Nocrypto.Dh.shared group secret keyshare with
     | None -> fail (`Fatal `InvalidDH)
     | Some shared -> return shared) >>= fun es ->
    let hs_secret = Handshake_crypto13.derive early_secret es in

    let sh, session = base_server_hello `DHE cipher [`KeyShare (group, public)] in
    let sh_raw = Writer.assemble_handshake (ServerHello sh) in

    Tracing.sexpf ~tag:"handshake-out" ~f:sexp_of_tls_handshake (ServerHello sh) ;

    let log = log <+> raw <+> sh_raw in
    let server_hs_secret, server_ctx, client_hs_secret, client_ctx = hs_ctx hs_secret log in

    (* ONLY if client sent a `Hostname *)
    let ee = EncryptedExtensions [ `Hostname ] in
    (* TODO also max_fragment_length ; client_certificate_url ; trusted_ca_keys ; user_mapping ; client_authz ; server_authz ; cert_type ; use_srtp ; heartbeat ; alpn ; status_request_v2 ; signed_cert_timestamp ; client_cert_type ; server_cert_type *)
    let ee_raw = Writer.assemble_handshake ee in

    Tracing.sexpf ~tag:"handshake-out" ~f:sexp_of_tls_handshake ee ;

    let crt, pr = match state.config.Config.own_certificates with
      | `Single (chain, priv) -> chain, priv
      | _ -> assert false
    in
    let certs = List.map X509.Encoding.cs_of_cert crt in
    let cert = Certificate (Writer.assemble_certificates_1_3 Cstruct.empty certs) in
    let cert_raw = Writer.assemble_handshake cert in

    Tracing.sexpf ~tag:"handshake-out" ~f:sexp_of_tls_handshake cert ;

    let log = Cstruct.concat [ log ; ee_raw ; cert_raw ] in
    signature TLS_1_3 ~context_string:"TLS 1.3, server CertificateVerify"
      log (Some sigalgs) state.config.Config.signature_algorithms pr >>= fun signed ->
    let cv = CertificateVerify signed in
    let cv_raw = Writer.assemble_handshake cv in

    Tracing.cs ~tag:"cv" cv_raw ;
    Tracing.sexpf ~tag:"handshake-out" ~f:sexp_of_tls_handshake cv ;

    let log = log <+> cv_raw in
    let master_secret = Handshake_crypto13.derive hs_secret (Cstruct.create 32) in
    Tracing.cs ~tag:"master-secret" master_secret.secret ;
    (* let resumption_secret = resumption_secret cipher master_secret log in *)

    let f_data = finished hs_secret.hash server_hs_secret log in
    let fin = Finished f_data in
    let fin_raw = Writer.assemble_handshake fin in

    Tracing.sexpf ~tag:"handshake-out" ~f:sexp_of_tls_handshake fin ;

    let log = log <+> fin_raw in
    let _, server_app_ctx, _, client_app_ctx = app_ctx master_secret log in

    guard (Cs.null state.hs_fragment) (`Fatal `HandshakeFragmentsNotEmpty) >|= fun () ->

    let session = { session with own_private_key = Some pr ; own_certificate =  crt ; master_secret = master_secret.secret (* ; resumption_secret *) } in
    (* new state: one of AwaitClientCertificate13 , AwaitClientFinished13 *)
    let st = AwaitClientFinished13 (session, client_hs_secret, client_app_ctx, log) in
    ({ state with machina = Server13 st },
     [ `Record (Packet.HANDSHAKE, sh_raw) ;
       `Change_enc (Some server_ctx) ;
       `Change_dec (Some client_ctx) ;
       `Record (Packet.HANDSHAKE, ee_raw) ;
       `Record (Packet.HANDSHAKE, cert_raw) ;
       `Record (Packet.HANDSHAKE, cv_raw) ;
       `Record (Packet.HANDSHAKE, fin_raw) ;
       `Change_enc (Some server_app_ctx) ] )

  | None, None, None
  | None, Some _, None
  | None, None, Some _ -> invalid_arg "NYI"

(*  | _, None, _, _, Some cipher when Cs.null log ->
    ( match first_match groups state.config.Config.groups with
      | None -> fail (`Fatal `NoSupportedGroup)
      | Some group ->
        let hrr = { version = TLS_1_3 ;
                    ciphersuite = cipher ;
                    selected_group = group ;
                    extensions = [] }
        in
        let hrr_raw = Writer.assemble_handshake (HelloRetryRequest hrr) in

        Tracing.sexpf ~tag:"handshake-out" ~f:sexp_of_tls_handshake (HelloRetryRequest hrr) ;

        let log = raw <+> hrr_raw in
        let st = AwaitClientHello13 (ch, hrr, log) in
        return ({ state with machina = Server13 st },
                [ `Record (Packet.HANDSHAKE, hrr_raw) ]) )

  | _, _, _, _, Some _ ->
    (* already sent a hello retry request, not doing this game again *)
    fail (`Fatal `InvalidMessage)

  | _, _, _, _, None ->
    fail (`Error (`NoConfiguredCiphersuite ciphers)) *)

let answer_client_finished state fin (sd : session_data13) client_fini dec_ctx raw log =
  let hash = Ciphersuite.hash13 sd.ciphersuite in
  let data = finished hash client_fini log in
  guard (Cs.equal data fin) (`Fatal `BadFinished) >>= fun () ->
  guard (Cs.null state.hs_fragment) (`Fatal `HandshakeFragmentsNotEmpty) >|= fun () ->
  let ret =
    (* only change dec if we're in handshake, also send out session ticket only just after handshake (and only if no PSK) *)
    [`Change_dec (Some dec_ctx)]
(*    and st, sd =
      match sd.kex with
      | `PSK -> ([], sd)
      | `DHE_PSK | `DHE ->
        let st, psk_id =
          let rand = Nocrypto.Rng.generate 48 in
          let buf = Writer.assemble_session_ticket_1_3 0l rand in
          (SessionTicket buf, rand)
        in
        let st_raw = Writer.assemble_handshake st in
        ([ `Record (Packet.HANDSHAKE, st_raw) ], { sd with psk_id })
      in *)
  in
  ({ state with
     machina = Server13 Established13 ;
     session = `TLS13 sd :: state.session },
    ret)

let answer_client_hello_retry state oldch ch hrr raw log =
  (* ch = oldch + keyshare for hrr.selected_group (6.3.1.3) *)
  guard (oldch.client_version = ch.client_version) (`Fatal `InvalidMessage) >>= fun () ->
  guard (oldch.ciphersuites = ch.ciphersuites) (`Fatal `InvalidMessage) >>= fun () ->
  (* XXX: properly check that extensions are the same, plus a keyshare for the selected_group *)
  (* clients must send keyshare extension in any case (6.3.2.3), but may be empty *)
  guard (List.length oldch.extensions = List.length ch.extensions) (`Fatal `InvalidMessage) >>= fun () ->
  answer_client_hello state ch raw log (* XXX: TLS draft: restart hash? https://github.com/tlswg/tls13-spec/issues/104 *)

let handle_handshake cs hs buf =
  let open Reader in
  match parse_handshake buf with
  | Ok handshake ->
     Tracing.sexpf ~tag:"handshake-in" ~f:sexp_of_tls_handshake handshake;
     (match cs, handshake with
      | AwaitClientHello13 (oldch, hrr, log), ClientHello ch ->
         answer_client_hello_retry hs oldch ch hrr buf log
      | AwaitClientCertificate13, Certificate _ -> assert false (* process C, move to CV *)
      | AwaitClientCertificateVerify13, CertificateVerify _ -> assert false (* validate CV *)
      | AwaitClientFinished13 (sd, cf, cc, log), Finished x ->
         answer_client_finished hs x sd cf cc buf log
      | _, hs -> fail (`Fatal (`UnexpectedHandshake hs)) )
  | Error re -> fail (`Fatal (`ReaderError re))
