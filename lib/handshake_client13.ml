open Utils

open State
open Core
open Handshake_common
open Config

(* TODO CCS *)

let answer_server_hello state ch (sh : server_hello) secrets raw log =
  (* assume SH valid, version 1.3, extensions are subset *)
  Logs.info (fun m -> m "here") ;
  match Ciphersuite.ciphersuite_to_ciphersuite13 sh.ciphersuite with
  | None -> fail (`Fatal `InvalidServerHello)
  | Some cipher ->
    guard (List.mem cipher state.config.ciphers13) (`Fatal `InvalidServerHello) >>= fun () ->
    guard (Cs.null state.hs_fragment) (`Fatal `HandshakeFragmentsNotEmpty) >>= fun () ->

    (* TODO: PSK *)
    (* TODO: early_secret elsewhere *)
    match map_find ~f:(function `KeyShare ks -> Some ks | _ -> None) sh.extensions with
    | None -> fail (`Fatal `InvalidServerHello)
    | Some (g, share) ->
      match List.find_opt (fun (g', _) -> g = g') secrets with
      | None -> fail (`Fatal `InvalidServerHello)
      | Some (_, secret) ->
        match Handshake_crypto13.dh_shared g secret share with
        | None -> fail (`Fatal `InvalidServerHello)
        | Some psk ->
          let hlen = Nocrypto.Hash.digest_size (Ciphersuite.hash13 cipher) in
          let early_secret = Handshake_crypto13.(derive (empty cipher) (Cstruct.create hlen)) in
          let hs_secret = Handshake_crypto13.derive early_secret psk in
          let log = log <+> raw in
          let server_hs_secret, server_ctx, client_hs_secret, client_ctx =
            Handshake_crypto13.hs_ctx hs_secret log in
          let master_secret = Handshake_crypto13.derive hs_secret (Cstruct.create hlen) in
          (* TODO: preserve more data
             master_secret
          *)
          let session =
            let base = empty_session13 cipher in
            let common_session_data13 =
              { base.common_session_data13 with
                server_random = sh.server_random ;
                client_random = ch.client_random ;
                master_secret = master_secret.secret }
            in
            { base with master_secret ; common_session_data13 }
          in
          let st = AwaitServerEncryptedExtensions13 (session, server_hs_secret, client_hs_secret, log) in
          Ok ({ state with machina = Client13 st ; protocol_version = TLS_1_3 },
              [ `Change_enc (Some client_ctx) ;
                `Change_dec (Some server_ctx) ])

(* called from handshake_client.ml *)
let answer_hello_retry_request state (ch : client_hello) hrr secrets raw log =
  (* when is a HRR invalid / what do we need to check?
     -> we advertised the group and cipher
     -> TODO we did advertise such a keyshare already (does it matter?)
  *)
  guard (TLS_1_3 = hrr.retry_version) (`Fatal `InvalidMessage) >>= fun () ->
  guard (List.mem hrr.selected_group state.config.groups) (`Fatal `InvalidMessage) >>= fun () ->
  guard (List.mem hrr.ciphersuite state.config.ciphers13) (`Fatal `InvalidMessage) >>= fun () ->
  (* generate a fresh keyshare *)
  let secret, keyshare =
    let g = hrr.selected_group in
    let priv, share = Handshake_crypto13.dh_gen_key g in
    (g, priv), (group_to_named_group g, share)
  in
  (* append server extensions (i.e. cookie!) *)
  let cookie = match map_find ~f:(function `Cookie c -> Some c | _ -> None) hrr.extensions with
    | None -> []
    | Some c -> [ `Cookie c ]
  in
  (* use the same extensions as in original CH, apart from PSK!? and early_data *)
  let other_exts = List.filter (function `KeyShare _ -> false | _ -> true) ch.extensions in
  let new_ch = { ch with extensions = `KeyShare [keyshare] :: other_exts @ cookie} in
  let new_ch_raw = Writer.assemble_handshake (ClientHello new_ch) in
  let ch0_data = Nocrypto.Hash.digest (Ciphersuite.hash13 hrr.ciphersuite) log in
  let ch0_hdr = Writer.assemble_message_hash (Cstruct.len ch0_data) in
  let st = AwaitServerHello13 (new_ch, [secret], Cs.appends [ ch0_hdr ; ch0_data ; raw ; new_ch_raw ]) in

  Tracing.sexpf ~tag:"handshake-out" ~f:sexp_of_tls_handshake (ClientHello new_ch);
  return ({ state with machina = Client13 st ; protocol_version = TLS_1_3 }, [`Record (Packet.HANDSHAKE, new_ch_raw)])

let answer_encrypted_extensions state (session : session_data13) server_hs_secret client_hs_secret ee raw log =
  (* TODO we now know: - hostname - early_data (preserve this in session!!) *)
  (* next message is either CertificateRequest or Certificate (or finished if PSK) *)
  let alpn_protocol = map_find ~f:(function `ALPN proto -> Some proto | _ -> None) ee in
  let session =
    let common_session_data13 = { session.common_session_data13 with alpn_protocol } in
    { session with common_session_data13 }
  in
  let st =
(*    if Ciphersuite.ciphersuite_psk session.ciphersuite then
      AwaitServerFinished13 (session, server_hs_secret, client_hs_secret, log <+> raw)
      else*)
    AwaitServerCertificateRequestOrCertificate13 (session, server_hs_secret, client_hs_secret, log <+> raw)
  in
  return ({ state with machina = Client13 st }, [])

let answer_certificate state (session : session_data13) server_hs_secret client_hs_secret certs raw log =
  let name = match state.config.peer_name with
    | None -> None | Some x -> Some (`Wildcard x)
  in
  (* certificates are (cs, ext) list - ext being statusrequest or signed_cert_timestamp *)
  let certs = List.map fst certs in
  validate_chain state.config.authenticator certs name >>=
  fun (peer_certificate, received_certificates, peer_certificate_chain, trust_anchor) ->
  let session =
    let common_session_data13 = {
      session.common_session_data13 with
      received_certificates ; peer_certificate_chain ; peer_certificate ; trust_anchor
    } in
    { session with common_session_data13 }
  in
  let st = AwaitServerCertificateVerify13 (session, server_hs_secret, client_hs_secret, log <+> raw) in
  return ({ state with machina = Client13 st }, [])

let answer_certificate_verify (state : handshake_state) (session : session_data13) server_hs_secret client_hs_secret cv raw log =
  verify_digitally_signed state.protocol_version
    ~context_string:"TLS 1.3, server CertificateVerify"
    state.config.signature_algorithms cv log
    session.common_session_data13.peer_certificate >>= fun () ->
  let st = AwaitServerFinished13 (session, server_hs_secret, client_hs_secret, log <+> raw) in
  return ({ state with machina = Client13 st }, [])

let answer_finished state (session : session_data13) server_hs_secret client_hs_secret fin raw log =
  let hash = Ciphersuite.hash13 session.ciphersuite13 in
  let f_data = Handshake_crypto13.finished hash server_hs_secret log in
  guard (Cs.equal fin f_data) (`Fatal `BadFinished) >>= fun () ->
  guard (Cs.null state.hs_fragment) (`Fatal `HandshakeFragmentsNotEmpty) >|= fun () ->

  let log = log <+> raw in
  let _, server_app_ctx, _, client_app_ctx = Handshake_crypto13.app_ctx session.master_secret log in
  let myfin = Handshake_crypto13.finished hash client_hs_secret log in
  let mfin = Writer.assemble_handshake (Finished myfin) in
  let machina = Client13 Established13 in

  Tracing.sexpf ~tag:"handshake-out" ~f:sexp_of_tls_handshake (Finished myfin);

  ({ state with machina ; session = `TLS13 session :: state.session },
   [ `Change_dec (Some server_app_ctx) ;
     `Record (Packet.HANDSHAKE, mfin) ;
     `Change_enc (Some client_app_ctx) ])

let answer_session_ticket state _se =
  (* XXX: do sth with lifetime *)
(*  (match state.session with
   (*   | s::xs when not (Ciphersuite.ciphersuite_psk s.ciphersuite) -> return ({ s with psk_id } :: xs) *)
    | _ -> fail (`Fatal `InvalidMessage)) >>= fun session -> *)
  (*  return ({ state with session }, []) *)
  return (state, [])

let handle_handshake cs hs buf =
  let open Reader in
  match parse_handshake buf with
  | Ok handshake ->
     Tracing.sexpf ~tag:"handshake-in" ~f:sexp_of_tls_handshake handshake;
     (match cs, handshake with
      | AwaitServerHello13 (ch, secrets, log), ServerHello sh ->
         answer_server_hello hs ch sh secrets buf log
      | AwaitServerEncryptedExtensions13 (sd, es, ss, log), EncryptedExtensions ee ->
         answer_encrypted_extensions hs sd es ss ee buf log
      | AwaitServerCertificateRequestOrCertificate13 (sd, es, ss, log), CertificateRequest _ ->
        assert false (* TODO process CR *)
      | AwaitServerCertificateRequestOrCertificate13 (sd, es, ss, log), Certificate cs ->
        (match parse_certificates_1_3 cs with
         | Ok (con, cs) ->
           (* during handshake, context must be empty! and we'll not get any new certificate from server *)
           guard (Cs.null con) (`Fatal `InvalidMessage) >>= fun () ->
           answer_certificate hs sd es ss cs buf log
         | Error re -> fail (`Fatal (`ReaderError re)))
      | AwaitServerCertificateVerify13 (sd, es, ss, log), CertificateVerify cv ->
         answer_certificate_verify hs sd es ss cv buf log
      | AwaitServerFinished13 (sd, es, ss, log), Finished fin ->
         answer_finished hs sd es ss fin buf log
      | Established13, SessionTicket se -> answer_session_ticket hs se
      | Established13, CertificateRequest _ -> assert false (* maybe send out C, CV, F *)
      | _, hs -> fail (`Fatal (`UnexpectedHandshake hs)))
  | Error re -> fail (`Fatal (`ReaderError re))
