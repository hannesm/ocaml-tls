open Utils

open State
open Core
open Handshake_common

open Handshake_crypto13

let add_to_cache, find_in_cache =
  let c = ref [] in
  (fun id session ->
     Logs.info (fun m -> m "adding id %a to cache" Cstruct.hexdump_pp id) ;
     c := (id, session) :: !c),
  (fun id -> match List.find_opt (fun (id', _) -> Cstruct.compare id id' = 0) !c with
     | None -> None
     | Some (_, ep) -> Some ep)

let answer_client_hello state ch raw =
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
        sessionid = ch.sessionid ;
        ciphersuite ;
        extensions }
    in
    let session : session_data13 =
      (* let s = match epoch with None -> empty_session13 | Some e -> session_of_epoch13 e in *)
      let empty = empty_session13 cipher in
      let common_session_data13 = {
        empty.common_session_data13 with
        server_random = sh.server_random ;
        client_random = ch.client_random ;
      } in
      { empty with common_session_data13 ; ciphersuite13 = cipher ; kex13 = kex }
    in
    (sh, session)
  and keyshare group =
    try Some (snd (List.find (fun (g, _) -> g = group) keyshares)) with Not_found -> None
  in

  (* TODO a bit too early, may still be the case that we've to bail out if there
     is no matching cipher / group  *)
  Tracing.sexpf ~tag:"version" ~f:sexp_of_tls_version TLS_1_3 ;
  Log.info (fun m -> m "TLS 1.3");

  (* KEX to use:
    - if client has keyshare (+supportedgroup) ext, we can use (EC)DHE (if we have the same)
    - if client has presharedkey ext, plus PSK is in our databse, we can use PSK!
    - if client has keyshare (+supportedgroup) + presharedkey, we can use (EC)DHE-PSK

     error conditions:
      - no KS found that meets our demands -> HRR
      - TODO: what if KS found, but not part of supportedgroup?
      - what is PSK + KS + SG found, but PSK does not match --> (EC)DHE *)
  match
    first_match groups state.config.Config.groups,
    first_match ciphers state.config.Config.ciphers13
  with
  | None, _ -> fail (`Fatal `NoSupportedGroup)
  | _, None -> fail (`Error (`NoConfiguredCiphersuite ciphers))
  | Some group, Some cipher ->
    Log.info (fun m -> m "cipher %a" Sexplib.Sexp.pp_hum (Ciphersuite.sexp_of_ciphersuite13 cipher)) ;

    (* TODO handle PSK here (check PSK_KEY_EXCHANGE_MODES as well), there's no
       need for keyshare in a PSK-only handshake *)
    (* DHE_PSK OTOH requires a good group *)

    match keyshare group with
    | None ->
      let cookie = Nocrypto.Hash.digest (Ciphersuite.hash13 cipher) raw in
      let hrr = { retry_version = TLS_1_3 ; ciphersuite = cipher ; sessionid = ch.sessionid ; selected_group = group ; extensions = [ `Cookie cookie ] } in
      let hrr_raw = Writer.assemble_handshake (HelloRetryRequest hrr) in
      Tracing.sexpf ~tag:"handshake-out" ~f:sexp_of_tls_handshake (HelloRetryRequest hrr) ;
      return (state, [ `Record (Packet.HANDSHAKE, hrr_raw) ])
    | Some keyshare ->
      (* XXX: check sig_algs (better cert_sig_algs) whether we can present a
         suitable certificate chain and signature *)

      (* DHE - full handshake *)
      let log = match map_find ~f:(function `Cookie c -> Some c | _ -> None) ch.extensions with
        | None -> Cstruct.empty
        | Some c ->
          (* log is: 254 00 00 length c :: HRR *)
          let cs = Cstruct.create 4 in
          Cstruct.set_uint8 cs 0 (Packet.handshake_type_to_int Packet.MESSAGE_HASH) ;
          Cstruct.set_uint8 cs 3 (Cstruct.len c) ;
          let hrr = { retry_version = TLS_1_3 ; ciphersuite = cipher ; sessionid = ch.sessionid ; selected_group = group ; extensions = [ `Cookie c ]} in
          let hs_buf = Writer.assemble_handshake (HelloRetryRequest hrr) in
          Cstruct.concat [ cs ; c ; hs_buf ]
      in

      let early_secret, resumed_session =
        let secret ?(psk = Cstruct.create 32) () = Handshake_crypto13.(derive (empty cipher) psk) in
        match map_find ~f:(function `PreSharedKeys ids -> Some ids | _ -> None) ch.extensions with
        | None -> secret (), None
        | Some ids ->
          Log.info (fun m -> m "received %d ids" (List.length ids));

          let binders_len = binders_len ids in
          let ch_part = Cstruct.(sub raw 0 (len raw - binders_len)) in
          Log.info (fun m -> m "len is %d, part %d" binders_len (Cstruct.len ch_part)) ;
          match
            List.filter (fun ((id, _), _) ->
                (* TODO: verify max_age in here! *)
                match (* state.config.Config.psk_cache *) find_in_cache id with
                  None -> false | Some _ -> true)
              ids
          with
          | [] ->
            Log.info (fun m -> m "found no id in psk cache") ;
            secret (), None
          | ((id, max_age), binder)::_ ->
            (* need to verify binder, do the max_age computations + checking,
               figure out whether the id is in our psk cache, and use the resumption secret as input
               and return the idx *)
            (*            let old_epoch = *)
            let psk =
              match find_in_cache id (* state.config.Config.psk_cache id *) with
              | None -> assert false (* see above *)
              | Some x -> x
            in
            (*            let psk = match old_epoch.psk with None -> assert false | Some psk -> psk.secret in *)
            let early_secret = secret ~psk () in
            let binder_key = Handshake_crypto13.derive_secret early_secret "res binder" Cstruct.empty in
            let log = Cstruct.append log ch_part in
            let binder' = Handshake_crypto13.finished early_secret.hash binder_key log in
            if Cstruct.equal binder binder' then begin
              Log.info (fun m -> m "binder matched") ;
              early_secret, None
            end else begin
              Log.info (fun m -> m "binder mismatch %a vs %a"
                           Cstruct.hexdump_pp binder Cstruct.hexdump_pp binder') ;
              secret (), None
            end
      in

      (* match resumed_session with ... *)

        (* if acceptable, do server hello *)
        let secret, public = Handshake_crypto13.dh_gen_key group in
        (match Handshake_crypto13.dh_shared group secret keyshare with
         | None -> fail (`Fatal `InvalidDH)
         | Some shared -> return shared) >>= fun es ->
        let hs_secret = Handshake_crypto13.derive early_secret es in

        let sh, session = base_server_hello `DHE_RSA cipher [`KeyShare (group, public)] in
        let sh_raw = Writer.assemble_handshake (ServerHello sh) in

        Tracing.sexpf ~tag:"handshake-out" ~f:sexp_of_tls_handshake (ServerHello sh) ;

        let log = log <+> raw <+> sh_raw in
        let server_hs_secret, server_ctx, client_hs_secret, client_ctx = hs_ctx hs_secret log in

        (* ONLY if client sent a `Hostname *)
        let sg = `SupportedGroups (List.map Ciphersuite.group_to_any_group state.config.Config.groups) in
        let ee = EncryptedExtensions [ ] (* sg ] (* `Hostname ] *) *) in
        (* TODO also max_fragment_length ; client_certificate_url ; trusted_ca_keys ; user_mapping ; client_authz ; server_authz ; cert_type ; use_srtp ; heartbeat ; alpn ; status_request_v2 ; signed_cert_timestamp ; client_cert_type ; server_cert_type *)
        let ee_raw = Writer.assemble_handshake ee in

        Tracing.sexpf ~tag:"handshake-out" ~f:sexp_of_tls_handshake ee ;

        let cert_request, session = match state.config.Config.authenticator with
          | None -> (None, session)
          | Some _ ->
            let certreq =
              let exts =
                `SignatureAlgorithms state.config.Config.signature_algorithms ::
                (match state.config.Config.acceptable_cas with
                 | [] -> []
                 | cas -> [ `CertificateAuthorities cas ])
              in
              CertificateRequest (Writer.assemble_certificate_request_1_3 exts)
            in
            Tracing.sexpf ~tag:"handshake-out" ~f:sexp_of_tls_handshake certreq ;
            let common_session_data13 = { session.common_session_data13 with client_auth = true } in
            (Some (Writer.assemble_handshake certreq), { session with common_session_data13 })
        in

        let crt, pr = match state.config.Config.own_certificates with
          | `Single (chain, priv) -> chain, priv
          | _ -> assert false
        in
        let certs = List.map X509.Encoding.cs_of_cert crt in
        let cert = Certificate (Writer.assemble_certificates_1_3 Cstruct.empty certs) in
        let cert_raw = Writer.assemble_handshake cert in

        Tracing.sexpf ~tag:"handshake-out" ~f:sexp_of_tls_handshake cert ;

        let log =
          let req = match cert_request with None -> [] | Some xs -> [ xs ] in
          Cstruct.concat (log :: ee_raw :: req @ [ cert_raw ])
        in
        signature TLS_1_3 ~context_string:"TLS 1.3, server CertificateVerify"
          log (Some sigalgs) state.config.Config.signature_algorithms pr >>= fun signed ->
        let cv = CertificateVerify signed in
        let cv_raw = Writer.assemble_handshake cv in

        Tracing.cs ~tag:"cv" cv_raw ;
        Tracing.sexpf ~tag:"handshake-out" ~f:sexp_of_tls_handshake cv ;

        let log = log <+> cv_raw in
        let master_secret = Handshake_crypto13.derive hs_secret (Cstruct.create 32) in
        Tracing.cs ~tag:"master-secret" master_secret.secret ;

        let f_data = finished hs_secret.hash server_hs_secret log in
        let fin = Finished f_data in
        let fin_raw = Writer.assemble_handshake fin in

        Tracing.sexpf ~tag:"handshake-out" ~f:sexp_of_tls_handshake fin ;

        let log = log <+> fin_raw in
        let _, server_app_ctx, _, client_app_ctx = app_ctx master_secret log in

        guard (Cs.null state.hs_fragment) (`Fatal `HandshakeFragmentsNotEmpty) >|= fun () ->

        (* send sessionticket early *)
        (* TODO track the nonce across handshakes / newsessionticket messages (i.e. after post-handshake auth) - needs to be unique! *)
        let age_add =
          let cs = Nocrypto.Rng.generate 4 in
          Cstruct.BE.get_uint32 cs 0
        in
        let psk_id = Nocrypto.Rng.generate 32 in
        let nonce = Nocrypto.Rng.generate 4 in
        let st = { lifetime = 30000l ; age_add ; nonce ; ticket = psk_id } in
        Tracing.sexpf ~tag:"handshake-out" ~f:sexp_of_tls_handshake (SessionTicket st);
        let st_raw = Writer.assemble_handshake (SessionTicket st) in

        let session =
          let common_session_data13 = {
            session.common_session_data13 with
            own_private_key = Some pr ;
            own_certificate = crt ;
            master_secret = master_secret.secret
          } in
          { session with common_session_data13 ; master_secret (* TODO ; exporter_secret *) } in
        (* new state: one of AwaitClientCertificate13 , AwaitClientFinished13 *)
        let st, cert_req = match cert_request with
          | None -> AwaitClientFinished13 (session, client_hs_secret, client_app_ctx, st, log), []
          | Some creq -> AwaitClientCertificate13 (session, client_hs_secret, client_app_ctx, st, log),
                         [ `Record (Packet.HANDSHAKE, creq) ]
        in
        ({ state with machina = Server13 st },
         `Record (Packet.HANDSHAKE, sh_raw) ::
         (match ch.sessionid with
          | None -> []
          | Some _ -> [`Record change_cipher_spec]) @
         [ `Change_enc (Some server_ctx) ;
           `Change_dec (Some client_ctx) ;
           `Record (Packet.HANDSHAKE, ee_raw) ] @
         cert_req
         @ [ `Record (Packet.HANDSHAKE, cert_raw) ;
             `Record (Packet.HANDSHAKE, cv_raw) ;
             `Record (Packet.HANDSHAKE, fin_raw) ;
             `Change_enc (Some server_app_ctx) ;
             `Record (Packet.HANDSHAKE, st_raw)
         ])

let answer_client_certificate state cert (sd : session_data13) client_fini dec_ctx st raw log =
  match Reader.parse_certificates_1_3 cert, state.config.Config.authenticator with
  | Error re, _ -> fail (`Fatal (`ReaderError re))
  | Ok (_, []), None -> assert false
  | Ok (_ctx, []), Some auth ->
    begin match auth [] with
      | `Ok anchor ->
        let trust_anchor = match anchor with
          | None -> None
          | Some (_chain, ta) -> Some ta
        in
        let common_session_data13 = { sd.common_session_data13 with trust_anchor } in
        let sd = { sd with common_session_data13 } in
        let st = AwaitClientFinished13 (sd, client_fini, dec_ctx, st, log <+> raw) in
        Ok ({ state with machina = Server13 st }, [])
      | `Fail e -> fail (`Error (`AuthenticationFailure e))
    end
  | Ok (_ctx, cert_exts), auth ->
    (* TODO what to do with ctx? send through authenticator? *)
    (* TODO what to do with extensions? *)
    let certs = List.map fst cert_exts in
    validate_chain auth certs None >|= fun (peer_certificate, received_certificates, peer_certificate_chain, trust_anchor) ->
    let sd' = let common_session_data13 = {
        sd.common_session_data13 with
        received_certificates ;
        peer_certificate ;
        peer_certificate_chain ;
        trust_anchor
      } in
      { sd with common_session_data13 }
    in
    let st = AwaitClientCertificateVerify13 (sd', client_fini, dec_ctx, st, log <+> raw) in
    ({ state with machina = Server13 st }, [])

let answer_client_certificate_verify state cv (sd : session_data13) client_fini dec_ctx st raw log =
  verify_digitally_signed TLS_1_3 ~context_string:"TLS 1.3, client CertificateVerify" state.config.Config.signature_algorithms cv log sd.common_session_data13.peer_certificate >|= fun () ->
  let st = AwaitClientFinished13 (sd, client_fini, dec_ctx, st, log <+> raw) in
  ({ state with machina = Server13 st }, [])

let answer_client_finished state fin (sd : session_data13) client_fini dec_ctx st raw log =
  let hash = Ciphersuite.hash13 sd.ciphersuite13 in
  let data = finished hash client_fini log in
  guard (Cs.equal data fin) (`Fatal `BadFinished) >>= fun () ->
  guard (Cs.null state.hs_fragment) (`Fatal `HandshakeFragmentsNotEmpty) >|= fun () ->
  let sd =
    let resumption_secret = Handshake_crypto13.resumption sd.master_secret (log <+> raw) in
    let secret = Handshake_crypto13.res_secret (Ciphersuite.hash13 sd.ciphersuite13) resumption_secret st.nonce in
    let psk = { identifier = st.ticket ; obfuscation = st.age_add ; secret } in
    add_to_cache st.ticket secret ;
    { sd with psk = Some psk ; resumption_secret }
  in
  ({ state with
     machina = Server13 Established13 ;
     session = `TLS13 sd :: state.session },
   [ `Change_dec (Some dec_ctx) ])

let handle_handshake cs hs buf =
  let open Reader in
  match parse_handshake buf with
  | Ok handshake ->
     Tracing.sexpf ~tag:"handshake-in" ~f:sexp_of_tls_handshake handshake;
     (match cs, handshake with
      | AwaitClientCertificate13 (sd, cf, cc, st, log), Certificate cert ->
        answer_client_certificate hs cert sd cf cc st buf log
      | AwaitClientCertificateVerify13 (sd, cf, cc, st, log), CertificateVerify cv ->
        answer_client_certificate_verify hs cv sd cf cc st buf log
      | AwaitClientFinished13 (sd, cf, cc, st, log), Finished x ->
         answer_client_finished hs x sd cf cc st buf log
      | _, hs -> fail (`Fatal (`UnexpectedHandshake hs)) )
  | Error re -> fail (`Fatal (`ReaderError re))
