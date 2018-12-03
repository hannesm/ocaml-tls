
open Lwt
open Ex_common

let http_client ?ca ?fp hostname port =
  let port          = int_of_string port in
  X509_lwt.authenticator
    ( match ca, fp with
      | None, Some fp  -> `Hex_key_fingerprints (`SHA256, [ Domain_name.(host_exn (of_string_exn hostname)), fp ])
      | None, _        -> `Ca_dir ca_cert_dir
      | Some "NONE", _ -> `No_authentication_I'M_STUPID
      | Some f, _      -> `Ca_file f ) >>= fun authenticator ->
  Tls_lwt.connect_ext
    (Tls.Config.client ~authenticator ())
    (hostname, port) >>= fun (ic, oc) ->
  let req = String.concat "\r\n" [
    "GET / HTTP/1.1" ; "Host: " ^ hostname ; "Connection: close" ; "" ; ""
  ] in
  Lwt_io.(write oc req >>= fun () -> read ic >>= print >>= fun () -> printf "++ done.\n%!")

let () =
  try
    match Sys.argv with
    | [| _ ; host ; port ; "FP" ; fp |] -> Lwt_main.run (http_client host port ~fp)
    | [| _ ; host ; port ; trust |] -> Lwt_main.run (http_client host port ~ca:trust)
    | [| _ ; host ; port |]         -> Lwt_main.run (http_client host port)
    | [| _ ; host |]                -> Lwt_main.run (http_client host "443")
    | args                          -> Printf.eprintf "%s <host> <port>\n%!" args.(0)
  with
  | Tls_lwt.Tls_alert alert as exn ->
      print_alert "remote end" alert ; raise exn
  | Tls_lwt.Tls_failure fail as exn ->
      print_fail "our end" fail ; raise exn

