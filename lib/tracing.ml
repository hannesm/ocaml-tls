(* This is so not thread-safe it's not even funny. *)

let src = Logs.Src.create "tracing" ~doc:"TLS tracing"
module Log = (val Logs.src_log src : Logs.LOG)

let form_trace id sexp =
  let open Sexplib in
  Sexp.(List [ Atom id ; sexp ])

let sexp ~tag lz =
  Log.debug (fun m -> m "%a" Sexplib.Sexp.pp_hum (form_trace tag (Lazy.force lz)))

let sexps ~tag lzs = List.iter (sexp ~tag) lzs

let sexpf ~tag ~f x = sexp ~tag @@ lazy (f x)

let sexpfs ~tag ~f xs = List.iter (sexpf ~tag ~f) xs

let cs ~tag = sexpf ~tag ~f:(fun cs -> Cstruct.hexdump cs ; Cstruct.sexp_of_t cs)

let css ~tag css = List.iter (cs ~tag) css
