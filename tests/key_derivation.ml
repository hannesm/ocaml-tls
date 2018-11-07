let cs =
  let module M = struct
    type t = Cstruct.t
    let pp = Cstruct.hexdump_pp
    let equal = Cstruct.equal
  end in (module M : Alcotest.TESTABLE with type t = M.t)

let secret0 = Cstruct.of_hex {|
33 ad 0a 1c 60 7e c0 3b  09 e6 cd 98 93 68 0c e2
10 ad f3 00 aa 1f 26 60  e1 b2 2e 10 f1 70 f9 2a
|}

let extract_secret_early () =
  (* draft-ietf-tls-tls13-vectors-07 Sec 3*)
  let salt = Cstruct.empty
  and ikm = Cstruct.create 32
  in
  Alcotest.check cs __LOC__ secret0 (Hkdf.extract ~hash:`SHA256 ~salt ikm)

let expand0 = Cstruct.of_hex {|
6f 26 15 a1 08 c7 02 c5  67 8f 54 fc 9d ba b6 97
16 c0 76 18 9c 48 25 0c  eb ea c3 57 6c 36 11 ba
|}

let derive_hs_secret () =
  let hash = Nocrypto.Hash.digest `SHA256 Cstruct.empty in
  Alcotest.check cs __LOC__ expand0
    (Handshake_crypto13.expand_label `SHA256 secret0 "derived" hash 32)

let hs_secret = Cstruct.of_hex {|
1d c8 26 e9 36 06 aa 6f  dc 0a ad c1 2f 74 1b 01
04 6a a6 b9 9f 69 1e d2  21 a9 f0 ca 04 3f be ac
|}

(* TODO: ikm should be computed (ECDHE) from the key share in client hello (see
   below), and the private key written in the RFC. *)
let ikm = Cstruct.of_hex {|
8b d4 05 4f b5 5b 9d 63  fd fb ac f9 f0 4b 9f 0d
35 e6 d6 3f 53 75 63 ef  d4 62 72 90 0f 89 49 2d
|}

let extract_handshake () =
  Alcotest.check cs __LOC__ hs_secret
    (Hkdf.extract ~hash:`SHA256 ~salt:expand0 ikm)

let ch = Cstruct.of_hex {|
01 00 00 c0 03 03 cb 34  ec b1 e7 81 63 ba 1c 38
c6 da cb 19 6a 6d ff a2  1a 8d 99 12 ec 18 a2 ef
62 83 02 4d ec e7 00 00  06 13 01 13 03 13 02 01
00 00 91 00 00 00 0b 00  09 00 00 06 73 65 72 76
65 72 ff 01 00 01 00 00  0a 00 14 00 12 00 1d 00
17 00 18 00 19 01 00 01  01 01 02 01 03 01 04 00
23 00 00 00 33 00 26 00  24 00 1d 00 20 99 38 1d
e5 60 e4 bd 43 d2 3d 8e  43 5a 7d ba fe b3 c0 6e
51 c1 3c ae 4d 54 13 69  1e 52 9a af 2c 00 2b 00
03 02 03 04 00 0d 00 20  00 1e 04 03 05 03 06 03
02 03 08 04 08 05 08 06  04 01 05 01 06 01 02 01
04 02 05 02 06 02 02 02  00 2d 00 02 01 01 00 1c
00 02 40 01
|}

let sh = Cstruct.of_hex {|
02 00 00 56 03 03 a6 af  06 a4 12 18 60 dc 5e 6e
60 24 9c d3 4c 95 93 0c  8a c5 cb 14 34 da c1 55
77 2e d3 e2 69 28 00 13  01 00 00 2e 00 33 00 24
00 1d 00 20 c9 82 88 76  11 20 95 fe 66 76 2b db
f7 c6 72 e1 56 d6 cc 25  3b 83 3d f1 dd 69 b1 b0
4e 75 1f 0f 00 2b 00 02  03 04
|}

let c_hs_traffic_secret = Cstruct.of_hex {|
b3 ed db 12 6e 06 7f 35  a7 80 b3 ab f4 5e 2d 8f
3b 1a 95 07 38 f5 2e 96  00 74 6a 0e 27 a5 5a 21
|}

let s_hs_traffic_secret = Cstruct.of_hex {|
b6 7b 7d 69 0c c1 6c 4e  75 e5 42 13 cb 2d 37 b4
e9 c9 12 bc de d9 10 5d  42 be fd 59 d3 91 ad 38
|}

let derive_c_hs_traffic () =
  let hash = Nocrypto.Hash.digest `SHA256 (Cstruct.append ch sh) in
  Alcotest.check cs __LOC__ c_hs_traffic_secret
    (Handshake_crypto13.expand_label `SHA256 hs_secret "c hs traffic" hash 32)

let derive_s_hs_traffic () =
  let hash = Nocrypto.Hash.digest `SHA256 (Cstruct.append ch sh) in
  Alcotest.check cs __LOC__ s_hs_traffic_secret
    (Handshake_crypto13.expand_label `SHA256 hs_secret "s hs traffic" hash 32)

let master = Cstruct.of_hex {|
43 de 77 e0 c7 77 13 85  9a 94 4d b9 db 25 90 b5
31 90 a6 5b 3e e2 e4 f1  2d d7 a0 bb 7c e2 54 b4
|}

let derive_master () =
  let hash = Nocrypto.Hash.digest `SHA256 Cstruct.empty in
  Alcotest.check cs __LOC__ master
    (Handshake_crypto13.expand_label `SHA256 hs_secret "derived" hash 32)

let master_secret = Cstruct.of_hex {|
18 df 06 84 3d 13 a0 8b  f2 a4 49 84 4c 5f 8a 47
80 01 bc 4d 4c 62 79 84  d5 a4 1d a8 d0 40 29 19
|}

let extract_master () =
  Alcotest.check cs __LOC__ master_secret
    (Hkdf.extract ~hash:`SHA256 ~salt:master (Cstruct.create 32))

let tests = [
  "initial extract", `Quick, extract_secret_early ;
  "initial derive", `Quick, derive_hs_secret ;
  "handshake extract", `Quick, extract_handshake ;
  "derive c hs", `Quick, derive_c_hs_traffic ;
  "derive s hs", `Quick, derive_s_hs_traffic ;
  "derive master", `Quick, derive_master ;
  "extract master", `Quick, extract_master ;
]

let () = Alcotest.run "Key derivation tests"
    [ "key extraction and derivation", tests ]
