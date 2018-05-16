
let cs_of_b b  = Cstruct.of_bytes b
and b_of_cs cs = Cstruct.to_string cs |> Bytes.unsafe_of_string

module Bytes = struct

  include Bytes

  type bytes = t

  let s xs =
    let rec go b i = function
      []    -> b
    | c::cs -> unsafe_set b i c; go b (i + 1) cs in
    go (create (List.length xs)) 0 xs

  let zeros l = make l '\x00'

  let append b1 b2 =
    let n1 = length b1 and n2 = length b2 in
    let r = create (n1 + n2) in
    unsafe_blit b1 0 r 0 n1; unsafe_blit b2 0 r n1 n2; r

  let concat = concat empty

  let take x b = sub b 0 x

  let xor b1 b2 = b_of_cs (Nocrypto.Uncommon.Cs.xor (cs_of_b b1) (cs_of_b b2))


  let v = unsafe_of_string
end

module Wire = struct

  type nonrec bytes = bytes

  open Generated
  open Byterw

  (* type 'a t = 'a R.t * ('a -> W.t) *)
  type 'a t = (bytes -> (('a * bytes) option, unit) result) * ('a -> bytes)

  let read = fst and write = snd


  let rd_cipher_suite rd = match R.u16 rd with
      0x1301 -> Aes_128_gcm_sha256
    | 0x1302 -> Aes_256_gcm_sha384
    | 0x1303 -> Chacha20_poly1305_sha256
    | 0x1304 -> Aes_128_ccm_sha256
    | 0x1305 -> Aes_128_ccm_8_sha256
    | cs     -> Other_ciphersuite cs
  and wr_cipher_suite cs = W.u16 @@ match cs with
      Aes_128_gcm_sha256       -> 0x1301
    | Aes_256_gcm_sha384       -> 0x1302
    | Chacha20_poly1305_sha256 -> 0x1303
    | Aes_128_ccm_sha256       -> 0x1304
    | Aes_128_ccm_8_sha256     -> 0x1305
    | Other_ciphersuite cs         -> cs

  let rd_version rd = match R.u16 rd with
      0x0301 -> Tls1_0
    | 0x0302 -> Tls1_1
    | 0x0303 -> Tls1_2
    | 0x0304 -> Tls1_3
    | n      -> match (n lsr 8) with
        0x7f -> Tls1_3_draft (n land 0xff)
      | _    -> R.err "version: %04x" n
  and wr_version v = W.u16 @@ match v with
      Tls1_0         -> 0x0301
    | Tls1_1         -> 0x0302
    | Tls1_2         -> 0x0303
    | Tls1_3         -> 0x0304
    | Tls1_3_draft v -> 0x7f00 lor v

  let rd_signature_scheme rd = match R.u16 rd with
    | 0x0401 -> Rsa_pkcs1_sha256
    | 0x0501 -> Rsa_pkcs1_sha384
    | 0x0601 -> Rsa_pkcs1_sha512
    | 0x0403 -> Ecdsa_secp256r1_sha256
    | 0x0503 -> Ecdsa_secp384r1_sha384
    | 0x0603 -> Ecdsa_secp521r1_sha512
    | 0x0804 -> Rsa_pss_rsae_sha256
    | 0x0805 -> Rsa_pss_rsae_sha384
    | 0x0806 -> Rsa_pss_rsae_sha512
    | 0x0807 -> Ed25519
    | 0x0808 -> Ed448
    | 0x0809 -> Rsa_pss_pss_sha256
    | 0x080a -> Rsa_pss_pss_sha384
    | 0x080b -> Rsa_pss_pss_sha512
    | 0x0201 -> Rsa_pkcs1_sha1
    | 0x0203 -> Ecdsa_sha1
    | ss     -> Other_signature_scheme ss
  and wr_signature_scheme ss = W.u16 @@ match ss with
    | Rsa_pkcs1_sha256          -> 0x0401
    | Rsa_pkcs1_sha384          -> 0x0501
    | Rsa_pkcs1_sha512          -> 0x0601
    | Ecdsa_secp256r1_sha256    -> 0x0403
    | Ecdsa_secp384r1_sha384    -> 0x0503
    | Ecdsa_secp521r1_sha512    -> 0x0603
    | Rsa_pss_rsae_sha256       -> 0x0804
    | Rsa_pss_rsae_sha384       -> 0x0805
    | Rsa_pss_rsae_sha512       -> 0x0806
    | Ed25519                   -> 0x0807
    | Ed448                     -> 0x0808
    | Rsa_pss_pss_sha256        -> 0x0809
    | Rsa_pss_pss_sha384        -> 0x080a
    | Rsa_pss_pss_sha512        -> 0x080b
    | Rsa_pkcs1_sha1            -> 0x0201
    | Ecdsa_sha1                -> 0x0203
    | Other_signature_scheme ss -> ss

  let rd_named_group rd = match R.u16 rd with
    | 0x0017 -> Secp256r1
    | 0x0018 -> Secp384r1
    | 0x0019 -> Secp521r1
    | 0x001D -> X25519
    | 0x001E -> X448
    | 0x0100 -> Ffdhe2048
    | 0x0101 -> Ffdhe3072
    | 0x0102 -> Ffdhe4096
    | 0x0103 -> Ffdhe6144
    | 0x0104 -> Ffdhe8192
    | ng     -> R.err "named group: %04x" ng
  and wr_named_group ng = W.u16 @@ match ng with
    | Secp256r1 -> 0x0017
    | Secp384r1 -> 0x0018
    | Secp521r1 -> 0x0019
    | X25519    -> 0x001D
    | X448      -> 0x001E
    | Ffdhe2048 -> 0x0100
    | Ffdhe3072 -> 0x0101
    | Ffdhe4096 -> 0x0102
    | Ffdhe6144 -> 0x0103
    | Ffdhe8192 -> 0x0104

  let rd_key_share_entry rd =
    R.(let ng = rd_named_group rd in (ng, vec (1, 0xffff) bytes rd))
  and wr_key_share_entry (ng, data) =
    W.(wr_named_group ng @+ vec u16 (bytes data))

  let rd_psk_kex_mode rd = match R.u8 rd with
    0 -> Psk_ke | 1 -> Psk_dhe_ke | n -> R.err "psk_kex_mode: %d" n
  and wr_psk_kex_mode m = W.u8 @@ match m with Psk_ke -> 0 | Psk_dhe_ke -> 1

  (* TODO *)
  (* 0    server_name                            [RFC 6066] *)
  (* 1    max_fragment_length                    [RFC 6066] *)
  (* 5    status_request                         [RFC 6066] *)
  (* 14   use_srtp                               [RFC 5764] *)
  (* 15   heartbeat                              [RFC 6520] *)
  (* 16   application_layer_protocol_negotiation [RFC 7301] *)
  (* 18   signed_certificate_timestamp           [RFC 6962] *)
  (* 19   client_certificate_type                [RFC 7250] *)
  (* 20   server_certificate_type                [RFC 7250] *)
  (* 21   padding                                [RFC 7685] *)
  (* 41   pre_shared_key *)
  (* 42   early_data  *)
  (* 44   cookie  *)
  (* 47   certificate_authorities *)
  (* 48   oid_filters *)
  (* 49   post_handshake_auth *)
  (* 50   signature_algorithms_cert *)

  let rd_extn side rd =
    let e = R.u16 rd in
    R.(rd |> vec (0, 0xffff) @@ fun n rd -> match e with
      0x0a -> Supported_groups (list (2, 0xffff) rd_named_group rd) (* [RFC 4492, 7919] *)
    | 0x0d -> Signature_algorithms (list (2, 0xfffe) rd_signature_scheme rd)
    | 0x2b -> ( match side with
          `Client -> Supported_versions (list (2, 0xfe) rd_version rd)
        | `Server -> Supported_version (rd_version rd) )
    | 0x2d -> Psk_kex_modes (list (1, 0xff) rd_psk_kex_mode rd)
    | 0x33 -> ( match side with
          `Client -> Key_shares (list (0, 0xffff) rd_key_share_entry rd)
        | `Server -> Key_share (rd_key_share_entry rd)
        (* XXX KeyShareHelloRetryRequest variant *) )
    | e  -> Other_extension (e, bytes n rd))

  and wr_extn ext = W.(
    let e, f = match ext with
      Supported_groups gs      -> 0x0a, list u16 wr_named_group gs
    | Signature_algorithms sss -> 0x0d, list u16 wr_signature_scheme sss
    | Supported_versions vs    -> 0x2b, list u8 wr_version vs
    | Supported_version v      -> 0x2b, wr_version v
    | Psk_kex_modes kexs       -> 0x2d, list u8 wr_psk_kex_mode kexs
    | Key_shares kss           -> 0x33, list u16 wr_key_share_entry kss
    | Key_share ks             -> 0x33, wr_key_share_entry ks
    | Other_extension (e, d)   -> e, bytes d
    in
    u16 e @+ vec u16 f )

  let rd_extns min side = R.list (min, 0xffff) (rd_extn side)
  and wr_extns = W.(list u16) wr_extn

  let rd_cert rd = R.(
    let cert = vec (1, 0xffffff) bytes rd in
    (cert, rd_extns 0 `Client (* XXX ? *) rd))
  and wr_cert (cert, extns) = W.(vec u24 (bytes cert) @+ wr_extns extns)

  (* TODO *)
  (* 0x04 new_session_ticket *)
  (* 0x05 end_of_early_data *)
  (* 0x18 key_update *)
  (* 0xf5 message_hash *)

  let handshake =
    let read = R.(run @@ fun rd ->
      let hst = u8 rd in
      rd |> vec_ u24 @@ fun n rd -> match hst with
        0x01 ->
          const u16 0x0303 rd ~or_err:"legacy_version";
          let random  = bytes 0x20 rd
          and ssn_id  = vec (0, 0x20) bytes rd
          and css     = list (2, 0xfffe) rd_cipher_suite rd
          and _       = const u16 0x0100 rd ~or_err:"compression"
          and extns   = rd_extns 8 `Client rd in
          ClientHello (random, ssn_id, css, extns)
      | 0x02 ->
          const u16 0x0303 rd ~or_err:"legacy_version";
          let random  = bytes 0x20 rd
          and ssn_id  = vec (0, 0x20) bytes rd
          and cs      = rd_cipher_suite rd
          and _       = const u8 0 rd ~or_err:"compression"
          and extns   = rd_extns 6 `Server rd in
          ServerHello (random, ssn_id, cs, extns)
      | 0x08 -> EncryptedExtensions (rd_extns 0 `Server rd)
      | 0x0b ->
          let crcx  = vec (0, 0xff) bytes rd
          and certs = list (0, 0xffffff) rd_cert rd in
          Certificate (crcx, certs)
      | 0x0d ->
          let crcx  = vec (0, 0xff) bytes rd
          and extns = rd_extns 2 `Client(* XXX ? *) rd in
          CertificateRequest (crcx, extns)
      | 0x0f ->
          let ss = rd_signature_scheme rd in
          CertificateVerify (ss, vec (0, 0xffff) bytes rd)
      | 0x14 -> Finished (bytes n rd)
      | _  -> err "handshake type: %d" hst
    )
    and write hs = W.(run @@
      let hst, f = match hs with
        ClientHello (random, ssn_id, css, extns) -> 0x01,
          u16 0x0303 @+ bytes random @+ vec u8 (bytes ssn_id) @+
            list u16 wr_cipher_suite css @+ vec u8 (u8 0) @+ wr_extns extns
      | ServerHello (random, ssn_id, cs, extns) -> 0x02,
          u16 0x0303 @+ bytes random @+ vec u8 (bytes ssn_id) @+
            wr_cipher_suite cs @+ u8 0 @+ wr_extns extns
      | EncryptedExtensions extns -> 0x08, wr_extns extns
      | Certificate (crcx, certs) -> 0x0b,
          vec u8 (bytes crcx) @+ list u24 wr_cert certs
      | CertificateRequest (crcx, extns) -> 0x0d,
          vec u8 (bytes crcx) @+ wr_extns extns
      | CertificateVerify (ss, sign) -> 0x0f,
          wr_signature_scheme ss @+ vec u16 (bytes sign)
      | Finished (hash) -> 0x14, bytes hash
      in
      u8 hst @+ vec u24 f ) in
    (read, write)

  let ctype_of_int = function
      20 -> Some Change_cipher_spec
    | 21 -> Some Alert
    | 22 -> Some Handshake
    | 23 -> Some Application_data
    | _  -> None
  let wr_ctype ct = W.( u8 @@ match ct with
      Change_cipher_spec -> 20
    | Alert              -> 21
    | Handshake          -> 22
    | Application_data   -> 23 )

  let record =
    let read = R.(run @@ fun rd ->
      let ct = let x = u8 rd in match ctype_of_int x with
        Some ct -> ct | None -> err "content type: %d" x
      and _  = match u16 rd with
        0x0303 | 0x0301 -> () | v -> err "record (legacy) version: %04x" v in
      TLSRecord (ct, vec (0, 0x4000) bytes rd) )
    and write (TLSRecord (ct, data)) =
      W.(run @@ wr_ctype ct @+ u16 0x0303 @+ vec u16 (bytes data))
    in (read, write)

  open EndianBytes.BigEndian

  let record_enc =
    let open Bytes in
    let read b =
      let n = length b in
      let rec go b = function
        0 -> None
      | i -> if get_uint8 b (i - 1) = 0 then go b (i - 1) else Some i in
      match go b n with
      | None   -> Error ()
      | Some i -> match get_uint8 b (i - 1) |> ctype_of_int with
          None    -> Error ()
        | Some ct -> Ok (Some (TLSRecord (ct, sub b 0 (i - 1)), sub b i (n - i)))
    and write (TLSRecord (ct, data)) = W.(run @@ bytes data @+ wr_ctype ct) in
    (read, write)

end

module Crypto_core = struct

  open Generated
  open Bytes
  open Nocrypto

  type nonrec bytes = bytes

  let word8 x = make 1 (Char.unsafe_chr (x land 0xff))

  let hash_of = function
    Sha1   -> `SHA1
  | Sha256 -> `SHA256
  | Sha384 -> `SHA384
  | Sha512 -> `SHA512

  module Hash = struct

    let mac hash key msg =
      b_of_cs Hash.(mac (hash_of hash) ~key:(cs_of_b key) (cs_of_b msg))

    let length hash = Hash.digest_size (hash_of hash)

    type t = T : (module Hash.S with type t = 'a) * 'a -> t

    let empty h =
      let m = Hash.module_of (hash_of h) in
      let module H = (val m) in
      T ((module H), H.empty)

    let feed (T (m, t)) msg =
      let module H = (val m) in T (m, cs_of_b msg |> H.feed t)

    let get (T (m, t)) =
      let module H = (val m) in H.get t |> b_of_cs
  end

  module Rng = struct
    include Rand
    let gen g n = Rng.generate ~g:(prj g) n |> b_of_cs
  end

  module Kex = struct
    let gen rng grp =
      let open Dh in
      let grp = Group.( match grp with
          Ffdhe2048 -> ffdhe2048
        | Ffdhe3072 -> ffdhe3072
        | Ffdhe4096 -> ffdhe4096
        | Ffdhe6144 -> ffdhe6144
        | Ffdhe8192 -> ffdhe8192
        | _         -> assert false ) in
      let (sec, key) = gen_key ~g:(Rng.prj rng) grp in
      let k key' = match shared grp sec (cs_of_b key') with
        Some x -> Some (b_of_cs x) | _ -> None in
      (b_of_cs key, k)

  end

  module Int64 = struct
    type nonrec int64 = int64
    let zero = 0L
    and succ = Int64.succ
    and format_be x =
      let b = Bytes.create 8 in EndianBytes.BigEndian.set_int64 b 0 x; b
  end

  module AEAD = struct

    open Cipher_block.AES

    type k = GCM of GCM.key

    let key c sec = match c with
      Aes_128_gcm | Aes_256_gcm -> GCM (GCM.of_secret (cs_of_b sec))
    | _ -> invalid_arg "key"

    let key_size = function
      Aes_128_ccm | Aes_128_ccm_8 | Aes_128_gcm -> 16
    | Aes_256_gcm -> 32
    | _ -> invalid_arg "key_size"

    let iv_size = function
      Aes_128_gcm | Aes_256_gcm -> 12 | _ -> invalid_arg "iv_size"

    let encrypt k nonce x = match k with
      GCM key ->
        let res = GCM.encrypt ~key ~iv:(cs_of_b nonce) (cs_of_b x) in
        b_of_cs (Cstruct.append res.GCM.message res.GCM.tag)

    let decrypt k nonce x = match k with
      GCM key ->
        if Bytes.length x >= 16 then
          let x = cs_of_b x in
          let (msg, tag) = Cstruct.(split x (len x - 16)) in
          let res = GCM.decrypt ~key ~iv:(cs_of_b nonce) msg in
          if Cstruct.equal tag res.GCM.tag then
            Some (b_of_cs res.GCM.message)
          else None
        else None
  end

  (* XXX move *)
  let hkdf_label label context len =
    let label = Bytes.append (v"tls13 ") label in
    Byterw.W.(run @@ u16 len @+ vec u8 (bytes label) @+ vec u8 (bytes context))
end
