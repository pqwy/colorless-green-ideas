Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Prelude.
Require Types Sig.
Require Import Lists.List Strings.String.

Module Make_crypto
  (Bytes: Sig.Bytes)
  (CCore: Sig.Crypto_core with Definition bytes := Bytes.bytes).

  Import Bytes CCore.

  Module HKDF.
    (* RFC 5869 *)

    (* Definition expand hash prk info n := *)
    (*   let hmac t i := Hash.mac hash prk (t ++ info ++ word8 i) in *)
    (*   downby (fun k t i => take k (hmac t i)) *)
    (*          (fun _ F t i => let t' := hmac t i in t' ++ F t' (S i)) *)
    (*          (Hash.length hash) n empty 1. *)

    Definition extract := Hash.mac.

    (* Single-iter. Assumes hash >= AEAD key/iv. *)
    Definition expand hash prk info := Hash.mac hash prk (info ++ word8 1).

    Definition expand_lbl hash secret label ctx n :=
      expand hash secret (hkdf_label label ctx n) |> take n.
  End HKDF.

  Definition hashv hash xs :=
    fold_left Hash.feed xs (Hash.empty hash) |> Hash.get.

  Definition derive_secret hash secret label msgs :=
    HKDF.expand_lbl hash secret label (hashv hash msgs) (Hash.length hash).

  Definition lbl_derived := s"derived".
  Definition lbl_c_hs_traffic := s"c hs traffic".
  Definition lbl_s_hs_traffic := s"s hs traffic".
  Definition lbl_c_ap_traffic := s"c ap traffic".
  Definition lbl_s_ap_traffic := s"s ap traffic".

  Definition key_schedule hash dhe :=
    let derived s := derive_secret hash s lbl_derived nil in
    let b0        := zeros (Hash.length hash) in
    let early     := HKDF.extract hash b0 b0 in
    let handshake := HKDF.extract hash (derived early) dhe in
    let k_hs msgs := (derive_secret hash handshake lbl_c_hs_traffic msgs,
                      derive_secret hash handshake lbl_s_hs_traffic msgs) in
    let master    := HKDF.extract hash (derived handshake) b0 in
    let k_ap msgs := (derive_secret hash master lbl_c_ap_traffic msgs,
                      derive_secret hash master lbl_s_ap_traffic msgs) in
    (k_hs, k_ap).

  Definition lbl_finished := s"finished".

  Definition finished hash base_key msgs :=
    let fin_key :=
      HKDF.expand_lbl hash base_key lbl_finished empty (Hash.length hash) in
    Hash.mac hash fin_key (hashv hash msgs).

  Module Cipher.

    Import Int64.

    Inductive ctx := CTX : AEAD.k * bytes -> int64 -> ctx.

    Definition lbl_key := s"key".
    Definition lbl_iv  := s"iv".

    Definition context '(c, hash) sec :=
      let key := HKDF.expand_lbl hash sec lbl_key empty (AEAD.key_size c) in
      let iv  := HKDF.expand_lbl hash sec lbl_iv empty (AEAD.iv_size c) in
      CTX (AEAD.key c key, iv) zero.

    Definition nonce iv seq :=
      xor iv (zeros (length iv - 8) ++ format_be seq).

    Definition encrypt '(CTX ((key, iv) as kiv) seq) b :=
      (AEAD.encrypt key (nonce iv seq) b, CTX kiv (succ seq)).

    Definition decrypt '(CTX ((key, iv) as kiv) seq) b :=
      match AEAD.decrypt key (nonce iv seq) b with
        Some r => Some (r, CTX kiv (succ seq)) | _ => None
      end.

  End Cipher.

End Make_crypto.
