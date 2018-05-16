Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Prelude Types.
Require Sig Control Crypto.

Require Import Program.Basics Lists.List Strings.String.
(* Require Import Classes.EquivDec. *)
Import ListNotations.

Module Make_proto (Bytes: Sig.Bytes)
                  (CCore: Sig.Crypto_core with Definition bytes := Bytes.bytes)
                  (Wire : Sig.Wire with Definition bytes := Bytes.bytes).

  Import Bytes CCore.

  Module Crypto := Crypto.Make_crypto Bytes CCore.

  Definition error := bytes.

  Module Handshake.

    (* Import Control Control.Effect. *)

    (* Inductive req: Type -> Type := *)
    (*   RqSend : bytes -> req unit *)
    (* | RqRecv : req bytes *)
    (* | RqKeys : cipher -> bytes * bytes -> req unit. *)

    (* Definition process (r: Set) := t req error r. *)

    (* Definition send msg     : process _     := Effect.eff (RqSend msg). *)
    (* Definition recv         : process bytes := Effect.eff RqRecv. *)
    (* Definition set_keys c k : process _     := Effect.eff (RqKeys c k). *)

    Import Control Control.Coroutine.

    Inductive req: Type :=
      RqSend : bytes -> req
    | RqKeys : cipher * hash -> bytes * bytes -> req.

    Definition process := t bytes req error.

    Definition send msg     : process _     := Coroutine.send (RqSend msg).
    Definition recv         : process bytes := Coroutine.recv.
    Definition set_keys c k : process _     := Coroutine.send (RqKeys c k).

    Definition write := Wire.write Wire.handshake.
    Definition read b: process _ :=
      match Wire.read Wire.handshake b with
        Error _      => err (s"read error")
      | Ok None      => err (s"fragmented handshake")
      | Ok (Some ab) => ret ab
      end.

    (* XXX params *)
    Definition group       := Ffdhe2048.
    Definition ciphersuite := Aes_128_gcm_sha256.
    Definition signature   := Rsa_pkcs1_sha256.
    Definition hash        := Sha256.
    Definition cipher      := Aes_128_gcm.

    Definition extensions := list (extension bytes).

    Definition get_key_shares (extns: extensions): process _ :=
      let pick e := match e with Key_shares xs => Some xs | _ => None end in
      ffind pick extns |> opt (s"no Key_shares").

    Definition get_key_share (extns: extensions): process _ :=
      let pick e := match e with Key_share x => Some x | _ => None end in
      ffind pick extns |> opt (s"no Key_share").

    Definition err_unexpected {A} 'tt: process A :=
      err (s "unexpected hs msg").

    Definition schedule hash secret (kex: bytes): process _ :=
      (secret kex |> opt (s"kex")) >>| Crypto.key_schedule hash.


    Definition client rng: process _ :=

      let (rng1, rng2)   := Rng.split rng in
      let (kexc, secret) := Kex.gen rng1 group in
      let ssn_id         := empty in (* ... or 32 bytes in compat mode *)

      let c_raw1 :=
        ClientHello (Rng.gen rng2 32) ssn_id [ciphersuite] [
          Supported_groups _ [group]
        ; Key_shares [(group, kexc)]
        ; Signature_algorithms _ [signature]
        ; Supported_versions _ [this_version]
        ] |> write in
      send c_raw1 ;;

      s_raw1 <- recv ;; read s_raw1 >>= fun '(msg, _) => match msg with
        ServerHello _ ssn_id' ciphersuite' extns' =>
          (* ssn_id == ssn_id' *)
          (* ciphersuite' in ciphersuites *)
          get_key_share extns'      >>= fun '(grp, kexs) =>
          schedule hash secret kexs >>= fun '(sched1, sched2) =>
          let (c_hs_sec, s_hs_sec) := sched1 [c_raw1; s_raw1] in
          set_keys (cipher, hash) (s_hs_sec, c_hs_sec) ;;

          s_raw2 <- recv ;;
          read s_raw2 >>= fun '(m1, raw) =>
          read raw    >>= fun '(m2, raw) =>
          read raw    >>= fun '(m3, raw) =>
          read raw    >>= fun '(m4, _) =>
            match m1, m2, m3, m4 with
            | EncryptedExtensions ee,
              Certificate _ _,
              CertificateVerify _ _,
              Finished sg =>

                let fin1 := Crypto.finished hash c_hs_sec [c_raw1; s_raw1; s_raw2] in
                let c_raw2 := Finished fin1 |> write in
                send c_raw2;;

                set_keys (cipher, hash) (sched2 [c_raw1; s_raw1; s_raw2] |> swap)

            | _, _, _, _ => err_unexpected tt
            end
      | _ => err_unexpected tt
      end .

    Definition server rng cert: process _ :=

      c_raw1 <- recv ;; read c_raw1 >>= fun '(msg, s_raw) => match msg with
      | ClientHello _ ssn_id ciphersuites extns =>
          (* assert s_raw is empty *)
          (* select ciphersuite from ciphersuites *)
          (* pick a group/kex from key_shares -- otherwise retry*)
          get_key_shares extns >>= fun ks => match ks with
          | []             => err (s"empty key shares")
          | (grp, kexc)::_ =>

            let (rng1, rng2)   := Rng.split rng in
            let (kexs, secret) := Kex.gen rng1 grp in

            let s_raw1 :=
              ServerHello (Rng.gen rng2 32) ssn_id ciphersuite [
                Key_share (grp, kexs) ; Supported_version _ this_version
              ] |> write in
            send s_raw1 ;;

            schedule hash secret kexc >>= fun '(sched1, sched2) =>
            let (c_hs_sec, s_hs_sec) := sched1 [c_raw1; s_raw1] in
            set_keys (cipher, hash) (c_hs_sec, s_hs_sec) ;;

            let s_raw2 := EncryptedExtensions [ Supported_groups _ [group] ] |> write in
            let s_raw3 :=
              write (Certificate empty [(cert, [])]) ++
              write (CertificateVerify signature empty) ++
              write (Finished (Crypto.finished hash s_hs_sec [c_raw1; s_raw1; s_raw2])) in
            send (s_raw2 ++ s_raw3) ;;

            c_raw2 <- recv ;; read c_raw2 >>= fun '(msg, c_raw) => match msg with
              Finished sg =>
                set_keys (cipher, hash) (sched2 [c_raw1; s_raw1; s_raw2; s_raw3])
            | _ => err_unexpected tt
            end
          end
      | _ => err_unexpected tt
      end .

  End Handshake.

  Module Record.

    Import Crypto Control Control.Result.

    Definition unprotect ctx msg := match msg with
      TLSRecord Application_data raw =>
        match Cipher.decrypt ctx raw with
          Some (raw, ctx) =>
            match Wire.read Wire.record_enc raw with
              Ok (Some (msg, rest)) => ret (msg, ctx) (* rest == empty! *)
            | _ => err (s"inner record")
            end
        | None => err (s"decrypt")
        end
    | _ => err (s"protected record type")
    end.

    Definition protect ctx record :=
      let (raw, ctx) :=
        Wire.write Wire.record_enc record |> Cipher.encrypt ctx in
      (TLSRecord Application_data raw, ctx).


    Inductive evt (msg: Set) :=
      DoSend : bytes -> evt msg
    | DoRecv : msg -> evt msg.

    CoInductive resp (msg: Set) :=
      Err  : error -> resp msg
    | Send : msg -> resp msg -> resp msg
    | Data : bytes -> resp msg -> resp msg
    | Tick : resp msg -> resp msg
    | Cont : (evt msg -> resp msg) -> resp msg.

    Definition err {msg} e := Err msg (s e).

    Definition eternal :=
      cofix F ctxrd ctxwr e := match e with
        DoSend raw =>
          let (msg, ctxwr) := protect ctxwr (TLSRecord Application_data raw) in
          Send msg (Cont (F ctxrd ctxwr))
      | DoRecv msg => match unprotect ctxrd msg with
          Error e => Err _ e
        | Ok (TLSRecord t raw, ctxrd) => match t with
            Application_data => Data raw (Cont (F ctxrd ctxwr))
          | Alert            => Data raw (Cont (F ctxrd ctxwr))
          | _                => err "unexpected"
          end
        end
      end.

    Definition initial :=
      cofix F ctx hs := match hs with
        Coroutine.Err e   => Err _ e
      | Coroutine.Pure tt => match ctx with
          Some (c1, c2) => Cont (eternal c1 c2) | _ => err "hs died"
        end
      | Coroutine.Send (Handshake.RqKeys cip (sec1, sec2)) hs =>
          Tick (F (Some (Cipher.context cip sec1, Cipher.context cip sec2)) hs)
      | Coroutine.Send (Handshake.RqSend raw) hs => match ctx with
          None => Send (TLSRecord Handshake raw) (F None hs)
        | Some (ctxrd, ctxwr) =>
            let (msg, ctxwr) := protect ctxwr (TLSRecord Handshake raw) in
            Send msg (F (Some (ctxrd, ctxwr)) hs)
        end
      | Coroutine.Recv k => Cont (fun e => match e with
          DoSend _ => err "hs: send"
        | DoRecv (TLSRecord t raw as msg) => match ctx with
            None => match t with Handshake => F None (k raw) | _ => err "unexpected" end
          | Some (ctxrd, ctxwr) => match unprotect ctxrd msg with
              Ok (TLSRecord Handshake raw, ctxrd) => F (Some (ctxrd, ctxwr)) (k raw)
            | Ok _    => err "unexpected"
            | Error e => Err _ e
            end
          end
        end)
      end.

    Definition wired :=
    ( cofix F buf t := match t with
        Err e      => Err _ e
      | Send msg t => Send (Wire.write Wire.record msg) (F buf t)
      | Data raw t => Data raw (F buf t)
      | Tick t     => Tick (F buf t)
      | Cont k     => match Wire.read Wire.record buf with
        | Ok (Some (msg, buf)) => Tick (F buf (k (DoRecv msg)))
        | Ok None => Cont (fun e => match e with
            DoRecv raw => F (buf ++ raw) t
          | DoSend raw => F buf (k (DoSend _ raw))
          end)
        | Error _ => err "record parse"
        end
      end ) empty.

    Definition client rng := wired (initial None (Handshake.client rng)).
    Definition server rng cert := wired (initial None (Handshake.server rng cert)).
    Definition send (k: evt bytes -> resp bytes) raw := k (DoSend _ raw).
    Definition recv (k: evt bytes -> resp bytes) raw := k (DoRecv raw).


    (* Module V2. *)

    (*   Definition snd_prot ctxwr msg := *)
    (*     let (msg, ctxwr) := protect ctxwr msg in *)
    (*     (Wire.write Wire.record msg, ctxwr). *)

    (*   Inductive state := *)
    (*   | HS : option (Cipher.ctx * Cipher.ctx) -> (bytes -> Handshake.process unit) -> state *)
    (*   | AD : Cipher.ctx -> Cipher.ctx -> state. *)

    (*   Inductive response := *)
    (*     Send  : bytes -> response -> response *)
    (*   | Data  : bytes -> response -> response *)
    (*   | Err   : error -> response *)
    (*   | State : state -> response. *)

    (*   Definition shake := fix F ctx hs := match hs with *)
    (*     Coroutine.Err e   => Err e *)
    (*   | Coroutine.Pure tt => *)
    (*       match ctx with Some (c1, c2) => State (AD c1 c2) | _ => Err (s"hs ded") end *)
    (*   | Coroutine.Send (Handshake.RqKeys cip (sec1, sec2)) hs => *)
    (*       F (Some (Cipher.context cip sec1, Cipher.context cip sec2)) hs *)
    (*   | Coroutine.Send (Handshake.RqSend raw) hs => match ctx with *)
    (*       None => Send (Wire.write Wire.record (TLSRecord Handshake raw)) (F None hs) *)
    (*     | Some (ctxrd, ctxwr) => *)
    (*         let (msg, ctxwr) := snd_prot ctxwr (TLSRecord Handshake raw) in *)
    (*         Send msg (F (Some (ctxrd, ctxwr)) hs) *)
    (*     end *)
    (*   | Coroutine.Recv k => State (HS ctx k) *)
    (*   end. *)

    (*   Definition recv state raw := match Wire.read Wire.record raw with *)
    (*     Ok (Some (msg, rest)) => match state with *)
    (*       HS None k => match msg with *)
    (*         TLSRecord Handshake raw => shake None (k raw) | _ => Err (s"x") *)
    (*       end *)
    (*     | HS (Some (ctxrd, ctxwr)) k => match unprotect ctxrd msg with *)
    (*         Ok (TLSRecord Handshake raw, ctxrd) => shake (Some (ctxrd, ctxwr)) (k raw) *)
    (*       | Ok _    => Err (s"wat") *)
    (*       | Error e => Err e *)
    (*       end *)
    (*     | AD ctxrd ctxwr => match unprotect ctxrd msg with *)
    (*         Ok (TLSRecord Application_data raw, ctxrd) => Data raw (State (AD ctxrd ctxwr)) *)
    (*       | Ok _    => Err (s"wat") *)
    (*       | Error e => Err e *)
    (*       end *)
    (*     end *)
    (*   | Error _ => Err (s"wat") *)
    (*   | Ok None => Err (s"wat") *)
    (*   end. *)

    (*   Definition send state raw := match state with *)
    (*     AD ctxrd ctxwr => *)
    (*       let (msg, ctxwr) := snd_prot ctxwr (TLSRecord Application_data raw) in *)
    (*       Send msg (State (AD ctxrd ctxwr)) *)
    (*   | _ => Err (s"handshake") *)
    (*   end. *)

    (*   Definition client 'tt := shake None (Handshake.client tt). *)
    (*   Definition server 'tt := shake None (Handshake.server tt). *)

    (* End V2. *)

  End Record.

End Make_proto.
