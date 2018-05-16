Set Implicit Arguments.
Set Asymmetric Patterns.

Require Prelude Types Lists.List Strings.String.
Import Prelude.

Module Type Bytes.

  Parameter bytes : Set.

  Parameter empty  : bytes.
  Parameter append : bytes -> bytes -> bytes.
  Parameter concat : list bytes -> bytes.

  Parameter s : String.string -> bytes.
  Parameter zeros : nat -> bytes.

  Parameter length : bytes -> nat.
  Parameter take   : nat -> bytes -> bytes.

  Parameter xor : bytes -> bytes -> bytes.

  Notation "a '++' b" := (append a b) (at level 60, right associativity).
End Bytes.

Module Type Crypto_core.

  Parameter bytes: Set.

  Parameter word8: nat -> bytes.

  Module Hash.
    Parameter length : Types.hash -> nat.
    Parameter mac    : Types.hash -> bytes -> bytes -> bytes.
    Parameter t     : Set.
    Parameter empty : Types.hash -> t.
    Parameter feed  : t -> bytes -> t.
    Parameter get   : t -> bytes.
  End Hash.

  Module Rng.
    Parameter g : Set.
    Parameter split : g -> g * g.
    Parameter gen   : g -> nat -> bytes.
  End Rng.

  Module Kex.
    Parameter gen : Rng.g -> Types.named_group -> (bytes * (bytes -> option bytes)).
  End Kex.

  Module AEAD.
    Parameter k: Set.
    Parameter key     : Types.cipher -> bytes -> k.
    Parameter key_size: Types.cipher -> nat.
    Parameter iv_size : Types.cipher -> nat.
    Parameter encrypt : k -> bytes -> bytes -> bytes.
    Parameter decrypt : k -> bytes -> bytes -> option bytes.
  End AEAD.

  (* misc *)

  Module Int64.
    Parameter int64: Set.
    Parameter zero: int64.
    Parameter succ: int64 -> int64.
    Parameter format_be: int64 -> bytes.
  End Int64.

  Parameter hkdf_label : bytes -> bytes -> nat -> bytes.

End Crypto_core.

Module Type Wire.

  Parameter bytes: Set.

  Parameter t: Type -> Type.

  Parameter read: forall A: Set, t A -> bytes -> result (option (A * bytes)) unit.
  Parameter write: forall A: Set, t A -> A -> bytes.

  Parameter record     : t (Types.record bytes).
  Parameter record_enc : t (Types.record bytes).
  Parameter handshake  : t (Types.hs_message bytes).

End Wire.
