Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Prelude.

Module Type Monad.

  Parameter m : Type -> Type.

  Parameter map : forall A B, (A -> B) -> m A -> m B.
  Parameter ret : forall A, A -> m A.
  Parameter bind : forall A B, m A -> (A -> m B) -> m B.

  Notation "m >>= f" := (bind m f)
    (at level 69, left associativity).
  Notation "f >=> g" := (fun x => bind (f x) g)
    (at level 68, left associativity).
  Notation "m >>| f" := (map f m)
    (at level 69, left associativity).
  Notation "x <- c1 ;; c2" := (c1 >>= (fun x => c2))
    (at level 100, c1 at next level, right associativity).
  Notation "e1 ;; e2" := (_ <- e1 ;; e2)
    (at level 100, right associativity).
  (* Notation "'letm' P ':=' E 'in' E1" := (bind E (fun P => E1)) *)
  (*   (at level 99, right associativity). *)

  (* Axiom map_id: forall A (m: m A), map (fun x => x) m = m. *)
  (* Axiom map_comp: forall A B C (f: A -> B) (g: B -> C) x, *)
  (*   map (fun x => g (f x)) x = map g (map f x). *)
  (* Axiom ret_id_r: forall A (m: m A), m >>= (@ret A) = m. *)
  (* Axiom ret_id_l: forall A B (f: A -> m B) x, ret x >>= f = f x. *)
  (* Axiom bind_ass: forall A B C (f: A -> m B) (g: B -> m C) m, *)
  (*   (m >>= f) >>= g = m >>= (fun x => f x >>= g). *)

  (* Parameter mFix: forall A, (A -> m A) -> m A. *)
End Monad.

Class Monad (m: Type -> Type) := {
  ret  : forall {A: Type}, A -> m A
; bind : forall {A B: Type}, m A -> (A -> m B) -> m B
}.

Notation "m >>= f" := (bind m f)
  (at level 91, left associativity).
Notation "f >=> g" := (fun x => bind (f x) g)
  (at level 91, left associativity).
Notation "m >>| f" := (bind m (fun x => ret (f x)))
  (at level 91, left associativity).
Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
  (at level 100, c1 at next level, right associativity).
Notation "c1 ;; c2" := (bind c1 (fun _ => c2))
  (at level 100, right associativity).

Module Result.

  Definition t e a := result a e.

  Instance result_monad: forall e, Monad (t e) := {
    ret  := fun {A} x => Ok _ x
  ; bind := fun {A B} a f =>
      match a with Error e => Error _ e | Ok x => f x end
  }.

  Definition err {e a: Type} (msg: e): t e a := Error a msg.

  Definition opt {e r: Type} msg xo: t e r :=
    match xo with Some x => ret x | None => err msg end.

End Result.

Module Coroutine.

  Inductive t (i o e r: Type): Type :=
    Pure  : r -> t i o e r
  | Err   : e -> t i o e r
  | Recv  : (i -> t i o e r) -> t i o e r
  | Send  : o -> t i o e r -> t i o e r .


  Instance coroutine_monad: forall (i o e: Type), Monad (t i o e) := {
    ret  := fun {A} x => Pure _ _ _ x
  ; bind := fun {A B} => fix F a f := match a with
      Pure x   => f x
    | Err e    => Err _ _ _ e
    | Recv k   => Recv (fun x => F (k x) f)
    | Send x m => Send x (F m f)
    end
  }.

  Definition err {i o e r: Type} (msg: e) := Err i o r msg.
  Definition send {i o e: Type} x := Send x (Pure i o e tt).
  Definition recv {i o e: Type} := Recv (fun x => Pure i o e x).

  Definition opt {i o e r: Type} msg xo: t i o e r :=
    match xo with Some x => ret x | None => err msg end.

End Coroutine.

Module Coeff.

  CoInductive t (eff: Type -> Type) (e a: Type) :=
    Pure : a -> t eff e a
  | Err  : e -> t eff e a
  | Eff  : forall {T}, eff T -> (T -> t eff e a) -> t eff e a.

  Instance effect_monad: forall eff e, Monad (t eff e) := {
    ret  := fun {A} x => Pure _ _ x
  ; bind := fun {A B} => cofix F a f := match a with
      Pure a      => f a
    | Err e       => Err _ _ e
    | Eff _ req k => Eff req (fun resp => F (k resp) f)
    end
  }.

  Definition err {eff e a} (msg: e) := Err eff a msg.
  Definition eff {eff e r} (req: eff r) := Eff req (fun x => Pure eff e x).
  Definition case {eff e a ret}
                  f0 f1 (f2: forall {T}, eff T -> (T -> t eff e a) -> ret)
                  m : ret :=
    match m with
      Pure a      => f0 a
    | Err e       => f1 e
    | Eff _ req k => f2 req k
    end.

(*   Definition catch {eff1 eff2 e a} *)
(*                    (f: forall {T}, eff1 T -> (T -> t eff2 e a) -> t eff2 e a) := *)
(*     cofix F m := match m with *)
(*       Pure a      => Pure _ _ a *)
(*     | Err e       => Err _ _ e *)
(*     | Eff _ req k => f req (fun resp => F (k resp)) *)
(*     end. *)

End Coeff.

(* Module Eff. *)

(*   Inductive t (eff: Type -> Type) (e a: Type) := *)
(*     Pure : a -> t eff e a *)
(*   | Err  : e -> t eff e a *)
(*   | Eff  : forall {x}, eff x -> (x -> t eff e a) -> t eff e a *)
(*   . *)

(*   Instance effect_monad: forall eff e, Monad (t eff e) := { *)
(*     ret  := fun {A} x => Pure _ _ x *)
(*   ; bind := fun {A B} => fix F a f := match a with *)
(*       Pure x     => f x *)
(*     | Err e      => Err _ _ e *)
(*     | Eff _ ex k => Eff ex (fun x => F (k x) f) *)
(*     end *)
(*   }. *)

(*   Definition err {eff e r} (msg: e) := Err eff r msg. *)
(*   Definition eff {eff} {e r: Type} (req: eff r) := Eff req (fun x => Pure eff e x). *)

(*   Definition opt {eff} {e r: Type} o msg: t eff e r := *)
(*     match o with Some x => ret x | None => err msg end. *)

  (* Definition handle {eff} {e r: Type} (t: t eff e r) *)
  (*   (f: forall T, eff T -> (T -> t eff e r) *)

(* End Eff. *)
