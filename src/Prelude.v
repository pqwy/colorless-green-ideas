Set Implicit Arguments.
Set Asymmetric Patterns.


Inductive result (a err: Type): Type :=
  Ok    : a   -> result a err
| Error : err -> result a err.

Definition app {A: Type} {B: A -> Type} (f: forall x, B x) x := f x.

Notation "x |> f" := (app f x) (at level 90, right associativity).

Definition opt {A B: Type} x (f: A -> B) o :=
  match o with Some a => f a | None => x end.

Definition res {A B C: Type} (f: A -> C) (g: B -> C) r :=
  match r with Error a => f a | Ok b => g b end. 

Require Import Lists.List.

Definition ffind {A B: Type} (f: A -> option B) :=
  fix F xs := match xs with
    nil     => None
  | x :: xs => match f x with None => F xs | r => r end
  end.

Definition swap {A B: Type} (p: A * B) := let (a, b) := p in (b, a).


(* Require Import Nat. *)
(* Require Import Coq.omega.Omega. *)

(* Theorem wf_lt: well_founded lt. *)
(*   intros x. induction x; constructor; intros; [omega|inversion H]. *)
(*   - auto. *)
(*   - destruct IHx as [Hacc]. apply Hacc. omega. *)
(* Qed. *)

(* Definition downby (A: Set) (f0: nat -> A) (fn: nat -> A -> A) (d: nat): nat -> A. *)
(*   refine ( *)
(*     match d as x return d = x -> _ with *)
(*       0 => fun _ => f0 *)
(*     | _ => fun H => *)
(*         Fix wf_lt (fun _ => A) (fun n F => *)
(*           if le_lt_dec d n then fn n (F (n - d) _) else f0 n ) *)
(*     end eq_refl). *)
(*   omega. *)
(* Defined. *)

(* Definition down (A: Set) (a0: A) (fn: nat -> (nat -> A) -> A): nat -> A. *)
(*   refine ( Fix wf_lt (fun _ => A) (fun x F => *)
(*     match x as x' return x = x' -> _ with *)
(*       0 => fun _    => a0 *)
(*     | _ => fun Heqx => *)
(*         fn x (fun d => match d as d' return d = d' -> _ with *)
(*             0 => fun _    => a0 *)
(*           | _ => fun Heqd => F (x - d) _ *)
(*       end eq_refl) *)
(*     end eq_refl) ). *)
(*   omega. *)
(* Defined. *)
