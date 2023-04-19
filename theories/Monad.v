(* (Yet another) description of monads *)

From Equations Require Import Equations.
From Coq Require Import Utf8 List Arith Lia.
Import ListNotations.

Set Default Goal Selector "!".
Set Equations Transparent.
Set Universe Polymorphism.

Class Monad (M : Type → Type) := {
  ret : ∀ A, A → M A ;
  bind : ∀ A B, M A → (A → M B) → M B
}.

Arguments ret {M _ A}.
Arguments bind {M _ A B}.

Definition map {M} `{Monad M} {A B} (f : A → B) (m : M A) : M B :=
  bind m (λ x, ret (f x)).

Module MonadNotations.

  Declare Scope monad_scope.
  Delimit Scope monad_scope with monad.

  Open Scope monad_scope.

  Notation "c >>= f" :=
    (bind c f)
    (at level 50, left associativity) : monad_scope.

  Notation "x ← e ;; f" :=
    (bind e (λ x, f))
    (at level 100, e at next level, right associativity)
    : monad_scope.

  Notation "' pat ← e ;; f" :=
    (bind e (λ pat, f))
    (at level 100, e at next level, right associativity, pat pattern)
    : monad_scope.

  Notation "e ;; f" :=
    (bind e (λ _, f))
    (at level 100, right associativity)
    : monad_scope.

  Notation "f '<*>' m" :=
    (map f m)
    (at level 50, left associativity)
    : monad_scope.

End MonadNotations.

(** ** The error monad and monad transformer *)

Inductive exn E A :=
| success (x : A)
| exception (e : E).

Arguments success {E A}.
Arguments exception {E A}.

Definition exn_bind {E A B} (c : exn E A) (f : A → exn E B) :=
  match c with
  | success x => f x
  | exception e => exception e
  end.

#[local] Instance MonadExn {E} : Monad (exn E) := {|
  ret A x := success x ;
  bind A B c f := exn_bind c f
|}.

(* Exception monad transformer *)
#[local] Instance MonadExnT {E M} `{Monad M} : Monad (λ A, M (exn E A)) := {|
  ret A x := ret (success x) ;
  bind A B c f := bind (M := M) c (λ x,
    match x with
    | success y => f y
    | exception e => ret (exception e)
    end
  )
|}.

Class MonadRaise E (M : Type → Type) := {
  raise : ∀ (A : Type), E → M A
}.

Arguments raise {E M _ A} e.

#[local] Instance MonadRaiseExnT {E M} `{Monad M} : MonadRaise E (λ A, M (exn E A)) := {|
  raise A e := ret (exception e)
|}.

Definition succeeds {E A} (m : exn E A) :=
  match m with
  | success _ => true
  | _ => false
  end.