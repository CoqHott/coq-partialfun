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

Import MonadNotations.

Class MonadTransformer (L : (Type -> Type) -> (Type → Type)) :=
{
  mon_trans_mon : ∀ M, Monad M → Monad (L M) ;
  lift : ∀ M, Monad M → ∀ A, M A -> L M A 
}.

Open Scope type_scope.

Definition id {X : Type} := fun x : X => x.

Arguments id {_} _ /.

#[local] Instance MonadId : Monad id := {
  ret := @id ;
  bind := fun A B x f => f x
}.

Class Errors := error_type : Type.

Inductive result `{E : Errors} A : Type :=
  | ok : A -> result A
  | error : error_type -> result A.

Arguments ok {E A}.
Arguments error {E A}.

#[export, refine] Instance MonadTransResult `{Errors} :
  MonadTransformer (fun M A => M (result A)) := {}.
Proof.
  - intros M HM.
    split.
    + exact (fun _ x => ret (ok x)).
    + exact (
        fun _ _ v f =>
          v >>=
          (fun v =>
            match v with
            | ok x => f x
            | error e => ret (error e)
            end)
      ).
  - intros M HM A x.
    exact (x >>= (fun y => (ret (ok y)))).
Defined.

Definition success {M} `{Monad M} `{E : Errors} : M (result unit) := ret (ok tt).
Definition raise {M} `{Monad M} `{Errors} {A : Type} (e : error_type): M (result A) :=
  ret (error e).