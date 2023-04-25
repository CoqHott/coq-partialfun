(* Open general recursion library *)

From Equations Require Import Equations.
From Coq Require Import Utf8 List Arith Lia.
From PartialFun Require Import Monad.

Import ListNotations.

Set Default Goal Selector "!".
Set Equations Transparent.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Set Printing Universes.

(* TODOs

  - Maybe some subclasses to be able to only specify the fueled and/or the wf
    versions.
    + Maybe use a hint with high cost for the default instance to ease override.
  - Mutual functions without the need for encoding?
  - Better support for monads by having orec be a monad transformer?
  - Have scopes or even modules for notations.
  - Better class for autodef.

*)

(* Parameters *)

#[local] Notation default_fuel := 1000.
#[local] Notation acc_fuel := default_fuel.

(* A class of true booleans *)

Class IsTrue (b : bool) := {
  is_true : b = true
}.

#[export] Hint Extern 1 (IsTrue ?b) =>
  constructor ; reflexivity
  : typeclass_instances.

(* Specific to fuel implementations *)

Inductive Fueled (A : Type) :=
| Success (b : A)
| NotEnoughFuel
| Undefined.

Arguments Success {A}.
Arguments NotEnoughFuel {A}.
Arguments Undefined {A}.

Derive NoConfusion NoConfusionHom for Fueled.

(* Partial function class *)
Class PFun {A} (f : A) := {
  psrc : Type ;
  ptgt : psrc → Type ;
  pgraph : ∀ x, ptgt x → Prop ;
  pdomain x := ∃ v, pgraph x v ;
  pgraph_fun : ∀ x v w, pgraph x v → pgraph x w → v = w ;
  pfueled : nat → ∀ x, Fueled (ptgt x) ;
  pfueled_graph : ∀ n x v, pfueled n x = Success v → pgraph x v ;
  pdef : ∀ x, pdomain x → ptgt x ;
  pdef_graph : ∀ x h, pgraph x (pdef x h)
}.

Arguments psrc {A} f {_}.
Arguments ptgt {A} f {_}.
Arguments pgraph {A} f {_}.
Arguments pdomain {A} f {_}.
Arguments pgraph_fun {A} f {_}.
Arguments pfueled {A} f {_}.
Arguments pfueled_graph {A} f {_}.
Arguments pdef {A} f {_}.
Arguments pdef_graph {A} f {_}.

Module IndexedDefinitions.
Section IndexedCalls.
  Universes i f j k a b c.
  Context {I : Type@{i}}
    {F : I -> Type@{f}} (f : forall i, F i)
    {pfun : forall (i : I), PFun@{f j k} (f i)}
    (A : Type@{a}) (B : A -> Type@{b}).

  Inductive irec (C : Type@{c}) : Type@{c} :=
  | _ret (x : C)
  | _rec (x : A) (κ : B x → irec C)
  | _call (i : I) (x : @psrc _ _ (pfun i)) (κ : @ptgt _ _ (pfun i) x → irec C)
  | undefined.

  Fixpoint _bind {C D} (c : irec C) (f : C → irec D) : irec D :=
    match c with
    | _ret _ x => f x
    | _rec _ x κ => _rec _ x (λ y, _bind (κ y) f)
    | _call _ g x κ => _call _ g x (λ y, _bind (κ y) f)
    | undefined _ => undefined _
    end.




End IndexedCalls.

Arguments _ret {I F f pfun A B C}.
Arguments _rec {I F f pfun A B C}.
Arguments _call {I F f pfun A B C}.
Arguments undefined {I F f pfun A B C}.

Section WithIndexes.

  Universes i f j k.
  Context {I : Type@{i}}
    {F : I -> Type@{f}} (ϕ : forall i, F i)
    {pfun : forall (i : I), PFun@{f j k} (ϕ i)}.

  Let orec := @irec I F ϕ pfun.

  #[local]
  Notation "∇ x , B" :=
    (∀ x, orec _ (λ x, B) B)
    (x binder, at level 200).

  #[local]
  Notation "A ⇀ B" :=
    (∇ (_ : A), B)
    (at level 199).

  #[local] Notation "t ∙1" := (proj1_sig t) (at level 20).
  #[local] Notation "⟨ x ⟩" := (exist _ x _) (only parsing).
  #[local] Notation "⟨ x | h ⟩" := (exist _ x h).

  Section Lib.
    Context {A B} (f : ∇ (x : A), B x).

    Existing Instance pfun.

    Inductive orec_graph {a} : orec A B (B a) → B a → Prop :=
    | ret_graph :
        ∀ x,
          orec_graph (_ret x) x

    | rec_graph :
        ∀ x κ v w,
          orec_graph (f x) v →
          orec_graph (κ v) w →
          orec_graph (_rec x κ) w

    | call_graph :
        ∀ g x κ v w,
          pgraph (ϕ g) x v →
          orec_graph (κ v) w →
          orec_graph (_call g x κ) w.

    Definition graph x v :=
      orec_graph (f x) v.

    Inductive orec_lt {a} : A → orec A B (B a) → Prop :=
    | top_lt :
        ∀ x κ,
          orec_lt x (_rec x κ)

    | rec_lt :
        ∀ x κ v y,
          graph x v →
          orec_lt y (κ v) →
          orec_lt y (_rec x κ)

    | call_lt :
        ∀ g x κ v y,
          pgraph (ϕ g) x v →
          orec_lt y (κ v) →
          orec_lt y (_call g x κ).

    Definition partial_lt x y :=
      orec_lt x (f y).

    Definition domain x :=
      ∃ v, graph x v.

    Derive Signature for orec_graph.
    Derive Signature for orec_lt.
    Derive NoConfusion NoConfusionHom for irec.

    Lemma orec_graph_functional :
      ∀ a o v w,
        orec_graph (a := a) o v →
        orec_graph o w →
        v = w.
    Proof.
      intros a o v w hv hw.
      induction hv in w, hw |- *.
      - depelim hw. reflexivity.
      - depelim hw.
        assert (v = v0).
        { apply IHhv1. assumption. }
        subst. apply IHhv2. assumption.
      - depelim hw.
        assert (v = v0).
        { apply pgraph_fun. all: assumption. }
        subst. apply IHhv. assumption.
    Qed.

    Lemma lt_preserves_domain :
      ∀ x y,
        domain x →
        partial_lt y x →
        domain y.
    Proof.
      intros x y h hlt.
      destruct h as [v h].
      red in hlt. red in h.
      set (o := f _) in *. clearbody o.
      induction h in y, hlt |- *.
      - depelim hlt.
      - depelim hlt.
        + eexists. eassumption.
        + assert (v = v0).
          { eapply orec_graph_functional. all: eassumption. }
          subst.
          apply IHh2. assumption.
      - depelim hlt.
        assert (v = v0).
        { eapply pgraph_fun. all: eassumption. }
        subst.
        apply IHh. assumption.
    Qed.

    (* Fuel version *)

    Fixpoint orec_fuel_inst {a} n (e : orec A B (B a)) (r : ∀ x, Fueled (B x)) :=
      match e with
      | _ret v => Success v
      | _rec x κ =>
        match r x with
        | Success v => orec_fuel_inst n (κ v) r
        | NotEnoughFuel => NotEnoughFuel
        | Undefined => Undefined
        end
      | _call g x κ =>
        match pfueled (ϕ g) n x with
        | Success v => orec_fuel_inst n (κ v) r
        | NotEnoughFuel => NotEnoughFuel
        | Undefined => Undefined
        end
      | undefined => Undefined
      end.

    (* fumes is there to get depth exponential in n *)
    Fixpoint fueled_gen n (fumes : ∀ y, Fueled (B y)) x : Fueled (B x) :=
      match n with
      | 0 => fumes x
      | S n => orec_fuel_inst n (f x) (fueled_gen n (λ x, fueled_gen n fumes x))
      end.

    Definition fueled n x :=
      fueled_gen n (λ _, NotEnoughFuel) x.

    (* We show the fueled version is sound with respect to the graph *)

    Lemma orec_fuel_inst_graph :
      ∀ a n (o : orec _ _ (_ a)) r v,
        orec_fuel_inst n o r = Success v →
        (∀ x w, r x = Success w → graph x w) →
        orec_graph o v.
    Proof.
      intros a n o r v e hr.
      induction o as [w | x κ ih | g x κ ih |] in v, e |- *.
      - simpl in e. noconf e. constructor.
      - simpl in e. destruct r as [w | |] eqn:e'. 2,3: discriminate.
        econstructor.
        + eapply hr. eassumption.
        + apply ih. assumption.
      - simpl in e. destruct pfueled as [w | |] eqn:e'. 2,3: discriminate.
        econstructor.
        + eapply pfueled_graph. eassumption.
        + apply ih. assumption.
      - discriminate.
    Qed.

    Lemma fueled_gen_graph_sound :
      ∀ n fumes x v,
        (∀ y w, fumes y = Success w → graph y w) →
        fueled_gen n fumes x = Success v →
        graph x v.
    Proof.
      intros n fumes x v hfumes e.
      induction n as [| n ih] in x, v, e, fumes, hfumes |- *.
      - eapply hfumes. assumption.
      - simpl in e.
        eapply orec_fuel_inst_graph.
        + eassumption.
        + intros y w e'.
          eapply ih. 2: eassumption.
          intros z k e2.
          eapply ih. 2: eassumption.
          eapply hfumes.
    Qed.

    Lemma fueled_graph_sound :
      ∀ n x v,
        fueled n x = Success v →
        graph x v.
    Proof.
      intros n x v e.
      eapply fueled_gen_graph_sound. 2: eassumption.
      intros. discriminate.
    Qed.

    (** Note: the lemma above says that if fueled succeeds, then its argument is
        in the domain of f, so later on we can use it in the well-founded version.
        In particular we can do a nice construction that automatically builds the
        proof when it exists.
    **)

    Definition succeeds n x :=
      match fueled n x with
      | Success v => true
      | _ => false
      end.

    Definition succeeds_domain :
      ∀ n x,
        succeeds n x = true →
        domain x.
    Proof.
      intros n x e.
      unfold succeeds in e. destruct fueled as [v | |] eqn: e'. 2,3: discriminate.
      exists v. eapply fueled_graph_sound. eassumption.
    Qed.

    (* Well-founded version *)

    Lemma partial_lt_acc :
      ∀ x,
        domain x →
        Acc partial_lt x.
    Proof.
      intros x h.
      destruct h as [v h].
      constructor. intros x' h'.
      red in h. red in h'.
      set (o := f _) in *. clearbody o.
      induction h in x', h' |- *.
      - depelim h'.
      - depelim h'.
        + constructor. intros y h.
          apply IHh1. assumption.
        + assert (v = v0).
          { eapply orec_graph_functional. all: eassumption. }
          subst.
          apply IHh2. assumption.
      - depelim h'.
        assert (v = v0).
        { eapply pgraph_fun. all: eassumption. }
        subst.
        apply IHh. assumption.
    Qed.

    Notation sigmaarg :=
      (sigma (λ x, domain x)).

    #[local] Instance wf_partial :
      WellFounded (λ (x y : sigmaarg), partial_lt (pr1 x) (pr1 y)).
    Proof.
      eapply Acc_intro_generator with (1 := acc_fuel).
      intros [x h].
      pose proof (partial_lt_acc x h) as hacc.
      induction hacc as [x hacc ih] in h |- *.
      constructor. intros [y h'] hlt.
      apply ih. assumption.
    Defined.

    (* We need this for the proofs to go through *)
    Opaque wf_partial.

    Definition image x :=
      { v | graph x v }.

    Definition oimage {a} (o : orec A B (B a)) :=
      { v | orec_graph o v }.

    Definition orec_domain {a} (o : orec A B (B a)) :=
      ∃ v, orec_graph o v.

    Equations? orec_inst {a} (e : orec A B (B a)) (de : orec_domain e)
      (da : domain a)
      (ha : ∀ x, orec_lt x e → partial_lt x a)
      (r : ∀ y, domain y → partial_lt y a → image y) : oimage e :=
      orec_inst (_ret v) de da ha r := ⟨ v ⟩ ;
      orec_inst (_rec x κ) de da ha r := ⟨ (orec_inst (κ ((r x _ _) ∙1)) _ _ _ r) ∙1 ⟩ ;
      orec_inst (_call g x κ) de da ha r := ⟨ (orec_inst (κ (pdef (ϕ g) x _)) _ _ _ r) ∙1 ⟩ ;
      orec_inst undefined de da ha r := False_rect _ _.
    Proof.
      - constructor.
      - eapply lt_preserves_domain. 1: eassumption.
        apply ha. constructor.
      - apply ha. constructor.
      - destruct de as [v hg]. depelim hg. simpl in *.
        destruct r as [w hw]. simpl.
        red in hw.
        assert (w = v0).
        { eapply orec_graph_functional. all: eassumption. }
        subst.
        eexists. eassumption.
      - apply ha. econstructor. 2: eassumption.
        red. destruct r. assumption.
      - simpl. destruct orec_inst. simpl.
        econstructor. 2: eassumption.
        destruct r. assumption.
      - destruct de as [v hg]. depelim hg.
        eexists. eassumption.
      - lazymatch goal with
        | |- context [ pdef _ x ?prf ] => set (hh := prf) ; clearbody hh
        end.
        destruct de as [v hg]. depelim hg. simpl in *.
        pose proof (pdef_graph (ϕ g) x hh) as hg'.
        move hg' at top. eapply pgraph_fun in hg'. 2: eassumption.
        subst. eexists. eassumption.
      - lazymatch goal with
        | h : context [ pdef _ x ?prf ] |- _ =>
            set (hh := prf) in h ; clearbody hh
        end.
        apply ha. econstructor. 2: eassumption.
        apply pdef_graph.
      - destruct orec_inst. simpl.
        lazymatch goal with
        | h : context [ pdef _ x ?prf ] |- _ =>
            set (hh := prf) in h ; clearbody hh
        end.
        econstructor. 2: eassumption.
        apply pdef_graph.
      - destruct de as [v hg]. depelim hg.
    Defined.

    Equations def_p (x : A) (h : domain x) : image x
      by wf x partial_lt :=
      def_p x h := orec_inst (a := x) (f x) _ _ _ (λ y hy hr, def_p y _).

    Definition def x h :=
      def_p x h ∙1.

    Lemma def_graph_sound :
      ∀ x h,
        graph x (def x h).
    Proof.
      intros x h.
      unfold def. destruct def_p. assumption.
    Qed.

    (* Well-founded version with automatic domain inferrence *)

    Definition autodef (x : A) `{e : IsTrue (succeeds default_fuel x)} :=
      def x (succeeds_domain default_fuel x e.(is_true)).

    (* Proving properties about such functions *)

    Notation precond := (A → Prop).
    Notation postcond := (∀ x, B x → Prop).

    Fixpoint orec_ind_step a (pre : precond) (post : postcond) o :=
      match o with
      | _ret v => post a v
      | _rec x κ => pre x ∧ ∀ v, post x v → orec_ind_step a pre post (κ v)
      | _call g x κ => ∀ v, pgraph (ϕ g) x v → orec_ind_step a pre post (κ v)
      | undefined => True
      end.

    Definition funind (pre : precond) post :=
      ∀ x, pre x → orec_ind_step x pre post (f x).

    (* The fueled case *)

    Lemma orec_fuel_inst_ind_step :
      ∀ a n pre post o r v,
        orec_ind_step a pre post o →
        orec_fuel_inst n o r = Success v →
        (∀ x w, pre x → r x = Success w → post x w) →
        post a v.
    Proof.
      intros a n pre post o r v h e hr.
      induction o as [w | x κ ih | g x κ ih |] in v, h, e |- *.
      - simpl in *. noconf e. assumption.
      - simpl in *. destruct r as [w | |] eqn:e'. 2,3: discriminate.
        eapply ih. 2: eassumption.
        apply h. eapply hr.
        + apply h.
        + assumption.
      - simpl in *.
        destruct pfueled as [w | |] eqn:e'. 2,3: discriminate.
        eapply ih. 2: eassumption.
        apply h. eapply pfueled_graph. eassumption.
      - discriminate.
    Qed.

    Lemma funind_fuel_gen :
      ∀ pre post x n fumes v,
        funind pre post →
        pre x →
        (∀ x v, fumes x = Success v → pre x → post x v) →
        fueled_gen n fumes x = Success v →
        post x v.
    Proof.
      intros pre post x n fumes v h hpre hfumes e.
      induction n as [| n ih] in x, v, hpre, e, fumes, hfumes |- *.
      - simpl in e. apply hfumes. all: assumption.
      - simpl in e. eapply orec_fuel_inst_ind_step. 2: eassumption.
        + apply h. assumption.
        + intros y w hy e'.
          eapply ih. 1,3: eassumption.
          simpl.
          intros z u hz e2.
          eapply ih. all: eassumption.
    Qed.

    Lemma funind_fuel :
      ∀ pre post x n v,
        funind pre post →
        pre x →
        fueled n x = Success v →
        post x v.
    Proof.
      intros pre post x n v h hpre e.
      eapply funind_fuel_gen. 1,2,4: eassumption.
      simpl. intros. discriminate.
    Qed.

    (* The wf case *)

    Lemma orec_inst_ind_step :
      ∀ a o hdo da ha (r : ∀ y, domain y → partial_lt y a → image y) pre post,
        orec_ind_step a pre post o →
        (∀ x h hlt, pre x → post x ((r x h hlt) ∙1)) →
        post a ((orec_inst (a := a) o hdo da ha r) ∙1).
    Proof.
      intros a o hdo da ha r pre post ho hr.
      induction o as [w | x κ ih | g x κ ih |] in ha, hdo, ho |- *.
      - simpl in ho. simp orec_inst.
      - simpl in ho. simp orec_inst. simpl.
        apply ih. apply ho. apply hr. apply ho.
      - simpl in ho. simp orec_inst. simpl.
        apply ih. eapply ho. apply pdef_graph.
      - destruct hdo as [? h]. depelim h.
    Qed.

    Lemma def_ind :
      ∀ pre post x h,
        funind pre post →
        pre x →
        post x (def x h).
    Proof.
      intros pre post x h ho hpre.
      unfold def.
      revert hpre.
      (* funelim fails with an anomaly *)
      apply_funelim (def_p x h). intros.
      refine (orec_inst_ind_step _ _ _ _ _ _ _ _ _ _).
      - apply ho. assumption.
      - intros. eapply H1. assumption.
    Qed.

    (* We deduce the graph case from the above *)

    Lemma funind_graph :
      ∀ pre post x v,
        funind pre post →
        pre x →
        graph x v →
        post x v.
    Proof.
      intros pre post x v h hpre e.
      assert (hx : domain x).
      { eexists. eassumption. }
      pose proof (def_graph_sound x hx) as hgr.
      assert (v = def x hx).
      { eapply orec_graph_functional. all: eassumption. }
      subst.
      eapply def_ind. all: eassumption.
    Qed.

    (* Same as funind but for Type *)

    Notation precondT := (A → Type).
    Notation postcondT := (∀ x, B x → Type).

    Fixpoint orec_ind_stepT a (pre : precondT) (post : postcondT) o :=
      match o with
      | _ret v => post a v
      | _rec x κ => pre x * ∀ v, post x v → orec_ind_stepT a pre post (κ v)
      | _call g x κ => ∀ v, pgraph (ϕ g) x v → orec_ind_stepT a pre post (κ v)
      | undefined => True
      end%type.

    Definition funrect pre post :=
      ∀ x, pre x → orec_ind_stepT x pre post (f x).

    Lemma orec_inst_ind_stepT :
      ∀ a o hdo da ha (r : ∀ y, domain y → partial_lt y a → image y) pre post,
        orec_ind_stepT a pre post o →
        (∀ x h hlt, pre x → post x ((r x h hlt) ∙1)) →
        post a ((orec_inst (a := a) o hdo da ha r) ∙1).
    Proof.
      intros a o hdo da ha r pre post ho hr.
      induction o as [w | x κ ih | g x κ ih |] in ha, hdo, ho |- *.
      - simpl in ho. simp orec_inst.
      - simpl in ho. simp orec_inst. simpl.
        apply ih. apply ho. apply hr. apply ho.
      - simpl in ho. simp orec_inst. simpl.
        apply ih. eapply ho. apply pdef_graph.
      - exfalso. destruct hdo as [? h]. depelim h.
    Qed.

    Lemma def_rect :
      ∀ pre post x h,
        funrect pre post →
        pre x →
        post x (def x h).
    Proof.
      intros pre post x h ho hpre.
      unfold def.
      revert hpre.
      (* funelim fails with an anomaly *)
      apply_funelim (def_p x h). intros.
      refine (orec_inst_ind_stepT _ _ _ _ _ _ _ _ _ _).
      - apply ho. assumption.
      - intros. eapply X1. assumption.
    Qed.

    Lemma funrect_graph :
      ∀ pre post x v,
        funrect pre post →
        pre x →
        graph x v →
        post x v.
    Proof.
      intros pre post x v h hpre e.
      assert (hx : domain x).
      { eexists. eassumption. }
      pose proof (def_graph_sound x hx) as hgr.
      assert (v = def x hx).
      { eapply orec_graph_functional. all: eassumption. }
      subst.
      eapply def_rect. all: eassumption.
    Qed.

    Lemma funrect_fuel :
      ∀ pre post x n v,
        funrect pre post →
        pre x →
        fueled n x = Success v →
        post x v.
    Proof.
      intros pre post x n v h hpre e.
      eapply fueled_graph_sound in e.
      eapply funrect_graph in e. all: eassumption.
    Qed.

    (* Computing the domain, easier than using the graph *)

    Fixpoint comp_domain {a} (o : orec A B a) :=
      match o with
      | _ret v => True
      | _rec x κ => domain x ∧ ∀ v, graph x v → comp_domain (κ v)
      | _call g x κ => pdomain (ϕ g) x ∧ ∀ v, pgraph (ϕ g) x v → comp_domain (κ v)
      | undefined => False
      end.

    Lemma comp_domain_orec_domain :
      ∀ a (o : orec A B (B a)),
        comp_domain o →
        orec_domain o.
    Proof.
      intros a o h.
      induction o as [w | x κ ih | g x κ ih |] in h |- *.
      - eexists. constructor.
      - simpl in h. destruct h as [[v hx] hκ].
        specialize (hκ v hx). apply ih in hκ. destruct hκ as [w h].
        eexists. econstructor. all: eassumption.
      - simpl in h. destruct h as [[v hx] hκ].
        specialize (hκ v hx). apply ih in hκ. destruct hκ as [w h].
        eexists. econstructor. all: eassumption.
      - contradiction.
    Qed.

    Lemma compute_domain :
      ∀ x,
        comp_domain (f x) →
        domain x.
    Proof.
      intro x. apply comp_domain_orec_domain.
    Qed.

    (* Now we can let it compute *)
    Transparent wf_partial.

  End Lib.

  (* We can provide an instance for all partial functions defined as above. *)
  #[export, refine] Instance pfun_gen A B (f : ∇ (x : A), B x) : PFun f := {|
    psrc := A ;
    ptgt := B ;
    pgraph := graph f ;
    pfueled := fueled f ;
    pdef := def f
  |}.
  Proof.
    - intros. eapply orec_graph_functional. all: eassumption.
    - apply fueled_graph_sound.
    - apply def_graph_sound.
  Defined.

  (* orec is a monad *)
  #[export] Instance MonadOrec {A B} : Monad (orec A B) := {|
    ret C x := _ret x ;
    bind C D c f := _bind ϕ A B c f
  |}.

  (* It has some actions *)
  Definition rec {A B} (x : A) : orec A B (B x) :=
    _rec x (λ y, ret y).

  Definition call {A B} g (x : psrc (ϕ g)) : orec A B (ptgt (ϕ g) x) :=
    _call g x (λ y, ret y).

  End WithIndexes.

  Definition irecBound@{i j | i <= j +}
    {I : Type@{i}} {F : I -> Type@{i}}
    (ϕ : forall i, F i)
    `{pfun : forall i, PFun@{i i i} (ϕ i)}
    (A : Type@{i}) (B : A -> Type@{i}) (C : Type@{j}) : Type@{j} :=
    @irec@{i i i i i i j} I F ϕ pfun A B C.

  Notation "∇[ ϕ ] x , B" :=
    (∀ x, irec ϕ _ (λ x, B) B)
    (x binder, ϕ at level 50, at level 200).

  Section Test.
    Context {I : Type} {F : I -> Type}
    (ϕ : forall i, F i)
    `{pfun : forall i, PFun (ϕ i)}.

    Check ∇[ ϕ ] _, _.
  End Test.

  Notation "A ⇀[ ϕ ] B" :=
    (∇[ϕ] (_ : A), B)
    (at level 199).

  (* Handy notation for autodef *)
  Notation "f @ x" := (autodef f x) (at level 10).

  (* Useful tactics *)
  Tactic Notation "funind" constr(p) "in" hyp(h) :=
    lazymatch type of h with
    | graph ?ϕ ?f ?x ?v =>
      lazymatch type of p with
      | context [ funind _ _ _ _ ] =>
        eapply funind_graph with (1 := p) in h ; [| try (exact I)]
      | context [ funrect _ _ _ _ ] =>
        eapply funrect_graph with (1 := p) in h ; [| try (exact I)]
      | _ => fail "Argument should be of type funind or funrect"
      end
    | _ => fail "Hypothesis should be about graph"
    end.

  Tactic Notation "funind" constr(p) "in" hyp(h) "as" ident(na) :=
    lazymatch type of h with
    | graph ?ϕ ?f ?x ?v =>
      lazymatch type of p with
      | context [ funind _ _ _ _ ] =>
        eapply funind_graph with (f := p) in h as na ; [| try (exact I)]
      | context [ funrect _ _ _ _ ] =>
        eapply funrect_graph with (f := p) in h as na ; [| try (exact I)]
      | _ => fail "Argument should be of type funind or funrect"
      end
    | _ => fail "Hypothesis should be about graph"
    end.
End IndexedDefinitions.


Module StdInstance.

Record PackedPfun := { carrier :> Type ; elt : carrier ; pfun : @PFun carrier elt }.


Definition orec@{j a b c} (A : Type@{a}) (B : A -> Type@{b}) (C : Type@{c}) : Type@{c} :=
  @IndexedDefinitions.irec@{c j j j a b c} PackedPfun@{j j j} carrier elt pfun A B C.

Section Redef.
  Context {A B} (f : ∀ x : A, orec A B (B x)).

  Definition domain x := IndexedDefinitions.domain _ f x.

  Definition image x := IndexedDefinitions.image _ f x.

  Definition oimage {a} (o : orec A B (B a)) := IndexedDefinitions.oimage _ f o.

  Definition comp_domain {a} (o : orec A B a) : Prop := IndexedDefinitions.comp_domain _ f o.

  Lemma compute_domain :
    ∀ x,
      comp_domain (f x) →
      domain x.
  Proof. apply IndexedDefinitions.compute_domain. Qed.

  Definition fueled n x := IndexedDefinitions.fueled _ f n x.

  Definition def x h := IndexedDefinitions.def _ f x h.

  Definition funind : (A → Prop) → (∀ x : A, B x → Prop) → Prop := IndexedDefinitions.funind _ f.

  Lemma def_ind :
    ∀ pre post x h,
      funind pre post →
      pre x →
      post x (def x h).
  Proof. apply IndexedDefinitions.def_ind. Qed.

  Definition graph : ∀ x : A, B x → Prop := IndexedDefinitions.graph _ f.

  Lemma def_graph_sound :
    ∀ x h,
      graph x (def x h).
  Proof. apply IndexedDefinitions.def_graph_sound. Qed.

  Definition succeeds n x := IndexedDefinitions.succeeds _ f n x.

  Definition succeeds_domain :
    ∀ n x,
      succeeds n x = true →
      domain x.
  Proof. apply IndexedDefinitions.succeeds_domain. Qed.

  Lemma funind_fuel :
    ∀ pre post x n v,
      funind pre post →
      pre x →
      fueled n x = Success v →
      post x v.
  Proof. apply IndexedDefinitions.funind_fuel. Qed.

  Lemma funind_graph :
    ∀ pre post x v,
      funind pre post →
      pre x →
      graph x v →
      post x v.
  Proof. apply IndexedDefinitions.funind_graph. Qed.

  Definition funrect : (A → Type) → (∀ x : A, B x → Type) → Type :=
    IndexedDefinitions.funrect _ f.

  Lemma funrect_graph :
    ∀ pre post x v,
      funrect pre post →
      pre x →
      graph x v →
      post x v.
  Proof. apply IndexedDefinitions.funrect_graph. Qed.


  (* Well-founded version with automatic domain inferrence *)

  Definition autodef (x : A) `{e : IsTrue (succeeds default_fuel x)} :=
    def x (succeeds_domain default_fuel x e.(is_true)).

End Redef.

Notation "∇ x , B" :=
  (∀ x, orec _ (λ x, B) B)
  (x binder, at level 200).

Notation "A ⇀ B" :=
  (∇ (_ : A), B)
  (at level 199).


#[export] Instance pfun_gen A B (f : ∇ (x : A), B x) : PFun f :=
  IndexedDefinitions.pfun_gen _ A B f.

(* orec is a monad *)
#[export] Instance MonadOrec {A B} : Monad (orec A B) :=
  IndexedDefinitions.MonadOrec _.

(* It has some actions *)
Definition rec {A B} (x : A) : orec A B (B x) :=
  IndexedDefinitions._rec x (λ y, ret y).

Definition call {A B} {F} f `{h : PFun F f} (x : psrc f) : orec A B (ptgt f x) :=
  IndexedDefinitions._call {| carrier := F; elt := f ; pfun := h |} x
    (λ y, ret y).

Notation "f @ x" := (IndexedDefinitions.autodef _ f x) (at level 10).

(* Useful tactics *)
Tactic Notation "funind" constr(p) "in" hyp(h) :=
  lazymatch type of h with
  | graph ?f ?x ?v =>
    lazymatch type of p with
    | context [ funind _ _ _ ] =>
      eapply funind_graph with (1 := p) in h ; [| try (exact I)]
    | context [ funrect _ _ _ ] =>
      eapply funrect_graph with (1 := p) in h ; [| try (exact I)]
    | _ => fail "Argument should be of type funind or funrect"
    end
  | _ => fail "Hypothesis should be about graph"
  end.

Tactic Notation "funind" constr(p) "in" hyp(h) "as" ident(na) :=
  lazymatch type of h with
  | graph ?f ?x ?v =>
    lazymatch type of p with
    | context [ funind _ _ _ ] =>
      eapply funind_graph with (1 := p) in h as na ; [| try (exact I)]
    | context [ funrect _ _ _ ] =>
      eapply funrect_graph with (1 := p) in h as na ; [| try (exact I)]
    | _ => fail "Argument should be of type funind or funrect"
    end
  | _ => fail "Hypothesis should be about graph"
  end.

End StdInstance.


