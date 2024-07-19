Require Import Autosubst2.syntax unscoped core FunInd ssreflect.
From Hammer Require Import Tactics.
From stdpp Require Import relations (rtc(..)).

Variant Level := Rel | Irrel.

Reserved Infix "⇒" (at level 60, right associativity).
Inductive Par : Tm -> Tm -> Prop :=
| P_Var i :
  (* ------- *)
  VarTm i ⇒ VarTm i
| P_Univ n :
  (* -------- *)
  Univ n ⇒ Univ n
| P_Pi A0 A1 B0 B1 :
  A0 ⇒ A1 ->
  B0 ⇒ B1 ->
  (* --------------------- *)
  Pi A0 B0 ⇒ Pi A1 B1
| P_Abs a0 a1 :
  a0 ⇒ a1 ->
  (* -------------------- *)
  Abs a0 ⇒ Abs a1
| P_App a0 a1 b0 b1 :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  (* ------------------------- *)
  App a0 b0 ⇒ App a1 b1
| P_AppAbs a a0 b0 b1 :
  a ⇒ a0 ->
  b0 ⇒ b1 ->
  (* ---------------------------- *)
  App (Abs a) b0 ⇒ subst_Tm (scons b1 ids) a0
| P_Squash A0 A1 :
  A0 ⇒ A1 ->
  (* ------------------- *)
  Squash A0 ⇒ Squash A1
| P_Box a0 a1 :
  a0 ⇒ a1 ->
  (* -------------------------- *)
  Box a0 ⇒ Box a1
| P_Let a0 a1 b0 b1 :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  (* ------------------------- *)
  Let a0 b0 ⇒ Let a1 b1
| P_LetBox a0 a1 b0 b1 :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  (* ------------------------- *)
  Let (Box a0) b0 ⇒ subst_Tm (scons a1 ids) b1
| P_Empty :
  (* ----------- *)
  Empty ⇒ Empty
| P_Absurd a0 a1 :
  a0 ⇒ a1 ->
  (* ------------------- *)
  Absurd a0 ⇒ Absurd a1
where "A ⇒ B" := (Par A B).
#[export]Hint Constructors Par : par.

Definition Coherent A B := exists C, rtc Par A C /\ rtc Par B C.

Derive Inversion Par_inv with (forall a b, a ⇒ b).

Lemma Par_refl a : a ⇒ a.
Proof. elim : a; hauto lq:on ctrs:Par. Qed.

Lemma P_AppAbs_cbn a b b0 :
  b0 = subst_Tm (scons b ids) a ->
  (App (Abs a) b) ⇒ b0.
Proof. hauto lq:on ctrs:Par use:Par_refl. Qed.

Lemma P_AppAbs' a a0 b0 b1 b:
  b = subst_Tm (scons b1 ids) a0 ->
  a ⇒ a0 ->
  b0 ⇒ b1 ->
  (* ---------------------------- *)
  App (Abs a) b0 ⇒ b.
Proof. hauto lq:on use:P_AppAbs. Qed.

Lemma P_LetBox' a0 a1 b0 b1 b :
  b = subst_Tm (scons a1 ids) b1 ->
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  (* ------------------------- *)
  Let (Box a0) b0 ⇒ b.
Proof. hauto lq:on use:P_LetBox. Qed.

Lemma Par_renaming a b ξ :
  a ⇒ b -> ren_Tm ξ a ⇒ ren_Tm ξ b.
Proof.
  move => h.
  move : ξ.
  elim : a b / h => /=; eauto with par.
  - move => *.
    apply : P_AppAbs'; eauto. by asimpl.
  - move => *.
    apply : P_LetBox'; eauto; by asimpl.
Qed.

Lemma Par_morphing_lift (ξ0 ξ1 : nat -> Tm)
  (h : forall i, (ξ0 i ⇒ ξ1 i)) :
  forall i, (up_Tm_Tm ξ0 i ⇒ up_Tm_Tm ξ1 i).
Proof. qauto l:on inv:nat use:Par_refl, Par_renaming. Qed.

Lemma Par_morphing a b σ0 σ1
  (h : forall i, σ0 i ⇒ σ1 i) :
  (a ⇒ b) ->
  (subst_Tm σ0 a ⇒ subst_Tm σ1 b).
Proof.
  move => h0.
  move : σ0 σ1 h.
  elim : a b/h0; try solve [move => //=; eauto with par].
  - hauto lq:on ctrs:Par use:Par_morphing_lift.
  - hauto lq:on ctrs:Par use:Par_morphing_lift.
  - move => a a0 b0 b1 h0 ih0 h1 ih1 σ0 σ h /=.
    apply : P_AppAbs'; cycle 1; eauto.
    sfirstorder use:Par_morphing_lift.
    by asimpl.
  - hauto lq:on ctrs:Par use:Par_morphing_lift.
  - move => * /=.
    apply : P_LetBox'; cycle 1; eauto.
    sfirstorder use:Par_morphing_lift.
    by asimpl.
Qed.

Lemma Par_subst a0 a1 (h : a0 ⇒ a1) σ :
  (subst_Tm σ a0 ⇒ subst_Tm σ a1).
Proof. hauto l:on use:Par_refl, Par_morphing. Qed.
