Require Import Autosubst2.syntax unscoped par typing.
Require Import FunctionalExtensionality PropExtensionality.
From stdpp Require Import relations (rtc(..)).
Require Import ssreflect.
From Hammer Require Import Tactics.
From Equations Require Import Equations.

Definition ProdSpace (PA : Tm -> Prop) (PF : Tm -> (Tm -> Prop) -> Prop) (b : Tm) :=
  forall a PB, PA a -> PF a PB -> PB (App b a).

Inductive InterpExt i I : Tm -> (Tm -> Prop) -> Prop :=
| InterpExt_Ne A
| InterpExt_Fun A B PA PF :
  InterpExt i I A PA ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a PB, PA a -> PF a PB -> InterpExt i I (subst_Tm (scons a ids) B) PB) ->
  InterpExt i I (Pi A B) (ProdSpace PA PF)

| InterpExt_Squash A :
  (* -------------------- *)
  InterpExt i I (Squash A) (fun a => exists b, rtc Par a (Box b))

| InterpExt_Empty :
  InterpExt i I Empty (fun a => False)

| InterpExt_Univ j :
  j < i ->
  InterpExt i I (Univ j) (fun A => I j A)

| InterpExt_Step A A0 PA :
  A ⇒ A0 ->
  InterpExt i I A0 PA ->
  InterpExt i I A PA.

Equations InterpUnivN (i : nat) : Tm -> (Tm -> Prop) -> Prop
  by wf i lt :=
  InterpUnivN i := InterpExt i
                       (fun j A =>
                          match Compare_dec.lt_dec j i with
                          | left h => exists PA, InterpUnivN j A PA
                          | right _ => False
                          end).

Lemma InterpExt_Univ' i I j PF :
  PF = (fun A => I j A) ->
  j < i ->
  InterpExt i I (Univ j) PF.
Proof. hauto lq:on ctrs:InterpExt. Qed.

Lemma InterpExt_lt_redundant i I0 I1 A PA
  (h0 : forall j,  j < i -> I0 j = I1 j)
  (h : InterpExt i I0 A PA) :
       InterpExt i I1 A PA.
Proof.
  elim : A PA / h.
  - hauto lq:on ctrs:InterpExt.
  - hauto l:on.
  - hauto l:on ctrs:InterpExt.
  - hauto lq:on use:InterpExt_Univ.
  - hauto l:on ctrs:InterpExt.
Qed.

Lemma InterpExt_lt_redundant_iff i I0 I1 A PA
  (h0 : forall j,  j < i -> I0 j = I1 j) :
  (InterpExt i I0 A PA <-> InterpExt i I1 A PA).
Proof.
  have : forall j : nat, j < i -> I1 j = I0 j by firstorder.
  firstorder using InterpExt_lt_redundant.
Qed.

Lemma InterpUnivN_nolt i :
  InterpUnivN i = InterpExt i (fun j A => exists PA, InterpUnivN j A PA).
Proof.
  simp InterpUnivN.
  extensionality A.
  extensionality S.
  apply propositional_extensionality.
  apply InterpExt_lt_redundant_iff.
  move => j ?.
  case : Compare_dec.lt_dec=>//=.
Qed.

#[export]Hint Rewrite InterpUnivN_nolt : InterpUniv.

Lemma InterpExt_Fun_inv i I A B P
  (h :  InterpExt i I (Pi A B) P) :
  exists PA PF,
    InterpExt i I A PA /\
    (forall a, PA a -> exists PB, PF a PB) /\
    (forall a PB, PA a -> PF a PB -> InterpExt i I (subst_Tm (scons a ids) B) PB) /\
    P = ProdSpace PA PF.
Proof.
  move E : (Pi A B) h => T h.
  move : A B E.
  elim : T P / h => //.
  - hauto l:on.
  - move => *. subst.
    admit.
Admitted.


Definition ρ_ok Γ := forall i ℓ A,
    Lookup i Γ ℓ A ->
    match ℓ with
    | Irrel => True
    | Rel => forall m PA, InterpUnivN .

IOk (c2e Δ) ℓ (ρ i) /\ forall m PA, ⟦ c2e Δ ⊨ A [ρ] ⟧ m ↘ PA -> PA ℓ (ρ i).
