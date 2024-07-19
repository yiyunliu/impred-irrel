Require Import Autosubst2.syntax unscoped par typing.
Require Import FunctionalExtensionality PropExtensionality.
From stdpp Require Import relations (rtc(..)).
Require Import ssreflect ssrbool.
From Hammer Require Import Tactics.
From Equations Require Import Equations.

Definition ProdSpace (PA : Tm -> Prop) (PF : Tm -> (Tm -> Prop) -> Prop) (b : Tm) :=
  forall a PB, PA a -> PF a PB -> PB (App b a).

Inductive InterpExt i I : Tm -> (Tm -> Prop) -> Prop :=
| InterpExt_Ne A :
  (* ----------------------- *)
  ne A -> InterpExt i I A wne

| InterpExt_Fun A B PA PF :
  InterpExt i I A PA ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a PB, PA a -> PF a PB -> InterpExt i I (subst_Tm (scons a ids) B) PB) ->
  InterpExt i I (Pi A B) (ProdSpace PA PF)

| InterpExt_Squash A :
  (* -------------------- *)
  InterpExt i I (Squash A) (fun a => wne a \/ exists b, rtc Par a (Box b) /\ wn b)

| InterpExt_Empty :
  InterpExt i I Empty wne

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
  - by case.
  - hauto l:on.
  - move => *. subst.
    hauto lq:on rew:off inv:Par ctrs:InterpExt use:Par_subst.
Qed.

Lemma InterpExt_Fun_nopf i I A B PA :
  InterpExt i I A PA ->
  (forall a, PA a -> exists PB, InterpExt i I (subst_Tm (scons a ids) B) PB) ->
  InterpExt i I (Pi A B) (ProdSpace PA (fun a PB => InterpExt i I (subst_Tm (scons a ids) B) PB)).
Proof. hauto l:on ctrs:InterpExt. Qed.

Lemma InterpExt_cumulative i j I A PA :
  i <= j ->
  InterpExt i I A PA ->
  InterpExt j I A PA.
Proof.
  move => h h0.
  elim : A PA /h0;
    hauto l:on ctrs:InterpExt use:PeanoNat.Nat.le_trans.
Qed.

Lemma InterpUnivN_cumulative i j A PA :
  i <= j ->
  InterpUnivN i A PA ->
  InterpUnivN j A PA.
Proof.
  hauto l:on rew:db:InterpUniv use:InterpExt_cumulative.
Qed.

Lemma Pars_antirenaming (a b0 : Tm) ξ
  (h : rtc Par (ren_Tm ξ a) b0) : exists b, b0 = ren_Tm ξ b /\ (rtc Par a b).
Proof.
  move E : (ren_Tm ξ a) h => a0 h.
  move : a E.
  elim : a0 b0 / h.
  - hauto lq:on ctrs:rtc.
  - move => a b c h0 h ih a0 ?. subst.
    move /Par_antirenaming : h0.
    hauto lq:on ctrs:rtc, eq.
Qed.

Lemma wn_antirenaming a ξ : wn (ren_Tm ξ a) -> wn a.
Proof.
  hauto lq:on use:Pars_antirenaming, ne_nf_renaming unfold:wn.
Qed.

Lemma S_Abs a b
  (h : rtc Par a b) :
  rtc Par (Abs a) (Abs b).
Proof. elim : a b /h; hauto lq:on ctrs:Par,rtc. Qed.

Lemma wn_abs (a : Tm) (h : wn a) : wn (Abs a).
Proof.
  move : h => [v [? ?]].
  exists (Abs v).
  eauto using S_Abs.
Qed.

Lemma ext_wn i (a : Tm) :
    wn (App a (VarTm i)) ->
    wn a.
Proof.
  set D := VarTm i.
  move E : (App a D) => a0 [v [hr hv]].
  move : hv a E.
  elim : a0 v /hr.
  - hauto inv:Tm ctrs:rtc b:on db: nfne.
  - move => a0 a1 a2 hr0 hr1 ih hnfa2.
    move /(_ hnfa2) in ih.
    move => a.
    case : a0 hr0=>// => b0 b1.
    elim /Par_inv=>//.
    + hauto q:on inv:Par ctrs:rtc b:on.
    + move => ? a0 a3 b2 b3  ? ? [? ?] ? [? ?]. subst.
      have ? : b3 = D by hauto lq:on inv:Par. subst.
      suff : wn (Abs a3) by hauto lq:on ctrs:Par, rtc unfold:wn.
      have : wn (subst_Tm (scons D ids) a3) by sfirstorder.
      have -> : subst_Tm (scons D ids) a3 = ren_Tm (scons i ids) a3.
      subst D. substify. by asimpl.
      move /wn_antirenaming => h.
      by apply : wn_abs.
Qed.

Lemma InterpExt_adequacy i I A PA
  (hI : forall j A,  j < i -> (I j A -> wn A) /\ (wne A -> I j A))
  (h :  InterpExt i I A PA) :
  (forall a, PA a -> wn a) /\ (forall a, ne a -> PA a) /\ wn A.
Proof.
  set D := VarTm 0.
  elim : A PA /h.
  - hauto lq:on use:rtc_refl unfold:wne db:nfne.
  - move => A B PA PF hPA ihPA hTot hRes ihPF.
    have hzero : PA D by firstorder.
    repeat split.
    + rewrite /ProdSpace => b hb.
      move /hTot : (hzero) => [PB]hPB.



Lemma InterpExt_preservation i I A B P (h : ⟦ Ξ ⊨ A ⟧ i ; I ↘ P) :
  (A ⇒ B) ->
  ⟦ Ξ ⊨ B ⟧ i ; I ↘ P.

Definition ρ_ok Γ := forall i ℓ A,
    Lookup i Γ ℓ A ->
    match ℓ with
    | Irrel => True
    | Rel => forall m PA, InterpUnivN .
