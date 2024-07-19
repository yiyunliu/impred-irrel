Require Import Autosubst2.syntax unscoped par.
Require Import ssreflect ssrbool.
From Hammer Require Import Tactics.

Definition Basis := list (Level * Tm).

Fixpoint lookup n (Γ : Basis) :=
  match n, Γ with
  | O, (cons (ℓ, A)  _) => Some (ℓ, ren_Tm S A)
  | S n, (cons _ Γ) => match lookup n Γ with
                       | None => None
                       | Some (ℓ, A) => Some (ℓ, ren_Tm S A)
                       end
  | _ , _ => None
  end.

Inductive Lookup : nat -> Basis -> Level -> Tm -> Prop :=
| Here ℓ A Γ : Lookup 0 ((ℓ, A) :: Γ)%list ℓ (ren_Tm S A)
| There n Γ ℓ A ℓA : Lookup n Γ ℓ A ->
                     Lookup (S n) (cons ℓA Γ) ℓ (ren_Tm S A).

Lemma LookupIff n Γ ℓ A : Lookup n Γ ℓ A <-> lookup n Γ = Some (ℓ , A).
Proof.
  split.
  - elim; hauto lq:on.
  - elim : n Γ ℓ A; hauto q:on inv:list ctrs:Lookup.
Qed.

Fixpoint resurrect (Γ : Basis) :=
  match Γ with
  | nil => nil
  | cons (ℓ, A) Γ => cons (Rel, A) (resurrect Γ)
  end.

Definition cresurrect ℓ (Γ : Basis) :=
  match ℓ with
  | Rel => Γ
  | _ => resurrect Γ
  end.

Definition cmax ℓ i j :=
  match ℓ with
  | Rel => j
  | _ => max i j
  end.

Reserved Notation "Γ ⊢ a ∈ A" (at level 70, no associativity).
Reserved Notation "⊢ Γ" (at level 70, no associativity).
Inductive WellTyped : Basis -> Tm -> Tm -> Prop :=
| T_Var Γ i A :
  ⊢ Γ ->
  Lookup i Γ Rel A ->
  (* -------------- *)
  Γ ⊢ VarTm i ∈ A

| T_Univ Γ i :
  ⊢ Γ ->
  (* ------------- *)
  Γ ⊢ Univ i ∈ Univ (S i)

| T_Pi Γ i j A B :
  Γ ⊢ A ∈ Univ i ->
  cons (Rel, A) Γ ⊢ B ∈ Univ j ->
  (* --------------------- *)
  Γ ⊢ Pi A B ∈ Univ (max i j)

| T_Abs Γ i A B b :
  Γ ⊢ Pi A B ∈ Univ i ->
  cons (Rel, A) Γ ⊢ b ∈ B ->
  (* --------------------- *)
  Γ ⊢ Abs b ∈ Pi A B

| T_App Γ b a A B :
  Γ ⊢ b ∈ Pi A B ->
  (* cresurrect ℓ *)
  Γ ⊢ a ∈ A ->
  (* -------------------- *)
  Γ ⊢ App b a ∈ subst_Tm (scons a ids) B

| T_Squash Γ A i j :
  Γ ⊢ A ∈ Univ i ->
  (* ----------- *)
  Γ ⊢ Squash A ∈ Univ j

| T_Box Γ a A i :
  Γ ⊢ A ∈ Univ i ->
  resurrect Γ ⊢ a ∈ A ->
  (* ----------- *)
  Γ ⊢ Box a ∈ Squash A

| T_Let Γ a A b B i :
  Γ ⊢ a ∈ Squash A ->
  cons (Irrel, A) Γ ⊢ b ∈ subst_Tm (scons (Box (VarTm 0)) ids) B ->
  cons (Rel, Squash A) Γ ⊢ B ∈ Univ i ->
  (* ------------------------- *)
  Γ ⊢ Let a b ∈ subst_Tm (scons a ids) B

| T_Empty Γ i :
  ⊢ Γ ->
  (* --------- *)
  Γ ⊢ Empty ∈ Univ i

| T_Absurd Γ a A i :
  resurrect Γ ⊢ a ∈ Empty ->
  Γ ⊢ A ∈ Univ i ->
  (* --------- *)
  Γ ⊢ Absurd a ∈ A

| T_Conv Γ a A B i :
  Γ ⊢ a ∈ A ->
  Γ ⊢ B ∈ Univ i ->
  Coherent A B ->
  (* ----------- *)
  Γ ⊢ a ∈ B

with WellFormed : Basis -> Prop :=
| W_Nil :
(* ----------------- *)
  ⊢ nil
| W_Cons Γ ℓ0 A i :
  ⊢ Γ ->
  Γ ⊢ A ∈ Univ i ->
(* ----------------- *)
  ⊢ cons (ℓ0, A) Γ
where "Γ ⊢ a ∈ A" := (WellTyped Γ a A)
and "⊢ Γ" := (WellFormed Γ).
