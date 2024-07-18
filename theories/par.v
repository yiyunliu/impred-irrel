Require Import Autosubst2.syntax unscoped.
From stdpp Require Import relations.

Reserved Infix "⇒" (at level 60, right associativity).

Inductive Par : Tm -> Tm -> Prop :=
| P_Var i :
  (* ------- *)
  VarTm i ⇒ VarTm i
| P_Univ n :
  (* -------- *)
  Univ n ⇒ Univ n
| P_Pi ℓ A0 A1 B0 B1 :
  A0 ⇒ A1 ->
  B0 ⇒ B1 ->
  (* --------------------- *)
  Pi ℓ A0 B0 ⇒ Pi ℓ A1 B1
| P_Abs ℓ a0 a1 :
  a0 ⇒ a1 ->
  (* -------------------- *)
  Abs ℓ a0 ⇒ Abs ℓ a1
| P_App ℓ a0 a1 b0 b1 :
  a0 ⇒ a1 ->
  b0 ⇒ b1 ->
  (* ------------------------- *)
  App ℓ a0 b0 ⇒ App ℓ a1 b1
| P_AppAbs ℓ a a0 b0 b1 :
  a ⇒ a0 ->
  b0 ⇒ b1 ->
  (* ---------------------------- *)
  App ℓ (Abs ℓ a) b0 ⇒ subst_Tm (scons b1 ids) a0
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
where "A ⇒ B" := (Par A B).

Definition Coherent A B := exists C, rtc Par A C /\ rtc Par B C.
