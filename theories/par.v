Require Import Autosubst2.syntax unscoped FunInd.
From stdpp Require Import relations (rtc(..)).

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

Definition Coherent A B := exists C, rtc Par A C /\ rtc Par B C.
