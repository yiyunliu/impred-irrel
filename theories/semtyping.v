Require Import Autosubst2.syntax unscoped par typing.
Require Import ssreflect.
From Hammer Require Import Tactics.

Definition ProdSpace (PA : Tm -> Prop) (PF : Tm -> (Tm -> Prop) -> Prop) (b : Tm) :=
  forall a PB, PA a -> PF a PB -> PB (App b a).

Definition ProdSpaceS (PA : Tm -> Prop) (PF : Tm -> Prop -> Prop) :=
  forall a P, PA a -> PF a P -> P.

(* Candidate : (Ty -> Prop) -> Prop *)

(* P in Candidate iff *)

(* let Box x = a in b *)

(* InterpExists A : exists i S, Interp i A S /\ exists a, S a. *)


(* How does I affect the inhabitance? *)
Inductive InterpExt i I : Tm -> (Tm -> Prop) -> Prop :=
| InterpExt_Fun A B PA PF :
  InterpExt i I A PA ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a PB, PA a -> PF a PB -> InterpExt i I (subst_Tm (scons a ids) B) PB) ->
  InterpExt i I (Pi A B) (ProdSpace PA PF)

(* TODO *)
(* Try using candidates to capture the definition of InterpExtSquashed? *)
| InterpExt_Squash j A  P :
  (* Latest thoughts: *)
  (* What if we don't pass in I but something else that's more generic? *)
  (* What can we say in terms of inhabitance? *)
  InterpExt j I A P ->
  (* -------------------- *)
  InterpExt i I (Squash A) P

| InterpExt_Univ j :
  j < i ->
  InterpExt i I (Univ j) (fun A => I j A)

| InterpExt_Step A A0 PA :
  A ⇒ A0 ->
  InterpExt i I A0 PA ->
  InterpExt i I A PA.

Lemma InterpExt_same_inhab i I0 I1 A S0 S1 :
  InterpExt i I0 A S0 ->
  InterpExt i I1 A S1 ->
  ((exists a, S0 a) <-> (exists a, S1 a)).
Proof.
  move => h. move : I1 S1.
  elim : i I0 A S0 / h.
  - move => i I0 A B PA PF hPA ihPA hTot hRes ihPF I1 S1.
    admit.
  - admit.
  - admit.
  -
(* Idea: the contravariance of function arguments might matter less if
the entire thing is a proposition (we only care about whether the
output is inhabited). In other words,   *)
with InterpExtSquashed I : Tm -> Prop -> Prop :=
| InterpExtS_Fun i A B PA (PF : Tm -> Prop -> Prop) :
  InterpExt i I A PA ->
  (forall a, PA a -> exists PB, PF a PB) ->
  (forall a PB, PA a -> PF a PB -> InterpExtSquashed I (subst_Tm (scons a ids) B) PB) ->
  InterpExtSquashed I (Pi A B) (ProdSpaceS PA PF)

| InterpExtS_Univ j :
  InterpExtSquashed I (Univ j) True

| InterpExtS_Squash A P :
  InterpExtSquashed I A P ->
  InterpExtSquashed I (Squash A) P

| InterpExtS_Step A A0 PA :
  A ⇒ A0 ->
  InterpExtSquashed I A0 PA ->
  InterpExtSquashed I A PA.



(* Define another InterpExtProp function that treats the codomains as squashed? *)
(* InterpExtProp: defined in terms of InterpExt *)
(* InterpExt: characterizes InterpExtProp with axioms *)
