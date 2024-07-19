Tm(VarTm) : Type
nat : Type

Abs : (bind Tm in Tm) -> Tm
App : Tm -> Tm -> Tm
Pi : Tm -> (bind Tm in Tm) -> Tm
Univ : nat -> Tm
Squash : Tm -> Tm
Box : Tm -> Tm
Let : Tm -> (bind Tm in Tm) -> Tm
Empty : Tm
Absurd : Tm -> Tm