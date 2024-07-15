Tm : Type
nat : Type

Abs : (Tm -> Tm) -> Tm
App : Tm -> Tm -> Tm
Pi : Tm -> (Tm -> Tm) -> Tm
Univ : nat -> Tm
Squash : Tm -> Tm
Box : Tm -> Tm
Let : Tm -> (Tm -> Tm) -> Tm