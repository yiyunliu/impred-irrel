Tm(VarTm) : Type
nat : Type
Level : Type

Rel : Level
Irrel : Level

Abs : Level -> (bind Tm in Tm) -> Tm
App : Level -> Tm -> Tm -> Tm
Pi : Level -> Tm -> (bind Tm in Tm) -> Tm
Univ : nat -> Tm
Squash : Tm -> Tm
Box : Tm -> Tm
Let : Tm -> (bind Tm in Tm) -> Tm