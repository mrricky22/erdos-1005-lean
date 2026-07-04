import Mathlib

open scoped BigOperators
open Filter

namespace Erdos1005

/-- A rational `q` is a Farey fraction of order `n` if it lies in `[0,1]` and has
denominator at most `n`. Recall every `q : ℚ` is stored in lowest terms, so `q.den`
is the reduced denominator and `q.num` the reduced numerator. -/
def IsFarey (n : ℕ) (q : ℚ) : Prop := 0 ≤ q ∧ q ≤ 1 ∧ q.den ≤ n

/-- The number of Farey fractions of order `n` strictly between `x` and `y`. -/
noncomputable def betweenCount (n : ℕ) (x y : ℚ) : ℕ :=
  {q : ℚ | IsFarey n q ∧ x < q ∧ q < y}.ncard

/-- Two Farey fractions `x = a/b < y = c/d` are *badly ordered* if `a < c` but `b > d`. -/
def BadlyOrdered (n : ℕ) (x y : ℚ) : Prop :=
  IsFarey n x ∧ IsFarey n y ∧ x < y ∧ x.num < y.num ∧ y.den < x.den

/-- `f(n)` is the minimum number of Farey fractions strictly between the endpoints of a
badly ordered pair in `F_n`. (If no badly ordered pair exists, `sInf ∅ = 0`.) -/
noncomputable def fVal (n : ℕ) : ℕ :=
  sInf {k | ∃ x y, BadlyOrdered n x y ∧ betweenCount n x y = k}

end Erdos1005
