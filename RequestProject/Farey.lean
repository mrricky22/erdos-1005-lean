import RequestProject.Statement

open scoped BigOperators

namespace Erdos1005

/-
The set of order-`n` Farey fractions is finite.
-/
theorem farey_finite (n : ℕ) : {q : ℚ | IsFarey n q}.Finite := by
  refine' Set.Finite.subset ( Set.toFinite ( Set.image ( fun p : ℤ × ℕ => ( p.1 : ℚ ) / p.2 ) ( Set.Icc ( -n : ℤ ) n ×ˢ Set.Icc ( 1 : ℕ ) n ) ) ) fun q hq => _;
  use (q.num, q.den);
  simp_all +decide [ IsFarey ];
  exact ⟨ ⟨ ⟨ by linarith [ q.num_nonneg.mpr hq.1 ], q.pos ⟩, by linarith [ show q.num ≤ q.den from by simpa [ Rat.le_iff ] using hq.2.1 ] ⟩, q.num_div_den ⟩

/-- The set of order-`n` Farey fractions strictly between `x` and `y` is finite. -/
theorem fareyBetween_finite (n : ℕ) (x y : ℚ) :
    {q : ℚ | IsFarey n q ∧ x < q ∧ q < y}.Finite := by
  apply (farey_finite n).subset
  intro q hq; exact hq.1

/-- `betweenCount` is monotone in the right endpoint: shrinking `y` cannot increase the count. -/
theorem betweenCount_mono_right (n : ℕ) (x : ℚ) {y y' : ℚ} (h : y' ≤ y) :
    betweenCount n x y' ≤ betweenCount n x y := by
  apply Set.ncard_le_ncard _ (fareyBetween_finite n x y)
  intro q hq
  exact ⟨hq.1, hq.2.1, lt_of_lt_of_le hq.2.2 h⟩

/-- The right endpoint of the elementary interval `I_{a,b} = (a/b, (a+1)/(b-1))`,
where `a = x.num`, `b = x.den`. -/
noncomputable def elemR (x : ℚ) : ℚ :=
  ((x.num + 1 : ℤ) : ℚ) / (((x.den : ℤ) - 1 : ℤ) : ℚ)

/-
**Section 1, key inequality.** For a badly ordered pair `x = a/b < y = c/d`
(with `a < c`, `d < b`, both reduced in `[0,1]`), the elementary right endpoint
`(a+1)/(b-1)` is `≤ y`.
-/
theorem elemR_le {n : ℕ} {x y : ℚ} (h : BadlyOrdered n x y) : elemR x ≤ y := by
  obtain ⟨ hx₁, hx₂, hx₃, hx₄, hx₅ ⟩ := h;
  rw [ elemR, div_le_iff₀ ];
  · rw [ ← Rat.num_div_den y ];
    rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> norm_cast;
    · rw [ Int.subNatNat_eq_coe ] ; push_cast ; nlinarith [ show x.num ≥ 0 from Rat.num_nonneg.mpr hx₁.1, show y.num ≤ y.den from by simpa [ Rat.le_iff ] using hx₂.2.1 ];
    · exact y.pos;
  · simp +zetaDelta at *;
    linarith [ y.pos ]

/-- **Section 1 reduction.** Every badly ordered pair contains the elementary interval
`I_{a,b}`, so its Farey count is at least that of the elementary interval. -/
theorem betweenCount_ge_elementary {n : ℕ} {x y : ℚ} (h : BadlyOrdered n x y) :
    betweenCount n x (elemR x) ≤ betweenCount n x y :=
  betweenCount_mono_right n x (elemR_le h)

end Erdos1005