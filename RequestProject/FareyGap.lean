import RequestProject.Statement

open scoped BigOperators

namespace Erdos1005

/-- The **mediant** `(a+c)/(b+d)` of two rationals `x = a/b`, `y = c/d`. -/
noncomputable def mediant (x y : ℚ) : ℚ :=
  ((x.num + y.num : ℤ) : ℚ) / ((x.den + y.den : ℕ) : ℚ)

/-
The mediant is strictly greater than the smaller fraction.
-/
theorem lt_mediant {x y : ℚ} (hxy : x < y) : x < mediant x y := by
  rw [ mediant ];
  rw [ lt_div_iff₀ ( by positivity ) ];
  simp +decide [ mul_add ];
  rw [ ← Rat.mul_den_eq_num ];
  exact mul_lt_mul_of_pos_right hxy ( Nat.cast_pos.mpr y.pos )

/-
The mediant is strictly less than the larger fraction.
-/
theorem mediant_lt {x y : ℚ} (hxy : x < y) : mediant x y < y := by
  unfold mediant;
  rw [ div_lt_iff₀ ] <;> norm_cast <;> norm_num;
  · rw [ ← Rat.mul_den_eq_num, ← Rat.mul_den_eq_num ];
    nlinarith [ show ( x.den : ℚ ) > 0 by exact Nat.cast_pos.mpr x.pos ];
  · exact Or.inl x.pos

/-
The denominator of the mediant is at most the sum of the denominators.
-/
theorem mediant_den_le (x y : ℚ) : (mediant x y).den ≤ x.den + y.den := by
  unfold mediant;
  rw [ div_eq_mul_inv, Rat.mul_den ] ; norm_num;
  norm_cast ; norm_num;
  exact Nat.div_le_self _ _ |> le_trans <| by norm_cast;

/-
The mediant of two nonnegative fractions is nonnegative.
-/
theorem mediant_nonneg {x y : ℚ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ mediant x y := by
  exact div_nonneg ( mod_cast add_nonneg ( Rat.num_nonneg.mpr hx ) ( Rat.num_nonneg.mpr hy ) ) ( Nat.cast_nonneg _ )

/-
The mediant of two fractions `≤ 1` is `≤ 1`.
-/
theorem mediant_le_one {x y : ℚ} (hx : x ≤ 1) (hy : y ≤ 1) : mediant x y ≤ 1 := by
  apply div_le_one_of_le₀;
  · have := Rat.num_div_den x; ( have := Rat.num_div_den y; simp_all +decide [ Rat.le_iff ] );
    norm_cast at *;
    erw [ Rat.num_natCast ] ; norm_num ; linarith;
  · positivity

/-
**Lemma 4.1 (denominator-sum half).** If `x < y` are *consecutive* (Farey-adjacent)
fractions of order `Q` — i.e. no order-`Q` Farey fraction lies strictly between them —
then `x.den + y.den > Q`.

The argument: the mediant of `x` and `y` lies strictly between them, has denominator
`≤ x.den + y.den`, and lies in `[0,1]`; if `x.den + y.den ≤ Q` it would be an order-`Q`
Farey fraction strictly between `x` and `y`, contradicting consecutiveness.
-/
theorem farey_neighbor_den_sum {Q : ℕ} {x y : ℚ}
    (hx : IsFarey Q x) (hy : IsFarey Q y) (hxy : x < y)
    (hgap : ∀ z : ℚ, IsFarey Q z → x < z → z < y → False) :
    Q < x.den + y.den := by
  -- Assume for contradiction that $x.den + y.den \leq Q$.
  by_contra h_contra;
  exact hgap ( mediant x y ) ⟨ mediant_nonneg hx.1 hy.1, mediant_le_one hx.2.1 hy.2.1, mediant_den_le x y |> le_trans <| mod_cast by linarith ⟩ ( lt_mediant hxy ) ( mediant_lt hxy )

/-
**Key determinant inequality.** Any fraction `p/q` (with `q > 0`) strictly between
`x` and `y` has `q · (y.num·x.den - x.num·y.den) ≥ x.den + y.den`.

This is the identity `(p·x.den - q·x.num)·y.den + (q·y.num - p·y.den)·x.den
= q·(y.num·x.den - x.num·y.den)`, with the two integer factors
`p·x.den - q·x.num ≥ 1` and `q·y.num - p·y.den ≥ 1` (both positive since `x < p/q < y`).
-/
theorem between_den_mul_det_ge {x y : ℚ} {p q : ℤ} (hq : 0 < q)
    (h1 : x < (p : ℚ) / q) (h2 : (p : ℚ) / q < y) :
    (x.den + y.den : ℤ) ≤ q * (y.num * x.den - x.num * y.den) := by
  -- From h1 : x < p/q, i.e. (a:ℚ)/b < (p:ℚ)/q: since b > 0, q > 0, cross-multiply (div_lt_div_iff) to get a*q < p*b, hence the integer u := p*b - q*a ≥ 1 (it is a positive integer).
  have hw1_ineq1 : (x.num : ℤ) * q < p * x.den := by
    rw [ Rat.lt_iff ] at h1;
    simp_all +decide [ div_eq_mul_inv, Rat.mul_den, Rat.mul_num ];
    simp_all +decide [ Int.sign_eq_one_of_pos hq, abs_of_pos hq, ne_of_gt hq ];
    convert mul_lt_mul_of_pos_right h1 ( show 0 < ( p.natAbs.gcd q.natAbs : ℤ ) from mod_cast Nat.gcd_pos_of_pos_right _ ( Int.natAbs_pos.mpr hq.ne' ) ) using 1 <;> ring;
    · rw [ mul_assoc, Int.ediv_mul_cancel ( Int.dvd_trans ( Int.natCast_dvd_natCast.mpr ( Nat.gcd_dvd_right _ _ ) ) ( by norm_num ) ) ];
    · rw [ mul_assoc, Int.ediv_mul_cancel ( Int.dvd_trans ( Int.natCast_dvd_natCast.mpr ( Nat.gcd_dvd_left _ _ ) ) ( by norm_num ) ) ] ; ring;
  -- From h2 : p/q < y, i.e. (p:ℚ)/q < (c:ℚ)/d: cross-multiply to get p*d < c*q, hence v := q*c - p*d ≥ 1.
  have hw1_ineq2 : (p : ℤ) * y.den < y.num * q := by
    rw [ div_lt_iff₀ ] at h2 <;> norm_cast at *;
    rw [ ← @Int.cast_lt ℚ ] ; simp_all +decide [ mul_comm ];
    convert mul_lt_mul_of_pos_right h2 ( Nat.cast_pos.mpr y.pos ) using 1 ; ring;
    simp +decide [ mul_assoc ];
  nlinarith [ show ( x.den : ℤ ) > 0 from mod_cast x.pos, show ( y.den : ℤ ) > 0 from mod_cast y.pos ]

/-
**Lemma 4.1 (determinant half).** If `x < y` are *consecutive* (Farey-adjacent) fractions
of order `Q` — i.e. no order-`Q` Farey fraction lies strictly between them — then the
determinant `x.den · y.num - x.num · y.den = 1`.

Constructive proof of `D ≤ 1` (where `D = s·h' - h·s'`, `s=x.den,h=x.num,s'=y.den,h'=y.num`):
suppose `D ≥ 2`.  Since `gcd(h,s)=1`, pick `p₀,q₀` with `s·p₀ - h·q₀ = 1`.  Adjusting
`(p,q) = (p₀+h·t, q₀+s·t)` keeps `s·p - h·q = 1` and shifts `A := h'·q - s'·p` by `t·D`,
so choose `t` with `0 ≤ A < D`.  Then `q = (s·A + s')/D ≥ 1`, `p = (h·A + h')/D`, and
`q ≤ max(s,s') ≤ Q`.  The fraction `z = p/q` satisfies `z - x = 1/(q·s) > 0` and
`y - z = A/(s'·q)`; here `A ≥ 1` because `A = 0` would force `D ∣ s'` and `D ∣ h'`, i.e.
`D ∣ gcd(s',h') = 1`.  Hence `x < z < y`, `z ∈ [0,1]`, and `z.den ≤ q ≤ Q`, so `z ∈ F_Q`
lies strictly between `x` and `y`, contradicting consecutiveness.
-/
theorem farey_neighbor_det {Q : ℕ} {x y : ℚ}
    (hx : IsFarey Q x) (hy : IsFarey Q y) (hxy : x < y)
    (hgap : ∀ z : ℚ, IsFarey Q z → x < z → z < y → False) :
    (x.den : ℤ) * y.num - x.num * (y.den : ℤ) = 1 := by
  contrapose! hgap;
  -- Let $D = x.den \cdot y.num - x.num \cdot y.den$. Since $D \geq 2$, we can find integers $p$ and $q$ such that $s \cdot p - h \cdot q = 1$ and $0 \leq A < D$.
  obtain ⟨p, q, hpq⟩ : ∃ p q : ℤ, (x.den : ℤ) * p - x.num * q = 1 ∧ 0 ≤ y.num * q - y.den * p ∧ y.num * q - y.den * p < x.den * y.num - x.num * y.den := by
    obtain ⟨p, q, hpq⟩ : ∃ p q : ℤ, (x.den : ℤ) * p - x.num * q = 1 := by
      have := Int.gcd_eq_gcd_ab x.den x.num;
      exact ⟨ Int.gcdA x.den x.num, -Int.gcdB x.den x.num, by linarith [ show Int.gcd x.den x.num = 1 from x.reduced.symm ] ⟩;
    -- Choose $t$ such that $0 \leq A < D$.
    obtain ⟨t, ht⟩ : ∃ t : ℤ, 0 ≤ y.num * (q + t * x.den) - y.den * (p + t * x.num) ∧ y.num * (q + t * x.den) - y.den * (p + t * x.num) < x.den * y.num - x.num * y.den := by
      have h_det_pos : 0 < x.den * y.num - x.num * y.den := by
        rw [ Rat.lt_iff ] at hxy;
        grind +splitIndPred;
      exact ⟨ - ( ( y.num * q - y.den * p ) / ( x.den * y.num - x.num * y.den ) ), by linarith [ Int.mul_ediv_add_emod ( y.num * q - y.den * p ) ( x.den * y.num - x.num * y.den ), Int.emod_nonneg ( y.num * q - y.den * p ) h_det_pos.ne' ], by linarith [ Int.mul_ediv_add_emod ( y.num * q - y.den * p ) ( x.den * y.num - x.num * y.den ), Int.emod_lt_of_pos ( y.num * q - y.den * p ) h_det_pos ] ⟩;
    exact ⟨ p + t * x.num, q + t * x.den, by linear_combination hpq, by linarith, by linarith ⟩;
  refine' ⟨ p / q, _, _, _, trivial ⟩;
  · refine' ⟨ _, _, _ ⟩;
    · refine' div_nonneg _ _ <;> norm_cast;
      · nlinarith [ hx.1, hx.2.1, hy.1, hy.2.1, Rat.num_nonneg.mpr hx.1, Rat.num_nonneg.mpr hy.1, Rat.den_pos x, Rat.den_pos y ];
      · nlinarith [ hx.1, hx.2.1, hy.1, hy.2.1, x.num_nonneg.mpr hx.1, y.num_nonneg.mpr hy.1 ];
    · rw [ div_le_iff₀ ] <;> norm_cast;
      · nlinarith [ show x.num ≤ x.den from by { have := hx.1; have := hx.2.1; rw [ Rat.le_iff ] at *; norm_num at *; linarith }, show y.num ≤ y.den from by { have := hy.1; have := hy.2.1; rw [ Rat.le_iff ] at *; norm_num at *; linarith } ];
      · nlinarith [ hx.1, hx.2, hy.1, hy.2, show ( x.den : ℤ ) > 0 from Nat.cast_pos.mpr x.pos, show ( y.den : ℤ ) > 0 from Nat.cast_pos.mpr y.pos ];
    · -- Since $q \leq Q$, we have $(p / q).den \leq Q$.
      have hq_le_Q : q.natAbs ≤ Q := by
        cases abs_cases q <;> cases max_cases x.den y.den <;> nlinarith [ hx.2.1, hy.2.1, hx.2.2, hy.2.2, show ( x.num : ℤ ) * y.den < x.den * y.num from by rw [ ← @Int.cast_lt ℚ ] ; push_cast; rw [ ← Rat.num_div_den x, ← Rat.num_div_den y ] at hxy; rw [ div_lt_div_iff₀ ] at hxy <;> norm_cast at * <;> linarith [ x.pos, y.pos ] ];
      rw [ div_eq_mul_inv ];
      rw [ Rat.mul_den ] ; norm_num;
      split_ifs <;> simp_all +decide [ Int.natAbs_mul, Int.natAbs_sign ];
      · linarith [ hx.2.2, hy.2.2, x.pos, y.pos ];
      · exact le_trans ( Nat.div_le_self _ _ ) hq_le_Q;
  · rw [ Rat.lt_iff ] at *;
    rw [ Rat.num_div_eq_of_coprime, Rat.den_div_eq_of_coprime ];
    · linarith;
    · nlinarith [ x.pos, y.pos ];
    · exact Int.isCoprime_iff_nat_coprime.mp ( by exact ⟨ x.den, -x.num, by linarith ⟩ );
    · nlinarith [ x.pos, y.pos ];
    · exact Int.isCoprime_iff_nat_coprime.mp ( by exact ⟨ x.den, -x.num, by linarith ⟩ );
  · rw [ div_lt_iff₀ ];
    · rw [ ← Rat.num_div_den y ];
      rw [ div_mul_eq_mul_div, lt_div_iff₀ ] <;> norm_cast;
      · by_cases h_eq : y.num * q - y.den * p = 0;
        · have h_contra : x.den * y.num - x.num * y.den ∣ y.den := by
            exact ⟨ q, by nlinarith ⟩;
          have h_contra : x.den * y.num - x.num * y.den ∣ 1 := by
            have h_contra : Int.gcd (x.den * y.num - x.num * y.den) y.den = 1 := by
              have h_coprime : Int.gcd (x.num : ℤ) x.den = 1 ∧ Int.gcd (y.num : ℤ) y.den = 1 := by
                exact ⟨ x.reduced, y.reduced ⟩;
              simp_all +decide [ Int.gcd_eq_natAbs, Int.natAbs_mul ];
              refine' Nat.Coprime.symm <| Nat.coprime_of_dvd' _;
              intro k hk hk₁ hk₂; have := Nat.dvd_gcd ( show k ∣ y.num.natAbs from ?_ ) hk₁; simp_all +decide [ Nat.Coprime, Nat.Coprime.gcd_eq_one ] ;
              rw [ ← Int.natCast_dvd ] at *;
              haveI := Fact.mk hk; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ;
              replace hpq := congr_arg ( ( ↑ ) : ℤ → ZMod k ) hpq.1 ; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ] ;
              replace h_eq := congr_arg ( ( ↑ ) : ℤ → ZMod k ) h_eq ; simp_all +decide ;
              grind;
            exact Int.dvd_coe_gcd ( dvd_refl _ ) ‹_› |> fun h => h.trans ( by simp +decide [ h_contra ] );
          exact False.elim <| hgap <| by linarith [ Int.le_of_dvd ( by linarith ) h_contra ] ;
        · grind;
      · exact y.pos;
    · norm_num +zetaDelta at *;
      nlinarith [ hx.1, hx.2.1, hy.1, hy.2.1, Rat.num_nonneg.mpr hx.1, Rat.num_nonneg.mpr hy.1, Rat.den_pos x, Rat.den_pos y ]

/-
**Farey gap containing an interval.** If no order-`Q` Farey fraction lies strictly inside
`(x, w)` (with `0 ≤ x < w ≤ 1`, `Q ≥ 1`), then there are consecutive order-`Q` Farey fractions
`gL ≤ x < w ≤ gR` (a gap of `F_Q` containing `(x, w)`).
-/
theorem farey_gap_between (Q : ℕ) (hQ : 1 ≤ Q) (x w : ℚ) (hx0 : 0 ≤ x) (hw1 : w ≤ 1)
    (hxw : x < w) (hno : ∀ f : ℚ, IsFarey Q f → x < f → f < w → False) :
    ∃ gL gR : ℚ, IsFarey Q gL ∧ IsFarey Q gR ∧ gL ≤ x ∧ w ≤ gR ∧ gL < gR ∧
      (∀ f : ℚ, IsFarey Q f → gL < f → f < gR → False) := by
  -- The set `F := {f : ℚ | IsFarey Q f}` is finite (`farey_finite Q`).
  have h_finite : Set.Finite {f : ℚ | IsFarey Q f} := by
    refine Set.Finite.subset ( Set.toFinite ( Finset.image ( fun p : ℤ × ℕ => ( p.1 : ℚ ) / p.2 ) ( Finset.Icc ( -Q : ℤ ) Q ×ˢ Finset.Icc 1 Q ) ) ) ?_;
    intro f hf; obtain ⟨ hf₀, hf₁, hf₂ ⟩ := hf; simp_all +decide [ IsFarey ] ;
    use f.num, f.den;
    exact ⟨ ⟨ ⟨ by linarith [ show ( f.num : ℤ ) ≥ 0 by exact_mod_cast Rat.num_nonneg.mpr hf₀ ], by linarith [ f.pos ] ⟩, by linarith [ show ( f.num : ℤ ) ≤ Q by exact_mod_cast ( by nlinarith [ show ( f.num : ℚ ) ≤ f.den by exact_mod_cast ( by nlinarith [ Rat.num_div_den f, mul_div_cancel₀ ( f.num : ℚ ) ( Nat.cast_ne_zero.mpr f.pos.ne' ) ] : ( f.num : ℚ ) ≤ f.den ), ( by norm_cast : ( f.den : ℚ ) ≤ Q ) ] : ( f.num : ℚ ) ≤ Q ) ], hf₂ ⟩, f.num_div_den ⟩;
  -- Let `gL := SL.max'` (greatest element `≤ x`) and `gR := SR.min'` (least element `≥ w`).
  obtain ⟨gL, hgL⟩ : ∃ gL : ℚ, gL ∈ {f : ℚ | IsFarey Q f} ∧ gL ≤ x ∧ ∀ f ∈ {f : ℚ | IsFarey Q f}, f ≤ x → f ≤ gL := by
    obtain ⟨gL, hgL⟩ : ∃ gL ∈ {f : ℚ | IsFarey Q f} ∩ Set.Iic x, ∀ f ∈ {f : ℚ | IsFarey Q f} ∩ Set.Iic x, f ≤ gL := by
      apply_rules [ Set.exists_max_image ];
      · exact h_finite.inter_of_left _;
      · exact ⟨ 0, ⟨ ⟨ by norm_num, by norm_num, by norm_num; linarith ⟩, hx0 ⟩ ⟩;
    exact ⟨ gL, hgL.1.1, hgL.1.2, fun f hf hf' => hgL.2 f ⟨ hf, hf' ⟩ ⟩
  obtain ⟨gR, hgR⟩ : ∃ gR : ℚ, gR ∈ {f : ℚ | IsFarey Q f} ∧ w ≤ gR ∧ ∀ f ∈ {f : ℚ | IsFarey Q f}, w ≤ f → gR ≤ f := by
    obtain ⟨gR, hgR⟩ : ∃ gR : ℚ, gR ∈ {f : ℚ | IsFarey Q f} ∧ w ≤ gR := by
      exact ⟨ 1, ⟨ by norm_num, by norm_num, by norm_num; linarith ⟩, hw1 ⟩;
    exact ⟨ Finset.min' ( h_finite.toFinset.filter fun f => w ≤ f ) ⟨ gR, by aesop ⟩, by simpa using Finset.min'_mem ( h_finite.toFinset.filter fun f => w ≤ f ) ⟨ gR, by aesop ⟩, by simp, fun f hf hf' => Finset.min'_le _ _ <| by aesop ⟩;
  grind

end Erdos1005