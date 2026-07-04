import RequestProject.PrimProg
import RequestProject.LowerCore
import RequestProject.TotientSum
import RequestProject.Farey

open scoped BigOperators
open Finset ArithmeticFunction

namespace Erdos1005

/-
**Per-denominator coprime count.** For `q ≥ 1` and reals `A ≤ B`, the number of integers
`p ∈ (A,B)` coprime to `q` is at least `(B-A)·φ(q)/q - τ(q)`.
-/
theorem coprime_count_lower (q : ℕ) (hq : 1 ≤ q) (A B : ℝ) (hAB : A ≤ B) :
    (B - A) * (Nat.totient q : ℝ) / q - (q.divisors.card : ℝ)
      ≤ ({p : ℤ | A < (p : ℝ) ∧ (p : ℝ) < B ∧ IsCoprime p (q : ℤ)}.ncard : ℝ) := by
  have h_residue_interval_count : ∀ d ∈ q.divisors, |((Set.ncard {p : ℤ | A < (p : ℝ) ∧ (p : ℝ) < B ∧ (d : ℤ) ∣ p}) - (B - A) / d : ℝ)| ≤ 1 := by
    intro d hd; have := @residue_interval_count d ( Nat.pos_of_mem_divisors hd ) 0 A B hAB; aesop;
  have h_coprime_count : (Set.ncard {p : ℤ | A < (p : ℝ) ∧ (p : ℝ) < B ∧ IsCoprime p q}) = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * (Set.ncard {p : ℤ | A < (p : ℝ) ∧ (p : ℝ) < B ∧ (d : ℤ) ∣ p}) := by
    have h_coprime_count : ∀ p : ℤ, (if A < (p : ℝ) ∧ (p : ℝ) < B ∧ IsCoprime p q then 1 else 0) = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * (if A < (p : ℝ) ∧ (p : ℝ) < B ∧ (d : ℤ) ∣ p then 1 else 0) := by
      intro p
      by_cases hp : A < (p : ℝ) ∧ (p : ℝ) < B;
      · have h_coprime_indicator : (if IsCoprime p q then 1 else 0 : ℝ) = ∑ d ∈ Nat.divisors (Int.gcd p q), (ArithmeticFunction.moebius d : ℝ) := by
          have h_coprime_indicator : ∑ d ∈ Nat.divisors (Int.gcd p q), (ArithmeticFunction.moebius d : ℝ) = if Int.gcd p q = 1 then 1 else 0 := by
            have h_coprime_indicator : ∑ d ∈ Nat.divisors (Int.gcd p q), (ArithmeticFunction.moebius d : ℝ) = (ArithmeticFunction.moebius * ArithmeticFunction.zeta) (Int.gcd p q) := by
              simp +decide [ zeta ];
              rw [ Nat.sum_divisorsAntidiagonal fun x y => if y = 0 then 0 else ( moebius x : ℝ ) ];
              exact Finset.sum_congr rfl fun x hx => by rw [ if_neg ( Nat.ne_of_gt ( Nat.div_pos ( Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by aesop ) ) ( Nat.dvd_of_mem_divisors hx ) ) ( Nat.pos_of_mem_divisors hx ) ) ) ] ;
            aesop;
          simp_all +decide [ Int.isCoprime_iff_gcd_eq_one ];
        simp_all +decide [ Finset.sum_ite ];
        refine' Finset.sum_bij ( fun x hx => x ) _ _ _ _ <;> simp_all +decide [ Int.gcd_eq_natAbs ];
        · exact fun a ha₁ ha₂ => ⟨ ⟨ Nat.dvd_trans ha₁ ( Nat.gcd_dvd_right _ _ ), by linarith ⟩, Int.natCast_dvd.mpr ( Nat.dvd_trans ha₁ ( Nat.gcd_dvd_left _ _ ) ) ⟩;
        · exact fun b hb₁ hb₂ hb₃ => Nat.dvd_gcd ( Int.natAbs_dvd_natAbs.mpr hb₃ ) hb₁;
      · rw [ Finset.sum_eq_zero ] <;> aesop;
    have h_coprime_count : ∑ p ∈ Finset.Icc (Int.floor A) (Int.ceil B), (if A < (p : ℝ) ∧ (p : ℝ) < B ∧ IsCoprime p q then 1 else 0) = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * ∑ p ∈ Finset.Icc (Int.floor A) (Int.ceil B), (if A < (p : ℝ) ∧ (p : ℝ) < B ∧ (d : ℤ) ∣ p then 1 else 0) := by
      rw [ Finset.sum_congr rfl fun p hp => h_coprime_count p, Finset.sum_comm, Finset.sum_congr rfl fun d hd => Finset.mul_sum _ _ _ ];
    convert h_coprime_count using 1;
    · simp +zetaDelta at *;
      rw [ ← Set.ncard_coe_finset ] ; congr ; ext ; simp +decide [ Int.floor_le, Int.le_ceil ] ;
      exact fun _ _ _ => ⟨ Int.le_of_lt_add_one <| Int.floor_lt.2 <| by norm_num; linarith, Int.le_of_lt_add_one <| by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ Int.le_ceil B ] ⟩;
    · refine' Finset.sum_congr rfl fun d hd => _;
      simp +zetaDelta at *;
      rw [ ← Set.ncard_coe_finset ] ; norm_num;
      exact Or.inl ( congr_arg _ ( by ext; exact ⟨ fun h => ⟨ ⟨ Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ h.1, Int.floor_le A ] ), Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ h.2.1, Int.le_ceil B ] ) ⟩, h ⟩, fun h => h.2 ⟩ ) );
  -- Applying the bound from `h_residue_interval_count` to each term in the sum.
  have h_sum_bound : |(∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * (Set.ncard {p : ℤ | A < (p : ℝ) ∧ (p : ℝ) < B ∧ (d : ℤ) ∣ p})) - (∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * ((B - A) / d))| ≤ ∑ d ∈ q.divisors, |(ArithmeticFunction.moebius d : ℝ)| := by
    rw [ ← Finset.sum_sub_distrib ];
    exact le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun x hx => by rw [ ← mul_sub ] ; exact abs_mul ( _ : ℝ ) _ ▸ mul_le_of_le_one_right ( abs_nonneg _ ) ( h_residue_interval_count x hx ) );
  -- Applying the bound from `h_sum_bound` to the sum.
  have h_sum_bound_simplified : |(∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * (Set.ncard {p : ℤ | A < (p : ℝ) ∧ (p : ℝ) < B ∧ (d : ℤ) ∣ p})) - ((B - A) * (Nat.totient q : ℝ) / q)| ≤ (q.divisors.card : ℝ) := by
    have h_sum_bound_simplified : ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * ((B - A) / d) = (B - A) * (Nat.totient q : ℝ) / q := by
      convert congr_arg ( fun x : ℝ => ( B - A ) * x ) ( moebius_div_sum_eq_totient_div q hq ) using 1 <;> ring;
      simp +decide only [mul_assoc, mul_left_comm, sum_sub_distrib, Finset.mul_sum _ _ _];
    exact h_sum_bound_simplified ▸ h_sum_bound.trans ( le_trans ( Finset.sum_le_sum fun _ _ => show |_| ≤ 1 by exact mod_cast by { unfold ArithmeticFunction.moebius; aesop } ) ( by norm_num ) );
  linarith [ abs_le.mp h_sum_bound_simplified ]

/-
**Density bridge.** The number of order-`n` Farey fractions in `(x, y)` (for `0 <= x < y <= 1`)
is at least the sum over denominators `q` in `[1,n]` of the per-`q` coprime counts.
-/
set_option maxHeartbeats 1000000 in
theorem density_bridge (n : ℕ) (x y : ℚ) (hx : 0 ≤ x) (hy : y ≤ 1) (hxy : x < y) :
    (∑ q ∈ Finset.Icc 1 n,
        ({p : ℤ | (x : ℝ) * q < (p : ℝ) ∧ (p : ℝ) < (y : ℝ) * q ∧ IsCoprime p (q : ℤ)}.ncard : ℝ))
      ≤ (betweenCount n x y : ℝ) := by
  rw_mod_cast [ Erdos1005.betweenCount ];
  have h_biUnion : ∀ q ∈ Finset.Icc 1 n, ({p : ℤ | (x : ℝ) * q < p ∧ p < (y : ℝ) * q ∧ IsCoprime p q} : Set ℤ).ncard ≤ ({r : ℚ | r.den = q ∧ IsFarey n r ∧ x < r ∧ r < y} : Set ℚ).ncard := by
    intro q hq
    have h_image : Set.image (fun p : ℤ => (p : ℚ) / q) {p : ℤ | (x : ℝ) * q < p ∧ p < (y : ℝ) * q ∧ IsCoprime p q} ⊆ {r : ℚ | r.den = q ∧ IsFarey n r ∧ x < r ∧ r < y} := by
      intro r hr; obtain ⟨ p, hp, rfl ⟩ := hr; simp_all +decide [ IsFarey ] ;
      have h_den : (p / q : ℚ).den = q := by
        rw [ div_eq_mul_inv, Rat.mul_den ] ; norm_num [ hp.2.2 ];
        simp_all +decide [ Int.sign_eq_one_of_pos ( by norm_cast; linarith : 0 < ( q : ℤ ) ) ];
        split_ifs <;> simp_all +decide [ Int.isCoprime_iff_gcd_eq_one ];
        simp_all +decide [ Int.gcd, Int.natAbs_neg ];
      simp_all +decide [ le_div_iff₀, div_le_iff₀, show q > 0 by linarith ];
      norm_cast at *;
      exact ⟨ ⟨ by exact_mod_cast ( by nlinarith [ ( by norm_cast; linarith : ( 1 : ℚ ) ≤ q ) ] : ( 0 : ℚ ) ≤ p ), by exact_mod_cast ( by nlinarith [ ( by norm_cast; linarith : ( 1 : ℚ ) ≤ q ) ] : ( p : ℚ ) ≤ q ) ⟩, by rw [ Rat.divInt_eq_div ] ; rw [ lt_div_iff₀ ] <;> norm_cast at * <;> linarith, by rw [ Rat.divInt_eq_div ] ; rw [ div_lt_iff₀ ] <;> norm_cast at * <;> linarith ⟩;
    have h_card_image : Set.ncard (Set.image (fun p : ℤ => (p : ℚ) / q) {p : ℤ | (x : ℝ) * q < p ∧ p < (y : ℝ) * q ∧ IsCoprime p q}) ≤ Set.ncard {r : ℚ | r.den = q ∧ IsFarey n r ∧ x < r ∧ r < y} := by
      apply_rules [ Set.ncard_le_ncard ];
      exact Set.Finite.subset ( fareyBetween_finite n x y ) fun r hr => ⟨ hr.2.1, hr.2.2.1, hr.2.2.2 ⟩;
    rwa [ Set.ncard_image_of_injective _ fun a b h => by simpa [ div_eq_iff, show q ≠ 0 by linarith [ Finset.mem_Icc.mp hq ] ] using h ] at h_card_image;
  convert Finset.sum_le_sum h_biUnion using 1;
  · norm_cast;
  · have h_card_biUnion : ∀ {S : Finset ℕ} (hS : ∀ q ∈ S, 1 ≤ q ∧ q ≤ n), ({r : ℚ | ∃ q ∈ S, r.den = q ∧ IsFarey n r ∧ x < r ∧ r < y}.ncard = ∑ q ∈ S, ({r : ℚ | r.den = q ∧ IsFarey n r ∧ x < r ∧ r < y}.ncard)) := by
      intros S hS;
      induction S using Finset.induction <;> simp_all +decide [ Set.ncard_eq_toFinset_card' ];
      rw [ ← ‹ { r : ℚ | r.den ∈ _ ∧ IsFarey n r ∧ x < r ∧ r < y }.ncard = ∑ q ∈ _, _ ›, ← @Set.ncard_union_eq ];
      · exact congr_arg _ ( by ext; aesop );
      · grind +splitImp;
      · exact Set.Finite.subset ( farey_finite n ) fun x hx => hx.2.1;
      · exact Set.Finite.subset ( farey_finite n ) fun x hx => hx.2.1;
    convert h_card_biUnion fun q hq => Finset.mem_Icc.mp hq using 2;
    ext; simp [IsFarey];
    exact fun _ _ _ _ _ => ⟨ Rat.pos _, by assumption ⟩

/-
**Density count (small-`b` range).** For `0 ≤ x < y ≤ 1`,
`betweenCount n x y ≥ (y-x)·Φ(n) - ∑_{q≤n} τ(q) ≥ (y-x)·n(n+1)/4 - n·(1+log n)`.
-/
theorem density_count_lower (n : ℕ) (x y : ℚ) (hx : 0 ≤ x) (hy : y ≤ 1) (hxy : x < y) :
    ((y : ℝ) - x) * ((n : ℝ) * ((n : ℝ) + 1) / 4) - (n : ℝ) * (1 + Real.log n)
      ≤ (betweenCount n x y : ℝ) := by
  have h_density : (betweenCount n x y : ℝ) ≥ (∑ q ∈ Finset.Icc 1 n, ((y - x) * (Nat.totient q : ℝ) - (q.divisors.card : ℝ))) := by
    -- Apply the density bridge theorem to get the lower bound.
    have h_lower_bound : (betweenCount n x y : ℝ) ≥ ∑ q ∈ Finset.Icc 1 n, ((y - x) * (Nat.totient q : ℝ) - (q.divisors.card : ℝ)) := by
      have := density_bridge n x y hx hy hxy
      refine' le_trans ( Finset.sum_le_sum _ ) this;
      intro q hq; specialize hq; have := coprime_count_lower q ( by linarith [ Finset.mem_Icc.mp hq ] ) ( x * q ) ( y * q ) ( by nlinarith [ show ( q : ℝ ) ≥ 1 by norm_cast; linarith [ Finset.mem_Icc.mp hq ], show ( x : ℝ ) < y by exact_mod_cast hxy ] ) ; simp_all +decide [ mul_comm, mul_div_assoc ] ;
      rwa [ ← mul_sub, mul_div_cancel_left₀ _ ( by norm_cast; linarith ) ] at this
    generalize_proofs at *; (
    convert h_lower_bound using 1);
  refine le_trans ?_ h_density;
  -- By `four_mul_Phi_ge n : n*(n+1) ≤ 4*Phi n` (i.e. `(Phi n : ℝ) ≥ n*(n+1)/4`).
  have h_phi : (Phi n : ℝ) ≥ (n * (n + 1) / 4 : ℝ) := by
    exact div_le_iff₀' ( by positivity ) |>.2 ( mod_cast four_mul_Phi_ge n );
  convert sub_le_sub ( mul_le_mul_of_nonneg_left h_phi <| sub_nonneg.mpr <| Rat.cast_le.mpr hxy.le ) <| divisor_sum_le n using 1;
  unfold Phi; erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.mul_sum _ _ _, Finset.sum_range_succ' ] ;
  erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ]

end Erdos1005