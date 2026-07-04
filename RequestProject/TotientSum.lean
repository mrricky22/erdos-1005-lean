import Mathlib

open scoped BigOperators
open Finset

namespace Erdos1005

/-- The totient summatory function `Φ(m) = ∑_{j ≤ m} φ(j)`. -/
def Phi (m : ℕ) : ℕ := ∑ j ∈ Finset.range (m + 1), Nat.totient j

/-- The number of *ordered* coprime pairs `(a,b)` with `1 ≤ a,b ≤ m`. -/
def Pcard (m : ℕ) : ℕ :=
  ((Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter (fun p => Nat.Coprime p.1 p.2)).card

/-
**Coprime-pair identity.** Classifying ordered coprime pairs by `max(a,b)` gives
`2·Φ(m) = P(m) + 1` for `m ≥ 1`.
-/
theorem two_mul_Phi_eq (m : ℕ) (hm : 1 ≤ m) : 2 * Phi m = Pcard m + 1 := by
  induction hm <;> simp_all +decide [ Finset.sum_range_succ, Phi, Pcard ];
  rename_i k hk ih;
  rw [ show Finset.filter ( fun p : ℕ × ℕ => Nat.Coprime p.1 p.2 ) ( Finset.Icc 1 ( k + 1 ) ×ˢ Finset.Icc 1 ( k + 1 ) ) = Finset.filter ( fun p : ℕ × ℕ => Nat.Coprime p.1 p.2 ) ( Finset.Icc 1 k ×ˢ Finset.Icc 1 k ) ∪ Finset.filter ( fun p : ℕ × ℕ => Nat.Coprime p.1 p.2 ) ( Finset.image ( fun x => ( k + 1, x ) ) ( Finset.Icc 1 ( k + 1 ) ) ) ∪ Finset.filter ( fun p : ℕ × ℕ => Nat.Coprime p.1 p.2 ) ( Finset.image ( fun x => ( x, k + 1 ) ) ( Finset.Icc 1 k ) ) from ?_, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint ];
  · simp_all +decide [ Finset.filter_image, Nat.coprime_comm ];
    rw [ Finset.card_image_of_injective, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
    rw [ show # ( Finset.filter ( fun a => Nat.Coprime a ( k + 1 ) ) ( Finset.Icc 1 ( k + 1 ) ) ) = Nat.totient ( k + 1 ) from ?_, show # ( Finset.filter ( fun a => Nat.Coprime a ( k + 1 ) ) ( Finset.Icc 1 k ) ) = Nat.totient ( k + 1 ) from ?_ ];
    · grind;
    · congr 1 with x ; simp +decide [ Nat.coprime_comm ];
      grind;
    · congr 1 with x ; simp +decide [ Nat.coprime_comm ];
      exact fun hx => ⟨ fun h => Nat.le_of_lt_succ <| h.2.lt_of_ne <| by aesop_cat, fun h => ⟨ Nat.pos_of_ne_zero <| by aesop_cat, by linarith ⟩ ⟩;
  · rw [ Finset.disjoint_left ] ; aesop;
  · rw [ Finset.disjoint_left ] ; aesop;
  · grind

/-
**Union bound on non-coprime pairs.** The ordered pairs in `[1,m]²` that are *not*
coprime are at most `∑_{p ≤ m, p prime} ⌊m/p⌋²`. Equivalently a lower bound on `P(m)`.
-/
theorem Pcard_ge (m : ℕ) :
    m * m ≤ Pcard m + ∑ p ∈ (Finset.Icc 2 m).filter Nat.Prime, (m / p) ^ 2 := by
  -- Let $N$ be the number of non-coprime pairs in $[1,m]^2$.
  set N := ((Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter (fun p => ¬Nat.Coprime p.1 p.2)).card;
  -- Every non-coprime pair $(a,b)$ (with $a,b \ge 1$) has gcd > 1, hence has a prime divisor $p = \text{minFac}(\gcd(a,b))$; this $p$ is prime, $p \mid a$, $p \mid b$, and $p \le a \le m$. Thus the non-coprime set is a subset of the union over primes $p \le m$ of $S_p := \{(a,b) \in [1,m]^2 : p \mid a \land p \mid b\}$.
  have h_subset : N ≤ ∑ p ∈ (Finset.Icc 2 m).filter Nat.Prime, ((Finset.Icc 1 m).filter (fun a => p ∣ a)).card ^ 2 := by
    have h_subset : N ≤ Finset.card (Finset.biUnion ((Finset.Icc 2 m).filter Nat.Prime) (fun p => Finset.image (fun (a, b) => (a, b)) (Finset.filter (fun a => p ∣ a) (Finset.Icc 1 m) ×ˢ Finset.filter (fun b => p ∣ b) (Finset.Icc 1 m)))) := by
      refine Finset.card_mono ?_;
      intro p hp; simp_all +decide [ Nat.coprime_iff_gcd_eq_one ] ;
      exact ⟨ Nat.minFac ( Nat.gcd p.1 p.2 ), ⟨ ⟨ Nat.Prime.two_le ( Nat.minFac_prime hp.2 ), Nat.le_trans ( Nat.minFac_le ( Nat.gcd_pos_of_pos_left _ hp.1.1.1 ) ) ( Nat.le_trans ( Nat.le_of_dvd hp.1.1.1 ( Nat.gcd_dvd_left _ _ ) ) hp.1.1.2 ) ⟩, Nat.minFac_prime hp.2 ⟩, Nat.dvd_trans ( Nat.minFac_dvd _ ) ( Nat.gcd_dvd_left _ _ ), Nat.dvd_trans ( Nat.minFac_dvd _ ) ( Nat.gcd_dvd_right _ _ ) ⟩;
    refine le_trans h_subset <| le_trans ( Finset.card_biUnion_le ) ?_;
    norm_num [ sq ];
  -- For each prime $p$, $|S_p| = \lfloor m/p \rfloor^2$ (since the conditions on $a$ and $b$ are independent — $S_p$ is a product).
  have h_card_Sp : ∀ p ∈ (Finset.Icc 2 m).filter Nat.Prime, ((Finset.Icc 1 m).filter (fun a => p ∣ a)).card = m / p := by
    intro p hp; rw [ show Finset.filter ( fun a => p ∣ a ) ( Finset.Icc 1 m ) = Finset.image ( fun a => p * a ) ( Finset.Icc 1 ( m / p ) ) from ?_ ] ; rw [ Finset.card_image_of_injective _ fun a b h => mul_left_cancel₀ ( Nat.Prime.ne_zero <| Finset.mem_filter.mp hp |>.2 ) h ] ; simp +decide [ Nat.div_eq_of_lt ] ;
    ext a; simp [Finset.mem_image];
    exact ⟨ fun h => ⟨ a / p, ⟨ Nat.div_pos ( Nat.le_of_dvd h.1.1 h.2 ) ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ), Nat.div_le_div_right h.1.2 ⟩, Nat.mul_div_cancel' h.2 ⟩, by rintro ⟨ k, ⟨ hk₁, hk₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by nlinarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) ], by nlinarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ), Nat.div_mul_le_self m p ] ⟩, by simp +decide ⟩ ⟩;
  convert Nat.add_le_add_left h_subset ( Pcard m ) using 1;
  · rw [ show Pcard m = Finset.card ( Finset.filter ( fun p : ℕ × ℕ => Nat.Coprime p.1 p.2 ) ( Finset.Icc 1 m ×ˢ Finset.Icc 1 m ) ) from rfl ] ; rw [ Finset.card_filter_add_card_filter_not ] ; aesop;
  · exact congr rfl ( Finset.sum_congr rfl fun x hx => by rw [ h_card_Sp x hx ] )

/-
**Prime reciprocal-square bound (with margin).** `∑_{p ≤ m, p prime} 1/p² ≤ 97/200`.
The true value of `∑_p 1/p²` is `≈ 0.4522`, so `97/200 = 0.485` is a valid upper bound,
and being `< 1/2` it leaves the margin needed in the assembly.
-/
theorem prime_recip_sq_bound (m : ℕ) :
    ∑ p ∈ (Finset.Icc 2 m).filter Nat.Prime, (1 / (p : ℝ)) ^ 2 ≤ 97 / 200 := by
  -- Split the sum into two parts: one over primes equal to 2 and one over odd primes.
  have h_split_sum : ∀ m : ℕ, (∑ p ∈ ((Finset.Icc 2 m).filter Nat.Prime), (1 / (p : ℝ)) ^ 2) ≤ 1 / 4 + ∑ p ∈ ((Finset.Icc 3 m).filter (fun p => Nat.Prime p ∧ p % 2 = 1)), (1 / (p : ℝ)) ^ 2 := by
    intro m
    have h_split : ((Finset.Icc 2 m).filter Nat.Prime) ⊆ {2} ∪ ((Finset.Icc 3 m).filter (fun p => Nat.Prime p ∧ p % 2 = 1)) := by
      intro p hp; rcases p with ( _ | _ | _ | p ) <;> simp_all +arith +decide;
      exact hp.2.eq_two_or_odd.resolve_left ( by linarith );
    refine le_trans ( Finset.sum_le_sum_of_subset_of_nonneg h_split fun _ _ _ => sq_nonneg _ ) ?_ ; norm_num [ Finset.sum_union ];
  -- Bound the odd tail. Write odd j = 2k+3 (k ≥ 0). Peel the first 6 terms (k = 0..5, i.e. j = 3,5,7,9,11,13) exactly and telescope the rest:
  have h_odd_tail_bound : ∀ m : ℕ, (∑ p ∈ ((Finset.Icc 3 m).filter (fun p => Nat.Prime p ∧ p % 2 = 1)), (1 / (p : ℝ)) ^ 2) ≤ (∑ k ∈ Finset.range 6, (1 / ((2 * k + 3) : ℝ)) ^ 2) + (∑' k : ℕ, (1 / ((2 * (k + 6) + 3) : ℝ)) ^ 2) := by
    intros m
    have h_odd_tail_bound : (∑ p ∈ ((Finset.Icc 3 m).filter (fun p => Nat.Prime p ∧ p % 2 = 1)), (1 / (p : ℝ)) ^ 2) ≤ (∑ k ∈ Finset.range 6, (1 / ((2 * k + 3) : ℝ)) ^ 2) + (∑ k ∈ Finset.Ico 6 (m / 2 + 1), (1 / ((2 * k + 3) : ℝ)) ^ 2) := by
      have h_odd_tail_bound : ((Finset.Icc 3 m).filter (fun p => Nat.Prime p ∧ p % 2 = 1)) ⊆ Finset.image (fun k => 2 * k + 3) (Finset.range (m / 2 + 1)) := by
        intro p hp; simp_all +decide;
        exact ⟨ p / 2 - 1, by omega, by omega ⟩;
      refine le_trans ( Finset.sum_le_sum_of_subset_of_nonneg h_odd_tail_bound fun _ _ _ => sq_nonneg _ ) ?_;
      rcases n : m / 2 with ( _ | _ | _ | _ | _ | _ | k ) <;> norm_num [ Finset.sum_range_succ, Finset.sum_Ico_eq_sub _ ] at *;
    refine le_trans h_odd_tail_bound ?_;
    norm_num [ add_assoc, mul_add, Finset.sum_Ico_eq_sum_range ];
    exact le_trans ( Finset.sum_le_sum fun _ _ => by ring_nf; norm_num ) ( Summable.sum_le_tsum ( Finset.range ( m / 2 + 1 - 6 ) ) ( fun _ _ => by positivity ) ( by exact_mod_cast Summable.comp_injective ( Real.summable_nat_pow_inv.2 one_lt_two ) fun a b h => by simpa using h ) );
  -- Bound the telescoping series.
  have h_telescoping_bound : (∑' k : ℕ, (1 / ((2 * (k + 6) + 3) : ℝ)) ^ 2) ≤ (∑' k : ℕ, (1 / ((2 * (k + 6) + 2) * (2 * (k + 6) + 4) : ℝ))) := by
    refine' Summable.tsum_le_tsum _ _ _;
    · exact fun k => by rw [ div_pow, div_le_div_iff₀ ] <;> ring <;> nlinarith;
    · exact Summable.of_nonneg_of_le ( fun _ => sq_nonneg _ ) ( fun n => by rw [ div_pow, div_le_div_iff₀ ] <;> norm_cast <;> ring <;> nlinarith ) ( summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two );
    · exact Summable.of_nonneg_of_le ( fun _ => by positivity ) ( fun n => by rw [ div_le_div_iff₀ ] <;> norm_cast <;> ring <;> nlinarith ) ( summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two );
  -- Evaluate the telescoping series.
  have h_telescoping_eval : (∑' k : ℕ, (1 / ((2 * (k + 6) + 2) * (2 * (k + 6) + 4) : ℝ))) = (1 / 4) * (1 / (6 + 1 : ℝ)) := by
    -- Recognize that this is a telescoping series.
    have h_telescoping_series : ∀ n : ℕ, ∑ k ∈ Finset.range n, (1 / ((2 * (k + 6) + 2) * (2 * (k + 6) + 4) : ℝ)) = (1 / 4) * (1 / (6 + 1 : ℝ)) - (1 / 4) * (1 / (n + 6 + 1 : ℝ)) := by
      intro n; induction n <;> norm_num [ Finset.sum_range_succ ] at *;
      grind;
    -- Taking the limit of the partial sum as $n$ approaches infinity, we have:
    have h_limit : Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, (1 / ((2 * (k + 6) + 2) * (2 * (k + 6) + 4) : ℝ))) Filter.atTop (nhds ((1 / 4) * (1 / (6 + 1 : ℝ)))) := by
      simpa only [ h_telescoping_series ] using le_trans ( tendsto_const_nhds.sub <| tendsto_const_nhds.mul <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_mono ( fun n => by linarith ) tendsto_natCast_atTop_atTop ) <| by norm_num;
    exact tendsto_nhds_unique ( by exact ( Summable.hasSum <| by exact ( by by_contra h; exact not_tendsto_atTop_of_tendsto_nhds ( h_limit ) <| by exact not_summable_iff_tendsto_nat_atTop_of_nonneg ( fun _ => by positivity ) |>.1 h ) ) |> HasSum.tendsto_sum_nat ) h_limit;
  exact le_trans ( h_split_sum m ) ( by linarith [ h_odd_tail_bound m, show ( ∑ k ∈ Finset.range 6, ( 1 / ( 2 * k + 3 : ℝ ) ) ^ 2 ) = 1 / 9 + 1 / 25 + 1 / 49 + 1 / 81 + 1 / 121 + 1 / 169 by norm_num ] )

/-
**Section 5 backbone.** `Φ(m) ≥ m(m+1)/4`, in the integer form `4·Φ(m) ≥ m(m+1)`.
-/
theorem four_mul_Phi_ge (m : ℕ) : m * (m + 1) ≤ 4 * Phi m := by
  by_cases hm : m ≤ 31;
  · native_decide +revert;
  · -- For $m \geq 32$, we use the provided bounds to show the inequality.
    have h_bound : (m * m : ℝ) ≤ (Pcard m : ℝ) + m^2 * (97 / 200) := by
      have h_bound : (m * m : ℝ) ≤ (Pcard m : ℝ) + ∑ p ∈ (Finset.Icc 2 m).filter Nat.Prime, (m / p : ℝ)^2 := by
        have h_bound : (m * m : ℝ) ≤ (Pcard m : ℝ) + ∑ p ∈ (Finset.Icc 2 m).filter Nat.Prime, (m / p : ℕ)^2 := by
          exact_mod_cast Pcard_ge m;
        refine le_trans h_bound ?_ ; norm_num [ Finset.sum_add_distrib ];
        exact Finset.sum_le_sum fun x hx => by gcongr ; exact Nat.cast_div_le ..;
      refine le_trans h_bound ?_;
      norm_num [ div_pow, ← Finset.mul_sum _ _ _ ];
      convert mul_le_mul_of_nonneg_left ( prime_recip_sq_bound m ) ( sq_nonneg ( m : ℝ ) ) using 1 ; norm_num [ div_eq_mul_inv, Finset.mul_sum _ _ _ ];
    have h_bound : (2 * Phi m : ℝ) = (Pcard m : ℝ) + 1 := by
      exact_mod_cast two_mul_Phi_eq m ( by linarith );
    exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast ; nlinarith [ show ( m : ℝ ) ≥ 32 by exact_mod_cast not_le.mp hm ] ;

end Erdos1005