import RequestProject.PrimProg
import RequestProject.TotientIncrement

open scoped BigOperators
open Finset

namespace Erdos1005

/-
**Harmonic-sum upper bound.** `∑_{d=1}^{N} 1/d ≤ 1 + log N`.
-/
theorem harmonic_le_one_add_log (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / d ≤ 1 + Real.log N := by
  induction' N with N ih <;> norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] at *;
  rcases N.eq_zero_or_pos with rfl | hN;
  · norm_num;
  · have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( N : ℝ ) / ( N + 1 ) );
    rw [ Real.log_div ] at this <;> norm_num at * <;> nlinarith [ mul_div_cancel₀ ( N : ℝ ) ( by positivity : ( N : ℝ ) + 1 ≠ 0 ), inv_mul_cancel₀ ( by positivity : ( N : ℝ ) + 1 ≠ 0 ) ]

/-
**Divisor-sum (`τ`-sum) bound.** `∑_{e=1}^{N} τ(e) ≤ N·(1 + log N)`, where
`τ(e) = e.divisors.card`. This controls the error terms in the Section-2 counting.
-/
theorem divisor_sum_le (N : ℕ) :
    ∑ e ∈ Finset.Icc 1 N, (e.divisors.card : ℝ) ≤ (N : ℝ) * (1 + Real.log N) := by
  have h_sum_divisors : ∑ e ∈ Finset.Icc 1 N, (Nat.divisors e).card = ∑ d ∈ Finset.Icc 1 N, (N / d : ℕ) := by
    erw [ Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range ];
    induction N <;> simp_all +decide [ Nat.succ_div, Finset.sum_range_succ ];
    simp_all +decide [ Finset.sum_add_distrib, Nat.add_comm 1 _, Nat.div_eq_of_lt ];
    rw [ ← Nat.cons_self_properDivisors ] <;> simp +arith +decide [ Nat.properDivisors ];
    rw [ Finset.card_filter, Finset.card_filter ];
    rw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_comm, add_left_comm ];
  rw_mod_cast [ h_sum_divisors ];
  refine' le_trans _ ( mul_le_mul_of_nonneg_left ( harmonic_le_one_add_log N ) ( Nat.cast_nonneg _ ) );
  push_cast [ Finset.mul_sum _ _ _ ];
  exact Finset.sum_le_sum fun x hx => by rw [ mul_one_div, le_div_iff₀ ] <;> norm_cast <;> linarith [ Finset.mem_Icc.mp hx, Nat.div_mul_le_self N x ] ;

/-
**Section-2→5 summation identity.** For all `u : ℕ` and `μ : ℝ`,
`∑_{0 ≤ e < ⌈μ·u⌉} (φ(e)/e)·(μ − e/u) = μ · S(μ·u)`.
-/
theorem totient_window_sum_eq (u : ℕ) (lam : ℝ) :
    ∑ e ∈ Finset.range ⌈lam * u⌉₊, ((Nat.totient e : ℝ) / e) * (lam - e / u)
      = lam * Sfun (lam * u) := by
  by_cases hlam' : lam = 0 <;> simp_all +decide [ Sfun ];
  rw [ Finset.mul_sum _ _ _ ] ; congr ; ext ; ring;
  simp +decide [ mul_assoc, mul_comm lam, hlam' ]

end Erdos1005