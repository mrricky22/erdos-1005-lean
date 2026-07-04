import RequestProject.TotientSum

open scoped BigOperators
open Finset

namespace Erdos1005

/-- The function `S(x) = ∑_{1 ≤ e < x} (1 - e/x) · φ(e)/e` from Section 5.
(The `e = 0` term contributes `0` since `Nat.totient 0 = 0`, and all `e` in the range
satisfy `e < x` for `x > 0`.) -/
noncomputable def Sfun (x : ℝ) : ℝ :=
  ∑ e ∈ Finset.range ⌈x⌉₊, (1 - (e : ℝ) / x) * (Nat.totient e / e)

/-- The auxiliary partial sum `A_m = ∑_{e ≤ m} φ(e)/e`. -/
noncomputable def Afun (m : ℕ) : ℝ :=
  ∑ e ∈ Finset.range (m + 1), (Nat.totient e / e : ℝ)

/-- `F(x) = S(x) - x/4` from Section 5. -/
noncomputable def Ffun (x : ℝ) : ℝ := Sfun x - x / 4

/-- `S(1) = 0`. -/
theorem Sfun_one : Sfun 1 = 0 := by
  unfold Sfun; norm_num

/-- `S(2) = 1/2`. -/
theorem Sfun_two : Sfun 2 = 1 / 2 := by
  unfold Sfun; norm_num [Finset.sum_range_succ]

/-
**Closed form on `[m, m+1]`.** For `m ≥ 1` and `x ∈ [m, m+1]`,
`S(x) = A_m - Φ(m)/x`.
-/
theorem Sfun_eq_on_Icc {m : ℕ} (hm : 1 ≤ m) {x : ℝ}
    (hx1 : (m : ℝ) ≤ x) (hx2 : x ≤ (m : ℝ) + 1) :
    Sfun x = Afun m - (Phi m : ℝ) / x := by
  -- For `x ∈ [m, m+1]` with `m ≥ 1`, the nat ceiling `⌈x⌉₊` is either `m` (only when `x = m`) or `m+1` (when `m < x ≤ m+1`).
  by_cases hx : x = m;
  · unfold Sfun Afun Phi; simp +decide [ Finset.sum_range_succ, hx ] ; ring;
    simp +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, Finset.sum_add_distrib ];
    exact Finset.sum_congr rfl fun x hx => by by_cases h : x = 0 <;> simp +decide [ h ] ;
  · -- For `x ∈ [m, m+1]` with `m ≥ 1`, the nat ceiling `⌈x⌉₊` is `m+1`.
    have h_ceil : ⌈x⌉₊ = m + 1 := by
      exact Nat.ceil_eq_iff ( by positivity ) |>.2 ⟨ by norm_num; contrapose! hx; linarith, by norm_num; contrapose! hx; linarith ⟩;
    unfold Sfun Afun Phi;
    simp_all +decide [ sub_mul, Finset.sum_div _ _ _, Finset.sum_mul ];
    exact Finset.sum_congr rfl fun i hi => by by_cases hi0 : i = 0 <;> simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, hi0 ] ;

/-
**Integer increment.** `S(m+1) - S(m) = Φ(m) / (m(m+1))` for `m ≥ 1`.
-/
theorem Sfun_int_increment {m : ℕ} (hm : 1 ≤ m) :
    Sfun (m + 1) - Sfun m = (Phi m : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) := by
  convert congr_arg₂ ( · - · ) ( Sfun_eq_on_Icc hm ( show ( m : ℝ ) ≤ ( m + 1 : ℝ ) by linarith ) ( show ( m + 1 : ℝ ) ≤ ( m + 1 : ℝ ) by linarith ) ) ( Sfun_eq_on_Icc hm ( show ( m : ℝ ) ≤ ( m : ℝ ) by linarith ) ( show ( m : ℝ ) ≤ ( m + 1 : ℝ ) by linarith ) ) using 1;
  -- Combine and simplify the fractions on the right-hand side.
  field_simp
  ring

/-
**`F` is nondecreasing at consecutive integers** (`m ≥ 1`), since
`Φ(m)/(m(m+1)) ≥ 1/4` by `four_mul_Phi_ge`.
-/
theorem Ffun_int_mono {m : ℕ} (hm : 1 ≤ m) : Ffun (m : ℝ) ≤ Ffun ((m : ℝ) + 1) := by
  -- By definition of $Ffun$, we have $Ffun (m + 1) - Ffun m = (Sfun (m + 1) - Sfun m) - 1/4$.
  have h_diff : Ffun (m + 1 : ℝ) - Ffun (m : ℝ) = (Phi m : ℝ) / (m * (m + 1)) - 1 / 4 := by
    unfold Ffun; have := Sfun_int_increment hm; norm_num at *; ring_nf at *; linarith;
  -- By `four_mul_Phi_ge`, we have $m(m+1) \leq 4 \Phi(m)$.
  have h_four_mul_Phi_ge : (m : ℝ) * (m + 1) ≤ 4 * (Phi m : ℝ) := by
    exact_mod_cast four_mul_Phi_ge m;
  nlinarith [ show ( 0 : ℝ ) < m * ( m + 1 ) by positivity, div_mul_cancel₀ ( Phi m : ℝ ) ( by positivity : ( m : ℝ ) * ( m + 1 ) ≠ 0 ) ]

/-
**`F` is nondecreasing along integers `≥ 1`.**
-/
theorem Ffun_int_mono_le {m k : ℕ} (hm : 1 ≤ m) (hmk : m ≤ k) :
    Ffun (m : ℝ) ≤ Ffun (k : ℝ) := by
  induction hmk <;> norm_num at *;
  exact le_trans ‹_› ( Ffun_int_mono <| by linarith )

/-- `F(2) = 0`. -/
theorem Ffun_two : Ffun 2 = 0 := by
  unfold Ffun; rw [Sfun_two]; norm_num

/-
**`S(m) ≥ m/4` for integers `m ≥ 2`** (the headline consequence of Lemma 5.1).
-/
theorem Sfun_ge_quarter {m : ℕ} (hm : 2 ≤ m) : (m : ℝ) / 4 ≤ Sfun (m : ℝ) := by
  -- By Ffun_int_mono_le applied with 2 ≤ m, Ffun 2 ≤ Ffun m. Since Ffun 2 = 0 (Ffun_two), we get 0 ≤ Ffun m = Sfun m - m/4, i.e. m/4 ≤ Sfun m.
  have h1 : 0 ≤ Ffun (m : ℝ) := by
    convert Ffun_int_mono_le ( by norm_num : 1 ≤ 2 ) hm using 1 ; norm_num [ Ffun_two ];
  unfold Ffun at h1; linarith;

/-
**Exact difference of `F` within a unit interval `[m, m+1]`** (`m ≥ 1`).
-/
theorem Ffun_diff_on_unit {m : ℕ} (hm : 1 ≤ m) {a b : ℝ}
    (ha : (m : ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ (m : ℝ) + 1) :
    Ffun b - Ffun a = (b - a) * ((Phi m : ℝ) / (a * b) - 1 / 4) := by
  rw [ show Ffun b = Sfun b - b / 4 by rfl, show Ffun a = Sfun a - a / 4 by rfl ];
  rw [ Sfun_eq_on_Icc hm ha ( by linarith ), Sfun_eq_on_Icc hm ( by linarith ) hb ] ; ring;
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp_all +decide ; ring;
  · linarith [ ( by norm_cast : ( 1 : ℝ ) ≤ m ) ];
  · ring

/-
**`F` lies above the minimum of the endpoint values on a unit interval** (`k ≥ 1`).
This is the (formalization-friendly form of) concavity of `F` on `[k, k+1]`.
-/
theorem Ffun_ge_min_on_unit {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hx1 : (k : ℝ) ≤ x) (hx2 : x ≤ (k : ℝ) + 1) :
    min (Ffun (k : ℝ)) (Ffun ((k : ℝ) + 1)) ≤ Ffun x := by
  have h_group : (x - k) * ((Phi k : ℝ) / (k * x) - 1 / 4) = Ffun x - Ffun k ∧ (k + 1 - x) * ((Phi k : ℝ) / (x * (k + 1)) - 1 / 4) = Ffun (k + 1) - Ffun x := by
    constructor <;> rw [ Ffun_diff_on_unit ] <;> aesop;
  by_contra h_contra; push_neg at h_contra; (
  -- From the first inequality, we have $P/(kx) < 1/4$, which implies $4P < kx$.
  have h1 : 4 * (Phi k : ℝ) < k * x := by
    have h1 : (Phi k : ℝ) / (k * x) < 1 / 4 := by
      cases lt_or_eq_of_le hx1 <;> cases lt_or_eq_of_le hx2 <;> nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, min_le_left ( Ffun k ) ( Ffun ( k + 1 ) ), min_le_right ( Ffun k ) ( Ffun ( k + 1 ) ) ];
    rw [ div_lt_iff₀ ] at h1 <;> nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( x : ℝ ) ≥ k by exact_mod_cast hx1 ];
  by_cases hx : x = k + 1 <;> simp_all +decide [ sub_eq_iff_eq_add ];
  nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( Phi k : ℝ ) ≥ 0 by positivity, mul_div_cancel₀ ( Phi k : ℝ ) ( show ( x * ( k + 1 ) : ℝ ) ≠ 0 by exact mul_ne_zero ( by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ) ( by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ) ), mul_pos ( show ( k + 1 - x : ℝ ) > 0 by exact sub_pos.mpr ( lt_of_le_of_ne hx2 hx ) ) ( show ( x : ℝ ) > 0 by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ) ]);

/-
**`F` is at least its value at any integer `j ≥ 1` for all larger arguments.**
-/
theorem Ffun_ge_int_for_ge {j : ℕ} (hj : 1 ≤ j) {t : ℝ} (ht : (j : ℝ) ≤ t) :
    Ffun (j : ℝ) ≤ Ffun t := by
  -- Let $k = \lfloor t \rfloor$ (Nat.floor $t$). Since $t \geq j \geq 1 \geq 0$, we have $k \geq j$ and $k \geq 1$.
  set k : ℕ := Nat.floor t
  have hk1 : k ≥ j := by
    exact Nat.le_floor ht
  have hk2 : k ≥ 1 := by
    bv_omega;
  -- Also, $k \leq t$ (Nat.floor_le, $t \geq 0$) and $t \leq k+1$ (Nat.lt_floor_add_one gives $t < \lfloor t \rfloor + 1$, so $t \leq k+1$).
  have hk3 : (k : ℝ) ≤ t := by
    exact Nat.floor_le ( by linarith )
  have hk4 : t ≤ (k : ℝ) + 1 := by
    exact le_of_lt <| Nat.lt_floor_add_one t;
  convert le_trans _ ( Ffun_ge_min_on_unit hk2 hk3 hk4 ) using 1;
  exact le_min ( Ffun_int_mono_le hj hk1 ) ( by exact_mod_cast Ffun_int_mono_le hj ( Nat.le_succ_of_le hk1 ) )

/-
**Stronger quadratic totient bound** `(m+1)² ≤ 4·Φ(m)` for `m ≥ 7`.
-/
theorem Phi_quad_lower {m : ℕ} (hm : 7 ≤ m) : ((m : ℝ) + 1) ^ 2 ≤ 4 * (Phi m : ℝ) := by
  -- For m ≥ 67, use the analytic chain from TotientSum.lean: 2·Phi m = Pcard m + 1 (two_mul_Phi_eq, needs m ≥ 1), and m·m ≤ Pcard m + ∑_{p ≤ m prime} (m/p)^2 (Pcard_ge), with ∑_{p ≤ m prime} (1/p)^2 ≤ 97/200 (prime_recip_sq_bound).
  have h_analytic : ∀ m : ℕ, 67 ≤ m → (2 : ℝ) * Phi m ≥ (m : ℝ) ^ 2 * (103 / 200) + 1 := by
    intro m hm
    have h_two_mul_Phi_eq : (2 : ℝ) * Phi m = (Pcard m : ℝ) + 1 := by
      exact_mod_cast two_mul_Phi_eq m ( by linarith )
    have h_Pcard_ge : (m : ℝ) * m ≤ (Pcard m : ℝ) + ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 m), (m / p : ℝ) ^ 2 := by
      have h_Pcard_ge : (m : ℝ) * m ≤ (Pcard m : ℝ) + ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 m), (m / p : ℕ) ^ 2 := by
        exact_mod_cast Pcard_ge m;
      refine le_trans h_Pcard_ge ?_;
      norm_num [ Finset.sum_div _ _ _ ];
      exact Finset.sum_le_sum fun x hx => by rw [ div_pow, le_div_iff₀ ] <;> norm_cast <;> nlinarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ), Nat.div_mul_le_self m x, Nat.div_add_mod m x, Nat.mod_lt m ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) ] : 0 < x ) ] ;
    have h_prime_recip_sq_bound : ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 m), (1 / (p : ℝ)) ^ 2 ≤ 97 / 200 := by
      convert prime_recip_sq_bound m using 1
    have h_sum_recip_sq_bound : ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 2 m), (m / p : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 * (97 / 200) := by
      convert mul_le_mul_of_nonneg_left h_prime_recip_sq_bound ( sq_nonneg ( m : ℝ ) ) using 1 ; norm_num [ div_eq_mul_inv, mul_pow, Finset.mul_sum _ _ _ ]
    have h_Pcard_ge_final : (Pcard m : ℝ) ≥ (m : ℝ) ^ 2 * (103 / 200) := by
      linarith
    linarith [h_two_mul_Phi_eq, h_Pcard_ge_final];
  by_cases hm67 : m ≥ 67;
  · nlinarith [ show ( m : ℝ ) ≥ 67 by norm_cast, h_analytic m hm67 ];
  · interval_cases m <;> exact mod_cast by native_decide;

/-
**`F` is nondecreasing on a unit interval `[m, m+1]` for `m ≥ 7`.**
-/
theorem Ffun_mono_on_unit_ge7 {m : ℕ} (hm : 7 ≤ m) {a b : ℝ}
    (ha : (m : ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ (m : ℝ) + 1) : Ffun a ≤ Ffun b := by
  -- By Ffun_diff_on_unit (m ≥ 7 ≥ 1), Ffun b - Ffun a = (b - a)·((Phi m)/(a·b) - 1/4).
  have h_diff : Ffun b - Ffun a = (b - a) * ((Phi m : ℝ) / (a * b) - 1 / 4) := by
    convert Ffun_diff_on_unit ( by linarith : 1 ≤ m ) ha hab hb using 1;
  -- By Phi_quad_lower, (m+1)^2 ≤ 4·(Phi m). Hence a·b ≤ 4·Phi m.
  have h_ab_le : a * b ≤ 4 * (Phi m : ℝ) := by
    exact le_trans ( by nlinarith [ ( by norm_cast : ( 7 :ℝ ) ≤ m ) ] ) ( Phi_quad_lower hm );
  nlinarith [ show ( 0 : ℝ ) < a * b by exact mul_pos ( lt_of_lt_of_le ( by positivity ) ha ) ( lt_of_lt_of_le ( lt_of_lt_of_le ( by positivity ) ha ) hab ), div_mul_cancel₀ ( Phi m : ℝ ) ( show ( a * b ) ≠ 0 by exact ne_of_gt ( mul_pos ( lt_of_lt_of_le ( by positivity ) ha ) ( lt_of_lt_of_le ( lt_of_lt_of_le ( by positivity ) ha ) hab ) ) ) ]

/-
**Unit-interval max bound:** `F(x) ≤ F(m+2)` for `x ∈ [m, m+1]`, every `m ≥ 0`.
-/
theorem Ffun_unit_le_succ2 {m : ℕ} {x : ℝ}
    (hx1 : (m : ℝ) ≤ x) (hx2 : x ≤ (m : ℝ) + 1) :
    Ffun x ≤ Ffun ((m : ℝ) + 2) := by
  by_cases hm : m = 0;
  · -- Since $m = 0$, we have $x \in [0, 1]$. By definition of $Sfun$, we know that $Sfun(x) = 0$ for $x \in [0, 1]$.
    have h_Sfun_zero : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → Sfun x = 0 := by
      unfold Sfun;
      intro x hx₁ hx₂; rcases eq_or_lt_of_le hx₁ with rfl | hx₁' <;> norm_num [ Finset.sum_range_succ' ] ;
      rw [ show ⌈x⌉₊ = 1 by exact Nat.ceil_eq_iff ( by positivity ) |>.2 ⟨ by norm_num; linarith, by norm_num; linarith ⟩ ] ; norm_num;
    simp_all +decide [ Ffun ];
    rw [ Sfun_two ] ; linarith;
  · -- For $1 \leq m \leq 6$, we can check each case individually.
    by_cases hm_cases : m ≤ 6;
    · rw [ Ffun, Ffun, Sfun_eq_on_Icc, Sfun ];
      any_goals assumption;
      · interval_cases m <;> norm_num [ Finset.sum_range_succ, Nat.totient_prime, Phi, Afun ] at *;
        all_goals norm_num [ show Nat.totient 4 = 2 by rfl, show Nat.totient 6 = 2 by rfl ] at *; ring_nf at *; nlinarith [ inv_mul_cancel₀ ( by linarith : x ≠ 0 ) ] ;
      · exact Nat.pos_of_ne_zero hm;
    · -- For $m \geq 7$, we can use the fact that $F$ is nondecreasing on $[m, m+1]$.
      have h_mono : Ffun x ≤ Ffun ((m : ℝ) + 1) := by
        apply Ffun_mono_on_unit_ge7 (by linarith) hx1 (by linarith) (by linarith);
      exact le_trans h_mono ( mod_cast Ffun_int_mono ( by linarith ) )

/-
**Unit step:** `F(x) ≤ F(x+1)` for all `x ≥ 1`.
-/
theorem Ffun_step_le {x : ℝ} (hx : 1 ≤ x) : Ffun x ≤ Ffun (x + 1) := by
  by_cases hm : Nat.floor x ≥ 7;
  · -- By Ffun_mono_on_unit_ge7 (index m) with a=x, b=(m:ℝ)+1: Ffun x ≤ Ffun ((m:ℝ)+1).
    have h_mono1 : Ffun x ≤ Ffun ((Nat.floor x : ℝ) + 1) := by
      apply Ffun_mono_on_unit_ge7 hm (Nat.floor_le (by linarith)) (by linarith [Nat.lt_floor_add_one x]) (by linarith [Nat.lt_floor_add_one x]);
    refine le_trans h_mono1 ?_;
    convert Ffun_ge_int_for_ge _ _;
    rotate_left;
    exacts [ ⌊x⌋₊ + 1, by linarith, by push_cast; linarith [ Nat.floor_le ( by linarith : 0 ≤ x ) ], by push_cast; ring ];
  · -- Since $m < 7$, we have $1 \leq m \leq 6$. We can split into subcases based on the value of $m$.
    have hm_cases : ∃ m : ℕ, m ∈ [1, 2, 3, 4, 5, 6] ∧ m ≤ x ∧ x < m + 1 := by
      use Nat.floor x;
      exact ⟨ by have := Nat.floor_pos.mpr hx; interval_cases ⌊x⌋₊ <;> trivial, Nat.floor_le <| by positivity, Nat.lt_floor_add_one _ ⟩;
    obtain ⟨ m, hm₁, hm₂, hm₃ ⟩ := hm_cases;
    -- By definition of $Ffun$, we have $Ffun x = Afun m - (Phi m : ℝ) / x - x / 4$ and $Ffun (x + 1) = Afun (m + 1) - (Phi (m + 1) : ℝ) / (x + 1) - (x + 1) / 4$.
    have hFfun_def : Ffun x = Afun m - (Phi m : ℝ) / x - x / 4 ∧ Ffun (x + 1) = Afun (m + 1) - (Phi (m + 1) : ℝ) / (x + 1) - (x + 1) / 4 := by
      have hFfun_def : Sfun x = Afun m - (Phi m : ℝ) / x ∧ Sfun (x + 1) = Afun (m + 1) - (Phi (m + 1) : ℝ) / (x + 1) := by
        apply And.intro;
        · apply Sfun_eq_on_Icc;
          · fin_cases hm₁ <;> trivial;
          · linarith;
          · linarith;
        · apply Sfun_eq_on_Icc;
          · linarith;
          · norm_num; linarith;
          · norm_num; linarith;
      exact ⟨ by rw [ ← hFfun_def.1, Ffun ], by rw [ ← hFfun_def.2, Ffun ] ⟩;
    simp_all +decide [ Afun, Phi ];
    rcases hm₁ with ( rfl | rfl | rfl | rfl | rfl | rfl ) <;> norm_num [ Finset.sum_range_succ, Nat.totient_prime ] at *;
    all_goals norm_num [ show Nat.totient 4 = 2 by rfl, show Nat.totient 6 = 2 by rfl ] at *;
    all_goals field_simp;
    all_goals nlinarith [ sq_nonneg ( x - 2 ) ]

/-
**`F` lies above the minimum of the values at any two points of a unit interval.**
-/
theorem Ffun_ge_min_on_unit_gen {k : ℕ} (hk : 1 ≤ k) {a z b : ℝ}
    (ha : (k : ℝ) ≤ a) (haz : a ≤ z) (hzb : z ≤ b) (hb : b ≤ (k : ℝ) + 1) :
    min (Ffun a) (Ffun b) ≤ Ffun z := by
  by_contra h_contra;
  -- From the assumption, we have $Ffun a > Ffun z$ and $Ffun b > Ffun z$.
  have hFfun_a : Ffun a > Ffun z := by
    exact lt_of_not_ge fun h => h_contra <| le_trans ( min_le_left _ _ ) h
  have hFfun_b : Ffun b > Ffun z := by
    grind;
  -- From the assumption, we have $4 \cdot \Phi(k) < a \cdot z$ and $4 \cdot \Phi(k) > z \cdot b$.
  have h_bounds : 4 * (Phi k : ℝ) < a * z ∧ 4 * (Phi k : ℝ) > z * b := by
    have h_bounds : (Phi k : ℝ) / (a * z) - 1 / 4 < 0 ∧ (Phi k : ℝ) / (z * b) - 1 / 4 > 0 := by
      constructor;
      · have hFfun_diff : Ffun z - Ffun a = (z - a) * ((Phi k : ℝ) / (a * z) - 1 / 4) := by
          convert Ffun_diff_on_unit hk ( by linarith : ( k : ℝ ) ≤ a ) ( by linarith : a ≤ z ) ( by linarith : z ≤ ( k : ℝ ) + 1 ) using 1;
        nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( z : ℝ ) ≥ a by linarith ];
      · have := Ffun_diff_on_unit hk ( show ( k : ℝ ) ≤ z by linarith ) ( show z ≤ b by linarith ) ( show b ≤ ( k : ℝ ) + 1 by linarith ) ; nlinarith [ show 0 < b - z by exact sub_pos.mpr ( lt_of_le_of_ne hzb ( by rintro rfl; norm_num at * ) ) ] ;
    constructor <;> nlinarith [ show 0 < a * z by exact mul_pos ( by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ) ( by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ), show 0 < z * b by exact mul_pos ( by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ) ( by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ), div_mul_cancel₀ ( Phi k : ℝ ) ( show a * z ≠ 0 by exact ne_of_gt ( mul_pos ( by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ) ( by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ) ) ), div_mul_cancel₀ ( Phi k : ℝ ) ( show z * b ≠ 0 by exact ne_of_gt ( mul_pos ( by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ) ( by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast ] ) ) ) ];
  nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, show ( Phi k : ℝ ) ≥ 0 by positivity ]

/-
**Lemma 5.1, real increment (case `x ≥ 1, y ≥ 1`).**
-/
theorem Sfun_increment_ge_one {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    y / 4 ≤ Sfun (x + y) - Sfun x := by
  -- Let $m = \lfloor x \rfloor$.
  set m := Nat.floor x with hm_def;
  -- Set $z = x + y \geq x + 1$.
  set z := x + y with hz_def;
  -- Case 1: $z \geq m + 2$.
  by_cases h_case1 : z ≥ m + 2;
  · -- Then $Ffun x \leq Ffun ((m:ℝ)+2)$ by Ffun_unit_le_succ2, and $Ffun ((m:ℝ)+2) = Ffun (((m+2:ℕ)):ℝ) \leq Ffun z$ by Ffun_ge_int_for_ge (j = m+2 ≥ 1, z ≥ (m+2:ℝ)).
    have h_case1_ineq : Ffun x ≤ Ffun ((m + 2 : ℕ) : ℝ) ∧ Ffun ((m + 2 : ℕ) : ℝ) ≤ Ffun z := by
      apply And.intro;
      · convert Ffun_unit_le_succ2 ( show ( m : ℝ ) ≤ x from Nat.floor_le ( by positivity ) ) ( show x ≤ ( m : ℝ ) + 1 from Nat.lt_floor_add_one x |> le_of_lt ) using 1;
        norm_cast;
      · apply Ffun_ge_int_for_ge;
        · linarith;
        · aesop;
    unfold Ffun at *; linarith;
  · -- Case 2: $z < m + 2$.
    have h_case2 : min (Ffun (x + 1)) (Ffun (m + 2)) ≤ Ffun z := by
      apply Ffun_ge_min_on_unit_gen;
      exact Nat.succ_pos m;
      · norm_num; linarith [ Nat.floor_le ( by positivity : 0 ≤ x ) ];
      · linarith;
      · linarith;
      · norm_num [ add_assoc ];
    -- Now $Ffun x \leq Ffun (x+1)$ by $Ffun_step_le$ (x ≥ 1), and $Ffun x \leq Ffun ((m:ℝ)+2)$ by $Ffun_unit_le_succ2$.
    have h_case2_le : Ffun x ≤ Ffun (x + 1) ∧ Ffun x ≤ Ffun (m + 2) := by
      apply And.intro;
      · exact Ffun_step_le hx;
      · convert Ffun_unit_le_succ2 ( show ( m : ℝ ) ≤ x from Nat.floor_le ( by positivity ) ) ( show x ≤ ( m : ℝ ) + 1 from Nat.lt_floor_add_one x |> le_of_lt ) using 1;
    unfold Ffun at *;
    grind

/-
**Lemma 5.1, real increment (case `x ≥ 0, y ≥ 2`).**
-/
theorem Sfun_increment_ge_two {x y : ℝ} (hx : 0 ≤ x) (hy : 2 ≤ y) :
    y / 4 ≤ Sfun (x + y) - Sfun x := by
  -- Let $m = \lfloor x \rfloor$ (a natural number $\geq 0$).
  set m := Nat.floor x with hm_def;
  -- By Ffun_unit_le_succ2 (hx1 : (m:ℝ) ≤ x, hx2 : x ≤ (m:ℝ)+1): Ffun x ≤ Ffun ((m:ℝ)+2).
  have h_unit : Ffun x ≤ Ffun ((m : ℝ) + 2) := by
    convert Ffun_unit_le_succ2 ( show ( m : ℝ ) ≤ x from Nat.floor_le hx ) ( show x ≤ ( m : ℝ ) + 1 from Nat.lt_floor_add_one x |> le_of_lt ) using 1;
  -- By Ffun_ge_int_for_ge (j = m+2, which is ≥ 1) with z ≥ (m+2:ℝ): Ffun ((m+2:ℕ):ℝ) ≤ Ffun z.
  have h_ge_int : Ffun ((m + 2 : ℕ) : ℝ) ≤ Ffun (x + y) := by
    apply Erdos1005.Ffun_ge_int_for_ge;
    · linarith;
    · norm_num; linarith [ Nat.floor_le hx ];
  unfold Ffun at *; norm_num at *; linarith;

end Erdos1005