import RequestProject.Lower
import RequestProject.Density
import RequestProject.Assembly
import RequestProject.FareyGap

open scoped BigOperators
open Filter Topology

namespace Erdos1005

/-! # Final assembly of the elementary-interval lower bound (Sections 6–9)

We prove `elem_interval_count_lower` by splitting on the size of `b = x.den`:

* **Small `b`** (`b*b < n`): the interval `I_{a,b}` has length `> 1/b > 1/√n`, so the
  crude density bound `density_count_lower` already gives a count `≥ (n+1)√n/4 - n(1+log n)`,
  which dominates `(1/4-ε)n`.

* **Large `b`** (`n ≤ b*b`): choose `Q` with `Q^3 ≤ n ≤ Q^4` (so `Q ≤ n^{1/3} < √n ≤ b`).
  The reference rational `z` is chosen by the Farey–gap dichotomy at order `Q`, and the count
  is bounded via `caseA_count` / `caseB_count` / `caseB_count_left` / `left_count_main`,
  with the Section-2 error terms controlled uniformly by `Q ≤ n^{1/3}`.
-/

/-- Uniform ceiling used to bound every Section-2 error term arising in the large-`b` case. -/
noncomputable def Kmax (n Q : ℕ) : ℕ :=
  ⌈(4 * ((n : ℝ) + 1) * (Q : ℝ)) / Real.sqrt n⌉₊ + 2

/-- `n`-only upper bound for `Kmax n Q` when `Q ≤ n^{1/3}` (i.e. `Q^3 ≤ n`). -/
noncomputable def Kbar (n : ℕ) : ℕ :=
  ⌈(4 * ((n : ℝ) + 1)) * (n : ℝ) ^ ((1 : ℝ) / 3) / Real.sqrt n⌉₊ + 2

/-
**Derived facts** for the left endpoint of a badly ordered pair.
`a = x.num ≥ 1`, `b = x.den ≥ 4`, `a + 3 ≤ b`, `0 < x < elemR x < 1`, `b ≤ n`.
-/
theorem badly_left_facts {n : ℕ} {x : ℚ} (h : ∃ y, BadlyOrdered n x y) :
    0 < x ∧ x < elemR x ∧ elemR x < 1 ∧ 4 ≤ x.den ∧ x.den ≤ n ∧
      1 ≤ x.num ∧ x.num + 3 ≤ (x.den : ℤ) := by
  have := h.choose_spec.1.2.2;
  obtain ⟨y, hy⟩ := h
  have hxy : x < y := by
    exact hy.2.2.1
  have hxy' : x.num < y.num := by
    exact hy.2.2.2.1
  have hyx' : y.den < x.den := by
    exact hy.2.2.2.2
  have hx_pos : 0 < x := by
    by_cases hx_zero : x = 0;
    · aesop;
    · exact lt_of_le_of_ne ( hy.1.1 ) ( Ne.symm hx_zero )
  have hx_lt_elemR : x < elemR x := by
    unfold elemR;
    rw [ lt_div_iff₀ ] <;> norm_num;
    · have := Rat.num_div_den x;
      rw [ ← this ] ; ring_nf ; norm_num [ hx_pos.ne' ];
      exact neg_lt_iff_pos_add'.mpr ( by positivity );
    · linarith [ y.pos ]
  have h_elemR_lt_1 : elemR x < 1 := by
    have h_elemR_lt_1 : elemR x ≤ y := by
      apply elemR_le; assumption;
    exact lt_of_le_of_lt h_elemR_lt_1 ( hy.2.1.2.1.lt_of_ne ( by rintro rfl; exact absurd hxy' ( by norm_num; linarith [ Rat.num_pos.mpr hx_pos ] ) ) )
  have hx_den_ge_4 : 4 ≤ x.den := by
    by_contra h_contra;
    interval_cases _ : x.den <;> simp_all +decide [ elemR ];
    · grind;
    · linarith [ show ( x.num : ℚ ) ≥ 1 by exact_mod_cast Rat.num_pos.mpr hx_pos ]
  have hx_num_ge_1 : 1 ≤ x.num := by
    exact Rat.num_pos.mpr hx_pos
  have hx_num_plus_3_le_den : x.num + 3 ≤ x.den := by
    unfold elemR at *;
    rw [ div_lt_iff₀ ] at h_elemR_lt_1 <;> norm_cast at *;
    · rw [ Int.subNatNat_eq_coe ] at h_elemR_lt_1 ; omega;
    · rw [ Int.subNatNat_eq_coe ] ; norm_num ; linarith
  exact ⟨hx_pos, hx_lt_elemR, h_elemR_lt_1, hx_den_ge_4, this, hx_num_ge_1, hx_num_plus_3_le_den⟩

/-
The elementary interval length exceeds `1/b`.
-/
theorem elemR_sub_gt {x : ℚ} (hpos : 0 < x) (hlt : x < elemR x)
    (hb : 4 ≤ x.den) (ha : 1 ≤ x.num) (hab : x.num + 3 ≤ (x.den : ℤ)) :
    (1 : ℝ) / (x.den : ℝ) < (elemR x : ℝ) - (x : ℝ) := by
  rw [ div_lt_iff₀ ( by positivity ) ];
  rw [ show elemR x = ( x.num + 1 ) / ( x.den - 1 ) from ?_, show ( x : ℝ ) = x.num / x.den from ?_ ];
  · field_simp;
    rw [ lt_sub_iff_add_lt, lt_iff_not_ge ] ; norm_cast;
    rw [ Rat.divInt_eq_div, div_mul_eq_mul_div, div_le_iff₀ ] <;> norm_cast;
    · grind +extAll;
    · grind +locals;
  · exact_mod_cast x.num_div_den.symm;
  · unfold elemR; norm_num;

/-
**Small-`b` bound.** If `b*b < n` then the count in the elementary interval is at least
`(n+1)√n/4 - n(1+log n)` (independent of `x`).
-/
theorem smallb_bound {n : ℕ} {x : ℚ} (h : ∃ y, BadlyOrdered n x y)
    (hsmall : x.den * x.den < n) :
    ((n : ℝ) + 1) * Real.sqrt n / 4 - (n : ℝ) * (1 + Real.log n)
      ≤ (betweenCount n x (elemR x) : ℝ) := by
  convert density_count_lower n x ( elemR x ) _ _ _ |> le_trans _ using 1;
  · have h_elemR_sub : 1 / (x.den : ℝ) < (elemR x : ℝ) - (x : ℝ) := by
      convert elemR_sub_gt _ _ _ _ _;
      · exact badly_left_facts h |>.1;
      · exact badly_left_facts h |>.2.1;
      · exact badly_left_facts h |>.2.2.2.1;
      · have := badly_left_facts h; aesop;
      · have := badly_left_facts h; aesop;
    gcongr;
    refine' le_trans _ ( mul_le_mul_of_nonneg_right h_elemR_sub.le _ );
    · rw [ div_mul_eq_mul_div, div_le_div_iff₀ ] <;> norm_cast;
      · norm_num ; nlinarith [ sq_nonneg ( Real.sqrt n - x.den : ℝ ), Real.mul_self_sqrt ( Nat.cast_nonneg n ), ( by norm_cast : ( x.den :ℝ ) * x.den + 1 ≤ n ) ];
      · exact x.pos;
    · positivity;
  · exact h.choose_spec.1.1;
  · exact badly_left_facts h |>.2.2.1.le;
  · exact badly_left_facts h |>.2.1

/-
Existence of a suitable order `Q` for the large-`b` case.
-/
theorem largeb_Q_exists (n : ℕ) (hn : 81 ≤ n) :
    ∃ Q : ℕ, 3 ≤ Q ∧ Q ^ 3 ≤ n ∧ n ≤ Q ^ 4 := by
  -- By definition of $Q$, we know that $Q^3 \leq n$.
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, 3 ≤ Q ∧ Q^3 ≤ n ∧ (Q + 1)^3 > n := by
    obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q^3 ≤ n ∧ n < (Q + 1)^3 := by
      use Nat.floor (Real.rpow n (1/3 : ℝ));
      norm_num +zetaDelta at *;
      exact ⟨ by rw [ ← @Nat.cast_le ℝ ] ; push_cast; exact le_trans ( pow_le_pow_left₀ ( by positivity ) ( Nat.floor_le ( by positivity ) ) _ ) ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num ), by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; exact lt_of_le_of_lt ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num ) ( pow_lt_pow_left₀ ( Nat.lt_floor_add_one _ ) ( by positivity ) ( by positivity ) ) ⟩;
    exact ⟨ Q, le_of_not_gt fun h => by interval_cases Q <;> linarith, hQ.1, hQ.2 ⟩
  use Q, hQ.left, hQ.right.left, by
    nlinarith [ Nat.pow_le_pow_left hQ.1 2 ]

/-
The Section-2 determinant `z.num·x.den − x.num·z.den` equals `x.den · z.den · (z − x)`.
-/
theorem det_real_eq (x z : ℚ) :
    ((z.num * (x.den : ℤ) - x.num * (z.den : ℤ) : ℤ) : ℝ)
      = (z.den : ℝ) * (x.den : ℝ) * ((z : ℝ) - (x : ℝ)) := by
  rw [ Rat.cast_def, Rat.cast_def ] ; ring;
  simp +decide [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt x.pos, ne_of_gt z.pos ]

/-
Ceiling comparison against the uniform bound `Kmax`.
-/
theorem ceil_le_Kmax {n Q : ℕ} (A : ℝ)
    (hA : A ≤ (4 * ((n : ℝ) + 1) * (Q : ℝ)) / Real.sqrt n) : ⌈A⌉₊ ≤ Kmax n Q := by
  exact Nat.le_succ_of_le ( Nat.le_succ_of_le ( Nat.ceil_mono hA ) )

/-
A Section-2 error term is bounded by the uniform quantity `Kmax·(1+log Kmax)` provided its
defining ceiling is `≤ Kmax`.
-/
theorem errTerm_le_Kmax {n Q : ℕ} (x z : ℚ)
    (hM : ⌈((n : ℝ) + 1) / x.den * ((z.num * (x.den : ℤ) - x.num * (z.den : ℤ) : ℤ) : ℝ)⌉₊
            ≤ Kmax n Q) :
    errTerm x z n ≤ (Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q)) := by
  refine' le_trans ( errTerm_le x z n ) _;
  by_cases h : ⌈ ( n + 1 : ℝ ) / x.den * ( z.num * x.den - x.num * z.den ) ⌉₊ = 0 <;> simp_all +decide [ mul_add ];
  · rw [ Nat.ceil_eq_zero.mpr h ] ; norm_num;
    exact add_nonneg ( Nat.cast_nonneg _ ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( Real.log_nonneg ( mod_cast Nat.one_le_iff_ne_zero.mpr ( by unfold Kmax; positivity ) ) ) );
  · gcongr; all_goals exact Nat.ceil_le.mpr hM

/-
**Large-`b`, Case I.** The right endpoint `elemR x` is itself a low-order Farey fraction
(`(elemR x).den ≤ Q`). Apply `left_count_main` with reference `z = elemR x`.
-/
theorem largeb_caseI {n Q : ℕ} {x : ℚ} (h : ∃ y, BadlyOrdered n x y)
    (hQ : 3 ≤ Q) (hQ3 : Q ^ 3 ≤ n) (hbig : n ≤ x.den * x.den)
    (hsw : (elemR x).den ≤ Q) :
    (n : ℝ) / 4 - 2 * ((Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q))) - 1
      ≤ (betweenCount n x (elemR x) : ℝ) := by
  -- Let's obtain the necessary facts from `h`.
  obtain ⟨hx0, hxz, hz1, hb, ha, hab⟩ := badly_left_facts h;
  -- Let's simplify the expression for `det`.
  have hdet : (elemR x).num * (x.den : ℤ) - x.num * (elemR x).den = (elemR x).den + (elemR x).num := by
    unfold elemR; norm_num;
    have := Rat.num_div_den ( ( x.num + 1 : ℚ ) / ( x.den - 1 ) );
    rw [ div_eq_div_iff ] at this <;> norm_cast at * <;> simp_all +decide [ sub_eq_iff_eq_add ];
    · rw [ Int.subNatNat_eq_coe ] at * ; push_cast at * ; linarith;
    · grind +splitImp;
  -- Let's simplify the expression for `argX`.
  set argX := ((n + 1 : ℝ) / x.den) * ((elemR x).num * (x.den : ℤ) - x.num * (elemR x).den : ℝ) with hargX_def
  have hargX_ge_two : 2 ≤ argX := by
    -- Since $w.num \geq 1$ and $w.den \geq 1$, we have $w.den + w.num \geq 2$.
    have h_det_ge_two : (elemR x).den + (elemR x).num ≥ 2 := by
      linarith [ Rat.num_pos.mpr ( show 0 < elemR x from lt_trans hx0 hxz ), Rat.den_pos ( elemR x ) ];
    refine' le_trans _ ( mul_le_mul_of_nonneg_left ( show ( ( elemR x |> Rat.num ) : ℝ ) * x.den - x.num * ( elemR x |> Rat.den ) ≥ 2 by exact_mod_cast hdet.symm ▸ h_det_ge_two ) ( by positivity ) );
    rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> norm_cast <;> nlinarith only [ hb, ha, hbig ]
  have hargX_le_4Q : argX ≤ 4 * (n + 1) * Q / Real.sqrt n := by
    -- By `elemR_sub_gt` (with the facts): 1/b < (w:ℝ)-x. Also (w:ℝ)-x < 2/b: indeed (w:ℝ)-x = (a+b)/(b(b-1)) (cast elemR) and a+3≤b gives a+b < 2(b-1), so (a+b)/(b(b-1)) < 2/b.
    have h_diff_bounds : 1 / (x.den : ℝ) < (elemR x : ℝ) - x ∧ (elemR x : ℝ) - x < 2 / (x.den : ℝ) := by
      convert elemR_sub_gt hx0 hxz hb hab.1 hab.2 using 1;
      norm_num [ elemR ];
      rw [ Rat.cast_def ] ; ring_nf;
      intro h; nlinarith [ show ( x.den : ℝ ) ≥ 4 by norm_cast, inv_pos.mpr ( show ( x.den : ℝ ) > 0 by positivity ), inv_pos.mpr ( show ( -1 + x.den : ℝ ) > 0 by linarith [ show ( x.den : ℝ ) ≥ 4 by norm_cast ] ), mul_inv_cancel₀ ( show ( x.den : ℝ ) ≠ 0 by positivity ), mul_inv_cancel₀ ( show ( -1 + x.den : ℝ ) ≠ 0 by linarith [ show ( x.den : ℝ ) ≥ 4 by norm_cast ] ), show ( x.num : ℝ ) ≥ 1 by exact_mod_cast hab.1, show ( x.num : ℝ ) + 3 ≤ x.den by exact_mod_cast hab.2 ] ;
    -- Substitute the bounds for `w - x` into the expression for `argX`.
    have h_argX_bounds : argX ≤ (n + 1 : ℝ) * (elemR x).den * (2 / (x.den : ℝ)) := by
      have h_argX_bounds : argX = (n + 1 : ℝ) * (elemR x).den * ((elemR x : ℝ) - x) := by
        have := det_real_eq x ( elemR x ) ; simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] ;
        rw [ inv_mul_eq_div, div_eq_iff ] <;> norm_cast at * <;> simp_all +decide [ sub_eq_iff_eq_add ] ;
        ring;
      exact h_argX_bounds.symm ▸ mul_le_mul_of_nonneg_left h_diff_bounds.2.le ( by positivity );
    -- Since $x.den \geq \sqrt{n}$, we have $2 / x.den \leq 2 / \sqrt{n}$.
    have h_den_sqrt : (x.den : ℝ) ≥ Real.sqrt n := by
      exact Real.sqrt_le_iff.mpr ⟨ by positivity, by norm_cast; linarith ⟩;
    refine le_trans h_argX_bounds ?_;
    field_simp;
    rw [ le_div_iff₀ ( Real.sqrt_pos.mpr <| Nat.cast_pos.mpr <| by linarith ) ];
    nlinarith only [ show ( elemR x |> Rat.den : ℝ ) ≤ Q by exact_mod_cast hsw, show ( x.den : ℝ ) ≥ Real.sqrt n by exact h_den_sqrt, show ( Q : ℝ ) ≥ 3 by norm_cast, Real.sqrt_nonneg n, Real.sq_sqrt <| Nat.cast_nonneg n ];
  -- Let's simplify the expression for `main`.
  have hmain_ge_n_div_4 : ((n + 1 : ℝ) / (elemR x).den) * Sfun argX ≥ (n : ℝ) / 4 := by
    have hmain_ge_n_div_4 : ((n + 1 : ℝ) / (elemR x).den) * Sfun argX ≥ ((n + 1 : ℝ) / (elemR x).den) * (argX / 4) := by
      gcongr;
      convert Sfun_increment_ge_two ( show 0 ≤ 0 by norm_num ) ( show 2 ≤ argX by linarith ) |> le_trans <| le_rfl using 1 ; norm_num [ Sfun_eq_zero_of_lt_one ];
    have hmain_ge_n_div_4 : ((n + 1 : ℝ) / (elemR x).den) * (argX / 4) = ((n + 1 : ℝ) ^ 2 * ((elemR x : ℝ) - x)) / 4 := by
      have hmain_ge_n_div_4 : ((elemR x).num * (x.den : ℤ) - x.num * (elemR x).den : ℝ) = (elemR x).den * (x.den : ℝ) * ((elemR x : ℝ) - x) := by
        convert det_real_eq x ( elemR x ) using 1;
        norm_num;
      grind +qlia;
    have hmain_ge_n_div_4 : ((n + 1 : ℝ) ^ 2 * ((elemR x : ℝ) - x)) / 4 ≥ (n : ℝ) / 4 := by
      have hmain_ge_n_div_4 : (elemR x : ℝ) - x > 1 / (x.den : ℝ) := by
        apply elemR_sub_gt hx0 hxz hb hab.left hab.right;
      refine' le_trans _ ( div_le_div_of_nonneg_right ( mul_le_mul_of_nonneg_left hmain_ge_n_div_4.le <| sq_nonneg _ ) zero_le_four );
      field_simp;
      norm_cast ; nlinarith only [ ha, hb, hbig ];
    linarith;
  -- Let's simplify the expression for `errTerm`.
  have herrTerm_le_Kmax : errTerm x (elemR x) n ≤ (Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q)) := by
    apply errTerm_le_Kmax;
    convert ceil_le_Kmax _ hargX_le_4Q using 1;
    norm_num [ hargX_def ];
  have := left_count_main x ( elemR x ) ( le_of_lt hx0 ) hxz ( le_of_lt hz1 ) n;
  simp_all +decide [ errTerm ];
  rw [ show ( elemR x |> Rat.den : ℝ ) + ( elemR x |> Rat.num : ℝ ) = ( elemR x |> Rat.num : ℝ ) * x.den - x.num * ( elemR x |> Rat.den : ℝ ) by exact mod_cast hdet.symm ] at * ; linarith [ show ( 0 :ℝ ) ≤ Kmax n Q * ( 1 + Real.log ( Kmax n Q ) ) by exact mul_nonneg ( Nat.cast_nonneg _ ) ( add_nonneg zero_le_one ( Real.log_nonneg ( mod_cast Nat.one_le_iff_ne_zero.mpr <| by unfold Kmax; positivity ) ) ) ] ;

/-
**Large-`b`, Case II.** Some order-`Q` Farey fraction `z` lies strictly inside the
elementary interval. Apply `caseA_count`.
-/
theorem largeb_caseII {n Q : ℕ} {x : ℚ} (h : ∃ y, BadlyOrdered n x y)
    (hQ : 3 ≤ Q) (hQ3 : Q ^ 3 ≤ n) (hbig : n ≤ x.den * x.den)
    (z : ℚ) (hzF : IsFarey Q z) (hxz : x < z) (hzR : z < elemR x) :
    (n : ℝ) / 4 - 2 * ((Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q))) - 1
      ≤ (betweenCount n x (elemR x) : ℝ) := by
  -- By Lemma 2, we have $errTerm x z n \leq Kmax n Q * (1 + Real.log (Kmax n Q))$ and $errTerm (1 - elemR x) (1 - z) n \leq Kmax n Q * (1 + Real.log (Kmax n Q))$.
  have h_errTerm_xz : errTerm x z n ≤ (Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q)) := by
    apply errTerm_le_Kmax;
    refine' Nat.ceil_le.mpr _;
    have h_det_bound : ((n : ℝ) + 1) * (z.den : ℝ) * ((z : ℝ) - x) ≤ 4 * ((n : ℝ) + 1) * (Q : ℝ) / Real.sqrt n := by
      have h_det_bound : ((z : ℝ) - x) < 2 / (x.den : ℝ) := by
        have h_det_bound : (elemR x : ℝ) - x < 2 / (x.den : ℝ) := by
          unfold elemR; norm_num; ring_nf;
          have := badly_left_facts h; rcases this with ⟨ hx₀, hx₁, hx₂, hx₃, hx₄, hx₅, hx₆ ⟩ ; rw [ Rat.cast_def ] ; ring_nf ;
          field_simp;
          rw [ div_sub_one, mul_div, div_add_div_same, div_lt_iff₀ ] <;> nlinarith only [ show ( x.den : ℝ ) ≥ 4 by norm_cast, show ( x.num : ℝ ) ≥ 1 by norm_cast, show ( x.num : ℝ ) + 3 ≤ x.den by norm_cast ];
        exact lt_of_le_of_lt ( sub_le_sub_right ( mod_cast hzR.le ) _ ) h_det_bound;
      have h_det_bound : ((n : ℝ) + 1) * (z.den : ℝ) * (2 / (x.den : ℝ)) ≤ 4 * ((n : ℝ) + 1) * (Q : ℝ) / Real.sqrt n := by
        have h_det_bound : (z.den : ℝ) ≤ Q ∧ (x.den : ℝ) ≥ Real.sqrt n := by
          exact ⟨ mod_cast hzF.2.2, Real.sqrt_le_iff.mpr ⟨ by positivity, by norm_cast; linarith ⟩ ⟩;
        field_simp;
        rw [ le_div_iff₀ ] <;> nlinarith [ show 0 < Real.sqrt n by exact Real.sqrt_pos.mpr ( Nat.cast_pos.mpr ( by nlinarith [ pow_succ' Q 2 ] ) ), show ( Q : ℝ ) ≥ 3 by norm_cast, show ( z.den : ℝ ) ≤ Q by exact_mod_cast h_det_bound.1, show ( x.den : ℝ ) ≥ Real.sqrt n by exact_mod_cast h_det_bound.2 ];
      exact le_trans ( mul_le_mul_of_nonneg_left ( le_of_lt ‹_› ) ( by positivity ) ) h_det_bound;
    convert h_det_bound.trans _ using 1;
    · simp +decide [ Rat.cast_def, mul_sub, sub_mul, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ];
    · exact le_trans ( Nat.le_ceil _ ) ( by norm_num [ Kmax ] )
  have h_errTerm_1w_1z : errTerm (1 - elemR x) (1 - z) n ≤ (Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q)) := by
    apply errTerm_le_Kmax;
    refine' ceil_le_Kmax _ _;
    have h_det : ((n : ℝ) + 1) / (1 - elemR x).den * ((1 - z).num * (1 - elemR x).den - (1 - elemR x).num * (1 - z).den : ℤ) = (n + 1) * z.den * ((elemR x : ℝ) - z) := by
      have := det_real_eq ( 1 - elemR x ) ( 1 - z ) ; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
      rw [ ← mul_assoc, mul_div_cancel₀ _ ( Nat.cast_ne_zero.mpr <| Rat.den_nz _ ) ];
    have h_det_bound : (elemR x : ℝ) - z < 2 / x.den := by
      have h_det_bound : (elemR x : ℝ) - x < 2 / x.den := by
        have := badly_left_facts h
        unfold elemR; norm_num; ring_nf;
        rw [ Rat.cast_def ];
        field_simp;
        rw [ div_sub', ← add_div, div_lt_iff₀ ] <;> nlinarith [ show ( x.den : ℝ ) ≥ 4 by norm_cast; linarith, show ( x.num : ℝ ) ≥ 1 by norm_cast; linarith, show ( x.num : ℝ ) + 3 ≤ x.den by norm_cast; linarith ];
      exact lt_of_le_of_lt ( sub_le_sub_left ( mod_cast hxz.le ) _ ) h_det_bound;
    have h_det_bound : (n + 1) * z.den * ((elemR x : ℝ) - z) ≤ (n + 1) * Q * (2 / x.den) := by
      gcongr;
      · exact sub_nonneg_of_le <| mod_cast hzR.le;
      · exact hzF.2.2;
    have h_det_bound : (n + 1) * Q * (2 / x.den) ≤ 4 * (n + 1) * Q / Real.sqrt n := by
      field_simp;
      rw [ le_div_iff₀ ] <;> norm_num;
      · nlinarith only [ show ( n : ℝ ) ≤ x.den * x.den by norm_cast, Real.mul_self_sqrt ( Nat.cast_nonneg n ), show ( x.den : ℝ ) ≥ 1 by exact_mod_cast x.pos ];
      · exact Nat.pos_of_ne_zero ( by rintro rfl; linarith [ pow_pos ( by linarith : 0 < Q ) 3 ] );
    grind +splitImp;
  convert caseA_count n x z _ _ _ _ _ _ _ |> le_trans _ using 1;
  any_goals linarith [ badly_left_facts h ];
  exact_mod_cast Nat.le_succ_of_le ( show x.den ≤ n from by nlinarith [ show x.den ≤ n from by { obtain ⟨ y, hy ⟩ := h; exact hy.1.2.2 } ] )

/-
**Case III-a** (small endpoint on the right). The reference is `gR`, the smaller-denominator
endpoint of the `F_Q`-gap `gL < gR` containing `I`. Apply `caseB_count`.
-/
theorem largeb_caseIIIa {n Q : ℕ} {x gL gR : ℚ} (h : ∃ y, BadlyOrdered n x y)
    (hQ4 : n ≤ Q ^ 4) (hbig : n ≤ x.den * x.den)
    (hgLF : IsFarey Q gL) (hgRF : IsFarey Q gR)
    (hgLx : gL < x) (hRgR : elemR x < gR)
    (hdet : (gL.den : ℤ) * gR.num - gL.num * (gR.den : ℤ) = 1)
    (hsum : Q < gL.den + gR.den) (hle : gR.den ≤ gL.den) :
    (n : ℝ) / 4 - 2 * ((Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q))) - 1
      ≤ (betweenCount n x (elemR x) : ℝ) := by
  -- Let's obtain the facts from `badly_left_facts` regarding `x`.
  obtain ⟨hx0, hxR, hRz, hb, hle, ha, hab⟩ := badly_left_facts h;
  refine' le_trans _ ( _ : ( betweenCount n x ( elemR x ) : ℝ ) ≥ _ );
  exact ( n : ℝ ) / 4 - errTerm x gR n - errTerm ( elemR x ) gR n - 1;
  · -- Apply the error bounds from `errTerm_le_Kmax`.
    have h_err1 : errTerm x gR n ≤ (Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q)) := by
      apply errTerm_le_Kmax;
      refine' ceil_le_Kmax _ _;
      -- By simplifying, we can see that this inequality holds.
      have h_simplified : (gR.num * x.den - x.num * gR.den : ℝ) ≤ 4 * Q * x.den / Real.sqrt n := by
        have h_det_le : (gR.num * x.den - x.num * gR.den : ℝ) ≤ gR.den * x.den * (1 / (gL.den * gR.den : ℝ)) := by
          have h_det_le : (gR.num * x.den - x.num * gR.den : ℝ) ≤ gR.den * x.den * ((gR : ℝ) - (gL : ℝ)) := by
            rw [ Rat.cast_def, Rat.cast_def ] at *;
            field_simp;
            nlinarith [ show ( gL.num : ℝ ) * x.den < x.num * gL.den from by rw [ ← @Rat.num_div_den gL, ← @Rat.num_div_den x ] at hgLx; rw [ div_lt_div_iff₀ ] at hgLx <;> norm_cast at * <;> linarith [ Rat.pos x, Rat.pos gL ] ];
          have h_det_le : (gR : ℝ) - (gL : ℝ) = 1 / (gL.den * gR.den : ℝ) := by
            rw [ Rat.cast_def, Rat.cast_def ];
            rw [ div_sub_div ] <;> try positivity;
            exact congrArg₂ _ ( by norm_cast; linarith ) ( by ring );
          aesop;
        refine le_trans h_det_le ?_;
        rw [ mul_one_div, div_le_div_iff₀ ] <;> try positivity;
        · -- By simplifying, we can see that this inequality holds because $gL.den \geq Q/2$ and $gR.den \leq Q$.
          have h_simplified : Real.sqrt n ≤ 4 * Q * gL.den := by
            rw [ Real.sqrt_le_left ] <;> norm_cast;
            · exact hQ4.trans ( by nlinarith only [ show Q ^ 2 ≤ 4 * Q * gL.den by nlinarith only [ hsum, ‹gR.den ≤ gL.den›, hgLF.2.2, hgRF.2.2 ] ] );
            · positivity;
          convert mul_le_mul_of_nonneg_left h_simplified ( show ( 0 : ℝ ) ≤ gR.den * x.den by positivity ) using 1 ; ring;
        · exact Real.sqrt_pos.mpr ( Nat.cast_pos.mpr ( by linarith ) );
      convert mul_le_mul_of_nonneg_left h_simplified ( show ( 0 : ℝ ) ≤ ( n + 1 ) / x.den by positivity ) using 1 ; ring;
      · push_cast; ring;
      · ring ; norm_num [ ne_of_gt ( Rat.pos _ ) ]
    have h_err2 : errTerm (elemR x) gR n ≤ (Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q)) := by
      apply errTerm_le_Kmax;
      refine' ceil_le_Kmax _ _;
      -- By simplifying, we can see that the inequality holds.
      have h_simplify : (n + 1 : ℝ) * gR.den * ((gR : ℝ) - (elemR x : ℝ)) ≤ 4 * (n + 1) * Q / Real.sqrt n := by
        have h_simplify : (gR : ℝ) - (elemR x : ℝ) ≤ 1 / (gL.den * gR.den : ℝ) := by
          have h_simplify : (gR - gL : ℝ) = 1 / (gL.den * gR.den : ℝ) := by
            rw [ Rat.cast_def, Rat.cast_def ];
            rw [ div_sub_div ] <;> norm_cast <;> norm_num [ Rat.den_nz ];
            rw [ show gR.num * gL.den - gR.den * gL.num = 1 by linarith ] ; norm_num [ Rat.divInt_eq_div ] ; ring;
          linarith [ show ( gL : ℝ ) ≤ x from mod_cast hgLx.le, show ( elemR x : ℝ ) ≥ x from mod_cast hxR.le ];
        refine le_trans ( mul_le_mul_of_nonneg_left h_simplify <| by positivity ) ?_;
        rw [ mul_one_div, div_le_div_iff₀ ] <;> try positivity;
        · -- By simplifying, we can see that the inequality holds because $Q \geq 3$ and $n \leq Q^4$.
          have h_simplify : Real.sqrt n ≤ 4 * Q * gL.den := by
            rw [ Real.sqrt_le_left ] <;> norm_cast <;> try nlinarith only [ hQ4, hsum, ‹gR.den ≤ gL.den› ] ;
            exact hQ4.trans ( by nlinarith only [ show Q ^ 2 ≤ 4 * Q * gL.den by nlinarith only [ hsum, ‹gR.den ≤ gL.den›, hgLF.2.2, hgRF.2.2 ] ] );
          nlinarith [ show 0 ≤ ( n + 1 : ℝ ) * gR.den by positivity ];
        · exact Real.sqrt_pos.mpr ( Nat.cast_pos.mpr ( by linarith ) );
      convert h_simplify using 1;
      rw [ div_mul_eq_mul_div, div_eq_iff ] <;> norm_cast <;> norm_num [ Rat.cast_def ] ; ring;
      rw [ ← Rat.mul_den_eq_num, ← Rat.mul_den_eq_num ] ; ring;
    linarith;
  · apply caseB_count n x gR hx0.le hxR hRgR hgRF.2.1;
    · norm_cast;
    · convert elemR_sub_gt hx0 hxR hb ha hab |> le_of_lt using 1;
    · -- By `det_real_eq`, we have `(gR.num * (x.den : ℤ) - x.num * (gR.den : ℤ) : ℝ) = (gR.den : ℝ) * (x.den : ℝ) * ((gR : ℝ) - (x : ℝ))`.
      have h_det_real : (gR.num * (x.den : ℤ) - x.num * (gR.den : ℤ) : ℝ) = (gR.den : ℝ) * (x.den : ℝ) * ((gR : ℝ) - (x : ℝ)) := by
        simp +decide [ mul_sub, Rat.cast_def ];
        simp +decide [ mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv, ne_of_gt ( Rat.pos _ ) ];
      have h_det_ge_two : (gR.num * (x.den : ℤ) - x.num * (gR.den : ℤ) : ℝ) ≥ 2 := by
        have h_det_ge_two : (gR.num * (x.den : ℤ) - x.num * (gR.den : ℤ) : ℝ) > (gR.den : ℝ) := by
          have h_det_ge_two : (gR : ℝ) - (x : ℝ) > 1 / (x.den : ℝ) := by
            have h_det_ge_two : (elemR x : ℝ) - (x : ℝ) > 1 / (x.den : ℝ) := by
              convert elemR_sub_gt hx0 hxR hb ha hab using 1;
            exact h_det_ge_two.trans_le ( sub_le_sub_right ( mod_cast hRgR.le ) _ );
          simp_all +decide [ div_eq_mul_inv ];
          rw [ inv_eq_one_div, div_lt_iff₀ ] at h_det_ge_two <;> nlinarith [ show ( x.den : ℝ ) ≥ 4 by norm_cast, show ( gR.den : ℝ ) ≥ 1 by exact_mod_cast gR.pos ];
        norm_cast at *;
        linarith [ show gR.den ≥ 1 from gR.pos ];
      nlinarith [ show ( x.den : ℝ ) ≤ n by norm_cast ]

/-- Clean error bound: for any `p q`, if `(n+1)·q.den·(q−p)` is below the uniform threshold then
`errTerm p q n ≤ Kmax·(1+log Kmax)`. (Uses `det_real_eq` to rewrite the defining ceiling.) -/
theorem errTerm_le_Kmax' {n Q : ℕ} (p q : ℚ)
    (hM : ((n : ℝ) + 1) * (q.den : ℝ) * ((q : ℝ) - (p : ℝ))
            ≤ (4 * ((n : ℝ) + 1) * (Q : ℝ)) / Real.sqrt n) :
    errTerm p q n ≤ (Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q)) := by
  apply errTerm_le_Kmax
  apply ceil_le_Kmax
  have hp : (p.den : ℝ) ≠ 0 := by exact_mod_cast p.den_nz
  rw [show ((n : ℝ) + 1) / p.den
        * ((q.num * (p.den : ℤ) - p.num * (q.den : ℤ) : ℤ) : ℝ)
        = ((n : ℝ) + 1) * (q.den : ℝ) * ((q : ℝ) - (p : ℝ)) from by
    rw [det_real_eq p q]; field_simp]
  exact hM

/-
The `h2X` lower bound for the left-reference Case III-b: `2 ≤ (n+1)·gL.den·(elemR x − gL)`.
-/
theorem h2X_left {n : ℕ} {x gL : ℚ} (h : ∃ y, BadlyOrdered n x y) (hgLx : gL < x) :
    (2 : ℝ) ≤ ((n : ℝ) + 1) * (gL.den : ℝ) * ((elemR x : ℝ) - (gL : ℝ)) := by
  -- From badly_left_facts h: 0<x, x<elemR x, elemR x<1, 4≤x.den, x.den≤n, 1≤x.num, x.num+3≤x.den.
  obtain ⟨hx_pos, hx_lt_elemR, h_elemR_lt_one, hx_den_ge_4, hx_den_le_n, hx_num_ge_1, hx_num_plus_3_le_den⟩ := badly_left_facts h;
  -- From STEP 2: (elemR x:ℝ) - (gL:ℝ) = (RW:ℝ)/(((b:ℝ)-1)*(s:ℝ)), and RW ≥ 2.
  have h_RW_ge_2 : (x.num + 1) * (gL.den : ℤ) - gL.num * (x.den - 1) ≥ 2 := by
    have h_RW_ge_2 : (x.num + 1) * (gL.den : ℝ) - gL.num * (x.den - 1) ≥ (gL.den : ℝ) * ((x.num + x.den) / x.den) := by
      have h_RW_ge_2 : (x.num + 1 : ℝ) / (x.den - 1) - gL.num / gL.den ≥ (x.num + x.den : ℝ) / (x.den * (x.den - 1)) := by
        have h_RW_ge_2 : (gL.num : ℝ) / gL.den ≤ x.num / x.den := by
          rw [ div_le_div_iff₀ ] <;> norm_cast;
          · simpa [ Rat.le_iff ] using hgLx.le;
          · exact gL.pos;
          · grind;
        refine le_trans ?_ ( sub_le_sub_left h_RW_ge_2 _ );
        rw [ div_sub_div, div_le_div_iff₀ ] <;> nlinarith [ show ( x.den : ℝ ) ≥ 4 by norm_cast, show ( x.num : ℝ ) ≥ 1 by norm_cast, show ( x.den : ℝ ) ≥ x.num + 3 by norm_cast ];
      field_simp at h_RW_ge_2;
      rw [ div_le_iff₀ ] at h_RW_ge_2 <;> nlinarith [ show ( x.den : ℝ ) ≥ 4 by norm_cast, mul_div_cancel₀ ( ( x.num + x.den : ℝ ) ) ( show ( x.den : ℝ ) ≠ 0 by positivity ), mul_div_cancel₀ ( ( x.num + 1 : ℝ ) * gL.den ) ( show ( x.den - 1 : ℝ ) ≠ 0 by exact sub_ne_zero_of_ne ( by norm_cast; linarith ) ) ];
    have h_RW_ge_2 : (gL.den : ℝ) * ((x.num + x.den) / x.den) > 1 := by
      field_simp;
      exact_mod_cast ( by nlinarith [ show ( gL.den : ℤ ) ≥ 1 from mod_cast gL.pos ] : ( x.den : ℤ ) < gL.den * ( x.num + x.den ) );
    exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith )
  -- From STEP 3: ((n:ℝ)+1)*(s:ℝ)*((elemR x:ℝ)-gL) = ((n:ℝ)+1)*(RW:ℝ)/((b:ℝ)-1)
  have h_eq : ((n : ℝ) + 1) * (gL.den : ℝ) * ((elemR x : ℝ) - gL) = ((n : ℝ) + 1) * ((x.num + 1) * (gL.den : ℤ) - gL.num * (x.den - 1) : ℝ) / ((x.den : ℝ) - 1) := by
    unfold elemR; push_cast; rw [ div_sub', mul_div_assoc' ];
    · rw [ Rat.cast_def ] ; ring;
      simpa [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( Rat.pos _ ) ] using by ring;
    · linarith [ show ( x.den : ℝ ) ≥ 4 by norm_cast ];
  rw [ h_eq, le_div_iff₀ ] <;> norm_cast;
  · rw [ Int.subNatNat_eq_coe ] ; push_cast ; nlinarith;
  · rw [ Int.subNatNat_eq_coe ] ; norm_num ; linarith

/-
**Case III-b** (small endpoint on the left). The reference is `gL`. Apply `caseB_count_left`.
-/
theorem largeb_caseIIIb {n Q : ℕ} {x gL gR : ℚ} (h : ∃ y, BadlyOrdered n x y)
    (hQ4 : n ≤ Q ^ 4) (hbig : n ≤ x.den * x.den)
    (hgLF : IsFarey Q gL) (hgRF : IsFarey Q gR)
    (hgLx : gL < x) (hRgR : elemR x < gR)
    (hdet : (gL.den : ℤ) * gR.num - gL.num * (gR.den : ℤ) = 1)
    (hsum : Q < gL.den + gR.den) (hle : gL.den ≤ gR.den) :
    (n : ℝ) / 4 - 2 * ((Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q))) - 1
      ≤ (betweenCount n x (elemR x) : ℝ) := by
  have := @caseB_count_left n x gL;
  specialize this (by
  exact hgLF.1) hgLx (by
  exact ( badly_left_facts h ) |>.2.2.1.le |> le_trans <| by norm_num;) (by
  have := badly_left_facts h; aesop;) (by
  exact_mod_cast h.choose_spec.1.2.2) (by
  have := badly_left_facts h;
  exact elemR_sub_gt this.1 this.2.1 this.2.2.2.1 this.2.2.2.2.2.1 this.2.2.2.2.2.2 |> le_of_lt) (by
  convert h2X_left h hgLx using 1);
  have h2 : ((n + 1) : ℝ) * (gL.den : ℝ) * ((elemR x : ℝ) - (gL : ℝ)) ≤ 4 * ((n + 1) : ℝ) * (Q : ℝ) / Real.sqrt n := by
    have h2 : ((n + 1) : ℝ) * (gL.den : ℝ) * ((elemR x : ℝ) - (gL : ℝ)) ≤ (n + 1) / (gR.den : ℝ) := by
      have h2 : ((elemR x : ℝ) - (gL : ℝ)) ≤ 1 / ((gL.den : ℝ) * (gR.den : ℝ)) := by
        have h2 : ((gR : ℝ) - (gL : ℝ)) = 1 / (gL.den * gR.den : ℝ) := by
          rw [ eq_div_iff ] <;> norm_cast at * <;> simp_all +decide [ Rat.cast_def ];
          rw [ Rat.sub_def' ];
          simp +decide [ mul_comm, Rat.mkRat_eq_div, hdet ];
          rw [ mul_div_cancel₀ _ ( by norm_cast; aesop ) ] ; norm_cast ; linarith;
        exact h2 ▸ sub_le_sub_right ( mod_cast hRgR.le ) _;
      convert mul_le_mul_of_nonneg_left h2 ( show ( 0 : ℝ ) ≤ ( n + 1 ) * gL.den by positivity ) using 1 ; ring;
      norm_num [ hgLF.2.2, hgRF.2.2 ];
    have h3 : (n + 1) / (gR.den : ℝ) ≤ 2 * (n + 1) / (Q : ℝ) := by
      rw [ div_le_div_iff₀ ] <;> norm_cast;
      · nlinarith;
      · exact gR.pos;
      · rcases Q with ( _ | _ | Q ) <;> norm_num at *;
        cases hgLF ; cases hgRF ; aesop;
    refine le_trans h2 <| h3.trans ?_;
    rcases n with ( _ | _ | n ) <;> norm_num at *;
    · obtain ⟨ y, hy ⟩ := h;
      have := hy.1.2.2; aesop;
    · rcases Q with ( _ | _ | Q ) <;> norm_num at *;
      rw [ div_le_iff₀ ] <;> nlinarith only [ sq ( Q : ℝ ) ];
    · rw [ div_le_div_iff₀ ] <;> try positivity;
      · have h4 : (Q : ℝ) ^ 2 ≥ Real.sqrt (n + 1 + 1) := by
          exact Real.sqrt_le_iff.mpr ⟨ by positivity, by norm_cast; nlinarith ⟩;
        nlinarith only [ h4, Real.sqrt_nonneg ( n + 1 + 1 : ℝ ), Real.mul_self_sqrt ( show ( n : ℝ ) + 1 + 1 ≥ 0 by positivity ) ];
      · exact Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at hQ4 ) );
  have h3 : ((n + 1) : ℝ) * (gL.den : ℝ) * ((x : ℝ) - (gL : ℝ)) ≤ 4 * ((n + 1) : ℝ) * (Q : ℝ) / Real.sqrt n := by
    refine le_trans ?_ h2;
    gcongr;
    exact le_of_lt ( badly_left_facts h |>.2.1 );
  have h4 : errTerm (1 - elemR x) (1 - gL) n ≤ (Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q)) := by
    apply errTerm_le_Kmax';
    convert h2 using 1;
    rw [ one_sub_den ] ; ring;
    norm_num ; ring
  have h5 : errTerm (1 - x) (1 - gL) n ≤ (Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q)) := by
    apply errTerm_le_Kmax';
    convert h3 using 1 ; norm_num [ one_sub_den ]
  linarith [h4, h5]

/-- **Large-`b`, Case III.** No order-`Q` Farey fraction lies inside `I` and `(elemR x).den > Q`.
The interval lies in a single gap `gL < gR` of `F_Q`; use `caseB_count` / `caseB_count_left`
with the smaller-denominator endpoint. -/
theorem largeb_caseIII {n Q : ℕ} {x : ℚ} (h : ∃ y, BadlyOrdered n x y)
    (hQ : 3 ≤ Q) (hQ3 : Q ^ 3 ≤ n) (hQ4 : n ≤ Q ^ 4)
    (hQb : Q < x.den) (hbig : n ≤ x.den * x.den)
    (hsw : Q < (elemR x).den)
    (hno : ∀ f : ℚ, IsFarey Q f → x < f → f < elemR x → False) :
    (n : ℝ) / 4 - 2 * ((Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q))) - 1
      ≤ (betweenCount n x (elemR x) : ℝ) := by
  obtain ⟨hx0', hxw, hw1', hb, hbn, ha, hab⟩ := badly_left_facts h
  obtain ⟨gL, gR, hgLF, hgRF, hgLx0, hRgR0, hgLR, hgap⟩ :=
    farey_gap_between Q (by omega) x (elemR x) (le_of_lt hx0') (le_of_lt hw1') hxw hno
  have hdet := farey_neighbor_det hgLF hgRF hgLR hgap
  have hsum := farey_neighbor_den_sum hgLF hgRF hgLR hgap
  have hgLx : gL < x := by
    rcases lt_or_eq_of_le hgLx0 with hlt | heq
    · exact hlt
    · exfalso; have : gL.den ≤ Q := hgLF.2.2; rw [heq] at this; omega
  have hRgR : elemR x < gR := by
    rcases lt_or_eq_of_le hRgR0 with hlt | heq
    · exact hlt
    · exfalso; have : gR.den ≤ Q := hgRF.2.2; rw [← heq] at this; omega
  by_cases hcase : gR.den ≤ gL.den
  · exact largeb_caseIIIa h hQ4 hbig hgLF hgRF hgLx hRgR hdet hsum hcase
  · push_neg at hcase
    exact largeb_caseIIIb h hQ4 hbig hgLF hgRF hgLx hRgR hdet hsum (le_of_lt hcase)

/-- **Large-`b` core.** With `Q^3 ≤ n ≤ Q^4`, `Q < b`, and `n ≤ b*b`, the elementary-interval
count is at least `n/4` minus twice the uniform error `Kmax n Q · (1 + log (Kmax n Q))`. -/
theorem largeb_core {n Q : ℕ} {x : ℚ} (h : ∃ y, BadlyOrdered n x y)
    (hQ : 3 ≤ Q) (hQ3 : Q ^ 3 ≤ n) (hQ4 : n ≤ Q ^ 4)
    (hQb : Q < x.den) (hbig : n ≤ x.den * x.den) :
    (n : ℝ) / 4 - 2 * ((Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q))) - 1
      ≤ (betweenCount n x (elemR x) : ℝ) := by
  by_cases hsw : (elemR x).den ≤ Q
  · exact largeb_caseI h hQ hQ3 hbig hsw
  · push_neg at hsw
    by_cases hex : ∃ z : ℚ, IsFarey Q z ∧ x < z ∧ z < elemR x
    · obtain ⟨z, hzF, hxz, hzR⟩ := hex
      exact largeb_caseII h hQ hQ3 hbig z hzF hxz hzR
    · exact largeb_caseIII h hQ hQ3 hQ4 hQb hbig hsw
        (fun f hf h1 h2 => hex ⟨f, hf, h1, h2⟩)

/-
`Kmax n Q ≤ Kbar n` whenever `Q^3 ≤ n`.
-/
theorem Kmax_le_Kbar {n Q : ℕ} (hn : 1 ≤ n) (hQ3 : Q ^ 3 ≤ n) : Kmax n Q ≤ Kbar n := by
  -- It suffices to show that $Q \leq n^{1/3}$.
  have hQ_le_n13 : (Q : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
    exact le_trans ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( Nat.cast_nonneg Q ) ] ; norm_num ) ( Real.rpow_le_rpow ( by positivity ) ( show ( Q : ℝ ) ^ 3 ≤ n by exact_mod_cast hQ3 ) ( by positivity ) );
  refine' Nat.add_le_add_right ( Nat.ceil_mono _ ) 2;
  gcongr

/-
Small-`b` eventual estimate.
-/
theorem smallb_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (1 / 4 - ε) * (n : ℝ) ≤ ((n : ℝ) + 1) * Real.sqrt n / 4 - (n : ℝ) * (1 + Real.log n) := by
  -- We'll use that $Real.log n$ grows slower than any linear function to find such an $N$.
  have h_log_growth : Filter.Tendsto (fun n : ℕ => (Real.log n : ℝ) / Real.sqrt n) Filter.atTop (nhds 0) := by
    -- Let $y = \sqrt{n}$, so we can rewrite the limit as $\lim_{y \to \infty} \frac{\log(y^2)}{y}$.
    suffices h_log_sqrt_y : Filter.Tendsto (fun y : ℝ => Real.log (y^2) / y) Filter.atTop (nhds 0) by
      have := h_log_sqrt_y.comp ( show Filter.Tendsto ( fun n : ℕ => Real.sqrt n ) Filter.atTop ( Filter.atTop ) by simpa only [ Real.sqrt_eq_rpow ] using tendsto_rpow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
      exact this.congr fun n => by rw [ Function.comp_apply, Real.sq_sqrt ( Nat.cast_nonneg _ ) ] ;
    -- Let $z = \frac{1}{y}$, so we can rewrite the limit as $\lim_{z \to 0^+} 2z \log(1/z)$.
    suffices h_log_recip : Filter.Tendsto (fun z : ℝ => 2 * z * Real.log (1 / z)) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
      exact h_log_recip.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] );
    norm_num;
    exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using this.neg.const_mul 2 );
  have := h_log_growth.eventually ( gt_mem_nhds <| show 0 < 1 / 16 by norm_num );
  filter_upwards [ this, Filter.eventually_gt_atTop 0, Filter.eventually_gt_atTop ⌈ ( 16 * ( 1 + ε ) ) ^ 2⌉₊ ] with n hn hn' hn'' ; rw [ div_lt_iff₀ ( by positivity ) ] at hn ; nlinarith [ Nat.le_ceil ( ( 16 * ( 1 + ε ) ) ^ 2 ), show ( n : ℝ ) ≥ ⌈ ( 16 * ( 1 + ε ) ) ^ 2⌉₊ + 1 by exact_mod_cast hn'', Real.sqrt_nonneg n, Real.sq_sqrt <| Nat.cast_nonneg n, mul_self_nonneg <| Real.sqrt n - ( 16 * ( 1 + ε ) ) ] ;

/-
Large-`b` eventual estimate: the uniform error is eventually `≤ ε n`.
-/
theorem largeb_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      2 * ((Kbar n : ℝ) * (1 + Real.log (Kbar n))) + 1 ≤ ε * (n : ℝ) := by
  -- To prove the limit is 0, we can use the fact that $n^{-1/6} \cdot \log n \to 0$ as $n \to \infty$.
  have h_log_div_n : Filter.Tendsto (fun n : ℕ => (1 + Real.log (4 * (n : ℝ) + 7)) / (n : ℝ) ^ (1 / 6 : ℝ)) Filter.atTop (nhds 0) := by
    -- We can use the fact that $\frac{\log(n)}{n^{1/6}}$ tends to $0$ as $n$ tends to infinity.
    have h_log_div_n : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ) ^ (1 / 6 : ℝ)) Filter.atTop (nhds 0) := by
      -- Let $y = \frac{1}{n^{1/6}}$, so we can rewrite the limit as $\lim_{y \to 0^+} y \log(1/y^6)$.
      suffices h_log_recip : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y^6)) (Filter.map (fun n => 1 / (n : ℝ) ^ (1 / 6 : ℝ)) Filter.atTop) (nhds 0) by
        rw [ Filter.tendsto_map'_iff ] at h_log_recip;
        refine h_log_recip.comp tendsto_natCast_atTop_atTop |> Filter.Tendsto.congr' ?_ ; filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn ; norm_num [ Real.rpow_neg, hn.ne' ] ; ring;
        rw [ Real.log_rpow ( by positivity ) ] ; ring;
      norm_num;
      refine' Filter.Tendsto.comp _ ( tendsto_inv_atTop_zero.comp ( tendsto_rpow_atTop ( by norm_num ) ) );
      have := Real.continuous_mul_log.tendsto 0 ; convert this.neg.const_mul 6 using 2 <;> ring;
    -- We can use the fact that $\frac{\log(4n+7)}{n^{1/6}}$ tends to $0$ as $n$ tends to infinity.
    have h_log_div_n : Filter.Tendsto (fun n : ℕ => Real.log (4 * (n : ℝ) + 7) / (n : ℝ) ^ (1 / 6 : ℝ)) Filter.atTop (nhds 0) := by
      have h_log_div_n : Filter.Tendsto (fun n : ℕ => (Real.log (n : ℝ) + Real.log (4 + 7 / (n : ℝ))) / (n : ℝ) ^ (1 / 6 : ℝ)) Filter.atTop (nhds 0) := by
        simpa [ add_div ] using h_log_div_n.add ( Filter.Tendsto.div_atTop ( Filter.Tendsto.log ( tendsto_const_nhds.add ( tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop ) ) ( by norm_num ) ) ( tendsto_rpow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop ) );
      refine h_log_div_n.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ ← Real.log_mul ( by positivity ) ( by positivity ), mul_add, mul_div_cancel₀ _ ( by positivity ) ] ; ring );
    simpa [ add_div ] using Filter.Tendsto.add ( tendsto_inv_atTop_zero.comp ( tendsto_rpow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop ) ) h_log_div_n;
  -- Using the bound on $K(n)$, we can show that the expression tends to 0.
  have h_bound : Filter.Tendsto (fun n : ℕ => (2 * ((4 * ((n : ℝ) + 1) * (n : ℝ) ^ (1 / 3 : ℝ) / Real.sqrt n + 3) * (1 + Real.log (4 * (n : ℝ) + 7)) + 1) : ℝ) / (n : ℝ)) Filter.atTop (nhds 0) := by
    -- Simplify the expression inside the limit.
    suffices h_simplify : Filter.Tendsto (fun n : ℕ => (8 * (1 + 1 / (n : ℝ)) * (1 + Real.log (4 * (n : ℝ) + 7)) / (n : ℝ) ^ (1 / 6 : ℝ) + 6 * (1 + Real.log (4 * (n : ℝ) + 7)) / (n : ℝ) + 2 / (n : ℝ))) Filter.atTop (nhds 0) by
      refine h_simplify.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn ; norm_num [ Real.sqrt_eq_rpow, Real.rpow_neg, hn.ne', le_of_lt hn ] ; ring;
      norm_num [ ← Real.rpow_neg ( Nat.cast_nonneg _ ), ← Real.rpow_add ( Nat.cast_pos.mpr hn ), hn.ne' ] ; ring;
      norm_num [ mul_assoc, ← Real.rpow_add ( Nat.cast_pos.mpr hn ) ];
    -- We'll use the fact that $n^{-1/6} \cdot \log n \to 0$ as $n \to \infty$.
    have h_log_div_n : Filter.Tendsto (fun n : ℕ => (1 + Real.log (4 * (n : ℝ) + 7)) / (n : ℝ)) Filter.atTop (nhds 0) := by
      refine' squeeze_zero_norm' _ h_log_div_n;
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn using by rw [ Real.norm_of_nonneg ( by exact div_nonneg ( add_nonneg zero_le_one ( Real.log_nonneg ( by linarith ) ) ) ( Nat.cast_nonneg _ ) ) ] ; exact div_le_div_of_nonneg_left ( by exact add_nonneg zero_le_one ( Real.log_nonneg ( by linarith ) ) ) ( by positivity ) ( by exact le_trans ( Real.rpow_le_rpow_of_exponent_le ( by norm_cast; linarith ) ( show ( 1 : ℝ ) / 6 ≤ 1 by norm_num ) ) ( by norm_num ) ) ;
    simpa [ mul_div_assoc ] using Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.mul ( tendsto_const_nhds.mul ( tendsto_const_nhds.add ( tendsto_one_div_atTop_nhds_zero_nat ) ) ) ‹Tendsto ( fun n : ℕ => ( 1 + Real.log ( 4 * ↑n + 7 ) ) / ↑n ^ ( 1 / 6 : ℝ ) ) atTop ( 𝓝 0 ) › ) ( Filter.Tendsto.const_mul 6 h_log_div_n ) ) ( tendsto_const_nhds.mul tendsto_inv_atTop_nhds_zero_nat );
  have h_bound : ∀ᶠ n in Filter.atTop, (2 * (Kbar n * (1 + Real.log (Kbar n)) + 1) : ℝ) / (n : ℝ) ≤ (2 * ((4 * ((n : ℝ) + 1) * (n : ℝ) ^ (1 / 3 : ℝ) / Real.sqrt n + 3) * (1 + Real.log (4 * (n : ℝ) + 7)) + 1) : ℝ) / (n : ℝ) := by
    have h_bound : ∀ᶠ n in Filter.atTop, Kbar n ≤ 4 * ((n : ℝ) + 1) * (n : ℝ) ^ (1 / 3 : ℝ) / Real.sqrt n + 3 := by
      refine' Filter.eventually_atTop.mpr ⟨ 1, fun n hn => _ ⟩ ; norm_num [ Kbar ];
      linarith [ Nat.ceil_lt_add_one ( show 0 ≤ 4 * ( n + 1 : ℝ ) * n ^ ( 1 / 3 : ℝ ) / Real.sqrt n by positivity ) ];
    filter_upwards [ h_bound, Filter.eventually_gt_atTop 0 ] with n hn hn' ; gcongr;
    · exact Nat.cast_pos.mpr ( Nat.succ_pos _ );
    · refine le_trans hn ?_;
      rw [ div_add', div_le_iff₀ ] <;> try positivity;
      nlinarith only [ show ( n : ℝ ) ≥ 1 by exact_mod_cast hn', show ( n : ℝ ) ^ ( 1 / 3 : ℝ ) ≤ Real.sqrt n by rw [ Real.sqrt_eq_rpow ] ; exact Real.rpow_le_rpow_of_exponent_le ( by norm_cast ) ( by norm_num ), Real.sqrt_nonneg n, Real.sq_sqrt ( Nat.cast_nonneg n ) ];
  filter_upwards [ h_bound, ‹Filter.Tendsto ( fun n : ℕ => 2 * ( ( 4 * ( n + 1 ) * n ^ ( 1 / 3 : ℝ ) / Real.sqrt n + 3 ) * ( 1 + Real.log ( 4 * n + 7 ) ) + 1 ) / n ) atTop ( nhds 0 ) ›.eventually ( gt_mem_nhds hε ), Filter.eventually_gt_atTop 0 ] with n hn hn' hn'' using by rw [ div_le_iff₀ ( by positivity ) ] at hn; nlinarith [ show ( n : ℝ ) ≥ 1 by exact_mod_cast hn'' ] ;

/-
Monotonicity of `t ↦ t·(1 + log t)` on `[1, ∞)`.
-/
theorem mul_one_add_log_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    a * (1 + Real.log a) ≤ b * (1 + Real.log b) := by
  nlinarith [ Real.log_nonneg ha, Real.log_le_log ( by linarith ) hab ]

/-- **Sections 2–9 core.** For every `ε > 0`, eventually every badly-ordered left endpoint has
at least `(1/4 - ε) n` order-`n` Farey fractions in its elementary interval. -/
theorem elem_interval_count_lower_final :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ x : ℚ,
      (∃ y, BadlyOrdered n x y) → (1 / 4 - ε) * (n : ℝ) ≤ (betweenCount n x (elemR x) : ℝ) := by
  intro ε hε
  have hlog : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [smallb_eventually hε, largeb_eventually hε,
    eventually_ge_atTop 81] with n hsmallE hlargeE hn81
  intro x hx
  by_cases hcase : x.den * x.den < n
  · -- small b
    have := smallb_bound hx hcase
    linarith
  · -- large b: n ≤ b*b
    have hbig : n ≤ x.den * x.den := by omega
    obtain ⟨Q, hQ, hQ3, hQ4⟩ := largeb_Q_exists n hn81
    obtain ⟨-, -, -, hb4, -, -, -⟩ := badly_left_facts hx
    -- Q < b : since Q^3 ≤ n ≤ b*b and b ≥ 4 we get Q < b
    have hQb : Q < x.den := by
      by_contra hle
      push_neg at hle
      have h1 : x.den ^ 3 ≤ Q ^ 3 := Nat.pow_le_pow_left hle 3
      have h2 : x.den ^ 3 ≤ x.den * x.den := le_trans (le_trans h1 hQ3) hbig
      nlinarith [hb4]
    have hcore := largeb_core hx hQ hQ3 hQ4 hQb hbig
    have hKle : Kmax n Q ≤ Kbar n := Kmax_le_Kbar (by omega) hQ3
    -- monotonicity of t*(1+log t) to pass from Kmax to Kbar
    have hKmax1 : (1 : ℝ) ≤ (Kmax n Q : ℝ) := by
      have : 2 ≤ Kmax n Q := by unfold Kmax; omega
      exact_mod_cast le_trans (by norm_num) this
    have hmono : (Kmax n Q : ℝ) * (1 + Real.log (Kmax n Q))
        ≤ (Kbar n : ℝ) * (1 + Real.log (Kbar n)) :=
      mul_one_add_log_mono hKmax1 (by exact_mod_cast hKle)
    linarith [hcore, hlargeE, hmono]

/-- **Lower bound (Sections 1–9).** For every `ε > 0`, eventually `f(n) ≥ (1/4 - ε) n`.

Every badly ordered pair contains its elementary interval (`betweenCount_ge_elementary`), so
the count for any pair is at least the elementary-interval count, which is `≥ (1/4 - ε) n` by
`elem_interval_count_lower_final`. Since for `n ≥ 4` the set of badly ordered pairs is nonempty
(`badlyOrdered_construction`), `f(n) = sInf` is attained and inherits the bound. -/
theorem fVal_lower_bound :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (1 / 4 - ε) * (n : ℝ) ≤ (fVal n : ℝ) := by
  intro ε hε
  have hbig : ∀ᶠ n : ℕ in atTop, 4 ≤ n := eventually_atTop.2 ⟨4, fun n hn => hn⟩
  filter_upwards [elem_interval_count_lower_final ε hε, hbig] with n hcore hn4
  set m := n / 4 with hmdef
  have hm1 : 1 ≤ m := by omega
  have hmle : 4 * m ≤ n := by omega
  have hbad := badlyOrdered_construction n m hm1 hmle
  set S := {k | ∃ x y, BadlyOrdered n x y ∧ betweenCount n x y = k} with hS
  have hSne : S.Nonempty := ⟨betweenCount n (Lf m) (Rf m), Lf m, Rf m, hbad, rfl⟩
  have hmem : fVal n ∈ S := Nat.sInf_mem hSne
  obtain ⟨x, y, hxy, hcount⟩ := hmem
  have h1 : betweenCount n x (elemR x) ≤ betweenCount n x y := betweenCount_ge_elementary hxy
  have h2 : (1 / 4 - ε) * (n : ℝ) ≤ (betweenCount n x (elemR x) : ℝ) := hcore x ⟨y, hxy⟩
  have h3 : (betweenCount n x (elemR x) : ℝ) ≤ (betweenCount n x y : ℝ) := by exact_mod_cast h1
  have h4 : (betweenCount n x y : ℝ) = (fVal n : ℝ) := by exact_mod_cast hcount
  linarith [h2, h3, h4.ge, h4.le]

end Erdos1005