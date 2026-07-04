import Mathlib

open scoped BigOperators
open ArithmeticFunction

namespace Erdos1005

/-
**Möbius–totient identity (real form).** For `n ≥ 1`,
`∑_{d ∣ n} μ(d)/d = φ(n)/n`. This is the divided form of the Möbius inversion of
`n = ∑_{d ∣ n} φ(d)` (`Nat.sum_totient`).
-/
theorem moebius_div_sum_eq_totient_div (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ))
      = (Nat.totient n : ℝ) / (n : ℝ) := by
  convert congr_arg ( fun x : ℝ => x / n ) ( show ∑ d ∈ n.divisors, ( ArithmeticFunction.moebius d : ℝ ) * ( n / d : ℕ ) = ( Nat.totient n : ℝ ) from ?_ ) using 1;
  · rw [ Finset.sum_div _ _ _ ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rw [ Nat.cast_div ( Nat.dvd_of_mem_divisors hx ) ] ; ring ; aesop;
    aesop;
  · have := @ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq ℤ;
    specialize @this ( by infer_instance ) ( fun n => Nat.totient n ) ( fun n => n ) ; norm_cast at *;
    convert this.mp ( fun n hn => Nat.sum_totient n ) n hn using 1;
    rw [ ← Nat.sum_divisorsAntidiagonal fun x y => ( moebius x : ℝ ) * ( y : ℝ ) ] ; norm_cast

/-
**Residue-class interval count.** The number of integers `q` with `A < q < B` and
`q ≡ c [ZMOD M]` is within `1` of `(B - A)/M`.
-/
theorem residue_interval_count (M : ℕ) (hM : 1 ≤ M) (c : ℤ) (A B : ℝ) (hAB : A ≤ B) :
    |(({q : ℤ | A < (q : ℝ) ∧ (q : ℝ) < B ∧ (M : ℤ) ∣ (q - c)}.ncard : ℝ) - (B - A) / M)|
      ≤ 1 := by
  -- Let's define the interval $I = (A, B)$ and the residue class $c \pmod{M}$.
  set I := Set.Ioo A B
  set S := {q : ℤ | (q : ℝ) ∈ I ∧ (M : ℤ) ∣ q - c};
  -- The set $S$ is in bijection with the set of integers $k$ such that $⌊α⌋ < k < ⌈β⌉$.
  have h_bij : S = Finset.image (fun k : ℤ => c + M * k) (Finset.Ioo (⌊(A - c) / (M : ℝ)⌋) (⌈(B - c) / (M : ℝ)⌉)) := by
    ext q;
    constructor;
    · intro hq
      obtain ⟨hqI, hqM⟩ := hq
      have hq_div : ∃ k : ℤ, q = c + M * k := by
        exact ⟨ hqM.choose, eq_add_of_sub_eq' hqM.choose_spec ⟩;
      rcases hq_div with ⟨ k, rfl ⟩ ; simp_all +decide [ Int.floor_lt, Int.lt_ceil ];
      exact ⟨ k, ⟨ by rw [ div_lt_iff₀ ( by positivity ) ] ; linarith [ hqI.1 ], by rw [ lt_div_iff₀ ( by positivity ) ] ; linarith [ hqI.2 ] ⟩, Or.inl rfl ⟩;
    · simp +zetaDelta at *;
      rintro x hx₁ hx₂ rfl; exact ⟨ ⟨ by rw [ Int.floor_lt ] at hx₁; rw [ div_lt_iff₀ ( by positivity ) ] at hx₁; norm_num at *; linarith, by rw [ Int.lt_ceil ] at hx₂; rw [ lt_div_iff₀ ( by positivity ) ] at hx₂; norm_num at *; linarith ⟩, by norm_num ⟩ ;
  -- Therefore, the cardinality of $S$ is equal to the cardinality of the interval $(⌊α⌋, ⌈β⌉)$.
  have h_card : Set.ncard S = (⌈(B - c) / (M : ℝ)⌉ - ⌊(A - c) / (M : ℝ)⌋ - 1 : ℤ).toNat := by
    rw [ h_bij, Set.ncard_coe_finset, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective, hM, ne_of_gt ( zero_lt_one.trans_le hM ) ];
  -- Therefore, the cardinality of $S$ is within $1$ of $(B - A)/M$.
  have h_bound : |(⌈(B - c) / (M : ℝ)⌉ - ⌊(A - c) / (M : ℝ)⌋ - 1 : ℤ).toNat - (B - A) / (M : ℝ)| ≤ 1 := by
    rw [ abs_le ] ; constructor <;> cases' h : ⌈ ( B - c ) / M⌉ - ⌊ ( A - c ) / M⌋ - 1 with h <;> norm_num at *;
    · rw [ ← @Int.cast_inj ℝ ] at * ; norm_num at *;
      rw [ div_le_iff₀ ( by positivity ) ];
      nlinarith [ Int.floor_le ( ( A - c ) / M ), Int.lt_floor_add_one ( ( A - c ) / M ), Int.le_ceil ( ( B - c ) / M ), Int.ceil_lt_add_one ( ( B - c ) / M ), show ( M : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ ( A - c ) ( by positivity : ( M : ℝ ) ≠ 0 ), mul_div_cancel₀ ( B - c ) ( by positivity : ( M : ℝ ) ≠ 0 ) ];
    · rw [ div_le_iff₀ ( by positivity ) ];
      rw [ Int.negSucc_eq ] at h ; norm_num at h ; rw [ sub_sub, sub_eq_iff_eq_add ] at h ; norm_num [ Int.ceil_eq_iff, Int.floor_eq_iff ] at *;
      nlinarith [ Int.floor_le ( ( A - c ) / M : ℝ ), Int.lt_floor_add_one ( ( A - c ) / M : ℝ ), show ( M : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ ( B - c ) ( by positivity : ( M : ℝ ) ≠ 0 ), mul_div_cancel₀ ( A - c ) ( by positivity : ( M : ℝ ) ≠ 0 ) ];
    · rw [ ← @Int.cast_inj ℝ ] at * ; norm_num at *;
      nlinarith [ Int.floor_le ( ( A - c ) / M ), Int.lt_floor_add_one ( ( A - c ) / M ), Int.le_ceil ( ( B - c ) / M ), Int.ceil_lt_add_one ( ( B - c ) / M ), show ( M : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ ( B - A ) ( by positivity : ( M : ℝ ) ≠ 0 ), mul_div_cancel₀ ( B - c ) ( by positivity : ( M : ℝ ) ≠ 0 ), mul_div_cancel₀ ( A - c ) ( by positivity : ( M : ℝ ) ≠ 0 ) ];
    · exact le_trans ( neg_nonpos_of_nonneg ( div_nonneg ( sub_nonneg.mpr hAB ) ( Nat.cast_nonneg _ ) ) ) ( by norm_num );
  grind

/-
**Single residue class characterization.** For `d, s ≥ 1`, `h` coprime to `s`, and
`d ∣ e`, the set of `q` satisfying `d ∣ q` and `(s*d) ∣ (h*q - e)` is a single residue
class modulo `s*d`. (Note `(s*d) ∣ (h*q - e)` packages both `s ∣ (h*q - e)` and
`d ∣ (h*q - e)/s`, i.e. `d ∣ p` where `p = (h*q-e)/s`.)
-/
theorem residue_class_of_conditions (d s : ℕ) (hd : 1 ≤ d) (hs : 1 ≤ s) (h : ℤ)
    (hcop : IsCoprime h (s : ℤ)) (e : ℕ) (hde : (d : ℤ) ∣ (e : ℤ)) :
    ∃ c : ℤ, ∀ q : ℤ,
      ((d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e)) ↔ (((s * d : ℕ) : ℤ) ∣ (q - c)) := by
  obtain ⟨c, hc⟩ : ∃ c : ℤ, (d : ℤ) ∣ c ∧ (s * d : ℤ) ∣ (h * c - e) := by
    obtain ⟨ u, v, h ⟩ := hcop;
    obtain ⟨ e', he' ⟩ := hde;
    use d * u * e';
    exact ⟨ ⟨ u * e', by ring ⟩, ⟨ -v * e', by linear_combination' h * e' * d - he' ⟩ ⟩;
  use c;
  intro q; constructor <;> intro hq <;> simp_all +decide [ ← mul_assoc, ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ;
  · obtain ⟨ k, hk ⟩ := hq.2; obtain ⟨ m, hm ⟩ := hc.2; simp_all +decide [ sub_eq_iff_eq_add ] ;
    -- Since $h$ and $s$ are coprime, $s$ must divide $k - m$.
    have h_div : (s : ℤ) ∣ (q - c) / d := by
      have h_div : (s : ℤ) ∣ (h * ((q - c) / d)) := by
        exact ⟨ k - m, by cases lt_or_ge 0 h <;> nlinarith [ Int.ediv_mul_cancel ( show ( d : ℤ ) ∣ q - c from by rw [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ; aesop ) ] ⟩;
      exact hcop.symm.dvd_of_dvd_mul_left h_div;
    convert mul_dvd_mul h_div ( dvd_refl ( d : ℤ ) ) using 1 ; rw [ Int.ediv_mul_cancel ] ; simp_all +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ] ;
  · obtain ⟨ k, hk ⟩ := hq; simp_all +decide [ sub_eq_iff_eq_add ] ;
    convert dvd_add ( dvd_mul_right ( s * d : ℤ ) ( h * k ) ) hc.2 using 1 ; ring

/-- **Per-`d` count.** For `d ∈ e.divisors`, the number of `q ∈ (A,B)` with `d ∣ q` and
`(s*d) ∣ (h*q - e)` is within `1` of `(B - A)/(s*d)`. -/
theorem Nd_count_bound (d s : ℕ) (hd : 1 ≤ d) (hs : 1 ≤ s) (h : ℤ)
    (hcop : IsCoprime h (s : ℤ)) (e : ℕ) (hde : (d : ℤ) ∣ (e : ℤ)) (A B : ℝ) (hAB : A ≤ B) :
    |(({q : ℤ | A < (q : ℝ) ∧ (q : ℝ) < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e)}.ncard : ℝ)
        - (B - A) / (s * d : ℕ))| ≤ 1 := by
  obtain ⟨c, hc⟩ := residue_class_of_conditions d s hd hs h hcop e hde
  have hset : {q : ℤ | A < (q : ℝ) ∧ (q : ℝ) < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e)}
      = {q : ℤ | A < (q : ℝ) ∧ (q : ℝ) < B ∧ ((s * d : ℕ) : ℤ) ∣ (q - c)} := by
    ext q; simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, (hc q).mp ⟨h3, h4⟩⟩
    · rintro ⟨h1, h2, h3⟩; obtain ⟨h4, h5⟩ := (hc q).mpr h3; exact ⟨h1, h2, h4, h5⟩
  rw [hset]
  have hM : 1 ≤ s * d := Nat.one_le_iff_ne_zero.mpr (by positivity)
  simpa using residue_interval_count (s * d) hM c A B hAB

/-
**Primitive progression lower bound (Section 2).** For `h` coprime to `s ≥ 1`, `e ≥ 1`,
and reals `A ≤ B`, the number of integers `q ∈ (A,B)` such that `s ∣ (h*q - e)` and the
resulting `p = (h*q-e)/s` is coprime to `q`, is at least `(φ(e)/e)·(B-A)/s - τ(e)`,
where `τ(e) = e.divisors.card`.
-/
set_option maxHeartbeats 1000000 in
theorem prim_prog_lower (h : ℤ) (s : ℕ) (hs : 1 ≤ s) (hcop : IsCoprime h (s : ℤ))
    (e : ℕ) (he : 1 ≤ e) (A B : ℝ) (hAB : A ≤ B) :
    ((Nat.totient e : ℝ) / e) * (B - A) / s - (e.divisors.card : ℝ)
      ≤ ({q : ℤ | A < (q : ℝ) ∧ (q : ℝ) < B ∧ (s : ℤ) ∣ (h * q - e) ∧
            IsCoprime ((h * q - e) / s) q}.ncard : ℝ) := by
  -- By the Möbius inversion formula, we have
  have h_moebius : ∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * (Set.ncard {q : ℤ | A < (q : ℝ) ∧ (q : ℝ) < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e)}) = (Set.ncard {q : ℤ | A < (q : ℝ) ∧ (q : ℝ) < B ∧ (s : ℤ) ∣ (h * q - e) ∧ IsCoprime ((h * q - e) / s) q}) := by
    -- By the properties of the Möbius function and the definition of the sets involved, we can rewrite the left-hand side of the equation.
    have h_sum_indicator : ∀ q : ℤ, (∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * (if A < (q : ℝ) ∧ (q : ℝ) < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e) then 1 else 0)) = (if A < (q : ℝ) ∧ (q : ℝ) < B ∧ (s : ℤ) ∣ (h * q - e) ∧ IsCoprime ((h * q - e) / s) q then 1 else 0) := by
      intro q
      by_cases hq : A < (q : ℝ) ∧ (q : ℝ) < B ∧ (s : ℤ) ∣ (h * q - e);
      · -- Let $g = \gcd((h * q - e) / s, q)$.
        set g := Int.gcd ((h * q - e) / s) q with hg_def
        have hg_div_e : (g : ℤ) ∣ e := by
          have hg_div_e : (g : ℤ) ∣ (h * q - e) := by
            exact dvd_trans ( Int.gcd_dvd_left _ _ ) ( Int.ediv_dvd_of_dvd hq.2.2 ) |> fun x => x.trans ( by norm_num ) ;
          convert dvd_sub ( dvd_mul_of_dvd_right ( Int.gcd_dvd_right _ _ ) h ) hg_div_e using 1 ; ring
        have hg_divisors : (∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * (if (d : ℤ) ∣ g then 1 else 0)) = if g = 1 then 1 else 0 := by
          have hg_divisors : ∑ d ∈ Nat.divisors g, (ArithmeticFunction.moebius d : ℝ) = if g = 1 then 1 else 0 := by
            have hg_divisors : ∑ d ∈ Nat.divisors g, (ArithmeticFunction.moebius d : ℝ) = (ArithmeticFunction.moebius * ArithmeticFunction.zeta) g := by
              simp +decide [ ArithmeticFunction.moebius, ArithmeticFunction.zeta ];
              rw [ Nat.sum_divisorsAntidiagonal fun x y => if y = 0 then 0 else if Squarefree x then ( -1 : ℝ ) ^ cardFactors x else 0 ];
              exact Finset.sum_congr rfl fun x hx => by rw [ if_neg ( Nat.ne_of_gt ( Nat.div_pos ( Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by aesop ) ) ( Nat.dvd_of_mem_divisors hx ) ) ( Nat.pos_of_mem_divisors hx ) ) ) ] ;
            generalize_proofs at *; (
            rw [ hg_divisors, ArithmeticFunction.moebius_mul_coe_zeta ] ; aesop;)
          generalize_proofs at *; (
          rw [ ← hg_divisors, ← Finset.sum_subset ( show Nat.divisors g ⊆ Nat.divisors e from ?_ ) ];
          · exact Finset.sum_congr rfl fun x hx => by rw [ if_pos ( mod_cast Nat.dvd_of_mem_divisors hx ) ] ; ring;
          · simp +contextual [ Nat.mem_divisors ];
            exact fun x hx₁ hx₂ hx₃ hx₄ => absurd ( hx₃ <| Int.natCast_dvd_natCast.mp hx₄ ) ( by aesop ) ;
          · exact fun x hx => Nat.mem_divisors.mpr ⟨ dvd_trans ( Nat.dvd_of_mem_divisors hx ) ( mod_cast hg_div_e ), by linarith ⟩)
        have h_indicator : (∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * (if A < (q : ℝ) ∧ (q : ℝ) < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e) then 1 else 0)) = (∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * (if (d : ℤ) ∣ g then 1 else 0)) := by
          refine' Finset.sum_congr rfl fun x hx => _ ; simp_all +decide [ Int.natCast_dvd_natCast ] ;
          split_ifs <;> simp_all +decide [ Int.natCast_dvd_natCast, Nat.dvd_gcd_iff ];
          · rename_i h₁ h₂;
            exact False.elim <| h₂ <| Nat.dvd_gcd ( Int.natCast_dvd.mp <| by exact Int.dvd_div_of_mul_dvd <| by simpa [ mul_comm ] using h₁.2 ) ( Int.natCast_dvd.mp h₁.1 );
          · rename_i h₁ h₂; contrapose! h₁; simp_all +decide [ Nat.dvd_gcd_iff ] ;
            exact ⟨ Int.dvd_trans ( Int.natCast_dvd_natCast.mpr h₂ ) ( Int.gcd_dvd_right _ _ ), by convert mul_dvd_mul_left ( s : ℤ ) ( Int.natCast_dvd_natCast.mpr h₂ |> Int.dvd_trans <| Int.gcd_dvd_left _ _ ) using 1; rw [ Int.mul_ediv_cancel' hq.2.2 ] ⟩
        simp_all +decide [ Int.isCoprime_iff_gcd_eq_one ];
      · rw [ Finset.sum_eq_zero ] <;> simp_all +decide [ Finset.sum_ite ];
        exact fun x hx₁ hx₂ hx₃ hx₄ hx₅ hx₆ => False.elim <| hq hx₃ hx₄ <| dvd_of_mul_right_dvd hx₆;
    -- Apply the sum indicator equality to rewrite the left-hand side of the equation.
    have h_sum_rewrite : ∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * (Set.ncard {q : ℤ | A < (q : ℝ) ∧ (q : ℝ) < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e)}) = ∑ q ∈ Finset.Icc (Int.floor A + 1) (Int.ceil B - 1), (∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * (if A < (q : ℝ) ∧ (q : ℝ) < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e) then 1 else 0)) := by
      rw [ Finset.sum_comm, Finset.sum_congr rfl ];
      intro d hd; rw [ ← Finset.mul_sum _ _ _ ] ; norm_cast; simp +decide ;
      rw [ ← Set.ncard_coe_finset ] ; norm_num [ Set.ncard_eq_toFinset_card' ];
      exact Or.inl ( congr_arg _ ( by ext; exact ⟨ fun hx => ⟨ ⟨ Int.floor_lt.mpr hx.1, Int.lt_ceil.mpr hx.2.1 ⟩, hx ⟩, fun hx => hx.2 ⟩ ) );
    rw [ h_sum_rewrite, Finset.sum_congr rfl fun q hq => h_sum_indicator q ];
    simp +zetaDelta at *;
    rw [ ← Set.ncard_coe_finset ] ; congr ; ext ; simp +decide [ Int.floor_lt, Int.lt_ceil ] ;
    tauto;
  -- Applying the bound from `Nd_count_bound` to each term in the sum.
  have h_bound : |∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * (Set.ncard {q : ℤ | A < (q : ℝ) ∧ (q : ℝ) < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e)}) - ∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * ((B - A) / (s * d))| ≤ (e.divisors.card : ℝ) := by
    have h_bound : ∀ d ∈ e.divisors, |(ArithmeticFunction.moebius d : ℝ) * (Set.ncard {q : ℤ | A < (q : ℝ) ∧ (q : ℝ) < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e)}) - (ArithmeticFunction.moebius d : ℝ) * ((B - A) / (s * d))| ≤ 1 := by
      intro d hd
      have h_bound : |((Set.ncard {q : ℤ | A < (q : ℝ) ∧ (q : ℝ) < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e)}) : ℝ) - ((B - A) / (s * d))| ≤ 1 := by
        convert Nd_count_bound d s ( Nat.pos_of_mem_divisors hd ) hs h hcop e ( Int.natCast_dvd_natCast.mpr ( Nat.dvd_of_mem_divisors hd ) ) A B hAB using 1;
        norm_cast;
      simp_all +decide [ ← mul_sub, abs_mul ];
      exact le_trans ( mul_le_of_le_one_left ( abs_nonneg _ ) ( by exact_mod_cast ArithmeticFunction.abs_moebius_le_one ) ) h_bound;
    simpa only [ ← Finset.sum_sub_distrib ] using le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( le_trans ( Finset.sum_le_sum h_bound ) ( by norm_num ) );
  -- Applying the identity from `moebius_div_sum_eq_totient_div`.
  have h_identity : ∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * ((B - A) / (s * d)) = (B - A) / s * (Nat.totient e : ℝ) / e := by
    convert congr_arg ( fun x : ℝ => ( B - A ) / s * x ) ( moebius_div_sum_eq_totient_div e he ) using 1 <;> ring;
    simp +decide only [mul_assoc, mul_left_comm, Finset.sum_sub_distrib, Finset.mul_sum _ _ _];
  ring_nf at *; linarith [ abs_le.mp h_bound ] ;

/-
**Primitive progression upper bound (Section 2).** The matching upper bound: the same
count is at most `(phi(e)/e)*(B-A)/s + tau(e)`. Same Moebius argument as `prim_prog_lower`,
using the other direction of the `tau(e)` error estimate.
-/
set_option maxHeartbeats 1000000 in
theorem prim_prog_upper (h : ℤ) (s : ℕ) (hs : 1 ≤ s) (hcop : IsCoprime h (s : ℤ))
    (e : ℕ) (he : 1 ≤ e) (A B : ℝ) (hAB : A ≤ B) :
    ({q : ℤ | A < (q : ℝ) ∧ (q : ℝ) < B ∧ (s : ℤ) ∣ (h * q - e) ∧
            IsCoprime ((h * q - e) / s) q}.ncard : ℝ)
      ≤ ((Nat.totient e : ℝ) / e) * (B - A) / s + (e.divisors.card : ℝ) := by
  -- By Moebius inversion, the number of coprime solutions is $\sum_{d \mid e} \mu(d) \cdot N_d$.
  have h_moebius : ((Set.ncard {q : ℤ | A < q ∧ q < B ∧ (s : ℤ) ∣ (h * q - e) ∧ IsCoprime ((h * q - e) / s) q}) : ℝ) = ∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * ((Set.ncard {q : ℤ | A < q ∧ q < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e)}) : ℝ) := by
    have h_moebius : ∀ q : ℤ, (if A < q ∧ q < B ∧ (s : ℤ) ∣ (h * q - e) ∧ IsCoprime ((h * q - e) / s) q then 1 else 0) = ∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * (if A < q ∧ q < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e) then 1 else 0) := by
      intro q
      by_cases hq : A < q ∧ q < B ∧ (s : ℤ) ∣ (h * q - e);
      · -- Let $d = \gcd((h * q - e) / s, q)$. Then $d \mid e$.
        set d := Nat.gcd (Int.natAbs ((h * q - e) / s)) (Int.natAbs q) with hd'
        have hd_div_e : d ∣ e := by
          have hd_div_e : (d : ℤ) ∣ (h * q - e) := by
            convert Int.natCast_dvd.mpr ( Nat.gcd_dvd_left _ _ ) |> fun x => x.mul_left ( s : ℤ ) using 1;
            rw [ Int.mul_ediv_cancel' hq.2.2 ];
          rw [ ← Int.natCast_dvd_natCast ];
          convert dvd_sub ( dvd_mul_of_dvd_right ( Int.natCast_dvd.mpr ( Nat.gcd_dvd_right _ _ ) ) h ) hd_div_e using 1 ; ring;
        -- Since $d \mid e$, we can rewrite the sum as $\sum_{d \mid e} \mu(d) \cdot \mathbf{1}_{d \mid \gcd((h * q - e) / s, q)}$.
        have h_sum_div : ∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * (if (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e) then 1 else 0) = ∑ d ∈ Nat.divisors d, (ArithmeticFunction.moebius d : ℝ) := by
          rw [ ← Finset.sum_subset ( show Nat.divisors d ⊆ Nat.divisors e from fun x hx => Nat.mem_divisors.mpr ⟨ dvd_trans ( Nat.dvd_of_mem_divisors hx ) hd_div_e, by aesop ⟩ ) ];
          · refine' Finset.sum_congr rfl fun x hx => _;
            simp +zetaDelta at *;
            intro hx'; contrapose! hx'; simp_all +decide [ Nat.dvd_gcd_iff ] ;
            exact ⟨ Int.natCast_dvd.mpr hx.1.2, by convert mul_dvd_mul_left ( s : ℤ ) ( Int.natCast_dvd.mpr hx.1.1 ) using 1; rw [ Int.mul_ediv_cancel' hq.2.2 ] ⟩;
          · intro x hx hx'; split_ifs <;> simp_all +decide [ Nat.dvd_gcd_iff ] ;
            have := hx' ( Int.natAbs_dvd_natAbs.mpr <| show ( x : ℤ ) ∣ ( h * q - e ) / s from ?_ ) ( Int.natAbs_dvd_natAbs.mpr <| show ( x : ℤ ) ∣ q from ?_ ) ; aesop;
            · exact Int.dvd_div_of_mul_dvd ( by simpa only [ mul_comm ] using ‹ ( x : ℤ ) ∣ q ∧ ( s : ℤ ) * x ∣ h * q - e ›.2 );
            · tauto;
        -- Since $d \mid e$, we can rewrite the sum as $\sum_{d \mid e} \mu(d) \cdot \mathbf{1}_{d \mid \gcd((h * q - e) / s, q)}$ and use the fact that $\sum_{d \mid n} \mu(d) = 0$ for $n > 1$.
        have h_sum_zero : ∑ d ∈ Nat.divisors d, (ArithmeticFunction.moebius d : ℝ) = if d = 1 then 1 else 0 := by
          have h_sum_zero : ∑ d ∈ Nat.divisors d, (ArithmeticFunction.moebius d : ℝ) = (ArithmeticFunction.moebius * ArithmeticFunction.zeta) d := by
            simp +decide [ ArithmeticFunction.moebius, ArithmeticFunction.zeta ];
            rw [ Nat.sum_divisorsAntidiagonal fun x y => if y = 0 then 0 else if Squarefree x then ( -1 : ℝ ) ^ cardFactors x else 0 ];
            exact Finset.sum_congr rfl fun x hx => by rw [ if_neg ( Nat.ne_of_gt ( Nat.div_pos ( Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by aesop ) ) ( Nat.dvd_of_mem_divisors hx ) ) ( Nat.pos_of_mem_divisors hx ) ) ) ] ;
          convert h_sum_zero using 1;
          erw [ ArithmeticFunction.moebius_mul_coe_zeta ] ; aesop;
        simp_all +decide [ Int.isCoprime_iff_gcd_eq_one ];
        norm_num [ Int.gcd, Int.natAbs_abs ];
      · rw [ Finset.sum_eq_zero ] ; aesop;
        intro x hx; split_ifs <;> simp_all +decide [ dvd_mul_of_dvd_right ] ;
        exact False.elim <| hq <| dvd_of_mul_right_dvd <| by tauto;
    convert congr_arg ( fun x : ℝ => x ) ( Finset.sum_congr rfl fun q hq => h_moebius q ) using 1;
    any_goals exact Finset.Ico ⌊A⌋ ⌈B⌉;
    · simp +zetaDelta at *;
      rw [ ← Set.ncard_coe_finset ] ; congr ; ext ; simp +decide [ Int.floor_le, Int.lt_ceil ];
      exact fun _ _ _ _ => ⟨ Int.le_of_lt_add_one <| Int.floor_lt.2 <| by norm_num; linarith, by assumption ⟩;
    · rw [ Finset.sum_comm, Finset.sum_congr rfl ];
      simp +decide [ Finset.sum_ite ];
      intro x hx he; rw [ mul_comm ] ; rw [ ← Set.ncard_coe_finset ] ; congr; ext; simp +decide [ Int.floor_le, Int.lt_ceil ] ;
      exact fun _ _ _ _ => ⟨ Int.le_of_lt_add_one <| Int.floor_lt.2 <| by norm_num; linarith, by linarith ⟩;
  -- By Nd_count_bound, we have $|N_d - (B-A)/(s*d)| \le 1$ for each $d \mid e$.
  have h_bound : ∀ d ∈ e.divisors, |((Set.ncard {q : ℤ | A < q ∧ q < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e)}) : ℝ) - (B - A) / (s * d)| ≤ 1 := by
    intro d hd;
    convert Nd_count_bound d s ( Nat.pos_of_mem_divisors hd ) hs h hcop e ( Int.natCast_dvd_natCast.mpr ( Nat.dvd_of_mem_divisors hd ) ) A B hAB using 1;
    norm_cast;
  -- Applying the bound from `h_bound` to each term in the sum, we get:
  have h_sum_bound : |∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * ((Set.ncard {q : ℤ | A < q ∧ q < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e)}) : ℝ) - ∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * ((B - A) / (s * d))| ≤ (e.divisors.card : ℝ) := by
    have h_sum_bound : ∀ d ∈ e.divisors, |(ArithmeticFunction.moebius d : ℝ) * ((Set.ncard {q : ℤ | A < q ∧ q < B ∧ (d : ℤ) ∣ q ∧ ((s * d : ℕ) : ℤ) ∣ (h * q - e)}) : ℝ) - (ArithmeticFunction.moebius d : ℝ) * ((B - A) / (s * d))| ≤ 1 := by
      intro d hd; specialize h_bound d hd; simp_all +decide [ ← mul_sub, abs_mul ] ;
      exact le_trans ( mul_le_of_le_one_left ( abs_nonneg _ ) ( by exact_mod_cast ArithmeticFunction.abs_moebius_le_one ) ) h_bound;
    simpa only [ ← Finset.sum_sub_distrib ] using le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( le_trans ( Finset.sum_le_sum h_sum_bound ) ( by norm_num ) );
  -- By moebius_div_sum_eq_totient_div, we have $\sum_{d \mid e} \mu(d) \cdot \frac{1}{d} = \frac{\phi(e)}{e}$.
  have h_identity : ∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * (1 / (d : ℝ)) = (Nat.totient e : ℝ) / e := by
    convert moebius_div_sum_eq_totient_div e he using 1;
    exact Finset.sum_congr rfl fun _ _ => by ring;
  -- Substitute the identity into the sum.
  have h_substitute : ∑ d ∈ e.divisors, (ArithmeticFunction.moebius d : ℝ) * ((B - A) / (s * d)) = (Nat.totient e : ℝ) / e * (B - A) / s := by
    rw [ ← h_identity ] ; rw [ Finset.sum_mul _ _ _ ] ; rw [ Finset.sum_div ] ; congr ; ext ; ring;
  linarith [ abs_le.mp h_sum_bound ]

end Erdos1005