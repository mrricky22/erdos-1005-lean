import RequestProject.PrimProg
import RequestProject.LowerCore
import RequestProject.Farey

open scoped BigOperators
open Finset

namespace Erdos1005

/-
**Membership lemma (left fibers).** Fix a reference rational `z` and a left endpoint `x`
with `0 ≤ x < z ≤ 1`. For `e ≥ 1` and an integer denominator `d` with `0 < d ≤ n`,
`z.den ∣ (z.num·d − e)`, the numerator `p = (z.num·d − e)/z.den` coprime to `d`, and the
lower bound `x.den·e < (z.num·x.den − x.num·z.den)·d` (i.e. `x < p/d`), the fraction `p/d`
is an order-`n` Farey fraction strictly between `x` and `z`.
-/
theorem left_frac_mem (x z : ℚ) (hx0 : 0 ≤ x) (hxz : x < z) (hz1 : z ≤ 1)
    (n : ℕ) (e : ℕ) (he : 1 ≤ e) (d : ℤ)
    (hd_pos : 0 < d) (hdn : d ≤ (n : ℤ))
    (hdvd : (z.den : ℤ) ∣ (z.num * d - e))
    (hcop : IsCoprime ((z.num * d - e) / z.den) d)
    (hlow : (x.den : ℤ) * e < (z.num * (x.den : ℤ) - x.num * (z.den : ℤ)) * d) :
    IsFarey n (((z.num * d - e) / z.den : ℤ) / (d : ℚ)) ∧
      x < (((z.num * d - e) / z.den : ℤ) / (d : ℚ)) ∧
      (((z.num * d - e) / z.den : ℤ) / (d : ℚ)) < z := by
  refine' ⟨ _, _, _ ⟩;
  · refine' ⟨ _, _, _ ⟩;
    · refine' div_nonneg _ _ <;> norm_cast;
      · refine' Int.ediv_nonneg _ _ <;> norm_num;
        nlinarith [ show x.num * z.den ≥ 0 by exact mul_nonneg ( Rat.num_nonneg.mpr hx0 ) ( Nat.cast_nonneg _ ) ];
      · grind;
    · rw [ div_le_iff₀ ] <;> norm_cast;
      rw [ Int.ediv_le_iff_le_mul ] <;> norm_num;
      · nlinarith [ show z.num ≤ z.den from by simpa [ Rat.le_iff ] using hz1, show ( z.den : ℤ ) > 0 from mod_cast z.pos ];
      · exact z.pos;
    · rw [ div_eq_mul_inv ];
      erw [ Rat.mul_den ] ; norm_num [ hd_pos.ne', hdn ];
      exact le_trans ( Nat.div_le_self _ _ ) ( by linarith [ abs_of_pos hd_pos ] );
  · rw [ lt_div_iff₀ ] <;> norm_cast;
    rw [ ← Rat.num_div_den x ];
    rw [ div_mul_eq_mul_div, div_lt_iff₀ ] <;> norm_cast;
    · nlinarith [ Int.ediv_mul_cancel hdvd ];
    · exact x.pos;
  · rw [ div_lt_iff₀ ] <;> norm_cast;
    rw [ Int.cast_div ] <;> norm_num [ hdvd ];
    rw [ div_lt_iff₀ ] <;> norm_cast;
    · rw [ mul_right_comm, Rat.mul_den_eq_num ];
      rw [ Int.cast_sub, Int.cast_mul ] ; norm_num ; linarith;
    · exact z.pos

/-- The per-`e` fiber of left-side denominators: exactly the `prim_prog_lower` set with
reference `z`, window lower end `A_e = x.den·e/u` (`u = z.num·x.den − x.num·z.den`) and
upper end `n+1` (so `d < n+1 ↔ d ≤ n`). -/
noncomputable def leftFiber (x z : ℚ) (n e : ℕ) : Set ℤ :=
  {q : ℤ | ((x.den : ℝ) * e / ((z.num * (x.den : ℤ) - x.num * (z.den : ℤ) : ℤ) : ℝ)) < (q : ℝ)
      ∧ (q : ℝ) < (n : ℝ) + 1 ∧ (z.den : ℤ) ∣ (z.num * q - e)
      ∧ IsCoprime ((z.num * q - e) / z.den) q}

/-
**Left-side count bridge.** For `0 ≤ x < z ≤ 1`, the number of order-`n` Farey fractions
strictly between `x` and `z` is at least the sum over `e ∈ [1,E]` of the per-`e` fiber counts.
Proved by the injection `(e,d) ↦ ((z.num·d − e)/z.den)/d` from the disjoint union of the
fibers into the between-set (each fraction determines its denominator `d` and the value
`e = z.num·d − z.den·(num)`).
-/
set_option maxHeartbeats 1000000 in
theorem left_count_bridge (x z : ℚ) (hx0 : 0 ≤ x) (hxz : x < z) (hz1 : z ≤ 1) (n E : ℕ) :
    (∑ e ∈ Finset.Icc 1 E, ((leftFiber x z n e).ncard : ℝ)) ≤ (betweenCount n x z : ℝ) := by
  -- Define the mapping g from the fibers to the Farey fractions.
  set g : ℕ × ℤ → ℚ := fun ⟨e, d⟩ => (((z.num * d - e) / z.den : ℤ) : ℚ) / (d : ℚ);
  -- Show that the image of the fibers under g is a subset of the Farey fractions.
  have h_image_subset : ∀ e ∈ Finset.Icc 1 E, ∀ d ∈ leftFiber x z n e, g (e, d) ∈ {q : ℚ | IsFarey n q ∧ x < q ∧ q < z} := by
    intros e he d hd
    apply left_frac_mem x z hx0 hxz hz1 n e (Finset.mem_Icc.mp he).left d (by
    unfold leftFiber at hd;
    norm_num +zetaDelta at *;
    exact_mod_cast hd.1.trans_le' ( div_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( sub_nonneg.mpr ( by rw [ ← Rat.num_div_den x, ← Rat.num_div_den z ] at hxz; rw [ div_lt_div_iff₀ ] at hxz <;> norm_cast at * <;> nlinarith [ x.pos, z.pos ] ) ) )) (by
    exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ hd.2.1 ] )) (by
    exact hd.2.2.1) (by
    exact hd.2.2.2) (by
    obtain ⟨ hd₁, hd₂, hd₃, hd₄ ⟩ := hd;
    rw [ div_lt_iff₀ ] at hd₁ <;> norm_cast at *;
    · linarith;
    · rw [ Rat.lt_iff ] at hxz ; aesop);
  -- Show that the image of the fibers under g is injective.
  have h_image_inj : ∀ e₁ e₂ : ℕ, e₁ ∈ Finset.Icc 1 E → e₂ ∈ Finset.Icc 1 E → ∀ d₁ d₂ : ℤ, d₁ ∈ leftFiber x z n e₁ → d₂ ∈ leftFiber x z n e₂ → g (e₁, d₁) = g (e₂, d₂) → e₁ = e₂ ∧ d₁ = d₂ := by
    intros e₁ e₂ he₁ he₂ d₁ d₂ hd₁ hd₂ h_eq
    have h_den : d₁ = d₂ := by
      have h_den : (g (e₁, d₁)).den = d₁.natAbs ∧ (g (e₂, d₂)).den = d₂.natAbs := by
        have h_denom : ∀ e : ℕ, ∀ d : ℤ, d ∈ leftFiber x z n e → IsCoprime ((z.num * d - e) / z.den) d → (g (e, d)).den = d.natAbs := by
          intros e d hd h_coprime
          simp [g, h_coprime];
          rw [ div_eq_mul_inv, Rat.mul_den ];
          erw [ Rat.inv_intCast_den, Rat.inv_intCast_num ] ; norm_num;
          split_ifs <;> simp_all +decide [ Int.natAbs_mul, Int.natAbs_sign ];
          · have := hd.1; norm_num at this;
            contrapose! this;
            exact div_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( sub_nonneg_of_le <| by rw [ ← Rat.num_div_den x, ← Rat.num_div_den z ] at hxz; rw [ div_lt_div_iff₀ ] at hxz <;> norm_cast at * <;> nlinarith [ x.pos, z.pos ] );
          · rw [ Nat.Coprime.gcd_eq_one ] <;> norm_num [ Int.isCoprime_iff_gcd_eq_one ] at * ; aesop;
        exact ⟨ h_denom e₁ d₁ hd₁ hd₁.2.2.2, h_denom e₂ d₂ hd₂ hd₂.2.2.2 ⟩;
      have h_den_pos : 0 < d₁ ∧ 0 < d₂ := by
        have h_den_pos : ∀ e ∈ Finset.Icc 1 E, ∀ d ∈ leftFiber x z n e, 0 < d := by
          intros e he d hd
          have h_den_pos : 0 < (x.den : ℝ) * e / ((z.num * (x.den : ℤ) - x.num * (z.den : ℤ) : ℤ) : ℝ) := by
            refine' div_pos ( mul_pos ( Nat.cast_pos.mpr x.pos ) ( Nat.cast_pos.mpr ( Finset.mem_Icc.mp he |>.1 ) ) ) ( Int.cast_pos.mpr _ );
            rw [ Rat.lt_iff ] at hxz ; aesop;
          exact_mod_cast hd.1.trans_le' h_den_pos.le;
        exact ⟨ h_den_pos e₁ he₁ d₁ hd₁, h_den_pos e₂ he₂ d₂ hd₂ ⟩;
      grind
    have h_num : e₁ = e₂ := by
      simp +zetaDelta at *;
      have := hd₁.2.2.1; have := hd₂.2.2.1; simp_all +decide [ Rat.den_nz ] ;
      simp_all +decide [ div_eq_mul_inv, Rat.den_nz ];
      exact h_eq.resolve_right ( by linarith [ show 0 < d₂ from by exact_mod_cast hd₁.1.trans_le' ( div_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( by exact_mod_cast sub_nonneg.mpr ( show ( z.num * x.den : ℤ ) ≥ x.num * z.den from by rw [ Rat.lt_iff ] at hxz; linarith ) ) ) ] ) ▸ rfl
    exact ⟨h_num, h_den⟩;
  -- By definition of $g$, we know that the image of the fibers under $g$ is a subset of the Farey fractions.
  have h_image_subset : Finset.card (Finset.biUnion (Finset.Icc 1 E) (fun e => Finset.image (fun d => g (e, d)) (Set.Finite.toFinset (show Set.Finite (leftFiber x z n e) from by
                                                                                                                                        refine' Set.Finite.subset ( Set.finite_Icc ( 0 : ℤ ) ( n : ℤ ) ) _;
                                                                                                                                        intro d hd; exact ⟨ by
                                                                                                                                          have := hd.1;
                                                                                                                                          contrapose! this;
                                                                                                                                          exact le_trans ( mod_cast this.le ) ( div_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( mod_cast by nlinarith [ show 0 < z.num * x.den - x.num * z.den from by rw [ Rat.lt_iff ] at hxz; linarith ] ) ), by
                                                                                                                                          exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ hd.2.1 ] ) ⟩ ;)))) ≤ (betweenCount n x z : ℕ) := by
                                                                                                                                        rw [ ← Set.ncard_coe_finset ];
                                                                                                                                        apply Set.ncard_le_ncard;
                                                                                                                                        · simp +zetaDelta at *;
                                                                                                                                          exact fun e he₁ he₂ => fun d hd => h_image_subset e he₁ he₂ d hd;
                                                                                                                                        · exact fareyBetween_finite n x z
  generalize_proofs at *;
  rw [ Finset.card_biUnion ] at h_image_subset;
  · rw [ Finset.sum_congr rfl fun e he => Finset.card_image_of_injOn <| fun d₁ hd₁ d₂ hd₂ h => by specialize h_image_inj e e he he d₁ d₂ ; aesop ] at h_image_subset ; norm_cast;
    convert h_image_subset using 2;
    rw [ ← Set.ncard_coe_finset ] ; congr ; aesop;
  · intros e₁ he₁ e₂ he₂ he_ne; simp [Finset.disjoint_left, Finset.mem_image];
    exact fun a ha b hb hab => he_ne <| h_image_inj e₁ e₂ he₁ he₂ a b ha hb hab.symm |>.1

/-
**Left-side main bound.** Combining the bridge with `prim_prog_lower` (per `e`) and the
window identity `totient_window_sum_eq`, the number of order-`n` Farey fractions strictly
between `x` and `z` (for `0 <= x < z <= 1`) is at least
`((n+1)/z.den) * S(mu*u) - sum_{e=1}^{ceil(mu*u)-1} tau(e)`, where `mu = (n+1)/x.den` and
`u = z.num*x.den - x.num*z.den`.
-/
set_option maxHeartbeats 1000000 in
theorem left_count_main (x z : ℚ) (hx0 : 0 ≤ x) (hxz : x < z) (hz1 : z ≤ 1) (n : ℕ) :
    ((n : ℝ) + 1) / z.den
        * Sfun (((n : ℝ) + 1) / x.den * ((z.num * (x.den : ℤ) - x.num * (z.den : ℤ) : ℤ) : ℝ))
      - (∑ e ∈ Finset.Icc 1
          (⌈((n : ℝ) + 1) / x.den * ((z.num * (x.den : ℤ) - x.num * (z.den : ℤ) : ℤ) : ℝ)⌉₊ - 1),
          (e.divisors.card : ℝ))
      ≤ (betweenCount n x z : ℝ) := by
  -- Apply the `prim_prog_lower` bound to each term in the sum.
  have h_prime_lower_bound (e : ℕ) (he : 1 ≤ e) (he_le : e ≤ Nat.ceil ((n + 1) / x.den * (z.num * x.den - x.num * z.den : ℝ)) - 1) :
      ((Nat.totient e : ℝ) / e) * ((n + 1) - (x.den * e : ℝ) / ((z.num * x.den - x.num * z.den : ℤ) : ℝ)) / z.den - ((e.divisors.card : ℝ)) ≤ (leftFiber x z n e).ncard := by
        convert prim_prog_lower z.num z.den ( mod_cast z.pos ) _ e he _ _ _ using 1;
        · exact Int.isCoprime_iff_gcd_eq_one.mpr ( by simpa [ Int.gcd, Int.natAbs_abs ] using z.reduced );
        · rw [ div_le_iff₀ ] <;> norm_cast;
          · rw [ Nat.le_sub_iff_add_le ] at he_le;
            · contrapose! he_le;
              rw [ Nat.lt_succ_iff, Nat.ceil_le ];
              rw [ div_mul_eq_mul_div, div_le_iff₀ ] <;> norm_cast at *;
              · exact he_le.le.trans ( by norm_cast; linarith );
              · exact x.pos;
            · grind;
          · rw [ Rat.lt_iff ] at hxz ; aesop;
  -- Summing the bounds from `h_prime_lower_bound` over all `e` in the range.
  have h_sum_lower_bound :
      (∑ e ∈ Finset.Icc 1 (Nat.ceil ((n + 1) / x.den * (z.num * x.den - x.num * z.den : ℝ)) - 1), ((Nat.totient e : ℝ) / e) * ((n + 1) - (x.den * e : ℝ) / ((z.num * x.den - x.num * z.den : ℤ) : ℝ)) / z.den) -
      (∑ e ∈ Finset.Icc 1 (Nat.ceil ((n + 1) / x.den * (z.num * x.den - x.num * z.den : ℝ)) - 1), ((e.divisors.card : ℝ))) ≤
      (betweenCount n x z : ℝ) := by
        refine' le_trans _ ( left_count_bridge x z hx0 hxz hz1 n _ );
        simpa only [ ← Finset.sum_sub_distrib ] using Finset.sum_le_sum fun e he => h_prime_lower_bound e ( Finset.mem_Icc.mp he |>.1 ) ( Finset.mem_Icc.mp he |>.2 );
  by_cases h : ⌈ ( n + 1 : ℝ ) / x.den * ( z.num * x.den - x.num * z.den ) ⌉₊ = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
  · contrapose! h;
    refine' mul_pos ( inv_pos.mpr ( Nat.cast_pos.mpr x.pos ) ) ( mul_pos _ ( Nat.cast_add_one_pos _ ) );
    rw [ Rat.lt_iff ] at hxz ; norm_cast at *;
    linarith;
  · convert h_sum_lower_bound using 1;
    rw [ show Sfun ( ( x.den : ℝ ) ⁻¹ * ( ( z.num * x.den - x.num * z.den ) * ( n + 1 ) ) ) = ∑ e ∈ Finset.range ⌈ ( x.den : ℝ ) ⁻¹ * ( ( z.num * x.den - x.num * z.den ) * ( n + 1 ) ) ⌉₊, ( 1 - ( e : ℝ ) / ( ( x.den : ℝ ) ⁻¹ * ( ( z.num * x.den - x.num * z.den ) * ( n + 1 ) ) ) ) * ( Nat.totient e / e ) from rfl ] ; simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
    erw [ Finset.sum_Ico_eq_sub _ ] <;> norm_num [ Finset.sum_range_succ' ];
    cases k : ⌈ ( x.den : ℝ ) ⁻¹ * ( ( z.num * x.den - x.num * z.den ) * ( n + 1 ) ) ⌉₊ <;> simp_all +decide [ Finset.sum_range_succ' ] ; ring;
    grind

/-
**Splitting at an interior point.** The count over `(x,w)` is at least the sum of the
counts over `(x,z)` and `(z,w)` (disjoint open subintervals).
-/
theorem betweenCount_split (n : ℕ) (x z w : ℚ) (hxz : x ≤ z) (hzw : z ≤ w) :
    betweenCount n x z + betweenCount n z w ≤ betweenCount n x w := by
  by_contra h_contra;
  unfold betweenCount at *;
  apply h_contra;
  rw [ ← @Set.ncard_union_eq ];
  · apply Set.ncard_le_ncard;
    · rintro q ( ⟨ hq₁, hq₂, hq₃ ⟩ | ⟨ hq₁, hq₂, hq₃ ⟩ ) <;> exact ⟨ hq₁, by linarith, by linarith ⟩;
    · exact fareyBetween_finite n x w;
  · exact Set.disjoint_left.mpr fun q hq₁ hq₂ => by linarith [ hq₁.2.2, hq₂.2.1 ] ;
  · exact Set.Finite.subset ( farey_finite n ) fun q hq => hq.1;
  · exact fareyBetween_finite n z w

/-
**Upper split.** The count over `(a,c)` is at most the counts over `(a,b)` and `(b,c)`
plus one (for the interior point `b` itself).
-/
theorem betweenCount_split_le (n : ℕ) (a b c : ℚ) (hab : a ≤ b) (hbc : b ≤ c) :
    betweenCount n a c ≤ betweenCount n a b + betweenCount n b c + 1 := by
  -- Let's define the sets $A$, $B$, and $C$ as given in the provided solution.
  set A := {r : ℚ | IsFarey n r ∧ a < r ∧ r < c}
  set B := {r : ℚ | IsFarey n r ∧ a < r ∧ r < b}
  set C := {r : ℚ | IsFarey n r ∧ b < r ∧ r < c};
  -- By definition of $A$, $B$, and $C$, we have $A \subseteq B \cup C \cup \{b\}$.
  have h_subset : A ⊆ B ∪ C ∪ {b} := by
    grind;
  -- Using the subset relationship, we can bound the cardinality of $A$.
  have h_card : Set.ncard A ≤ Set.ncard (B ∪ C) + Set.ncard ({b} : Set ℚ) := by
    refine' le_trans _ ( Set.ncard_union_le _ _ );
    apply_rules [ Set.ncard_le_ncard ];
    exact Set.Finite.union ( Set.Finite.union ( fareyBetween_finite n a b ) ( fareyBetween_finite n b c ) ) ( Set.finite_singleton b );
  refine le_trans h_card ?_;
  refine' add_le_add ( Set.ncard_union_le _ _ ) _;
  norm_num

/-
**Reflection `q ↦ 1 - q`.** This order-reversing involution preserves Farey order-`n`
(`(1-q).den = q.den`), so the count over `(z,w)` equals the count over `(1-w, 1-z)`.
-/
theorem betweenCount_reflect (n : ℕ) (z w : ℚ) :
    betweenCount n z w = betweenCount n (1 - w) (1 - z) := by
  fapply Set.ncard_congr;
  use fun q hq => 1 - q;
  · simp +contextual [ IsFarey ];
  · grind;
  · simp +zetaDelta at *;
    intro b hb hb' hb''; use 1 - b; simp_all +decide [ IsFarey ] ;
    grind +splitImp

/-
**Pair bound for `S` (Lemma 5.1 corollary).** If `u, v ≥ 1`, `s ≥ 2` and `s + 1 ≤ u + v`,
then `S(u) + S(v) ≥ s/4`.
-/
theorem Sfun_pair_ge (u v : ℕ) (hu : 1 ≤ u) (hv : 1 ≤ v) (s : ℕ) (hs : 2 ≤ s)
    (hsum : s + 1 ≤ u + v) : (s : ℝ) / 4 ≤ Sfun u + Sfun v := by
  rcases u with ( _ | _ | u ) <;> rcases v with ( _ | _ | v ) <;> norm_num at *;
  · grind;
  · rw [ Sfun_one ] ; norm_num;
    have := Sfun_ge_quarter ( show 2 ≤ ( v + 1 + 1 : ℕ ) by linarith ) ; norm_num at * ; linarith [ ( by norm_cast : ( s : ℝ ) + 1 ≤ 1 + ( v + 1 + 1 ) ) ] ;
  · rw [ Sfun_one ] ; norm_num;
    have := Sfun_ge_quarter ( by linarith : 2 ≤ u + 1 + 1 ) ; norm_num at * ; linarith [ ( by norm_cast : ( s : ℝ ) ≤ u + 2 ) ] ;
  · linarith [ show Sfun ( u + 1 + 1 : ℝ ) ≥ ( u + 1 + 1 : ℝ ) / 4 by exact_mod_cast Sfun_ge_quarter ( by linarith ), show Sfun ( v + 1 + 1 : ℝ ) ≥ ( v + 1 + 1 : ℝ ) / 4 by exact_mod_cast Sfun_ge_quarter ( by linarith ), ( by norm_cast : ( s : ℝ ) + 1 ≤ u + 1 + 1 + ( v + 1 + 1 ) ) ]

/-
`S` is nonnegative on `[0, ∞)`.
-/
theorem Sfun_nonneg {b : ℝ} (hb : 0 ≤ b) : 0 ≤ Sfun b := by
  refine Finset.sum_nonneg fun e he => mul_nonneg ?_ ?_;
  · exact sub_nonneg_of_le ( div_le_one_of_le₀ ( by linarith [ Nat.lt_ceil.mp ( Finset.mem_range.mp he ) ] ) hb );
  · positivity

/-- `S(j) ≤ S(t)` whenever `j` is a positive integer and `t ≥ j` (from `Ffun_ge_int_for_ge`). -/
theorem Sfun_ge_int {j : ℕ} (hj : 1 ≤ j) {t : ℝ} (ht : (j : ℝ) ≤ t) : Sfun (j : ℝ) ≤ Sfun t := by
  have := Ffun_ge_int_for_ge hj ht
  unfold Ffun at this
  linarith

/-
`S` vanishes on `[0, 1)`.
-/
theorem Sfun_eq_zero_of_lt_one {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) : Sfun t = 0 := by
  unfold Sfun;
  cases eq_or_ne t 0 <;> simp_all +decide [ Finset.sum_range_succ' ];
  rw [ show ⌈t⌉₊ = 1 by exact Nat.ceil_eq_iff ( by positivity ) |>.2 ⟨ by norm_num; linarith [ show ( 0 : ℝ ) < t by positivity ], by norm_num; linarith ⟩ ] ; norm_num

/-
**Case-B S-ratio bound.** Under the listed size conditions, `((n+1)/s)·(S aX − S aE) ≥ n/4`.
-/
theorem caseB_ratio_ge (n s : ℕ) (hs : 1 ≤ s) (aX aE : ℝ) (haE0 : 0 ≤ aE)
    (h2X : (2 : ℝ) ≤ aX) (hdiff : (s : ℝ) ≤ aX - aE)
    (hbig : (n : ℝ) ≤ ((n : ℝ) + 1) / s * (aX - aE)) :
    (n : ℝ) / 4 ≤ ((n : ℝ) + 1) / s * (Sfun aX - Sfun aE) := by
  by_cases hs2 : s ≥ 2;
  · have h_case2 : Sfun aX - Sfun aE ≥ (aX - aE) / 4 := by
      have := Sfun_increment_ge_two haE0 ( show 2 ≤ aX - aE from le_trans ( mod_cast hs2 ) hdiff ) ; aesop;
    nlinarith [ show ( 0 : ℝ ) ≤ ( n + 1 ) / s by positivity ];
  · interval_cases s;
    by_cases haE1 : aE < 1;
    · rw [ Sfun_eq_zero_of_lt_one haE0 haE1 ] ; norm_num;
      have := Sfun_ge_int ( by norm_num : 1 ≤ 2 ) ( by linarith : ( 2 : ℝ ) ≤ aX ) ; norm_num at * ; nlinarith [ Sfun_two ] ;
    · have := Erdos1005.Sfun_increment_ge_one ( show 1 ≤ aE by linarith ) ( show 1 ≤ aX - aE by norm_num at *; linarith ) ; ( norm_num at * ; nlinarith; )

/-
The reflection `q ↦ 1 - q` preserves the denominator.
-/
theorem one_sub_den (q : ℚ) : (1 - q).den = q.den := by
  norm_num [ Rat.sub_def ];
  rw [ Nat.Coprime.gcd_eq_one ];
  · norm_num;
  · refine' Nat.Coprime.symm ( Nat.coprime_of_dvd' _ );
    intro k hk hk₁ hk₂; have := Nat.dvd_gcd hk₁ ( show k ∣ q.num.natAbs from ?_ ) ; simp_all +decide [ Rat.reduced ] ;
    · simp_all +decide [ Rat.reduced, Nat.Coprime, Nat.Coprime.symm ];
    · rw [ ← Int.natCast_dvd ] at *;
      simpa using dvd_sub ( Int.natCast_dvd_natCast.mpr hk₁ ) hk₂

/-- Abbreviation for the Section-2 error term of the left count `(x, z)`. -/
noncomputable def errTerm (x z : ℚ) (n : ℕ) : ℝ :=
  ∑ e ∈ Finset.Icc 1
    (⌈((n : ℝ) + 1) / x.den * ((z.num * (x.den : ℤ) - x.num * (z.den : ℤ) : ℤ) : ℝ)⌉₊ - 1),
    (e.divisors.card : ℝ)

/-
**Left-side count bridge (upper).** Every order-`n` Farey fraction in `(x, z)` lies in some
per-`e` fiber, so the between-count is at most the sum of the fiber counts.
-/
set_option maxHeartbeats 1000000 in
theorem left_count_bridge_upper (x z : ℚ) (hx0 : 0 ≤ x) (hxz : x < z) (hz1 : z ≤ 1) (n : ℕ) :
    (betweenCount n x z : ℝ)
      ≤ ∑ e ∈ Finset.Icc 1
          (⌈((n : ℝ) + 1) / x.den * ((z.num * (x.den : ℤ) - x.num * (z.den : ℤ) : ℤ) : ℝ)⌉₊ - 1),
          ((leftFiber x z n e).ncard : ℝ) := by
  -- Let `Bset := {r : ℚ | IsFarey n r ∧ x < r ∧ r < z}` (finite, `fareyBetween_finite`).
  set Bset := {r : ℚ | IsFarey n r ∧ x < r ∧ r < z} with hBset_def;
  -- By definition of `Bset`, we can partition it into subsets based on the value of `e`.
  have h_partition : Bset = ⋃ e ∈ Finset.Icc 1 (⌈((n + 1) / x.den * ((z.num * x.den - x.num * z.den) : ℤ) : ℝ)⌉₊ - 1), {r ∈ Bset | (z.num * r.den - z.den * r.num : ℤ).toNat = e} := by
    ext r
    simp [hBset_def];
    intro hr hxz hz1
    have h_e : 1 ≤ (z.num * r.den - z.den * r.num : ℤ).toNat := by
      grind +suggestions
    have h_e_le : (z.num * r.den - z.den * r.num : ℤ) < ((n + 1) / x.den * ((z.num * x.den - x.num * z.den) : ℤ) : ℝ) := by
      rw [ div_mul_eq_mul_div, lt_div_iff₀ ] <;> norm_cast at * <;> simp_all +decide [ Rat.lt_iff ];
      · nlinarith [ hr.2.2, show ( r.den : ℤ ) ≤ n from mod_cast hr.2.2 ];
      · exact x.pos
    generalize_proofs at *;
    rw [ Nat.cast_sub ] <;> norm_num;
    · norm_num [ Rat.mul_den, Rat.mul_num ] at *;
      exact ⟨ h_e, by linarith [ Nat.le_ceil ( ( n + 1 : ℝ ) / x.den * ( z.num * x.den - x.num * z.den ) ), show ( z.num * r.den : ℤ ) ≤ ⌈ ( n + 1 : ℝ ) / x.den * ( z.num * x.den - x.num * z.den ) ⌉₊ - 1 + z.den * r.num from by { exact Int.le_of_lt_add_one <| by { rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ Nat.le_ceil ( ( n + 1 : ℝ ) / x.den * ( z.num * x.den - x.num * z.den ) ) ] } } ] ⟩;
    · refine' mul_pos _ _ <;> norm_cast;
      · exact div_pos ( Nat.cast_pos.mpr ( Nat.succ_pos _ ) ) ( Nat.cast_pos.mpr ( Rat.pos _ ) );
      · rw [ Rat.lt_iff ] at * ; aesop;
  -- Each subset in the partition injects into the corresponding `leftFiber`.
  have h_injection : ∀ e ∈ Finset.Icc 1 (⌈((n + 1) / x.den * ((z.num * x.den - x.num * z.den) : ℤ) : ℝ)⌉₊ - 1), Set.ncard {r ∈ Bset | (z.num * r.den - z.den * r.num : ℤ).toNat = e} ≤ Set.ncard (leftFiber x z n e) := by
    intros e he
    have h_inj : Set.InjOn (fun r : ℚ => (r.den : ℤ)) {r ∈ Bset | (z.num * r.den - z.den * r.num : ℤ).toNat = e} := by
      intros r hr s hs hrs;
      -- Since $r.den = s.den$, we have $r.num = s.num$ because $r$ and $s$ are in lowest terms.
      have h_num_eq : r.num = s.num := by
        have h_num_eq : z.num * r.den - z.den * r.num = z.num * s.den - z.den * s.num := by
          grind +revert;
        norm_num +zetaDelta at *;
        rw [ hrs ] at h_num_eq; nlinarith [ show ( z.den : ℤ ) > 0 from Nat.cast_pos.mpr z.pos ] ;
      exact Rat.eq_iff_mul_eq_mul.mpr ( by simp +decide [ h_num_eq, hrs ] );
    have h_image : Set.image (fun r : ℚ => (r.den : ℤ)) {r ∈ Bset | (z.num * r.den - z.den * r.num : ℤ).toNat = e} ⊆ leftFiber x z n e := by
      intro d hd
      obtain ⟨r, hr, rfl⟩ := hd
      simp [leftFiber] at *;
      refine' ⟨ _, _, _, _ ⟩;
      · rw [ div_lt_iff₀ ] <;> norm_cast;
        · have := hr.1.2.1; rw [ Rat.lt_iff ] at this; norm_num at *;
          rw [ ← hr.2, Int.toNat_of_nonneg ];
          · nlinarith [ show ( z.den : ℤ ) > 0 by exact_mod_cast z.pos ];
          · have := hr.1.2.2; rw [ Rat.lt_iff ] at this; norm_num at *; linarith;
        · rw [ Rat.lt_iff ] at hxz ; linarith;
      · exact_mod_cast Nat.lt_succ_of_le ( hr.1.1.2.2 );
      · rw [ ← hr.2 ];
        rw [ Int.toNat_of_nonneg ];
        · norm_num;
        · grind;
      · rw [ ← hr.2, Int.toNat_of_nonneg ];
        · exact Int.isCoprime_iff_gcd_eq_one.mpr ( by simpa [ Int.gcd_natCast_natCast ] using r.reduced );
        · grind +suggestions;
    rw [ ← Set.InjOn.ncard_image h_inj ];
    apply_rules [ Set.ncard_le_ncard ];
    refine' Set.Finite.subset ( Set.finite_Ioo ( 0 : ℤ ) ( n + 1 ) ) _;
    intro q hq; exact ⟨ by
      have := hq.1; rw [ div_lt_iff₀ ] at this <;> norm_cast at * ;
      · nlinarith [ show 0 < z.num * x.den - x.num * z.den from by rw [ Rat.lt_iff ] at hxz; linarith ];
      · rw [ Rat.lt_iff ] at hxz ; linarith, by
      exact_mod_cast hq.2.1 ⟩ ;
  have h_card_union : Set.ncard Bset ≤ ∑ e ∈ Finset.Icc 1 (⌈((n + 1) / x.den * ((z.num * x.den - x.num * z.den) : ℤ) : ℝ)⌉₊ - 1), Set.ncard {r ∈ Bset | (z.num * r.den - z.den * r.num : ℤ).toNat = e} := by
    have h_card_union : ∀ (s : Finset ℕ) (f : ℕ → Set ℚ), Set.ncard (⋃ e ∈ s, f e) ≤ ∑ e ∈ s, Set.ncard (f e) := by
      intros s f;
      induction' s using Finset.induction with e s hes ih;
      · norm_num;
      · rw [ Finset.set_biUnion_insert, Finset.sum_insert hes ];
        refine ( Set.ncard_union_le _ _ ).trans ?_;
        exact Nat.add_le_add_left ih _;
    convert h_card_union _ _ using 2;
    convert h_partition using 1;
  exact_mod_cast h_card_union.trans ( Finset.sum_le_sum h_injection )

/-
**Left-side main bound (upper).** The matching upper bound to `left_count_main`:
`betweenCount n x z <= ((n+1)/z.den)*S(mu*u) + errTerm x z n`.
-/
set_option maxHeartbeats 1000000 in
theorem left_count_upper (x z : ℚ) (hx0 : 0 ≤ x) (hxz : x < z) (hz1 : z ≤ 1) (n : ℕ) :
    (betweenCount n x z : ℝ)
      ≤ ((n : ℝ) + 1) / z.den
          * Sfun (((n : ℝ) + 1) / x.den * ((z.num * (x.den : ℤ) - x.num * (z.den : ℤ) : ℤ) : ℝ))
        + errTerm x z n := by
  refine le_trans ( left_count_bridge_upper x z hx0 hxz hz1 n ) ?_;
  -- Applying the upper bound from `prim_prog_upper` to each term in the sum.
  have h_upper_bound : ∀ e ∈ Finset.Icc 1 (Nat.ceil (((n + 1) / x.den * (z.num * x.den - x.num * z.den : ℤ) : ℝ)) - 1), ((leftFiber x z n e).ncard : ℝ) ≤ ((Nat.totient e / e : ℝ) * ((n + 1) - ((x.den : ℝ) * e / ((z.num * (x.den : ℤ) - x.num * (z.den : ℤ) : ℤ) : ℝ))) / z.den) + (e.divisors.card : ℝ) := by
    intro e he;
    convert prim_prog_upper z.num z.den _ _ e _ _ _ _ using 1;
    · exact z.pos;
    · exact Int.isCoprime_iff_gcd_eq_one.mpr ( by simpa [ Int.gcd, Int.natAbs_abs ] using z.reduced );
    · linarith [ Finset.mem_Icc.mp he ];
    · rw [ div_le_iff₀ ] <;> norm_cast;
      · rw [ ← @Int.cast_le ℝ ] at * ; simp_all +decide [ mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv ];
        rw [ Nat.le_sub_iff_add_le ] at he;
        · contrapose! he;
          exact fun _ => Nat.lt_succ_of_le <| Nat.ceil_le.mpr <| by rw [ inv_mul_le_iff₀ <| Nat.cast_pos.mpr x.pos ] ; linarith;
        · omega;
      · rw [ Rat.lt_iff ] at hxz ; aesop;
  convert Finset.sum_le_sum h_upper_bound using 1;
  norm_num [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_div, Sfun, errTerm ];
  erw [ Finset.sum_Ico_eq_sub _ ] <;> norm_num [ Finset.sum_range_succ' ];
  cases h : ⌈ ( ( n : ℝ ) + 1 ) / x.den * ( z.num * x.den - x.num * z.den ) ⌉₊ <;> simp_all +decide [ Finset.sum_range_succ' ];
  field_simp;
  exact Finset.sum_congr rfl fun _ _ => by ring;

/-
**Right-side main bound.** The mirror of `left_count_main` via the reflection `q ↦ 1-q`:
for `0 ≤ z < w ≤ 1`, the count over `(z, w)` is at least
`((n+1)/z.den) * S((n+1)*z.den*(w-z)) - errTerm (1-w) (1-z) n`.
-/
set_option maxHeartbeats 1000000 in
theorem right_count_main (z w : ℚ) (hz0 : 0 ≤ z) (hzw : z < w) (hw1 : w ≤ 1) (n : ℕ) :
    ((n : ℝ) + 1) / z.den * Sfun (((n : ℝ) + 1) * z.den * ((w : ℝ) - z))
      - errTerm (1 - w) (1 - z) n ≤ (betweenCount n z w : ℝ) := by
  convert left_count_main ( 1 - w ) ( 1 - z ) _ _ _ n using 1;
  · congr! 1;
    congr! 2;
    · exact_mod_cast one_sub_den z |> Eq.symm;
    · rw [ div_mul_eq_mul_div, eq_div_iff ] <;> norm_cast <;> norm_num;
      rw [ ← Rat.mul_den_eq_num, ← Rat.mul_den_eq_num ] ; ring;
      grind +suggestions;
  · rw [ Erdos1005.betweenCount_reflect ];
  · linarith;
  · linarith;
  · linarith

/-
**Right-side main bound (upper).** The mirror of `left_count_upper` via `q ↦ 1-q`:
for `0 <= z < w <= 1`, `betweenCount n z w <= ((n+1)/z.den)*S((n+1)*z.den*(w-z)) + errTerm (1-w) (1-z) n`.
-/
set_option maxHeartbeats 1000000 in
theorem right_count_upper (z w : ℚ) (hz0 : 0 ≤ z) (hzw : z < w) (hw1 : w ≤ 1) (n : ℕ) :
    (betweenCount n z w : ℝ) ≤ ((n : ℝ) + 1) / z.den * Sfun (((n : ℝ) + 1) * z.den * ((w : ℝ) - z))
      + errTerm (1 - w) (1 - z) n := by
  -- Apply `left_count_upper` to the reflected interval `(1-w, 1-z)`.
  have h_left_count_upper : (betweenCount n (1 - w) (1 - z) : ℝ) ≤ ((n + 1) / (1 - z).den) * Sfun ((n + 1) / (1 - w).den * ((1 - z).num * (1 - w).den - (1 - w).num * (1 - z).den)) + errTerm (1 - w) (1 - z) n := by
    convert left_count_upper ( 1 - w ) ( 1 - z ) _ _ _ n using 1 <;> norm_num;
    · linarith;
    · linarith;
    · grobner;
  convert h_left_count_upper using 2;
  · convert betweenCount_reflect n z w using 1;
  · congr! 2;
    · rw [ one_sub_den ];
    · rw [ div_mul_eq_mul_div, eq_div_iff ] <;> norm_cast <;> norm_num [ Rat.den_nz ];
      rw [ ← Rat.mul_den_eq_num, ← Rat.mul_den_eq_num ] ; ring;
      grind +suggestions

/-
**Error-term bound.** `errTerm x z n ≤ M·(1 + log M)` where `M = ⌈((n+1)/x.den)·u⌉₊`,
`u = z.num·x.den − x.num·z.den`, via `divisor_sum_le`.
-/
theorem errTerm_le (x z : ℚ) (n : ℕ) :
    errTerm x z n
      ≤ (⌈((n : ℝ) + 1) / x.den * ((z.num * (x.den : ℤ) - x.num * (z.den : ℤ) : ℤ) : ℝ)⌉₊ : ℝ)
          * (1 + Real.log (⌈((n : ℝ) + 1) / x.den * ((z.num * (x.den : ℤ) - x.num * (z.den : ℤ) : ℤ) : ℝ)⌉₊)) := by
  refine' le_trans _ ( divisor_sum_le _ );
  refine' Finset.sum_le_sum_of_subset_of_nonneg ( Finset.Icc_subset_Icc_right _ ) fun _ _ _ => Nat.cast_nonneg _;
  exact Nat.pred_le _

/-
**Case A: two-sided count.** If the reference `z` is a reduced rational strictly inside
`(0,1)` and strictly inside the elementary interval `(x, elemR x)` (with `0 ≤ x` and
`elemR x ≤ 1`), then the number of order-`n` Farey fractions in `(x, elemR x)` is at least
`n/4` minus the two Section-2 error terms.
-/
theorem caseA_count (n : ℕ) (x z : ℚ) (hx0 : 0 ≤ x) (helemR1 : elemR x ≤ 1)
    (hz0 : 0 < z) (hz1 : z < 1) (hxz : x < z) (hzR : z < elemR x)
    (hmuL : (x.den : ℝ) ≤ (n : ℝ) + 1) :
    (n : ℝ) / 4 - errTerm x z n - errTerm (1 - elemR x) (1 - z) n
      ≤ (betweenCount n x (elemR x) : ℝ) := by
  -- From `0 < z < 1` reduced: `z.num ≥ 1` and `z.num < z.den`, so `z.den ≥ 2`.
  have hzden_ge_two : 2 ≤ z.den := by
    rw [ Rat.lt_iff ] at * ; norm_num at *;
    linarith [ show z.num > 0 from Rat.num_pos.mpr hz0 ];
  -- Note that from `0 ≤ x` and `x.den > 0` (by `Rat.den_pos`), `x.den ≥ 2`.
  have hxden_ge_two : 2 ≤ x.den := by
    contrapose! hzR; interval_cases _ : x.den <;> simp_all +decide [ elemR ] ;
    grind;
  -- From `x < z` reduced and `z.num ≥ 1` (by `Rat.num_pos.mpr`), `u = z.num * x.den - x.num * z.den > 0`.
  set u := z.num * x.den - x.num * z.den with hu
  have hu_pos : 0 < u := by
    exact sub_pos_of_lt ( by rw [ Rat.lt_iff ] at *; linarith );
  -- From `z < elemR x`, `v = (x.num + 1) * z.den - (x.den - 1) * z.num > 0`.
  set v := (x.num + 1) * z.den - (x.den - 1) * z.num with hv
  have hv_pos : 0 < v := by
    contrapose! hzR;
    unfold elemR;
    rw [ div_le_iff₀ ] <;> norm_cast at *;
    · rw [ ← Rat.num_div_den z ];
      rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> norm_cast at *;
      · grind;
      · positivity;
    · grind +splitIndPred;
  -- The arguments of `Sfun` satisfy `argL ≥ u` and `argR ≥ v`.
  have hargL_ge_u : ((n + 1 : ℝ) / x.den) * u ≥ u := by
    exact le_mul_of_one_le_left ( by positivity ) ( by rw [ le_div_iff₀ ( by positivity ) ] ; linarith )
  have hargR_ge_v : ((n + 1 : ℝ) * z.den * (elemR x - z)) ≥ v := by
    -- By definition of `elemR`, we have `elemR x = (x.num + 1) / (x.den - 1)`.
    have h_elemR : (elemR x : ℝ) = (x.num + 1) / (x.den - 1) := by
      unfold elemR; norm_num;
    simp_all +decide [ Rat.cast_def ];
    rw [ div_sub_div, mul_div, div_add', le_div_iff₀ ] <;> try nlinarith [ ( by norm_cast : ( 2 : ℝ ) ≤ x.den ), ( by norm_cast : ( 2 : ℝ ) ≤ z.den ) ];
    norm_cast at *;
    norm_num [ Int.subNatNat_eq_coe ] at * ; nlinarith [ mul_le_mul_of_nonneg_left hmuL ( show 0 ≤ z.den by positivity ) ];
  -- By `Sfun_ge_int`, `Sfun argL ≥ Sfun u.toNat` and `Sfun argR ≥ Sfun v.toNat`.
  have hSfun_ge_u : Sfun (((n + 1 : ℝ) / x.den) * u) ≥ Sfun u.toNat := by
    convert Sfun_ge_int _ _ using 1;
    · linarith [ Int.toNat_of_nonneg hu_pos.le ];
    · convert hargL_ge_u.le using 1;
      exact_mod_cast Int.toNat_of_nonneg hu_pos.le
  have hSfun_ge_v : Sfun (((n + 1 : ℝ) * z.den * (elemR x - z))) ≥ Sfun v.toNat := by
    convert Sfun_ge_int _ _ using 1;
    · grind;
    · exact le_trans ( mod_cast by rw [ Int.toNat_of_nonneg hv_pos.le ] ) hargR_ge_v;
  -- By `Sfun_pair_ge`, `Sfun u.toNat + Sfun v.toNat ≥ z.den / 4`.
  have hSfun_pair_ge : Sfun u.toNat + Sfun v.toNat ≥ (z.den : ℝ) / 4 := by
    have hSfun_pair_ge : u.toNat + v.toNat ≥ z.den + 1 := by
      linarith [ Int.toNat_of_nonneg hu_pos.le, Int.toNat_of_nonneg hv_pos.le, show z.num ≥ 1 from Rat.num_pos.mpr hz0 ];
    convert Sfun_pair_ge u.toNat v.toNat _ _ z.den _ _ using 1 <;> norm_cast;
    · linarith [ Int.toNat_of_nonneg hu_pos.le ];
    · grind;
  -- By `left_count_main` and `right_count_main`, we have:
  have h_left_count : (betweenCount n x z : ℝ) ≥ ((n + 1 : ℝ) / z.den) * Sfun (((n + 1 : ℝ) / x.den) * u) - errTerm x z n := by
    apply left_count_main x z hx0 hxz hz1.le n
  have h_right_count : (betweenCount n z (elemR x) : ℝ) ≥ ((n + 1 : ℝ) / z.den) * Sfun (((n + 1 : ℝ) * z.den * (elemR x - z))) - errTerm (1 - elemR x) (1 - z) n := by
    convert right_count_main z ( elemR x ) hz0.le hzR helemR1 n using 1;
  -- By `betweenCount_split`, we have:
  have h_betweenCount_split : (betweenCount n x (elemR x) : ℝ) ≥ (betweenCount n x z : ℝ) + (betweenCount n z (elemR x) : ℝ) := by
    exact_mod_cast betweenCount_split n x z ( elemR x ) hxz.le hzR.le;
  nlinarith [ show ( z.den : ℝ ) ≥ 2 by norm_cast, show ( x.den : ℝ ) ≥ 2 by norm_cast, mul_div_cancel₀ ( ( n : ℝ ) + 1 ) ( by positivity : ( z.den : ℝ ) ≠ 0 ) ]

/-
**Case B (small right endpoint).** If the reference `z` lies to the right of the elementary
interval (`elemR x < z ≤ 1`) with `0 ≤ x`, `x.num ≤ x.den - 2`, `x.den ≤ n`,
`|I| = elemR x - x ≥ 1/x.den`, and `2 ≤ (n+1)·z.den·(z - x)`, then the number of order-`n`
Farey fractions in `(x, elemR x)` is at least `n/4` minus the two error terms and one.
-/
theorem caseB_count (n : ℕ) (x z : ℚ) (hx0 : 0 ≤ x)
    (hxR : x < elemR x) (hRz : elemR x < z) (hz1 : z ≤ 1)
    (hbn : (x.den : ℝ) ≤ n) (hIb : (1 : ℝ) / x.den ≤ (elemR x : ℝ) - x)
    (h2X : (2 : ℝ) ≤ ((n : ℝ) + 1) * z.den * ((z : ℝ) - x)) :
    (n : ℝ) / 4 - errTerm x z n - errTerm (elemR x) z n - 1
      ≤ (betweenCount n x (elemR x) : ℝ) := by
  have h_caseB : (betweenCount n x (elemR x) : ℝ) ≥ (n : ℝ) / 4 - errTerm x z n - errTerm (elemR x) z n - 1 := by
    have h1 := betweenCount_split_le n x (elemR x) z (by
    lia) (by
    lia)
    have h2 := left_count_main x z hx0 (by
    linarith) (by
    linarith) n
    have h3 := left_count_upper (elemR x) z (by
    linarith) (by
    linarith) (by
    grobner) n
    -- Combining 1–4: `betweenCount n x (elemR x) ≥ ((n:ℝ)+1)/s * (Sfun argX - Sfun argE) - errTerm x z n - errTerm (elemR x) z n - 1`.
    have h4 : (n : ℝ) / 4 ≤ ((n : ℝ) + 1) / z.den * (Sfun ((n + 1) * z.den * (z - x)) - Sfun ((n + 1) * z.den * (z - elemR x))) := by
      convert caseB_ratio_ge n z.den ( mod_cast z.pos ) ( ( n + 1 ) * z.den * ( z - x ) ) ( ( n + 1 ) * z.den * ( z - elemR x ) ) _ _ _ _ using 1;
      · exact mul_nonneg ( mul_nonneg ( by positivity ) ( Nat.cast_nonneg _ ) ) ( sub_nonneg.mpr ( mod_cast hRz.le ) );
      · convert h2X using 1;
      · have h_caseB : (n + 1 : ℝ) * z.den * (elemR x - x) ≥ z.den := by
          refine' le_trans _ ( mul_le_mul_of_nonneg_left hIb <| by positivity );
          rw [ mul_one_div, le_div_iff₀ ] <;> norm_cast at * <;> nlinarith [ x.pos ];
        lia;
      · field_simp;
        rw [ div_le_iff₀ ] at hIb <;> norm_num at *;
        · nlinarith [ show ( x.den : ℝ ) ≤ n by norm_cast, show ( x.den : ℝ ) ≥ 1 by exact_mod_cast x.pos ];
        · exact x.pos;
    have h5 : (n + 1 : ℝ) / x.den * (z.num * x.den - x.num * z.den : ℝ) = (n + 1) * z.den * (z - x) ∧ (n + 1 : ℝ) / (elemR x).den * (z.num * (elemR x).den - (elemR x).num * z.den : ℝ) = (n + 1) * z.den * (z - elemR x) := by
      constructor <;> rw [ div_mul_eq_mul_div, div_eq_iff ] <;> norm_cast <;> norm_num [ Rat.num_div_den ]; all_goals rw [ ← Rat.mul_den_eq_num, ← Rat.mul_den_eq_num ] ; ring;
    simp_all +decide [ errTerm ];
    linarith [ ( by norm_cast : ( betweenCount n x z : ℝ ) ≤ betweenCount n x ( elemR x ) + betweenCount n ( elemR x ) z + 1 ) ];
  exact h_caseB

/-
**Case B (small left endpoint).** Mirror of `caseB_count` with the reference `z` to the left
(`0 ≤ z < x`).
-/
theorem caseB_count_left (n : ℕ) (x z : ℚ) (hz0 : 0 ≤ z) (hzx : z < x) (helemR1 : elemR x ≤ 1)
    (hxR : x < elemR x) (hbn : (x.den : ℝ) ≤ n) (hIb : (1 : ℝ) / x.den ≤ (elemR x : ℝ) - x)
    (h2X : (2 : ℝ) ≤ ((n : ℝ) + 1) * z.den * ((elemR x : ℝ) - z)) :
    (n : ℝ) / 4 - errTerm (1 - elemR x) (1 - z) n - errTerm (1 - x) (1 - z) n - 1
      ≤ (betweenCount n x (elemR x) : ℝ) := by
  -- Apply the two right-count lemmas, then `caseB_ratio_ge`, then `linarith`.
  have := @caseB_ratio_ge n;
  specialize this z.den (mod_cast z.pos) ((n + 1) * z.den * (elemR x - z)) ((n + 1) * z.den * (x - z)) ?_ ?_ ?_ ?_;
  · exact mul_nonneg ( mul_nonneg ( by positivity ) ( Nat.cast_nonneg _ ) ) ( sub_nonneg.mpr ( mod_cast hzx.le ) );
  · convert h2X using 1;
  · rw [ div_le_iff₀ ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero x.den_nz ) ] at hIb;
    rw [ ← mul_sub ];
    rw [ mul_right_comm ];
    exact le_mul_of_one_le_left ( Nat.cast_nonneg _ ) ( by nlinarith [ show ( x.den : ℝ ) ≥ 1 by exact_mod_cast x.pos, show ( z.den : ℝ ) ≥ 1 by exact_mod_cast z.pos ] );
  · field_simp;
    rw [ div_le_iff₀ ] at hIb <;> norm_num at *;
    · nlinarith [ show ( x.den : ℝ ) ≤ n by norm_cast, show ( x.den : ℝ ) ≥ 1 by exact_mod_cast x.pos ];
    · exact x.pos;
  · have h_betweenCount_split : (betweenCount n z (elemR x) : ℝ) ≤ (betweenCount n z x : ℝ) + (betweenCount n x (elemR x) : ℝ) + 1 := by
      exact_mod_cast betweenCount_split_le n z x ( elemR x ) hzx.le hxR.le;
    have := right_count_main z (elemR x) hz0 (hzx.trans hxR) helemR1 n
    have := right_count_upper z x hz0 hzx (hxR.le.trans helemR1) n
    linarith

end Erdos1005