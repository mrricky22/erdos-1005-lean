import RequestProject.Statement

open scoped BigOperators
open Filter Topology

namespace Erdos1005

/-- `f(n)` is a lower bound for the count over any badly ordered pair: this is the
defining `sInf` property. -/
theorem fVal_le_of_badlyOrdered {n : ℕ} {x y : ℚ} (h : BadlyOrdered n x y) :
    fVal n ≤ betweenCount n x y := by
  apply Nat.sInf_le
  exact ⟨x, y, h, rfl⟩

/-- Left endpoint of the Section-10 construction: `L = (2m-1)/(4m)`. -/
noncomputable def Lf (m : ℕ) : ℚ := ((2 * (m : ℤ) - 1 : ℤ) : ℚ) / ((4 * (m : ℤ) : ℤ) : ℚ)

/-- Right endpoint of the Section-10 construction: `R = 2m/(4m-1)`. -/
noncomputable def Rf (m : ℕ) : ℚ := ((2 * (m : ℤ) : ℤ) : ℚ) / ((4 * (m : ℤ) - 1 : ℤ) : ℚ)

/-- The explicit pair `L = (2m-1)/(4m)`, `R = 2m/(4m-1)` is badly ordered in `F_n`,
provided `m ≥ 1` and `4m ≤ n`. -/
theorem badlyOrdered_construction (n m : ℕ) (hm : 1 ≤ m) (hn : 4 * m ≤ n) :
    BadlyOrdered n (Lf m) (Rf m) := by
  unfold Lf Rf
  refine' ⟨ _, _, _, _, _ ⟩ <;> norm_num
  · refine' ⟨ _, _, _ ⟩
    · exact div_nonneg ( sub_nonneg_of_le ( by norm_cast; linarith ) ) ( by positivity )
    · rw [ div_le_iff₀ ] <;> linarith [ ( by norm_cast : ( 1 : ℚ ) ≤ m ) ]
    · rw [ div_eq_mul_inv ]
      norm_cast ; norm_num [ Rat.mul_den, Rat.mul_num ]
      split_ifs <;> simp_all +decide [ Int.sign_eq_one_of_pos ( by positivity : 0 < ( m : ℤ ) ) ]
      exact le_trans ( Nat.div_le_self _ _ ) ( by linarith )
  · refine' ⟨ _, _, _ ⟩
    · exact div_nonneg ( by positivity ) ( by linarith [ show ( m : ℚ ) ≥ 1 by norm_cast ] )
    · rw [ div_le_iff₀ ] <;> linarith [ show ( m : ℚ ) ≥ 1 by norm_cast ]
    · rw [ div_eq_mul_inv ]
      erw [ Rat.mul_den ] ; norm_num
      norm_cast ; simp_all +decide
      norm_num [ Int.subNatNat_eq_coe, Rat.mul_den, Rat.mul_num ]
      exact le_trans ( Nat.div_le_self _ _ ) ( by omega )
  · rw [ div_lt_div_iff₀ ] <;> nlinarith [ ( by norm_cast : ( 1 : ℚ ) ≤ m ) ]
  · have h_num_L : ((2 * m - 1 : ℚ) / (4 * m)).num = 2 * m - 1 := by
      convert Rat.num_div_eq_of_coprime ?_ ?_
      all_goals norm_cast
      · linarith
      · rw [ Int.subNatNat_of_le ( by linarith ) ] ; norm_cast
        rcases m with ( _ | _ | m ) <;> simp_all +arith +decide [ Nat.mul_succ ]
        norm_num [ ( by ring : 4 * m + 8 = 2 * ( 2 * m + 3 ) + 2 ) ]
        grind
    have h_num_R : ((2 * m : ℚ) / (4 * m - 1)).num = 2 * m := by
      have h_coprime : Int.gcd (2 * m : ℤ) (4 * m - 1) = 1 := by
        norm_num [ show ( 4 * m - 1 : ℤ ) = 2 * m * 2 - 1 by ring ]
      convert Rat.num_div_eq_of_coprime _ _ using 1
      rotate_left
      exacts [ 4 * m - 1, by omega, by simpa [ Int.gcd, Int.natAbs_neg ] using h_coprime, by norm_cast ]
    linarith
  · have h_denom_L : ((2 * m - 1 : ℚ) / (4 * m)).den = 4 * m := by
      convert Rat.den_div_eq_of_coprime _ _ using 1 <;> norm_cast
      convert Int.natCast_inj.symm
      · positivity
      · rw [ Int.subNatNat_of_le ( by linarith ) ] ; norm_cast
        rcases m with ( _ | _ | m ) <;> simp_all +arith +decide [ Nat.mul_succ ]
        norm_num [ ( by ring : 4 * m + 8 = 2 * ( 2 * m + 3 ) + 2 ) ]
        grind
    have h_denom_R : ((2 * m : ℚ) / (4 * m - 1)).den = 4 * m - 1 := by
      convert Rat.den_div_eq_of_coprime _ _ using 1
      rotate_left
      exact 2 * m
      exact 4 * m - 1
      · grind +splitImp
      · refine' Nat.Coprime.symm ( Nat.coprime_of_dvd' _ )
        intro k hk hk₁ hk₂; have := Int.natAbs_dvd_natAbs.mpr ( Int.dvd_sub ( Int.natCast_dvd.mpr hk₂ |> fun x => x.mul_left 2 ) ( Int.natCast_dvd.mpr hk₁ ) ) ; norm_num at this
        exact this.trans ( by ring_nf; norm_num )
      · norm_cast
        rw [ Int.subNatNat_of_le ( by linarith ) ] ; norm_cast
    omega

/-- The candidate finite set capturing every Farey fraction strictly between `L` and `R`.
The `e = den - 2·num = 1` family `a/(2a+1)` (with `a ∈ [m, 2m+1]`) is the dominant part;
the remaining `O(1)` exceptional fractions (from `e ∈ {-1,0,3}`) are listed explicitly. -/
noncomputable def Tset (m : ℕ) : Finset ℚ :=
  ((Finset.Icc (m : ℤ) (2 * m + 1)).image (fun a : ℤ => (a : ℚ) / (2 * a + 1)))
    ∪ {1 / 2, (2 * (m : ℚ) + 1) / (4 * m + 1), (2 * (m : ℚ) + 2) / (4 * m + 3), 2 / 7}

/-
The candidate set has at most `m + 6` elements.
-/
lemma Tset_card_le (m : ℕ) : (Tset m).card ≤ m + 6 := by
  refine' le_trans ( Finset.card_union_le _ _ ) _;
  refine' le_trans ( add_le_add ( Finset.card_image_le ) ( Finset.card_insert_le _ _ ) ) _ ; norm_num [ Finset.card_insert_of_notMem ] ; ring_nf ; norm_cast ; simp +arith +decide;
  grind +qlia

/-
Integer-inequality form of membership in the between-set.  For `q` strictly between
`L = (2m-1)/(4m)` and `R = 2m/(4m-1)` and `q ∈ F_n`, writing `a = q.num`, `b = q.den`:
`1 ≤ a ≤ b ≤ n`, `(2m-1)·b < 4m·a` and `(4m-1)·a < 2m·b`.
-/
lemma between_ineqs {n m : ℕ} (hm : 1 ≤ m) {q : ℚ}
    (hF : IsFarey n q) (hL : Lf m < q) (hR : q < Rf m) :
    1 ≤ q.num ∧ q.num ≤ (q.den : ℤ) ∧ (q.den : ℤ) ≤ (n : ℤ) ∧
      (2 * (m : ℤ) - 1) * (q.den : ℤ) < 4 * (m : ℤ) * q.num ∧
      (4 * (m : ℤ) - 1) * q.num < 2 * (m : ℤ) * (q.den : ℤ) := by
  refine' ⟨ _, _, _, _, _ ⟩;
  · contrapose! hL; simp_all +decide [ Lf ] ;
    exact le_trans ( Rat.num_nonpos.mp ( by linarith ) ) ( by exact div_nonneg ( sub_nonneg.mpr ( by norm_cast; linarith ) ) ( by positivity ) );
  · simpa [ Rat.le_iff ] using hF.2.1;
  · exact_mod_cast hF.2.2;
  · unfold Lf Rf at *;
    rw [ div_lt_iff₀ ] at hL <;> norm_cast at *;
    · rw [ ← Rat.num_div_den q ] at hL;
      rw [ div_mul_eq_mul_div, lt_div_iff₀ ] at hL <;> norm_cast at * ; linarith [ q.pos ];
      exact q.pos;
    · linarith;
  · have hR_cast : (q.num : ℚ) / q.den < (2 * m : ℚ) / (4 * m - 1) := by
      convert hR using 1 <;> norm_num [ Rat.num_div_den ];
      unfold Rf; norm_num;
    rw [ div_lt_div_iff₀ ] at hR_cast <;> norm_cast at *;
    · grind;
    · exact q.pos;
    · rw [ Int.subNatNat_eq_coe ] ; norm_num ; linarith

/-
**Section 10 classification.** Every order-`n` Farey fraction strictly between `L` and
`R` lies in the explicit finite set `Tset m` (with `4m ≤ n ≤ 4m+3`, `m ≥ 1`).
-/
set_option maxHeartbeats 1000000 in
lemma between_mem_Tset {n m : ℕ} (hm : 1 ≤ m) (hn : n ≤ 4 * m + 3) {q : ℚ}
    (hF : IsFarey n q) (hL : Lf m < q) (hR : q < Rf m) : q ∈ Tset m := by
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, 1 ≤ a ∧ a ≤ b ∧ b ≤ n ∧ (2 * m - 1) * b < 4 * m * a ∧ (4 * m - 1) * a < 2 * m * b ∧ q = a / b := by
    have := between_ineqs hm hF hL hR;
    exact ⟨ q.num, q.den, this.1, this.2.1, mod_cast this.2.2.1, mod_cast this.2.2.2.1, mod_cast this.2.2.2.2, q.num_div_den.symm ⟩;
  -- From the inequalities, we derive that $b = 2a + k$ for some $k \in \{-2, -1, 0, 1, 2, 3\}$.
  obtain ⟨k, hk⟩ : ∃ k : ℤ, b = 2 * a + k ∧ -2 ≤ k ∧ k ≤ 3 := by
    exact ⟨ b - 2 * a, by ring, by nlinarith, by nlinarith ⟩;
  rcases hk with ⟨ rfl, hk₁, hk₂ ⟩ ; interval_cases k <;> simp_all +decide ;
  any_goals nlinarith;
  · -- From the inequalities, we derive that $a = 2m + 1$ or $a = 2m + 2$.
    have ha : a = 2 * m + 1 ∨ a = 2 * m + 2 := by
      grind +qlia;
    rcases ha with ( rfl | rfl ) <;> norm_num [ Tset ];
    · exact Or.inr <| Or.inl <| by ring;
    · grind +qlia;
  · ring_nf at *; norm_num [ show a ≠ 0 by linarith ] at *;
    rw [ mul_inv_cancel₀ ( by norm_cast; linarith ) ] ; norm_num [ Tset ];
  · exact Finset.mem_union_left _ <| Finset.mem_image.mpr ⟨ a, Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩, rfl ⟩;
  · -- From the inequalities, we derive that $a = 2m$.
    have ha : a = 2 * m := by
      grind;
    have := hF.2.2; simp_all +decide [ IsFarey ] ;
    norm_num [ show ( 2 * ( 2 * m ) + 2 : ℚ ) = 2 * ( 2 * m + 1 ) by ring, Rat.divInt_eq_div ] at *;
    norm_num [ show ( 2 * m : ℚ ) / ( 2 * ( 2 * m + 1 ) ) = m / ( 2 * m + 1 ) by rw [ div_eq_div_iff ] <;> ring <;> positivity ] at *;
    exact Finset.mem_union_left _ ( Finset.mem_image.mpr ⟨ m, Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩, by push_cast; ring ⟩ );
  · -- From the inequalities, we derive that $a = 2$ and $m = 1$.
    have ha : a = 2 := by
      nlinarith only [ hab, hm, hn ]
    have hm : m = 1 := by
      grind +splitIndPred
    subst ha
    subst hm
    norm_num [ Tset ] at *

/-- **Section 10 count.** There is an absolute constant `C₀` such that for `m = ⌊n/4⌋`
(i.e. `4m ≤ n ≤ 4m+3`) with `m ≥ 1`, the number of order-`n` Farey fractions strictly
between `L = (2m-1)/(4m)` and `R = 2m/(4m-1)` is at most `m + C₀`.
This is the refined count of Section 10 (classification by `e = q - 2p`). -/
theorem upper_count_bound :
    ∃ C₀ : ℕ, ∀ n m : ℕ, 1 ≤ m → 4 * m ≤ n → n ≤ 4 * m + 3 →
      betweenCount n (Lf m) (Rf m) ≤ m + C₀ := by
  refine ⟨6, ?_⟩
  intro n m hm _ hn
  have hsub : {q : ℚ | IsFarey n q ∧ Lf m < q ∧ q < Rf m} ⊆ ↑(Tset m) := by
    rintro q ⟨hF, hL, hR⟩
    exact between_mem_Tset hm hn hF hL hR
  have hle : betweenCount n (Lf m) (Rf m) ≤ (Tset m).card := by
    unfold betweenCount
    rw [← Set.ncard_coe_finset (Tset m)]
    exact Set.ncard_le_ncard hsub (Tset m).finite_toSet
  exact le_trans hle (Tset_card_le m)

/-- **Upper bound (Section 10).** There is an absolute constant `C` such that
`f(n) ≤ n/4 + C` for all `n`. -/
theorem fVal_upper_bound : ∃ C : ℝ, ∀ n : ℕ, (fVal n : ℝ) ≤ (n : ℝ) / 4 + C := by
  obtain ⟨C₀, hC₀⟩ := upper_count_bound
  refine ⟨(C₀ : ℝ) + (fVal 0 + fVal 1 + fVal 2 + fVal 3 : ℕ), ?_⟩
  intro n
  rcases lt_or_ge n 4 with hsmall | hbig
  · -- Small cases n ∈ {0,1,2,3}: bound by the (finite) sum of those values.
    have hle : fVal n ≤ (fVal 0 + fVal 1 + fVal 2 + fVal 3 : ℕ) := by
      interval_cases n <;> omega
    have : (fVal n : ℝ) ≤ (fVal 0 + fVal 1 + fVal 2 + fVal 3 : ℕ) := by exact_mod_cast hle
    have hn0 : (0:ℝ) ≤ (n:ℝ) / 4 := by positivity
    push_cast at this ⊢
    nlinarith [this, hn0]
  · -- Main case: m = n/4 ≥ 1, 4m ≤ n ≤ 4m+3.
    set m := n / 4 with hmdef
    have hm1 : 1 ≤ m := by omega
    have hmle : 4 * m ≤ n := by omega
    have hmge : n ≤ 4 * m + 3 := by omega
    have hbad := badlyOrdered_construction n m hm1 hmle
    have h1 : fVal n ≤ betweenCount n (Lf m) (Rf m) := fVal_le_of_badlyOrdered hbad
    have h2 : betweenCount n (Lf m) (Rf m) ≤ m + C₀ := hC₀ n m hm1 hmle hmge
    have h3 : fVal n ≤ m + C₀ := le_trans h1 h2
    have h4 : (fVal n : ℝ) ≤ (m : ℝ) + C₀ := by exact_mod_cast h3
    have h5 : (m : ℝ) ≤ (n : ℝ) / 4 := by
      have : (4 * m : ℕ) ≤ n := hmle
      have : (4 : ℝ) * m ≤ n := by exact_mod_cast this
      linarith
    have h6 : (0:ℝ) ≤ (fVal 0 + fVal 1 + fVal 2 + fVal 3 : ℕ) := by positivity
    push_cast at h4 h6 ⊢
    nlinarith [h4, h5, h6]

end Erdos1005