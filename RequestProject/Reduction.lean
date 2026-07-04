import RequestProject.Statement

open scoped BigOperators
open Filter Topology

namespace Erdos1005

/-- The squeeze combiner: an `O(1)` upper bound and an `o(n)` lower bound imply
`f(n)/n → 1/4`. -/
theorem erdos_1005_of_bounds
    (hU : ∃ C : ℝ, ∀ n : ℕ, (fVal n : ℝ) ≤ (n : ℝ) / 4 + C)
    (hL : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (1 / 4 - ε) * (n : ℝ) ≤ (fVal n : ℝ)) :
    Tendsto (fun n : ℕ => (fVal n : ℝ) / n) atTop (nhds (1 / 4)) := by
  obtain ⟨C, hC⟩ := hU
  have hC' : ∀ n : ℕ, (fVal n : ℝ) ≤ (1 / 4 : ℝ) * n + C := by
    intro n; have := hC n; rw [show (1/4 : ℝ) * n = (n : ℝ) / 4 by ring]; linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hCdiv : Tendsto (fun n : ℕ => |C| / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat |C|
  have h1 : ∀ᶠ n : ℕ in atTop, |C| / (n : ℝ) < ε / 2 := by
    have := (hCdiv.eventually (gt_mem_nhds (by positivity : (0:ℝ) < ε/2)))
    simpa using this
  have h2 : ∀ᶠ n : ℕ in atTop, (1 / 4 - ε/2) * (n : ℝ) ≤ (fVal n : ℝ) :=
    hL (ε/2) (by positivity)
  have h3 : ∀ᶠ n : ℕ in atTop, (1 : ℕ) ≤ n := eventually_atTop.2 ⟨1, fun n hn => hn⟩
  have key : ∀ᶠ n : ℕ in atTop, dist ((fVal n : ℝ) / n) (1 / 4) < ε := by
    filter_upwards [h1, h2, h3] with n hn1 hn2 hn3
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn3
    rw [Real.dist_eq, abs_lt]
    refine ⟨?_, ?_⟩
    · have : (1 / 4 - ε/2) ≤ (fVal n : ℝ) / n := by
        rw [le_div_iff₀ hnpos]; linarith [hn2]
      linarith
    · have hub : (fVal n : ℝ) ≤ (1 / 4 : ℝ) * n + |C| := by
        linarith [hC' n, le_abs_self C]
      have hcc : |C| / (n:ℝ) * n = |C| := by field_simp
      have : (fVal n : ℝ) / n ≤ 1 / 4 + |C| / n := by
        rw [div_le_iff₀ hnpos]; nlinarith [hub, hcc]
      linarith [hn1]
  exact eventually_atTop.1 key

end Erdos1005
