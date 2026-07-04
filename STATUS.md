# Erdős 1005 — Lean formalization status

This project formalizes the statement and proof structure of the claim

> Let `f(n)` be the minimum number of Farey fractions of order `n` strictly between
> two *badly ordered* Farey fractions (a/b < c/d with a < c but b > d). Then
> `f(n) = (1/4 + o(1)) n`.

## Faithful statement

`RequestProject/Statement.lean` defines:

- `IsFarey n q := 0 ≤ q ∧ q ≤ 1 ∧ q.den ≤ n` (rationals are stored reduced, so `q.den`
  is the reduced denominator).
- `betweenCount n x y` — the number (`Set.ncard`) of order-`n` Farey fractions strictly
  between `x` and `y`.
- `BadlyOrdered n x y := IsFarey n x ∧ IsFarey n y ∧ x < y ∧ x.num < y.num ∧ y.den < x.den`.
- `fVal n := sInf {k | ∃ x y, BadlyOrdered n x y ∧ betweenCount n x y = k}` — i.e. `f(n)`.

The main theorem (`RequestProject/Main.lean`):

```
theorem erdos_1005 :
    Tendsto (fun n : ℕ => (fVal n : ℝ) / n) atTop (nhds (1 / 4))
```

This is the precise meaning of `f(n) = (1/4 + o(1)) n`.

## What is fully proved (0 sorries, only standard axioms)

- **High-level squeeze** (`erdos_1005_of_bounds`, `Reduction.lean`): the limit follows from an
  `O(1)` upper bound and an `o(n)` lower bound. ✔
- **`fVal` is a lower bound over any pair** (`fVal_le_of_badlyOrdered`, `Upper.lean`). ✔
- **Upper-bound construction** (`badlyOrdered_construction`, `Upper.lean`): the explicit pair
  `L = (2m-1)/(4m)`, `R = 2m/(4m-1)` (with `m = ⌊n/4⌋ ≥ 1`, `4m ≤ n`) is a genuine badly
  ordered pair in `F_n` (reducedness, `L < R`, `a < c`, `b > d`, both in `[0,1]`). ✔
- **Upper-bound assembly** (`fVal_upper_bound`, `Upper.lean`): given the Section-10 count, the
  `O(1)` upper bound `f(n) ≤ n/4 + C` follows (including the finitely many small `n`). ✔
- **Farey infrastructure** (`Farey.lean`): finiteness of the Farey set and of any between-set;
  monotonicity of `betweenCount`. ✔
- **Section-1 reduction** (`elemR_le`, `betweenCount_ge_elementary`, `Farey.lean`): every badly
  ordered pair contains the elementary interval `I_{a,b} = (a/b, (a+1)/(b-1))`, so its count is
  at least the elementary-interval count. ✔
- **Lower-bound reduction** (`fVal_lower_bound`, `Lower.lean`): the `sInf`/non-emptiness glue
  combined with the Section-1 reduction reduces the lower bound to a single
  elementary-interval count lemma. ✔
- **Section-5 totient backbone** (`four_mul_Phi_ge`, `TotientSum.lean`):
  `4·Φ(m) ≥ m(m+1)` where `Φ(m) = ∑_{j≤m} φ(j)`, fully proved, via three verified lemmas:
  the coprime-pair identity `2Φ(m) = P(m)+1`, the union bound on non-coprime pairs, and the
  prime reciprocal-square bound `∑_{p≤m} 1/p² ≤ 97/200`. ✔

## Section 10 upper-count core — NOW FULLY PROVED (0 sorries, standard axioms)

`upper_count_bound` (`Upper.lean`) is now **completely proved**. Hence the entire upper-bound
half `fVal_upper_bound` is machine-checked with only `propext`, `Classical.choice`, `Quot.sound`.
The proof formalizes the Section-10 classification by `e = den - 2·num`:

- `Tset m` (`Upper.lean`): an explicit finite set capturing every order-`n` Farey fraction
  strictly between `L` and `R` — the dominant `e = 1` family `a/(2a+1)` for `a ∈ [m, 2m+1]`
  (an `image` of `Finset.Icc`), together with the `O(1)` exceptional fractions from
  `e ∈ {-1, 0, 3}`.
- `Tset_card_le` : `(Tset m).card ≤ m + 6`.
- `between_ineqs` : the integer-inequality form of membership
  (`(2m-1)·b < 4m·a`, `(4m-1)·a < 2m·b`, `1 ≤ a ≤ b ≤ n`).
- `between_mem_Tset` : every such fraction lies in `Tset m` (the full `-2 ≤ e ≤ 3` case
  analysis, with `e = ±2` excluded by reducedness/integrality).
- `upper_count_bound` : `#(F_n ∩ (L,R)) ≤ m + 6` via `Set.ncard_le_ncard` against `↑(Tset m)`.

## What remains (1 clearly-marked `sorry`)

The single remaining deep counting core requires analytic Farey interval-counting machinery
(the `3/π²` density of Farey fractions, primitive-progression/determinant counting) that is
**not** present in Mathlib and would need to be built from scratch.

- `elem_interval_count_lower` (`Lower.lean`) — **Sections 2–9**: the uniform lower bound
  `#(F_n ∩ I_{a,b}) ≥ (1/4 - ε) n` for every elementary interval.

Consequently `erdos_1005` itself is **not** yet a complete (sorry-free) proof: it currently
depends on this one lemma.  This core has two independent missing infrastructures: (a) the
Section-2 primitive-progression counting `#{q : A<q<B, (p,q)=1, hq-sp=e} = (φ(e)/e)(B-A)/s +
O(τ(e))`, and (b) the Section-6 large-interval density (the `3/π²` Farey density, or
equivalently the max-gap `≤ 1/n` bound, which itself needs the still-open `det = 1` half of
Lemma 4.1).

## A note on the manuscript

While formalizing Section 5 we checked the prime constant. The true value of `∑_p 1/p²` is
`≈ 0.45224`. The manuscript's bound `∑_p 1/p² < 459/1000 = 0.459` is therefore **correct**.
(An initial tighter guess of `9/20 = 0.45` used during formalization was found to be *false*
by the prover — it is below the true value — which is why the formalized constant is `97/200 =
0.485`, chosen `< 1/2` with enough margin for the assembly.)

## Additional fully-proved delicate lemmas (later pass, 0 sorries, standard axioms)

### Section 5 — totient-increment Lemma 5.1 (`RequestProject/TotientIncrement.lean`)
The entire Lemma 5.1 is now formalized, building on the `four_mul_Phi_ge` backbone:
- `Sfun x = ∑_{1≤e<x} (1 - e/x)·φ(e)/e`, `Ffun x = Sfun x - x/4`, and the closed form
  `Sfun_eq_on_Icc : Sfun x = A_m - Φ(m)/x` on `[m, m+1]`.
- Integer increment `Sfun_int_increment`, integer monotonicity `Ffun_int_mono(_le)`, and the
  headline `Sfun_ge_quarter : (m:ℝ)/4 ≤ Sfun m` for `m ≥ 2`.
- The within-interval concavity facts (`Ffun_diff_on_unit`, `Ffun_ge_min_on_unit(_gen)`),
  the stronger totient bound `Phi_quad_lower : (m+1)² ≤ 4·Φ(m)` for `m ≥ 7`, unit-interval
  monotonicity for `m ≥ 7`, the max bound `Ffun_unit_le_succ2`, and unit step `Ffun_step_le`.
- The two real-variable increments `Sfun_increment_ge_one` (`x≥1, y≥1`) and
  `Sfun_increment_ge_two` (`x≥0, y≥2`): `Sfun(x+y) - Sfun x ≥ y/4`.

### Section 4 — Farey-gap geometry (`RequestProject/FareyGap.lean`)
- `mediant` with `lt_mediant`, `mediant_lt` (strict betweenness), `mediant_den_le`,
  `mediant_nonneg`, `mediant_le_one`.
- `farey_neighbor_den_sum` — the `s + s' > Q` half of Lemma 4.1 (consecutive order-`Q`
  Farey fractions have denominator sum exceeding `Q`).
- `between_den_mul_det_ge` — the determinant inequality `q·(c·b - a·d) ≥ b + d` for any
  fraction `p/q` strictly between `a/b` and `c/d` (the analytic form used in Sections 7–8).

The `det = 1` half of Lemma 4.1 (the integer-lattice fundamental-domain argument) and the two
original counting cores (`upper_count_bound`, `elem_interval_count_lower`) remain open.

---

## Newest pass — Section 4 `det = 1` and the complete Section 2 counting machinery

This pass closed two of the previously-open deep pieces of the lower-bound core, both fully
proved with only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

### Section 4 — Lemma 4.1 determinant half (`RequestProject/FareyGap.lean`)
- `farey_neighbor_det` : if `x < y` are consecutive order-`Q` Farey fractions (no order-`Q`
  fraction strictly between), then `x.den·y.num − x.num·y.den = 1`. This was previously the
  open "integer-lattice fundamental-domain" piece; it is proved by an explicit constructive
  argument (Bézout solution `s·p − h·q = 1`, adjusted to put `A = h'·q − s'·p` into `[0,D)`,
  yielding an in-between fraction `p/q` of denominator `≤ max(s,s') ≤ Q` when `D ≥ 2`).

### Section 2 — primitive-progression counting (`RequestProject/PrimProg.lean`, new file)
The entire Section-2 counting infrastructure is now machine-checked:
- `moebius_div_sum_eq_totient_div` : `∑_{d∣n} μ(d)/d = φ(n)/n`.
- `residue_interval_count` : the number of integers in `(A,B)` in a fixed residue class
  mod `M` is within `1` of `(B−A)/M`.
- `residue_class_of_conditions` : `{q : d∣q ∧ (s·d)∣(h·q−e)}` is a single residue class
  mod `s·d` (for `d∣e`, `gcd(h,s)=1`).
- `Nd_count_bound` : the per-`d` count `#{q∈(A,B) : d∣q ∧ (s·d)∣(h·q−e)}` is within `1`
  of `(B−A)/(s·d)`.
- `prim_prog_lower` : **the Section-2 primitive-progression lower bound** — for `gcd(h,s)=1`,
  `e ≥ 1`, `A ≤ B`, the number of `q∈(A,B)` with `s∣(h·q−e)` and `gcd((h·q−e)/s, q)=1` is
  `≥ (φ(e)/e)·(B−A)/s − τ(e)`, where `τ(e) = e.divisors.card`. Proved by the exact Möbius
  expansion of the coprimality indicator, the per-`d` residue-class count, and the
  totient/Möbius identity.

### What still remains (1 `sorry`, in `RequestProject/Lower.lean`)
`elem_interval_count_lower` (the uniform elementary-interval bound, Sections 3,6–9) is still
open. With Section 2 (`prim_prog_lower`), Section 4 (`farey_neighbor_det`,
`farey_neighbor_den_sum`, `between_den_mul_det_ge`) and Section 5 (`TotientIncrement.lean`)
now in place, the remaining work to close it is the *assembly*: the ℚ-`betweenCount`↔integer
double-count bridge; the Case-A/Case-B reference dichotomy and one-sided counts; the small-`b`
density range; a from-scratch harmonic/`τ`-sum bound (Mathlib has no harmonic-number bound);
and the uniform `o(n)` error/`ε` management combining all cases. Consequently the top-level
`erdos_1005` still depends on this single `sorry`.

### Section-2/5 assembly building blocks (`RequestProject/LowerCore.lean`, new file)
Reusable analytic lemmas that feed the (still open) elementary-interval assembly:
- `harmonic_le_one_add_log` : `∑_{d=1}^N 1/d ≤ 1 + log N` (built from scratch; Mathlib has no
  harmonic-number bound).
- `divisor_sum_le` : `∑_{e=1}^N τ(e) ≤ N·(1 + log N)` — the error-term (`τ`-sum) control.
- `totient_window_sum_eq` : `∑_{0≤e<⌈μu⌉} (φ(e)/e)·(μ − e/u) = μ·S(μu)` — the exact identity
  turning a summed `prim_prog_lower` main-term into the Section-5 function `Sfun`.

All proved with only the standard axioms. These, together with `prim_prog_lower`,
`farey_neighbor_det`, and `TotientIncrement.lean`, reduce the open `elem_interval_count_lower`
to the geometric assembly (betweenCount↔integer-fiber bridge, Case-A/B reference dichotomy,
small-`b` range, and uniform `o(n)` error management).

---

## COMPLETE — `erdos_1005` is now fully proved (0 sorries)

The final remaining core, `elem_interval_count_lower` (Sections 2–9, the uniform
elementary-interval lower bound), has been fully assembled in `RequestProject/LowerFinal.lean`.
Consequently the top-level theorem `erdos_1005` (in `RequestProject/Main.lean`) is now a
complete, sorry-free proof depending only on the standard axioms `propext`, `Classical.choice`,
`Quot.sound` (plus `Lean.ofReduceBool`/`Lean.trustCompiler` from the pre-existing `native_decide`
finite checks in the totient lemmas).

### `RequestProject/LowerFinal.lean` (new)
- `elem_interval_count_lower_final` : the `∀ ε>0, ∀ᶠ n, (1/4-ε)n ≤ betweenCount n x (elemR x)`
  bound, split on `b = x.den`:
  * **Small `b`** (`b*b < n`): `smallb_bound` + `density_count_lower` give `≥ (n+1)√n/4 - n(1+log n)`,
    dominating `(1/4-ε)n` (`smallb_eventually`).
  * **Large `b`** (`n ≤ b*b`): `largeb_core` with `Q` chosen by `largeb_Q_exists` (`Q^3 ≤ n ≤ Q^4`),
    giving `n/4 - 2·Kmax·(1+log Kmax) - 1 ≤ count`, where the uniform error `→ o(n)`
    (`largeb_eventually`, via `Kmax ≤ Kbar`).
- `largeb_core` dispatches the Farey-gap dichotomy at order `Q`:
  * `largeb_caseI` : `(elemR x).den ≤ Q` — direct `left_count_main`.
  * `largeb_caseII` : an order-`Q` fraction lies strictly inside — `caseA_count`.
  * `largeb_caseIII` (→ `largeb_caseIIIa` / `largeb_caseIIIb`) : `I` lies in a single `F_Q` gap;
    `caseB_count` / `caseB_count_left` with the smaller-denominator endpoint.
- Supporting: `badly_left_facts`, `elemR_sub_gt`, `det_real_eq`, `ceil_le_Kmax`,
  `errTerm_le_Kmax(')`, `h2X_left`, `mul_one_add_log_mono`, `Kmax_le_Kbar`.
- `fVal_lower_bound` (moved here from `Lower.lean`) now uses `elem_interval_count_lower_final`.

`RequestProject/Lower.lean` no longer contains the old `sorry`ed statement; `Main.lean` imports
`LowerFinal`. Verified: `#print axioms erdos_1005` uses only the allowed axioms.
