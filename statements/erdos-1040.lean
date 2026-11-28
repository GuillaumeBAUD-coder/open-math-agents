import Mathlib

/-!
# Erdős Problem 1040

Source: https://www.erdosproblems.com/1040
Credit: Sudharsan Rajendiran

Let `F ⊆ ℂ` be a closed infinite set, and let `μ(F) = inf |{z : |f(z)| < 1}|`, where the infimum
ranges over all polynomials `f(z) = ∏ (z - z_i)` with every `z_i ∈ F`. Let
`ρ(F) = lim_{n → ∞} sup_{z_1, …, z_n ∈ F} (∏_{i < j} |z_i - z_j|)^{1 / C(n, 2)}`
be the transfinite diameter of `F`. Is `μ(F)` determined by `ρ(F)`? In particular, is
`μ(F) = 0` whenever `ρ(F) ≥ 1`?

We formalize the second question, in its affirmative form: if `ρ(F) ≥ 1` then `μ(F) = 0`. It is
open (the first question was answered negatively, by an example of two sets of transfinite
diameter `0`, which does not settle the second). A disproof is the negation of `main`. (The first
question is not formalized here.)

Conventions:
- `|·|` of a subset of `ℂ` is its Lebesgue measure, `MeasureTheory.volume` on `ℂ`.
- The polynomials are the monic polynomials `∏ (z - z_i)` of degree at least `1` with all roots
  in `F`, given by a nonempty finite multiset of roots. (Degree `0` would give `f = 1`, for which
  `{|f| < 1}` is empty, and would make `μ(F) = 0` for every `F`.)
- Values are taken in `ℝ≥0∞`: the supremum in `ρ` is `∞` for unbounded `F`. For every `n` the
  quantity `d n` below is the `n`-th term of the sequence in the definition of `ρ`; "`ρ(F) ≥ 1`"
  is read as: this sequence converges, and its limit is at least `1`. (For compact `F` the limit
  is classically known to exist; for unbounded `F` the terms are `∞` from `n = 2` on.)
-/

namespace OMA.S_erdos_1040

open Filter Topology MeasureTheory
open scoped ENNReal

/-- `|{z : |∏ (z - w)| < 1}|`, the polynomial having root multiset `s`. -/
noncomputable def sublevelMeasure (s : Multiset ℂ) : ℝ≥0∞ :=
  volume {z : ℂ | ‖(s.map (fun w => z - w)).prod‖ < 1}

/-- `μ(F)`. -/
noncomputable def μ (F : Set ℂ) : ℝ≥0∞ :=
  ⨅ (s : Multiset ℂ) (_ : s ≠ 0 ∧ ∀ w ∈ s, w ∈ F), sublevelMeasure s

/-- The `n`-th term `sup_{z_1, …, z_n ∈ F} (∏_{i < j} |z_i - z_j|)^{1 / C(n, 2)}` of the
sequence defining the transfinite diameter. -/
noncomputable def d (F : Set ℂ) (n : ℕ) : ℝ≥0∞ :=
  ⨆ (z : Fin n → ℂ) (_ : ∀ i, z i ∈ F),
    (∏ p ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2),
        (‖z p.1 - z p.2‖₊ : ℝ≥0∞)) ^ ((1 : ℝ) / (n.choose 2 : ℝ))

/-- Erdős Problem 1040, second question, affirmative form: if the transfinite diameter of a
closed infinite set `F ⊆ ℂ` is at least `1`, then `μ(F) = 0`. -/
theorem main : ∀ F : Set ℂ, IsClosed F → F.Infinite → ∀ ρ : ℝ≥0∞,
    Tendsto (d F) atTop (𝓝 ρ) → 1 ≤ ρ → μ F = 0 := by
  sorry

end OMA.S_erdos_1040
