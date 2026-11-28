import Mathlib.Probability.Density
import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Extracting moments of $\max(X_1,\ldots,X_k)$ from asymptotic behavior of $\mathbb{E}[(X_1^n+\cdots+X_k^n)^m]$

Source: https://mathoverflow.net/questions/455319 (Ben Deitmar, September 26, 2023).
Credit: @jared-jasinski

Reading of the source:
* For a fixed positive integer `k`, we consider `k` non-negative real-valued random variables
  `X₁, …, Xₖ` on an arbitrary probability space `(Ω, ℙ)` (in `Type`, which loses no generality
  since the joint law lives on `Fin k → ℝ`).
* "with density functions" is read as each marginal `X i` having a probability density function
  with respect to Lebesgue measure on `ℝ` (`MeasureTheory.HasPDF (X i) ℙ volume`). In particular,
  each `X i` is a.e. positive, so `𝔼[(X₁^n + ⋯ + Xₖ^n)^m] > 0` for all `n, m : ℕ`.
* Knowing `𝔼[(X₁^n + ⋯ + Xₖ^n)^m]` as real numbers for all `n, m ∈ ℕ` presupposes that these
  expectations are finite, so we assume integrability of `(∑ i, X i ^ n) ^ m` for all `n, m : ℕ`.
* "the moments `𝔼[max(X₁, …, Xₖ)^a]`" is read with natural-number order `a : ℕ`.
* The source poses two settings:
  - Setting (a): exact knowledge of `M(n, m) = 𝔼[(X₁^n + ⋯ + Xₖ^n)^m]` for all `n, m ∈ ℕ`.
  - Setting (b): knowledge of an approximation `A(n, m) = M(n, m) + R(m, n)` whose relative
    error vanishes uniformly in `m` as `n → ∞`, i.e.
    `sup_{m ∈ ℕ} |R(m, n)| · M(n, m)⁻¹ → 0` as `n → ∞`.
  Both settings are formalized as the existence of a functional `F : (ℕ → ℕ → ℝ) → ℝ`
  (allowed to depend on `k` and `a`) that extracts `𝔼[max(X₁, …, Xₖ)^a]` from the moment table
  (exact in Setting (a), approximate in Setting (b)).
-/

namespace OMA.S_mo_455319

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory

/-- The `(n, m)` power-sum moment `𝔼[(X₁^n + ⋯ + Xₖ^n)^m]`. -/
noncomputable def powerSumMoment {Ω : Type} [MeasureSpace Ω] {k : ℕ}
    (X : Fin k → Ω → ℝ) (n m : ℕ) : ℝ :=
  ∫ ω, (∑ i : Fin k, X i ω ^ n) ^ m ∂ℙ

/-- The `a`-th moment of the maximum `𝔼[max(X₁, …, Xₖ)^a]`. -/
noncomputable def maxMoment {Ω : Type} [MeasureSpace Ω] {k : ℕ}
    (hk : 0 < k) (X : Fin k → Ω → ℝ) (a : ℕ) : ℝ :=
  ∫ ω, (Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩) fun i => X i ω) ^ a ∂ℙ

/-- `X₁, …, Xₖ` are non-negative random variables with probability density functions
(with respect to Lebesgue measure on `ℝ`) and finite power-sum moments of all orders. -/
def ValidTuple {Ω : Type} [MeasureSpace Ω] {k : ℕ} (X : Fin k → Ω → ℝ) : Prop :=
  (∀ i ω, 0 ≤ X i ω) ∧
  (∀ i, HasPDF (X i) ℙ volume) ∧
  (∀ n m : ℕ, Integrable (fun ω => (∑ i : Fin k, X i ω ^ n) ^ m) ℙ)

/-- Setting (b) approximation condition: `A n m = powerSumMoment X n m + R m n` with
`sup_{m ∈ ℕ} |R m n| · (powerSumMoment X n m)⁻¹ → 0` as `n → ∞`. -/
def UniformRelativeApprox {Ω : Type} [MeasureSpace Ω] {k : ℕ}
    (X : Fin k → Ω → ℝ) (A : ℕ → ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ m : ℕ,
    |A n m - powerSumMoment X n m| * (powerSumMoment X n m)⁻¹ < ε

/-- Setting (a): for fixed `k > 0` and moment order `a`, `𝔼[max(X₁, …, Xₖ)^a]` can be
extracted from the exact power-sum moments `𝔼[(X₁^n + ⋯ + Xₖ^n)^m]` (`n, m ∈ ℕ`). -/
def ExtractableSettingA : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (a : ℕ), ∃ F : (ℕ → ℕ → ℝ) → ℝ,
    ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (X : Fin k → Ω → ℝ), ValidTuple X →
      F (powerSumMoment X) = maxMoment hk X a

/-- Setting (b): for fixed `k > 0` and moment order `a`, `𝔼[max(X₁, …, Xₖ)^a]` can be
extracted from any approximation `A n m` to `𝔼[(X₁^n + ⋯ + Xₖ^n)^m]` with uniform-in-`m`
relative error tending to `0` as `n → ∞`. -/
def ExtractableSettingB : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (a : ℕ), ∃ F : (ℕ → ℕ → ℝ) → ℝ,
    ∀ (Ω : Type) [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (X : Fin k → Ω → ℝ), ValidTuple X →
      ∀ A : ℕ → ℕ → ℝ, UniformRelativeApprox X A →
      F A = maxMoment hk X a

theorem main : ExtractableSettingA ∧ ExtractableSettingB := by
  sorry

end OMA.S_mo_455319
