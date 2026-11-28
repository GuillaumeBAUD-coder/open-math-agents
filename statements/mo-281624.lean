import Mathlib

/-!
# Is the p.m.f. of the first return time of a random walk monotone?

Source: https://mathoverflow.net/questions/281624
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The question (MathOverflow 281624, Sep 2017): suppose `X₁, X₂, …` are i.i.d. `ℤ`-valued random
variables such that the random walk `Sₙ = X₁ + ⋯ + Xₙ` is recurrent with some period `k ≥ 1`
(i.e. `Pr[Sₙ = 0] > 0` if and only if `n ∈ kℕ`). Let `T = inf {n ≥ 1 : Sₙ = 0}` be the first
return time to zero. Is it always the case that the probabilities `pₙ := Pr[T = kn]` are
eventually nonincreasing in `n`, i.e. there is `N` such that `pₙ ≥ p_{n+m}` for all `m` and
`n ≥ N`? (For steps uniform on `{-1, 1}` or `{-1, 0, 1}` the `pₙ` are strictly decreasing.)
The question has no answer on the page; `main` states the affirmative answer.

Modelling choices:
* The steps are `X i`, `i : ℕ` (so `X 0` plays the role of `X₁`), on a probability space
  `(Ω, μ)`: measurable, mutually independent (`iIndepFun`) and identically distributed
  (`μ.map (X i) = μ.map (X 0)`). `S n = ∑ i < n, X i`, so `S 0 = 0`.
* "Recurrent" is the standard notion: almost surely `Sₙ = 0` for infinitely many `n`.
* "Period `k`": for every `n`, `0 < Pr[Sₙ = 0] ↔ k ∣ n` (for `n = 0` both sides hold).
* `{T = m}` for `m ≥ 1` is the event `S m = 0` and `S i ≠ 0` for `1 ≤ i < m`; `pₙ = Pr[T = kn]`.
  Since recurrence makes `T` finite a.s., no convention for `inf ∅` is needed. Only `n ≥ 1` is
  compared (`T ≥ 1`, so `p₀` is not part of the question).
-/

namespace OMA.S_mo_281624

open MeasureTheory ProbabilityTheory Filter

/-- **MathOverflow 281624.** For a recurrent `ℤ`-valued i.i.d. random walk of period `k`, the
probabilities `Pr[T = k n]` of the first return time `T` are eventually nonincreasing. -/
theorem main :
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → ℤ) (k : ℕ),
      (∀ i, Measurable (X i)) →
      iIndepFun X μ →
      (∀ i, μ.map (X i) = μ.map (X 0)) →
      1 ≤ k →
      -- recurrence: almost surely the walk returns to `0` infinitely often
      (∀ᵐ ω ∂μ, ∃ᶠ n in atTop, ∑ i ∈ Finset.range n, X i ω = 0) →
      -- period `k`
      (∀ n : ℕ, 0 < μ {ω | ∑ i ∈ Finset.range n, X i ω = 0} ↔ k ∣ n) →
      ∃ N : ℕ, ∀ n ≥ N, 1 ≤ n → ∀ m : ℕ,
        μ.real {ω | ∑ i ∈ Finset.range (k * (n + m)), X i ω = 0 ∧
            ∀ j, 1 ≤ j → j < k * (n + m) → ∑ i ∈ Finset.range j, X i ω ≠ 0} ≤
          μ.real {ω | ∑ i ∈ Finset.range (k * n), X i ω = 0 ∧
            ∀ j, 1 ≤ j → j < k * n → ∑ i ∈ Finset.range j, X i ω ≠ 0} := by
  sorry

end OMA.S_mo_281624
