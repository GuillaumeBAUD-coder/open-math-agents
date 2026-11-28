import Mathlib

/-!
# Erdős Problem 796

Source: https://www.erdosproblems.com/796
Credit: @joshuadc11

Let `k ≥ 2` and let `g_k(n)` be the largest possible size of `A ⊆ {1, ..., n}` such that
every `m` has `< k` solutions to `m = a₁ * a₂` with `a₁ < a₂` in `A`.
Is it true that
`g_3(n) = (log log n / log n) * n + (c + o(1)) * (n / log n)`
for some constant `c`?

Formalization notes:
- `g k n` is defined as the supremum of `A.card` over all `A ⊆ Finset.Icc 1 n` such that
  for every `m : ℕ`, the number of pairs `(a₁, a₂) ∈ A ×ˢ A` with `a₁ < a₂` and `a₁ * a₂ = m`
  is `< k`.
- The asymptotic `g_3(n) = (log log n / log n) * n + (c + o(1)) * (n / log n)` is expressed as
  `((g 3 n : ℝ) - (Real.log (Real.log n) / Real.log n) * n) / (n / Real.log n) → c` as `n → ∞`.
-/

namespace OMA.S_erdos_796

/-- `g k n` is the largest possible cardinality of `A ⊆ {1, ..., n}` such that every `m` has
strictly fewer than `k` representations `m = a₁ * a₂` with `a₁ < a₂` in `A`. -/
noncomputable def g (k n : ℕ) : ℕ :=
  sSup {s : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 n ∧ A.card = s ∧
    ∀ m : ℕ, ((A ×ˢ A).filter (fun p => p.1 < p.2 ∧ p.1 * p.2 = m)).card < k}

theorem main :
    ∃ c : ℝ, Filter.Tendsto
      (fun n : ℕ =>
        ((g 3 n : ℝ) - (Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) * (n : ℝ)) /
          ((n : ℝ) / Real.log (n : ℝ)))
      Filter.atTop (nhds c) := by
  sorry

end OMA.S_erdos_796
