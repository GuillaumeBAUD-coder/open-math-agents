import Mathlib

/-!
# Erdős Problem 870

Source: https://www.erdosproblems.com/870
Credit: @joshuadc11

Let `k ≥ 3` and `A` be an additive basis of order `k`. Does there exist a constant `c = c(k) > 0`
such that if `r(n) ≥ c log n` for all large `n` then `A` must contain a minimal basis of order `k`?
(Here `r(n)` counts the number of representations of `n` as the sum of at most `k` elements from `A`.)

Formalization notes:
- An (asymptotic) additive basis `A ⊆ ℕ` of order `k` is a set such that every sufficiently large
  `n : ℕ` is the sum of at most `k` elements of `A` (with repetition allowed, modeled via `Multiset ℕ`).
- `IsMinimalAdditiveBasis B k` means `B` is an additive basis of order `k` and removing any single
  element `b ∈ B` destroys this property.
- `repCount A k n` counts unordered representations (`Multiset ℕ` of size `≤ k` with elements in `A`
  summing to `n`); ordered vs unordered representations differ by at most a factor `k!`, which does
  not affect the existence of `c = c(k) > 0`.
-/

namespace OMA.S_erdos_870

/-- `A` is an asymptotic additive basis of order `k`: every sufficiently large natural number
is a sum of at most `k` elements of `A`. -/
def IsAdditiveBasis (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ s : Multiset ℕ, s.card ≤ k ∧ (∀ x ∈ s, x ∈ A) ∧ s.sum = n

/-- `A` is a minimal asymptotic additive basis of order `k`: it is an additive basis of order `k`,
and no proper subset `A \ {a}` (for `a ∈ A`) is an additive basis of order `k`. -/
def IsMinimalAdditiveBasis (A : Set ℕ) (k : ℕ) : Prop :=
  IsAdditiveBasis A k ∧ ∀ a ∈ A, ¬ IsAdditiveBasis (A \ {a}) k

/-- The number of representations of `n` as the sum of at most `k` elements of `A`. -/
noncomputable def repCount (A : Set ℕ) (k n : ℕ) : ℕ :=
  Set.ncard {s : Multiset ℕ | s.card ≤ k ∧ (∀ x ∈ s, x ∈ A) ∧ s.sum = n}

theorem main :
    ∀ k ≥ 3, ∃ c : ℝ, 0 < c ∧
      ∀ A : Set ℕ, IsAdditiveBasis A k →
        (∃ N₀ : ℕ, ∀ n ≥ N₀, c * Real.log (n : ℝ) ≤ (repCount A k n : ℝ)) →
        ∃ B ⊆ A, IsMinimalAdditiveBasis B k := by
  sorry

end OMA.S_erdos_870
