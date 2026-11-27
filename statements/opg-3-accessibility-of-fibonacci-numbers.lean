import Mathlib

/-!
# 3-accessibility of Fibonacci numbers

Source: https://www.openproblemgarden.org/op/3_accessibility_of_fibonacci_numbers
Credit: @Hyvok

Posed by Bruce M. Landman and Aaron Robertson ([LR1] B. M. Landman and A. Robertson, Avoiding
monochromatic sequences with special gaps, SIAM J. Discrete Math. 21:3 (2007), 794–801).

Definition (from the source): a set `S` is `r`-accessible if for every `r`-coloring of `ℕ` there are
arbitrarily long monochromatic `S`-diffsequences: for every `k ∈ ℕ \ {1}` there is a monochromatic
sequence `x₁, x₂, …, x_k` with `x_{i+1} - x_i ∈ S` for all `i ∈ {1, …, k-1}`.

Question: is the set `F` of Fibonacci numbers 3-accessible?
Known: `F` is 2-accessible [LR1] and not 6-accessible [Ardal, Gunderson, Jungić, Landman].

Formalization notes:
* As in Landman–Robertson, an `S`-diffsequence is increasing, `x₁ < x₂ < ⋯ < x_k`, with every gap
  `x_{i+1} - x_i` in `S`; the colored set `ℕ` is the positive integers `{1, 2, 3, …}`.
* A coloring with `r` colors is a map `ℕ → Fin r`; only its values on positive integers matter.
* `F = {Nat.fib n}` taken as a set, so the repeated `1` of the sequence plays no role. Whether `0`
  is included does not matter either: the gaps of an increasing sequence are positive.
* `k = 1` is excluded in the source; it is trivial anyway, so `main` quantifies over `k ≥ 2`.
* `main` states the positive answer (that `F` is 3-accessible).
-/

namespace OMA.S_opg_3_accessibility_of_fibonacci_numbers

/-- `S` is `r`-accessible: every `r`-coloring of the positive integers has, for every `k ≥ 2`, a
monochromatic increasing sequence of `k` positive integers whose consecutive gaps all lie in `S`. -/
def IsAccessible (S : Set ℕ) (r : ℕ) : Prop :=
  ∀ c : ℕ → Fin r, ∀ k : ℕ, 2 ≤ k →
    ∃ x : ℕ → ℕ, 0 < x 0 ∧
      (∀ i, i < k → c (x i) = c (x 0)) ∧
      (∀ i, i + 1 < k → x i < x (i + 1) ∧ x (i + 1) - x i ∈ S)

/-- The set of Fibonacci numbers. -/
def fibSet : Set ℕ := Set.range Nat.fib

/-- Landman–Robertson: is the set of Fibonacci numbers 3-accessible? -/
theorem main : IsAccessible fibSet 3 := by
  sorry

end OMA.S_opg_3_accessibility_of_fibonacci_numbers
