import Mathlib

/-!
# 2-accessibility of primes

Source: https://www.openproblemgarden.org/op/2_accessibility_of_primes
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: a set `S` of natural numbers is **r-accessible** if for any `r`-coloring of the natural
numbers and any `k >= 2` there is a monochromatic sequence `x_1, ..., x_k` such that
`x_{i+1} - x_i` lies in `S` for every `i`.  The question of Landman and Robertson is whether the
set of prime numbers is 2-accessible.  It is known that the primes are not 3-accessible.

So the proposition formalized below is: for every 2-coloring of the natural numbers and every
`k >= 2` there is a strictly increasing monochromatic `k`-term sequence whose consecutive
differences are all prime.
-/

namespace OMA.S_opg_2_accessibility_of_primes

-- definitions the statement needs (no sorry, no axiom)

/-- `S` is **r-accessible**: every `r`-coloring of the natural numbers admits, for every `k >= 2`,
a strictly increasing monochromatic sequence of `k` terms whose consecutive differences lie in
`S`. -/
def IsAccessible (S : Set ℕ) (r : ℕ) : Prop :=
  ∀ c : ℕ → Fin r, ∀ k : ℕ, 2 ≤ k →
    ∃ x : ℕ → ℕ,
      (∀ i : ℕ, i < k - 1 → x i < x (i + 1)) ∧
        (∃ col : Fin r, ∀ i : ℕ, i < k → c (x i) = col) ∧
          (∀ i : ℕ, i < k - 1 → x (i + 1) - x i ∈ S)

/-- Is the set of prime numbers 2-accessible? -/
theorem main : IsAccessible {p : ℕ | p.Prime} 2 := by
  sorry

end OMA.S_opg_2_accessibility_of_primes
