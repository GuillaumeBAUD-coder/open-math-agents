import FormalConjectures.GreensOpenProblems.«93»

-- Reduction Green93.green_93.variants.bskk_small.R1 of Ben Green's Open Problem 93 — bskk small
-- Credit: @cosmaticdev
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Green 93, BSKK small: reduction by the size M of the coefficient box

Bary-Soroker, Koukoulopoulos and Kozma [BSKK23, Theorem 1(b)] prove a positive lower bound for
`irreducibleProb M n` for every box size `2 ≤ N = M + 1 ≤ 34`, i.e. `1 ≤ M ≤ 33`. H1 is the
case `M = 1` (coefficients in {0,1}, the polynomial of `green_93`) and H2 is the range
`2 ≤ M ≤ 33`; main takes the smaller of the two constants and the larger of the two thresholds.
-/

namespace OMA.R_Green93_green_93_variants_bskk_small_R1

open Green93

/-- The case `M = 1`: a positive asymptotic lower bound for the irreducibility probability of
`0/1` monic polynomials. -/
def H1 : Prop := ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → δ ≤ irreducibleProb 1 n

/-- The cases `2 ≤ M ≤ 33` [BSKK23, Theorem 1(b)]. -/
def H2 : Prop := ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ M n : ℕ, 2 ≤ M → M ≤ 33 → n₀ ≤ n →
    δ ≤ irreducibleProb M n

theorem main : H1 → H2 → type_of% @Green93.green_93.variants.bskk_small := by
  intro h1 h2
  obtain ⟨δ1, hδ1, n1, H1⟩ := h1
  obtain ⟨δ2, hδ2, n2, H2⟩ := h2
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, max n1 n2, ?_⟩
  intro M n hM1 hM33 hn
  rcases Nat.eq_or_lt_of_le hM1 with rfl | h2M
  · exact (min_le_left δ1 δ2).trans (H1 n (le_trans (le_max_left n1 n2) hn))
  · exact (min_le_right δ1 δ2).trans
      (H2 M n (by omega) hM33 (le_trans (le_max_right n1 n2) hn))

end OMA.R_Green93_green_93_variants_bskk_small_R1
