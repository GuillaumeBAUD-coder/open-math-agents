import FormalConjectures.ErdosProblems.«876»

-- Reduction Erdos876.erdos_876.variants.recip_sum_bounds.R1 of Erdős Problem 876 — recip sum bounds
-- Credit: @minimumnz
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# `2.064 < R < 4` for sum-free sets: the two bounds are independent

* `H1` is the upper bound of Levine and O'Sullivan: the reciprocal sum of every infinite sum-free
  set is at most some constant below `4`.
* `H2` is Abbott's lower bound: one infinite sum-free set with reciprocal sum above `2.064`.
  A witness: `{1, 2, 4, 8}`, then `25 + 24 i` for `i < 55`, then `36167 + 24 i` for `i < 46`,
  then `T, 2T, 4T, …` with `T = 1725553` (one more than the sum of the earlier elements). Its
  reciprocal sum is `2.06491…`.
* `main` only needs that `H1` bounds the set of sums, so that the supremum is a least upper bound.
-/

namespace OMA.R_Erdos876_erdos_876_variants_recip_sum_bounds_R1

open Erdos876

-- Levine–O'Sullivan (1977): a uniform bound below `4`.
def H1 : Prop := ∃ c : ℝ, c < 4 ∧ ∀ A : Set ℕ, A.Infinite → IsSubsetSumFree A →
    ∀ s : ℝ, HasSum (fun a : A ↦ (1 : ℝ) / (a : ℕ)) s → s ≤ c

-- Abbott (1987): an infinite sum-free set with reciprocal sum above `2.064`.
def H2 : Prop := ∃ A : Set ℕ, A.Infinite ∧ IsSubsetSumFree A ∧
    ∃ s : ℝ, 2.064 < s ∧ HasSum (fun a : A ↦ (1 : ℝ) / (a : ℕ)) s

theorem main : H1 → H2 → type_of% @Erdos876.erdos_876.variants.recip_sum_bounds := by
  rintro ⟨c, hc, hup⟩ ⟨A, hAi, hAs, s, hs, hsum⟩
  have hle : ∀ x ∈ {s : ℝ | ∃ A : Set ℕ, A.Infinite ∧ IsSubsetSumFree A ∧
      HasSum (fun a : A ↦ (1 : ℝ) / (a : ℕ)) s}, x ≤ c := by
    rintro x ⟨A', h1, h2, h3⟩
    exact hup A' h1 h2 x h3
  unfold maxRecipSum
  constructor
  · exact lt_of_lt_of_le hs (le_csSup ⟨c, hle⟩ ⟨A, hAi, hAs, hsum⟩)
  · exact lt_of_le_of_lt (csSup_le ⟨s, A, hAi, hAs, hsum⟩ hle) hc

end OMA.R_Erdos876_erdos_876_variants_recip_sum_bounds_R1
