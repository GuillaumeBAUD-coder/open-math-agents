import OMAStatements.S_oeis_a175254

/-!
# Disproof of A175254 (Mathar's formula, Oct 17 2012)

The conjecture states, for every `n ≥ 1`,

  a n = ∑ k ∈ range (n + 1), A006218 (n - k),

where `a n = ∑ k ∈ Icc 1 n, σ₁(k) * (n - k + 1)` and `A006218 m = ∑ k ∈ Icc 1 m, m / k`.

It is refuted at `n = 2`: `a 2 = σ₁(1)*2 + σ₁(2)*1 = 1*2 + 3*1 = 5`, while
`A006218 2 + A006218 1 + A006218 0 = 3 + 1 + 0 = 4`.

Every step is a finite computation on numerals, so the kernel evaluates both
sides and the contradiction is `5 ≠ 4`.
-/

open OMA.S_oeis_a175254

namespace A175254Disproof

/-- The left-hand side at `n = 2`. -/
theorem a_two : a 2 = 5 := by decide

/-- The right-hand side at `n = 2` is the sum of three values of A006218. -/
theorem rhs_two : (∑ k ∈ Finset.range (2 + 1), A006218 (2 - k)) = 4 := by decide

end A175254Disproof

/-- The stated conjecture, instantiated at `n = 2`, reads `5 = 4`. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a175254.main) := by
  intro h
  have h2 := h 2 (by norm_num)
  have e1 : a 2 = 5 := A175254Disproof.a_two
  have e2 : (∑ k ∈ Finset.range (2 + 1), A006218 (2 - k)) = 4 := A175254Disproof.rhs_two
  rw [e1, e2] at h2
  exact absurd h2 (by norm_num)
