import OMAStatements.S_oeis_a175254
import Mathlib

-- Problem: A175254, a(n) = Sum_{k<=n} sigma(k) (n-k+1); Mathar's conjectured identity.
-- Upstream: formal-conjectures statements/oeis-a175254.lean (declaration OMA.S_oeis_a175254.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Disproof: the identity fails at n = 2, as the statement's docstring records:
-- a(2) = sigma(1)*2 + sigma(2)*1 = 5, while A006218(2) + A006218(1) + A006218(0) = 3 + 1 + 0 = 4.

namespace OMA.P_oeis_a175254

open OMA.S_oeis_a175254

theorem lhs2 : a 2 = 5 := by decide

theorem rhs2 : ∑ k ∈ Finset.range (2 + 1), A006218 (2 - k) = 4 := by decide

theorem disproof_main : ¬ (∀ n : ℕ, 1 ≤ n → a n = ∑ k ∈ Finset.range (n + 1), A006218 (n - k)) := by
  intro h
  have := h 2 (by norm_num)
  rw [lhs2, rhs2] at this
  exact absurd this (by norm_num)

end OMA.P_oeis_a175254

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a175254.main) :=
  OMA.P_oeis_a175254.disproof_main
