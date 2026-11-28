import OMAStatements.S_mo_230382
import Mathlib

-- Problem mo-230382: the statement claims that for N >= 5000 and 1 <= r <= N the largest value of
-- C(m0, j) * C(m1, r - j) over m0 + m1 = N (m0, m1 >= 1) and j <= r is C(N - 1, r).
-- Upstream: statements/mo-230382.lean (declaration OMA.S_mo_230382.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Refutation: take N = r = 5000. Then C(N - 1, r) = C(4999, 5000) = 0, but m0 = 4999, m1 = 1, j = 4999 gives
-- C(4999, 4999) * C(1, 1) = 1 > 0. So C(N - 1, r) is not an upper bound of the set.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_230382.main) := by
  intro h
  have hg := h 5000 5000 (le_refl _) (by norm_num) (le_refl _)
  have hmem : (1 : ℕ) ∈ {x : ℕ | ∃ m₀ m₁ j : ℕ, 1 ≤ m₀ ∧ 1 ≤ m₁ ∧ m₀ + m₁ = 5000 ∧ j ≤ 5000 ∧
      x = m₀.choose j * m₁.choose (5000 - j)} := by
    refine ⟨4999, 1, 4999, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    have e : 5000 - 4999 = 1 := by norm_num
    rw [e, Nat.choose_self, Nat.choose_self]
  have hle := hg.2 hmem
  have e2 : 5000 - 1 = 4999 := by norm_num
  rw [e2, Nat.choose_eq_zero_of_lt (by norm_num)] at hle
  omega
