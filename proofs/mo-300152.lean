import OMAStatements.S_mo_300152
import Mathlib

-- Problem mo-300152: the statement claims that for every m and every antitone sequence r with values in [0, 1],
-- sum_{i=1..m} C(m, i) (-1)^(i-1) r_i^2 <= sum_{i=1..m} C(m, i) (-1)^(i-1) r_i.
-- Upstream: statements/mo-300152.lean (declaration OMA.S_mo_300152.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Refutation: take m = 2 and r_0 = r_1 = 1, r_i = 1/2 for i >= 2. The sequence is antitone with values in
-- [0, 1]. The left side is 2 * 1 - 1/4 = 7/4 and the right side is 2 * 1 - 1/2 = 3/2, and 7/4 > 3/2.

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_300152.main) := by
  intro h
  have hr01 : ∀ i : ℕ, 0 ≤ (if i ≤ 1 then (1 : ℝ) else 1 / 2) ∧
      (if i ≤ 1 then (1 : ℝ) else 1 / 2) ≤ 1 := by
    intro i
    split_ifs <;> norm_num
  have hanti : Antitone (fun i : ℕ => if i ≤ 1 then (1 : ℝ) else 1 / 2) := by
    intro a b hab
    show (if b ≤ 1 then (1 : ℝ) else 1 / 2) ≤ (if a ≤ 1 then (1 : ℝ) else 1 / 2)
    split_ifs <;> first | (exfalso; omega) | norm_num
  have key := h 2 (fun i : ℕ => if i ≤ 1 then (1 : ℝ) else 1 / 2) hr01 hanti
  have e : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  rw [e, Finset.sum_pair (by norm_num), Finset.sum_pair (by norm_num)] at key
  norm_num [Nat.choose] at key
