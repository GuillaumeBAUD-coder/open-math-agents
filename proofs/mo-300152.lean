import OMAStatements.S_mo_300152
import Mathlib

/-!
# MathOverflow 300152: the alternating binomial sum is not majorised

Counterexample: `m = 2` and the antitone sequence `r = (1, 1, 1/2, 1/2, …)` in `[0, 1]`.
The left-hand side is `2 · r₁² - r₂² = 2 - 1/4 = 7/4`, the right-hand side is
`2 · r₁ - r₂ = 2 - 1/2 = 3/2`, and `7/4 > 3/2`.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_300152.main) := by
  intro h
  have hb : ∀ i : ℕ, 0 ≤ (if i ≤ 1 then (1 : ℝ) else 1 / 2) ∧
      (if i ≤ 1 then (1 : ℝ) else 1 / 2) ≤ 1 := by
    intro i
    split_ifs <;> norm_num
  have ha : Antitone fun i : ℕ => if i ≤ 1 then (1 : ℝ) else 1 / 2 := by
    intro i j hij
    simp only
    split_ifs <;> first | (exfalso; omega) | norm_num
  have key := h 2 (fun i => if i ≤ 1 then (1 : ℝ) else 1 / 2) hb ha
  have e : Finset.Icc 1 2 = {1, 2} := by decide
  rw [e] at key
  norm_num [Finset.sum_pair, Nat.choose] at key
