import OMAReductions.R_OeisA232616_conjecture_2_R1
import Mathlib

-- Step OeisA232616.conjecture_2.R1.H2: hypothesis H2 of reduction OeisA232616.conjecture_2.R1
-- Credit: @ivillar. Direct check: 2^5 - 5 = 27 = 3^3 and 2^7 - 7 = 121 = 11^2.

/-! Step OeisA232616.conjecture_2.R1.H2. -/

theorem P8A232616.backward : ∀ (x y n m : ℕ), 1 < x → 1 < y → 1 < n → 1 < m →
    ((x = 2 ∧ n = 5 ∧ y = 3 ∧ m = 3) ∨ (x = 2 ∧ n = 7 ∧ y = 11 ∧ m = 2)) →
    x ^ n - n = y ^ m := by
  rintro x y n m - - - - (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩) <;> norm_num

theorem OMA.solution : OMA.R_OeisA232616_conjecture_2_R1.H2 :=
  P8A232616.backward
