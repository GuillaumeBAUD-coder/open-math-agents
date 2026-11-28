import OMAReductions.R_LebesgueNagell_lebesgue_nagell_R1
import Mathlib

-- Step LebesgueNagell.lebesgue_nagell.R1.H2: hypothesis H2 of reduction LebesgueNagell.lebesgue_nagell.R1
-- Credit: @ivillar. Direct check: (±1)^2 - 2 = -1 = (-1)^p for odd p.

/-! Step LebesgueNagell.lebesgue_nagell.R1.H2. -/

theorem P8LebesgueNagell.backward : ∀ (p : ℕ) (hp : p.Prime) (hodd : Odd p) (x y : ℤ),
    (x = 1 ∨ x = -1) ∧ y = -1 → x ^ 2 - 2 = y ^ p := by
  intro p _ hodd x y ⟨hx, hy⟩
  subst hy
  rw [Odd.neg_one_pow hodd]
  rcases hx with rfl | rfl <;> norm_num

theorem OMA.solution : OMA.R_LebesgueNagell_lebesgue_nagell_R1.H2 :=
  P8LebesgueNagell.backward
