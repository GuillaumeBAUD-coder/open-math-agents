import OMAReductions.R_Erdos52_erdos_52_R1

-- Step Erdos52.erdos_52.R1.H1
-- Credit: @caa1982

open Finset
open scoped Pointwise

theorem OMA.solution : OMA.R_Erdos52_erdos_52_R1.H1 := by
  intro S
  have ha := le_card_add_mul_addEnergy S S
  have hm := le_card_mul_mul_mulEnergy S S
  rw [show S.card ^ 4 = S.card ^ 2 * S.card ^ 2 by ring]
  rcases le_total (addEnergy S S) (mulEnergy S S) with h | h
  · rw [min_eq_left h]
    exact ha.trans (Nat.mul_le_mul_right _ (le_max_left _ _))
  · rw [min_eq_right h]
    exact hm.trans (Nat.mul_le_mul_right _ (le_max_right _ _))
