import OMAStatements.S_oeis_a165105
import Mathlib.Tactic

/-! In octal, 52 - 25 = 25, so 25 is a two-digit fixed point. The
coefficient of degree two in the proposed generating function is zero. -/

open OMA.S_oeis_a165105

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a165105.main) := by
  intro h
  have first := h.2 1
  have coef := h.2 2
  change a 1 + 0 - 0 - 2*0 - 2*0 - 0 + 0 + 2*0 + 2*0 + 0 - 0 - 0 = 1 at first
  change a 2 + a 1 - 0 - 2*0 - 2*0 - 0 + 0 + 2*0 + 2*0 + 0 - 0 - 0 = 1 at coef
  have ds : digits 21 = [5, 2] := by
    change Nat.digits 8 (5 + 8*2) = [5, 2]
    rw [Nat.digits_add 8 (by decide) 5 2 (by decide) (by decide),
      Nat.digits_of_lt 8 2 (by decide) (by decide)]
  have fixed : kaprekar 21 = 21 := by
    unfold kaprekar
    rw [ds]
    decide
  have pos : 0 < a 2 := by
    unfold a
    apply Int.ofNat_lt.mpr
    apply Finset.card_pos.mpr
    exact ⟨21, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by decide), by simp [ds], fixed⟩⟩
  omega
