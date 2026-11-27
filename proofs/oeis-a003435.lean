import OMAStatements.S_oeis_a003435
import Mathlib

-- Credit: @physbuzz. Statement and independent prior verification: @Heart-galaxy.
-- The mathematical argument is due to Roberto Blanco Gómez (OEIS A003435, 2026).
open OMA.S_oeis_a003435

/-- Kotesovec's defining recurrence after clearing its positive denominator. -/
private lemma recurrence (k : ℕ) :
    (2*((k:ℚ)+4)-3)*a (k+4) =
      2*((k:ℚ)+4)*(4*((k:ℚ)+4)^2-8*((k:ℚ)+4)+5)*a (k+3) +
      4*((k:ℚ)+4-1)*((k:ℚ)+4)*(2*((k:ℚ)+4)-1)*a (k+2) := by
  rw [a]
  have pos : 0<2*((k:ℚ)+4)-3 := by linarith [show 0≤(k:ℚ) by positivity]
  field_simp

/-- Blanco Gómez's identity combines the defining recurrence at two successive indices. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a003435.main := by
  intro n lim
  obtain ⟨k,rfl⟩ : ∃ k : ℕ,n=k+5 := ⟨n-5,by omega⟩
  have rel := recurrence (k+1)
  push_cast at rel ⊢
  have pos : (2*((k:ℚ)+5)-3)≠0 := by linarith [show 0≤(k:ℚ) by positivity]
  apply (mul_eq_zero.mp (b := _) ?_).resolve_left pos
  linear_combination rel - 3*(recurrence k)
