import OMAStatements.S_oeis_a052227
import Mathlib

-- Problem: oeis-a052227
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P052227
open OMA.S_oeis_a052227

lemma ratio (m : ℕ) : ((3 * (m + 1)).choose (m + 1) : ℚ) * (((m : ℚ) + 1) * (2 * m + 2) * (2 * m + 1))
    = ((3 * m).choose m : ℚ) * ((3 * m + 3) * (3 * m + 2) * (3 * m + 1)) := by
  rw [Nat.cast_choose ℚ (by omega), Nat.cast_choose ℚ (by omega),
    show 3 * (m + 1) - (m + 1) = (2 * m + 1) + 1 by omega, show 3 * m - m = 2 * m by omega,
    show 3 * (m + 1) = ((3 * m + 1) + 1) + 1 by ring,
    Nat.factorial_succ (3 * m + 1 + 1), Nat.factorial_succ (3 * m + 1), Nat.factorial_succ (3 * m),
    Nat.factorial_succ (2 * m + 1), Nat.factorial_succ (2 * m), Nat.factorial_succ m]
  have h1 : (m.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((2 * m).factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem sol : type_of% @OMA.S_oeis_a052227.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold a
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  have r1 := ratio (m + 1)
  have r0 := ratio m
  rw [show m + 1 + 1 = m + 2 by ring] at r1
  set C2 : ℚ := ((3 * (m + 2)).choose (m + 2) : ℚ)
  set C1 : ℚ := ((3 * (m + 1)).choose (m + 1) : ℚ)
  set C0 : ℚ := ((3 * m).choose m : ℚ)
  push_cast at r1 r0 ⊢
  have hC2 : C2 = C1 * ((3 * (m:ℚ) + 6) * (3 * m + 5) * (3 * m + 4)) / (((m:ℚ) + 2) * (2 * m + 4) * (2 * m + 3)) := by
    rw [eq_div_iff (by positivity)]; linear_combination r1
  have hC1 : C1 = C0 * ((3 * (m:ℚ) + 3) * (3 * m + 2) * (3 * m + 1)) / (((m:ℚ) + 1) * (2 * m + 2) * (2 * m + 1)) := by
    rw [eq_div_iff (by positivity)]; linear_combination r0
  rw [hC2, hC1]
  field_simp
  ring

end OMA.P052227

theorem OMA.solution : type_of% @OMA.S_oeis_a052227.main := OMA.P052227.sol
