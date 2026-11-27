import OMAStatements.S_oeis_a026005
import Mathlib

-- Problem: oeis-a026005
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)

namespace OMA.P026005
open OMA.S_oeis_a026005

lemma ratio (m : ℕ) : ((4 * (m + 1) + 1).choose (m + 1) : ℚ) * (((m : ℚ) + 1) * (3 * m + 4) * (3 * m + 3) * (3 * m + 2))
    = ((4 * m + 1).choose m : ℚ) * ((4 * m + 5) * (4 * m + 4) * (4 * m + 3) * (4 * m + 2)) := by
  rw [Nat.cast_choose ℚ (by omega), Nat.cast_choose ℚ (by omega),
    show 4 * (m + 1) + 1 - (m + 1) = ((3 * m + 1) + 1 + 1) + 1 by omega, show 4 * m + 1 - m = 3 * m + 1 by omega,
    show 4 * (m + 1) + 1 = (((4 * m + 1) + 1) + 1 + 1) + 1 by ring,
    Nat.factorial_succ (4 * m + 1 + 1 + 1 + 1), Nat.factorial_succ (4 * m + 1 + 1 + 1),
    Nat.factorial_succ (4 * m + 1 + 1), Nat.factorial_succ (4 * m + 1),
    Nat.factorial_succ (3 * m + 1 + 1 + 1), Nat.factorial_succ (3 * m + 1 + 1),
    Nat.factorial_succ (3 * m + 1), Nat.factorial_succ m]
  have h1 : (m.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((3 * m + 1).factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

theorem sol : type_of% @OMA.S_oeis_a026005.main := by
  intro k
  simp only
  unfold a
  have r1 := ratio (k + 1)
  have r0 := ratio k
  rw [show k + 1 + 1 = k + 2 by ring] at r1
  set C2 : ℚ := ((4 * (k + 2) + 1).choose (k + 2) : ℚ)
  set C1 : ℚ := ((4 * (k + 1) + 1).choose (k + 1) : ℚ)
  set C0 : ℚ := ((4 * k + 1).choose k : ℚ)
  push_cast at r1 r0 ⊢
  have hC2 : C2 = C1 * ((4 * (k:ℚ) + 9) * (4 * k + 8) * (4 * k + 7) * (4 * k + 6)) /
      (((k:ℚ) + 2) * (3 * k + 7) * (3 * k + 6) * (3 * k + 5)) := by
    rw [eq_div_iff (by positivity)]; linear_combination r1
  have hC1 : C1 = C0 * ((4 * (k:ℚ) + 5) * (4 * k + 4) * (4 * k + 3) * (4 * k + 2)) /
      (((k:ℚ) + 1) * (3 * k + 4) * (3 * k + 3) * (3 * k + 2)) := by
    rw [eq_div_iff (by positivity)]; linear_combination r0
  rw [hC2, hC1]
  field_simp
  ring

end OMA.P026005

theorem OMA.solution : type_of% @OMA.S_oeis_a026005.main := OMA.P026005.sol
