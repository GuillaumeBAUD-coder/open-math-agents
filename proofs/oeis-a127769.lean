import OMAStatements.S_oeis_a127769
import Mathlib

namespace A127769

lemma fac4 (m : ℕ) :
    (m + 4).factorial = (m + 4) * ((m + 3) * ((m + 2) * ((m + 1) * m.factorial))) := by
  rw [Nat.factorial_succ (m + 3), Nat.factorial_succ (m + 2), Nat.factorial_succ (m + 1),
    Nat.factorial_succ m]

lemma fac2 (m : ℕ) : (m + 2).factorial = (m + 2) * ((m + 1) * m.factorial) := by
  rw [Nat.factorial_succ (m + 1), Nat.factorial_succ m]

end A127769

theorem OMA.solution : type_of% @OMA.S_oeis_a127769.main := by
  intro t
  show ((t : ℚ) + 2) * (2 * ((t : ℚ) + 2) + 1) * (2 * ((t : ℚ) + 2) - 3)
      * OMA.S_oeis_a127769.term (t + 1)
    - 2 * (4 * ((t : ℚ) + 2) - 5) * (4 * ((t : ℚ) + 2) - 3) * (2 * ((t : ℚ) + 2) - 1)
      * OMA.S_oeis_a127769.term t = 0
  unfold OMA.S_oeis_a127769.term
  rw [show 4 * (t + 1) + 2 = (4 * t + 2) + 4 by ring, show 2 * (t + 1) + 3 = (2 * t + 3) + 2 by ring,
    show 2 * (t + 1) = 2 * t + 2 by ring, A127769.fac4 (4 * t + 2), A127769.fac2 (2 * t + 3),
    A127769.fac2 (2 * t)]
  push_cast
  have h1 : ((4 * t + 2).factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((2 * t + 3).factorial : ℚ) ≠ 0 := by positivity
  have h3 : ((2 * t).factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring
