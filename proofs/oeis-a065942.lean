import OMAStatements.S_oeis_a065942
import Mathlib

-- Problem: A065942, Mathar's conjectured recurrence for a(n) = T(2n, n) = C(2n - floor((n+1)/2), floor(n/2)).
-- Upstream: formal-conjectures statements/oeis-a065942.lean (declaration OMA.S_oeis_a065942.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds).
-- Proof: a(2m) = C(3m, m) and a(2m+1) = C(3m+1, m). Splitting on the parity of n, all four terms are
-- explicit factorial quotients in m, and the recurrence reduces to an identity of rational functions.

namespace OMA.P_oeis_a065942

open OMA.S_oeis_a065942

theorem A_even (m : ℕ) : (a (2 * m) : ℚ) = ((3 * m).factorial : ℚ) / ((m.factorial : ℚ) * ((2 * m).factorial : ℚ)) := by
  unfold a T
  rw [show 2 * (2 * m) - (2 * m + 1) / 2 = 3 * m by omega, show 2 * m / 2 = m by omega,
    Nat.cast_choose ℚ (show m ≤ 3 * m by omega), show 3 * m - m = 2 * m by omega]

theorem A_odd (m : ℕ) : (a (2 * m + 1) : ℚ) = ((3 * m + 1).factorial : ℚ)
    / ((m.factorial : ℚ) * ((2 * m + 1).factorial : ℚ)) := by
  unfold a T
  rw [show 2 * (2 * m + 1) - (2 * m + 1 + 1) / 2 = 3 * m + 1 by omega, show (2 * m + 1) / 2 = m by omega,
    Nat.cast_choose ℚ (show m ≤ 3 * m + 1 by omega), show 3 * m + 1 - m = 2 * m + 1 by omega]

theorem main' : ∀ n : ℕ, 3 ≤ n →
      8 * (n : ℤ) * (n - 1) * a n - 36 * ((n : ℤ) - 1) * (n - 3) * a (n - 1)
        + 6 * (-9 * (n : ℤ) ^ 2 + 18 * n - 14) * a (n - 2)
        + 27 * (3 * (n : ℤ) - 7) * (3 * n - 8) * a (n - 3) = 0 := by
  intro n hn
  apply Int.cast_injective (α := ℚ)
  push_cast
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
    rw [show 2 * (j + 2) - 1 = 2 * (j + 1) + 1 by omega, show 2 * (j + 2) - 2 = 2 * (j + 1) by omega,
      show 2 * (j + 2) - 3 = 2 * j + 1 by omega]
    rw [A_even, A_odd, A_even, A_odd]
    rw [show 3 * (j + 2) = 3 * j + 6 by ring, show 2 * (j + 2) = 2 * j + 4 by ring,
      show 3 * (j + 1) + 1 = 3 * j + 4 by ring, show 2 * (j + 1) + 1 = 2 * j + 3 by ring,
      show 3 * (j + 1) = 3 * j + 3 by ring, show 2 * (j + 1) = 2 * j + 2 by ring]
    have h1 : (j.factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((2 * j).factorial : ℚ) ≠ 0 := by positivity
    have h3 : ((3 * j).factorial : ℚ) ≠ 0 := by positivity
    simp only [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [show 2 * (j + 1) + 1 - 1 = 2 * (j + 1) by omega, show 2 * (j + 1) + 1 - 2 = 2 * j + 1 by omega,
      show 2 * (j + 1) + 1 - 3 = 2 * j by omega]
    rw [A_odd, A_even, A_odd, A_even]
    rw [show 3 * (j + 1) + 1 = 3 * j + 4 by ring, show 2 * (j + 1) + 1 = 2 * j + 3 by ring,
      show 3 * (j + 1) = 3 * j + 3 by ring, show 2 * (j + 1) = 2 * j + 2 by ring]
    have h1 : (j.factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((2 * j).factorial : ℚ) ≠ 0 := by positivity
    have h3 : ((3 * j).factorial : ℚ) ≠ 0 := by positivity
    simp only [Nat.factorial_succ]
    push_cast
    field_simp
    ring

end OMA.P_oeis_a065942

theorem OMA.solution : type_of% @OMA.S_oeis_a065942.main := OMA.P_oeis_a065942.main'
