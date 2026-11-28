import OMAStatements.S_oeis_a348618
import Mathlib

/-!
For even n = 2m+2, a(n) = 4^n (3m+2)! / ((2m+2)! m!); for odd n = 2m+1,
a(n) = C(3m+1, 2m+1) C(6m+2, 3m+1) / C(2m, m), written with factorials. In each parity class the
factorials of a(n) are the factorials of a(n-2) times explicit linear factors, so the recurrence
is a rational identity.
-/

namespace R348618
open OMA.S_oeis_a348618
open scoped Nat

theorem chq (n k j : ℕ) (h : n = k + j) : (n.choose k : ℚ) = n ! / (k ! * j !) := by
  subst h
  exact Nat.cast_add_choose (K := ℚ)

theorem aeven (k m : ℕ) (h : k = 2 * m + 2) :
    a k = 4 ^ k * ((3 * m + 2)! / ((2 * m + 2)! * m !)) := by
  subst h
  unfold a
  have h1 : (-1 : ℚ) ^ (2 * m + 2) = 1 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [h1, show 3 * (2 * m + 2) / 2 - 1 = 3 * m + 2 by omega,
    chq (3 * m + 2) (2 * m + 2) m (by ring)]
  norm_num

theorem aodd (k m : ℕ) (h : k = 2 * m + 1) :
    a k = (3 * m + 1)! / ((2 * m + 1)! * m !) * ((6 * m + 2)! / ((3 * m + 1)! * (3 * m + 1)!)) /
      ((2 * m)! / (m ! * m !)) := by
  subst h
  unfold a
  have h1 : (-1 : ℚ) ^ (2 * m + 1) = -1 := by
    rw [pow_succ, pow_mul]
    norm_num
  rw [h1, show 3 * (2 * m + 1) - 1 = 6 * m + 2 by omega,
    show (6 * m + 2) / 2 = 3 * m + 1 by omega, show 2 * m + 1 - 1 = 2 * m by omega,
    show 2 * m / 2 = m by omega, chq (3 * m + 1) (2 * m + 1) m (by ring),
    chq (6 * m + 2) (3 * m + 1) (3 * m + 1) (by ring), chq (2 * m) m m (by ring)]
  norm_num

end R348618

open scoped Nat in
theorem OMA.solution : type_of% @OMA.S_oeis_a348618.main := by
  intro n hn
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
    rw [show 2 * (j + 2) - 2 = 2 * j + 2 by omega,
      R348618.aeven (2 * (j + 2)) (j + 1) (by ring), R348618.aeven (2 * j + 2) j rfl]
    have f1 : ((3 * (j + 1) + 2)! : ℚ) = (3 * j + 5) * (3 * j + 4) * (3 * j + 3) * (3 * j + 2)! := by
      rw [show 3 * (j + 1) + 2 = 3 * j + 2 + 1 + 1 + 1 by ring]
      simp only [Nat.factorial_succ]
      push_cast
      ring
    have f2 : ((2 * (j + 1) + 2)! : ℚ) = (2 * j + 4) * (2 * j + 3) * (2 * j + 2)! := by
      rw [show 2 * (j + 1) + 2 = 2 * j + 2 + 1 + 1 by ring]
      simp only [Nat.factorial_succ]
      push_cast
      ring
    have f3 : ((j + 1)! : ℚ) = (j + 1) * j ! := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [f1, f2, f3]
    push_cast
    field_simp
    ring
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [show 2 * (j + 1) + 1 - 2 = 2 * j + 1 by omega,
      R348618.aodd (2 * (j + 1) + 1) (j + 1) rfl, R348618.aodd (2 * j + 1) j rfl]
    have f1 : ((3 * (j + 1) + 1)! : ℚ) = (3 * j + 4) * (3 * j + 3) * (3 * j + 2) * (3 * j + 1)! := by
      rw [show 3 * (j + 1) + 1 = 3 * j + 1 + 1 + 1 + 1 by ring]
      simp only [Nat.factorial_succ]
      push_cast
      ring
    have f2 : ((2 * (j + 1) + 1)! : ℚ) = (2 * j + 3) * (2 * j + 2) * (2 * j + 1)! := by
      rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by ring]
      simp only [Nat.factorial_succ]
      push_cast
      ring
    have f3 : ((j + 1)! : ℚ) = (j + 1) * j ! := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have f4 : ((6 * (j + 1) + 2)! : ℚ) = (6 * j + 8) * (6 * j + 7) * (6 * j + 6) * (6 * j + 5) *
        (6 * j + 4) * (6 * j + 3) * (6 * j + 2)! := by
      rw [show 6 * (j + 1) + 2 = 6 * j + 2 + 1 + 1 + 1 + 1 + 1 + 1 by ring]
      simp only [Nat.factorial_succ]
      push_cast
      ring
    have f5 : ((2 * (j + 1))! : ℚ) = (2 * j + 2) * (2 * j + 1) * (2 * j)! := by
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
      simp only [Nat.factorial_succ]
      push_cast
      ring
    rw [f1, f2, f3, f4, f5]
    push_cast
    field_simp
    ring
