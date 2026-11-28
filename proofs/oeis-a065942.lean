import OMAStatements.S_oeis_a065942
import Mathlib

open OMA.S_oeis_a065942

namespace P065942

noncomputable def E (j : ℕ) : ℚ := ((3 * j).factorial : ℚ) / (j.factorial * (2 * j).factorial)

theorem Epos (j : ℕ) : E j ≠ 0 := by unfold E; positivity

theorem ch (N k : ℕ) (h : k ≤ N) : ((N.choose k : ℕ) : ℚ) = (N.factorial : ℚ) / (k.factorial * (N - k).factorial) :=
  Nat.cast_choose ℚ h

theorem v0 (j : ℕ) : (a (2 * j) : ℚ) = E j := by
  unfold a T E
  rw [show 2 * (2 * j) - (2 * j + 1) / 2 = 3 * j by omega, show 2 * j / 2 = j by omega,
    ch _ _ (by omega), show 3 * j - j = 2 * j by omega]

theorem v1 (j : ℕ) : (a (2 * j + 1) : ℚ) = E j * ((3 * j + 1) / (2 * j + 1)) := by
  unfold a T E
  rw [show 2 * (2 * j + 1) - (2 * j + 1 + 1) / 2 = 3 * j + 1 by omega, show (2 * j + 1) / 2 = j by omega,
    ch _ _ (by omega), show 3 * j + 1 - j = 2 * j + 1 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp

theorem v2 (j : ℕ) : (a (2 * j + 2) : ℚ) =
    E j * ((3 * j + 3) * (3 * j + 2) * (3 * j + 1) / ((j + 1) * (2 * j + 2) * (2 * j + 1))) := by
  unfold a T E
  rw [show 2 * (2 * j + 2) - (2 * j + 2 + 1) / 2 = 3 * j + 3 by omega, show (2 * j + 2) / 2 = j + 1 by omega,
    ch _ _ (by omega), show 3 * j + 3 - (j + 1) = 2 * j + 2 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem v3 (j : ℕ) : (a (2 * j + 3) : ℚ) =
    E j * ((3 * j + 4) * (3 * j + 3) * (3 * j + 2) * (3 * j + 1) / ((j + 1) * (2 * j + 3) * (2 * j + 2) * (2 * j + 1))) := by
  unfold a T E
  rw [show 2 * (2 * j + 3) - (2 * j + 3 + 1) / 2 = 3 * j + 4 by omega, show (2 * j + 3) / 2 = j + 1 by omega,
    ch _ _ (by omega), show 3 * j + 4 - (j + 1) = 2 * j + 3 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem v4 (j : ℕ) : (a (2 * j + 4) : ℚ) =
    E j * ((3 * j + 6) * (3 * j + 5) * (3 * j + 4) * (3 * j + 3) * (3 * j + 2) * (3 * j + 1) /
      ((j + 2) * (j + 1) * (2 * j + 4) * (2 * j + 3) * (2 * j + 2) * (2 * j + 1))) := by
  unfold a T E
  rw [show 2 * (2 * j + 4) - (2 * j + 4 + 1) / 2 = 3 * j + 6 by omega, show (2 * j + 4) / 2 = j + 2 by omega,
    ch _ _ (by omega), show 3 * j + 6 - (j + 2) = 2 * j + 4 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

end P065942

theorem OMA.solution : type_of% @OMA.S_oeis_a065942.main := by
  intro n hn
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
    subst hm
    rw [show j + 2 + (j + 2) - 1 = 2 * j + 3 by omega, show j + 2 + (j + 2) - 2 = 2 * j + 2 by omega,
      show j + 2 + (j + 2) - 3 = 2 * j + 1 by omega, show j + 2 + (j + 2) = 2 * j + 4 by omega]
    have h := P065942.Epos j
    have e : ((8 * ((2 * j + 4 : ℕ) : ℤ) * ((2 * j + 4 : ℕ) - 1) * a (2 * j + 4)
        - 36 * (((2 * j + 4 : ℕ) : ℤ) - 1) * ((2 * j + 4 : ℕ) - 3) * a (2 * j + 3)
        + 6 * (-9 * ((2 * j + 4 : ℕ) : ℤ) ^ 2 + 18 * (2 * j + 4 : ℕ) - 14) * a (2 * j + 2)
        + 27 * (3 * ((2 * j + 4 : ℕ) : ℤ) - 7) * (3 * (2 * j + 4 : ℕ) - 8) * a (2 * j + 1) : ℤ) : ℚ) = 0 := by
      push_cast
      rw [P065942.v1, P065942.v2, P065942.v3, P065942.v4]
      field_simp
      ring
    exact_mod_cast e
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    subst hm
    rw [show 2 * (j + 1) + 1 - 1 = 2 * j + 2 by omega, show 2 * (j + 1) + 1 - 2 = 2 * j + 1 by omega,
      show 2 * (j + 1) + 1 - 3 = 2 * j by omega, show 2 * (j + 1) + 1 = 2 * j + 3 by omega]
    have h := P065942.Epos j
    have e : ((8 * ((2 * j + 3 : ℕ) : ℤ) * ((2 * j + 3 : ℕ) - 1) * a (2 * j + 3)
        - 36 * (((2 * j + 3 : ℕ) : ℤ) - 1) * ((2 * j + 3 : ℕ) - 3) * a (2 * j + 2)
        + 6 * (-9 * ((2 * j + 3 : ℕ) : ℤ) ^ 2 + 18 * (2 * j + 3 : ℕ) - 14) * a (2 * j + 1)
        + 27 * (3 * ((2 * j + 3 : ℕ) : ℤ) - 7) * (3 * (2 * j + 3 : ℕ) - 8) * a (2 * j) : ℤ) : ℚ) = 0 := by
      push_cast
      rw [P065942.v0, P065942.v1, P065942.v2, P065942.v3]
      field_simp
      ring
    exact_mod_cast e
