import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H2_R1
import Mathlib

/-! A value `n > 1` that is a minimum of its own Collatz trajectory has `n % 4 = 3`: an even `n`
halves in one step, and `n % 4 = 1` gives `(3 n + 1) / 4 < n` after three steps. -/

namespace OMA.Step_CollatzConjecture_collatz_conjecture_R1_H2_R1_H2

open CollatzConjecture

theorem min_mod_four (n : ℕ) (hn : 1 < n) (h : ∀ i : ℕ, n ≤ collatzStep^[i] n) : n % 4 = 3 := by
  by_contra hne
  rcases Nat.even_or_odd n with he | ho
  · have h1 := h 1
    have e1 : collatzStep^[1] n = n / 2 := by
      change collatzStep n = n / 2
      rw [collatzStep, if_pos he]
    rw [e1] at h1
    omega
  · have hodd : n % 2 = 1 := Nat.odd_iff.mp ho
    have s1 : collatzStep n = 3 * n + 1 := by
      rw [collatzStep, if_neg (Nat.not_even_iff_odd.mpr ho)]
    have ev1 : Even (3 * n + 1) := Nat.even_iff.mpr (by omega)
    have s2 : collatzStep (3 * n + 1) = (3 * n + 1) / 2 := by rw [collatzStep, if_pos ev1]
    have ev2 : Even ((3 * n + 1) / 2) := Nat.even_iff.mpr (by omega)
    have s3 : collatzStep ((3 * n + 1) / 2) = (3 * n + 1) / 2 / 2 := by
      rw [collatzStep, if_pos ev2]
    have h3 := h 3
    have e3 : collatzStep^[3] n = collatzStep (collatzStep (collatzStep n)) := rfl
    rw [e3, s1, s2, s3] at h3
    omega

end OMA.Step_CollatzConjecture_collatz_conjecture_R1_H2_R1_H2

theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1.H2 :=
  OMA.Step_CollatzConjecture_collatz_conjecture_R1_H2_R1_H2.min_mod_four
