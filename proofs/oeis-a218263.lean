import OMAStatements.S_oeis_a218263
import Mathlib

namespace A218263Proof

lemma ratio (k : ℕ) :
    ((k : ℚ) + 1) * ((k + 1).centralBinom : ℚ) = 2 * (2 * (k : ℚ) + 1) * (k.centralBinom : ℚ) := by
  exact_mod_cast Nat.succ_mul_centralBinom_succ k

lemma b_even (j : ℕ) : (((2 * j).choose (2 * j / 2) : ℕ) : ℚ) = (j.centralBinom : ℚ) := by
  have h1 : 2 * j / 2 = j := by omega
  rw [h1, Nat.centralBinom_eq_two_mul_choose]

lemma b_odd (j : ℕ) :
    (((2 * j + 1).choose ((2 * j + 1) / 2) : ℕ) : ℚ) = ((j + 1).centralBinom : ℚ) / 2 := by
  have h1 : (2 * j + 1) / 2 = j := by omega
  have hc : (j + 1).centralBinom = 2 * (2 * j + 1).choose j := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    have e3 : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
    rw [e3, Nat.choose_succ_succ', Nat.choose_symm_half]
    ring
  rw [h1, hc]
  push_cast
  ring

lemma binom_part (m : ℕ) :
    (((m : ℚ) + 4) - 6) * (((m : ℚ) + 4) - 3) * (((m : ℚ) + 4) + 1)
        * (((m + 4).choose ((m + 4) / 2) : ℕ) : ℚ) +
      (-((m : ℚ) + 4) ^ 3 + 6 * ((m : ℚ) + 4) ^ 2 + 11 * ((m : ℚ) + 4) - 36)
        * (((m + 3).choose ((m + 3) / 2) : ℕ) : ℚ) -
      (((m : ℚ) + 4) - 1) * (((m : ℚ) + 4) ^ 3 - 4 * ((m : ℚ) + 4) ^ 2 - 21 * ((m : ℚ) + 4) + 76)
        * (((m + 2).choose ((m + 2) / 2) : ℕ) : ℚ) +
      2 * (((m : ℚ) + 4) - 1) * (((m : ℚ) + 4) - 2) * (3 * ((m : ℚ) + 4) - 19)
        * (((m + 1).choose ((m + 1) / 2) : ℕ) : ℚ) +
      4 * (((m : ℚ) + 4) - 5) * (((m : ℚ) + 4) - 1) * (((m : ℚ) + 4) - 2) * (((m : ℚ) + 4) - 3)
        * ((m.choose (m / 2) : ℕ) : ℚ) = 0 := by
  rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
  · have e4 : 2 * j + 4 = 2 * (j + 2) := by ring
    have e3 : 2 * j + 3 = 2 * (j + 1) + 1 := by ring
    have e2 : 2 * j + 2 = 2 * (j + 1) := by ring
    rw [e4, e3, e2]
    simp only [b_even, b_odd]
    have r1 := ratio (j + 1)
    have r0 := ratio j
    simp only [Nat.add_assoc, Nat.reduceAdd] at r1 ⊢
    push_cast at r1 r0 ⊢
    linear_combination (4 * (j : ℚ) ^ 2 - 4 * (j : ℚ) + 5) * r1
      + (-2 * (2 * (j : ℚ) - 1) * (2 * (j : ℚ) + 3) * (2 * (j : ℚ) + 2)) * r0
  · have e4 : 2 * j + 1 + 4 = 2 * (j + 2) + 1 := by ring
    have e3 : 2 * j + 1 + 3 = 2 * (j + 2) := by ring
    have e2 : 2 * j + 1 + 2 = 2 * (j + 1) + 1 := by ring
    have e1 : 2 * j + 1 + 1 = 2 * (j + 1) := by ring
    rw [e4, e3, e2, e1]
    simp only [b_even, b_odd]
    have r2 := ratio (j + 2)
    have r1 := ratio (j + 1)
    simp only [Nat.add_assoc, Nat.reduceAdd] at r2 r1 ⊢
    push_cast at r2 r1 ⊢
    linear_combination ((2 * (j : ℚ) - 1) * (2 * (j : ℚ) + 2)) * r2
      + (-(2 * (j : ℚ) + 4) * ((2 * (j : ℚ) + 5) ^ 2 - 5 * (2 * (j : ℚ) + 5) - 4)) * r1

end A218263Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a218263.main := by
  intro I _ _ hI a ha n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have R4 := hI (m + 4) (by omega)
  have R3 := hI (m + 3) (by omega)
  have R2 := hI (m + 2) (by omega)
  have i41 : m + 4 - 1 = m + 3 := by omega
  have i42 : m + 4 - 2 = m + 2 := by omega
  have i43 : m + 4 - 3 = m + 1 := by omega
  have i44 : m + 4 - 4 = m := by omega
  have i31 : m + 3 - 1 = m + 2 := by omega
  have i32 : m + 3 - 2 = m + 1 := by omega
  have i21 : m + 2 - 1 = m + 1 := by omega
  have i22 : m + 2 - 2 = m := by omega
  rw [i41, i42] at R4
  rw [i31, i32] at R3
  rw [i21, i22] at R2
  rw [i41, i42, i43, i44]
  rw [ha (m + 4), ha (m + 3), ha (m + 2), ha (m + 1), ha m]
  have hB := A218263Proof.binom_part m
  push_cast at R4 R3 R2 hB ⊢
  linear_combination ((((m : ℚ) + 4) - 6) * (((m : ℚ) + 4) - 3) * (((m : ℚ) + 4) + 1)) * R4
    + (-2 * (((m : ℚ) + 4) - 1) * (((m : ℚ) + 4) - 9)) * R3
    + (-4 * (((m : ℚ) + 4) - 1) * (((m : ℚ) + 4) - 2) * (((m : ℚ) + 4) - 5)) * R2 - hB
