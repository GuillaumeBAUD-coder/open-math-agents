import OMAStatements.S_oeis_a262768
import Mathlib

/-!
# A262768: Mathar's recurrence

With c(j) = binomial(2j, j), the off-centre coefficient satisfies
binomial(2k, k+1) = c(k)·k/(k+1), so for n ≥ 1
a(n) = c(n+1)(n+1)/(n+2) − 2c(n) + c(n−1)(n−1)/n. Using (j+1)c(j+1) = 2(2j+1)c(j), every term of the
recurrence at n = m + 3 is a rational function of m times c(m), and the identity is checked by
clearing denominators.
-/

namespace A262768Proof

/-- The central binomial coefficient as a rational number. -/
noncomputable def c (j : ℕ) : ℚ := ((2 * j).choose j : ℚ)

theorem c_succ (j : ℕ) : c (j + 1) = 2 * (2 * j + 1) / (j + 1) * c j := by
  have h := Nat.succ_mul_centralBinom_succ j
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
  unfold c
  have h' : ((j : ℚ) + 1) * ((2 * (j + 1)).choose (j + 1) : ℚ) = 2 * (2 * j + 1) * ((2 * j).choose j : ℚ) := by
    exact_mod_cast h
  field_simp
  linear_combination h'

theorem off (k : ℕ) : ((2 * k).choose (k + 1) : ℚ) = c k * k / (k + 1) := by
  have h := Nat.choose_succ_right_eq (2 * k) k
  rw [show 2 * k - k = k by omega] at h
  have h' : ((2 * k).choose (k + 1) : ℚ) * ((k : ℚ) + 1) = ((2 * k).choose k : ℚ) * k := by
    exact_mod_cast h
  unfold c
  field_simp
  linear_combination h'

theorem a_formula (n : ℕ) (hn : 1 ≤ n) :
    (OMA.S_oeis_a262768.a n : ℚ) =
      c (n + 1) * (n + 1) / (n + 2) - 2 * c n + c (n - 1) * (n - 1 : ℕ) / n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold OMA.S_oeis_a262768.a
  have e1 : (2 * (m + 1) + 2).choose (m + 1) = (2 * (m + 2)).choose (m + 2 + 1) := by
    rw [show 2 * (m + 1) + 2 = (m + 1) + (m + 2 + 1) by ring, Nat.choose_symm_add]
    congr 1; ring
  have e2 : (2 * (m + 1) - 2).choose (m + 1) = (2 * m).choose (m + 1) := by
    congr 1
  push_cast
  rw [e1, e2, off, off]
  unfold c
  push_cast
  ring

end A262768Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a262768.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have key : (-2 * (((m + 3 : ℕ) : ℤ) + 2) * (49 * ((m + 3 : ℕ) : ℤ) - 95) * OMA.S_oeis_a262768.a (m + 3) +
      325 * (((m + 3 : ℕ) : ℤ) - 1) * (((m + 3 : ℕ) : ℤ) + 1) * OMA.S_oeis_a262768.a (m + 3 - 1) +
      2 * (67 * ((m + 3 : ℕ) : ℤ) - 38) * (2 * ((m + 3 : ℕ) : ℤ) - 5) *
        OMA.S_oeis_a262768.a (m + 3 - 2) : ℚ) = 0 := by
    rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
    rw [A262768Proof.a_formula (m + 3) (by omega), A262768Proof.a_formula (m + 2) (by omega),
      A262768Proof.a_formula (m + 1) (by omega)]
    simp only [show m + 3 - 1 = m + 2 by omega, show m + 2 - 1 = m + 1 by omega,
      show m + 1 - 1 = m by omega, show m + 3 + 1 = m + 4 by omega, show m + 2 + 1 = m + 3 by omega]
    rw [A262768Proof.c_succ (m + 3), A262768Proof.c_succ (m + 2), A262768Proof.c_succ (m + 1),
      A262768Proof.c_succ m]
    push_cast
    field_simp
    ring
  exact_mod_cast key
