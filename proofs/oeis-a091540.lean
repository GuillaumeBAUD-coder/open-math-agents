import OMAStatements.S_oeis_a091540
import Mathlib

namespace OMA.A091540Proof

open OMA.S_oeis_a091540 Finset

theorem q_succ (n : ℕ) : q (n + 1) = q n * (3 * (n : ℤ) + 1) := by
  simp [q, Finset.prod_range_succ]

theorem two_dvd_q (n : ℕ) : 2 ∣ q (n + 2) := by
  induction n with
  | zero => exact ⟨2, by simp [q, Finset.prod_range_succ]⟩
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by ring, q_succ]
    exact Dvd.dvd.mul_right ih _

theorem six_dvd (n : ℕ) : 6 ∣ numerator (n + 2) := by
  unfold numerator
  have h3a : (3 : ℤ) ∣ (3 : ℤ) ^ (n + 2) * ((n + 2).factorial : ℤ) :=
    Dvd.dvd.mul_right (dvd_pow_self 3 (by omega)) _
  have h2a : (2 : ℤ) ∣ (3 : ℤ) ^ (n + 2) * ((n + 2).factorial : ℤ) := by
    apply Dvd.dvd.mul_left
    have : 2 ∣ (n + 2).factorial := Nat.dvd_factorial (by norm_num) (by omega)
    exact_mod_cast this
  have h3 : (3 : ℤ) ∣ (3 : ℤ) ^ (n + 2) * ((n + 2).factorial : ℤ) - 3 * q (n + 2) :=
    dvd_sub h3a (dvd_mul_right 3 _)
  have h2 : (2 : ℤ) ∣ (3 : ℤ) ^ (n + 2) * ((n + 2).factorial : ℤ) - 3 * q (n + 2) :=
    dvd_sub h2a (Dvd.dvd.mul_left (two_dvd_q n) 3)
  have : IsCoprime (2 : ℤ) 3 := by norm_num [Int.isCoprime_iff_gcd_eq_one]
  have := this.mul_dvd h2 h3
  simpa using this

theorem a_mul (n : ℕ) : a (n + 2) * 6 = numerator (n + 2) :=
  Int.ediv_mul_cancel (six_dvd n)

end OMA.A091540Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a091540.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  simp only [show m + 4 - 1 = (m + 1) + 2 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 = (m + 2) + 2 by omega]
  have e0 := OMA.A091540Proof.a_mul (m + 2)
  have e1 := OMA.A091540Proof.a_mul (m + 1)
  have e2 := OMA.A091540Proof.a_mul m
  simp only [OMA.S_oeis_a091540.numerator] at e0 e1 e2
  rw [show m + 2 + 2 = (m + 1 + 2) + 1 by ring, OMA.A091540Proof.q_succ,
    show m + 1 + 2 = (m + 2) + 1 by ring, OMA.A091540Proof.q_succ,
    Nat.factorial_succ, Nat.factorial_succ] at e0
  rw [show m + 1 + 2 = (m + 2) + 1 by ring, OMA.A091540Proof.q_succ, Nat.factorial_succ] at e1
  push_cast at e0 e1 e2
  have key : (OMA.S_oeis_a091540.a (m + 2 + 2) + (-6 * ((m + 2 + 2 : ℕ) : ℤ) + 5) *
      OMA.S_oeis_a091540.a (m + 1 + 2) + 3 * (((m + 2 + 2 : ℕ) : ℤ) - 1) *
      (3 * ((m + 2 + 2 : ℕ) : ℤ) - 5) * OMA.S_oeis_a091540.a (m + 2)) * 6 = 0 := by
    push_cast
    rw [pow_succ, pow_succ] at e0
    rw [pow_succ] at e1
    linear_combination e0 + (-6 * ((m : ℤ) + 2 + 2) + 5) * e1 +
      3 * (((m : ℤ) + 2 + 2) - 1) * (3 * ((m : ℤ) + 2 + 2) - 5) * e2
  have := mul_eq_zero.mp key
  rcases this with h | h
  · push_cast at h ⊢; linarith
  · norm_num at h
