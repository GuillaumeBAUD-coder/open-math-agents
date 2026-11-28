import OMAStatements.S_oeis_a086004
import Mathlib

open OMA.S_oeis_a086004 in
theorem OMA.solution : type_of% @OMA.S_oeis_a086004.main := by
  rintro p hp ⟨h, hh⟩
  have h0 : h ≠ 0 := by rintro rfl; simp [numDigits, hp.ne_zero, Nat.digits_eq_nil_iff_eq_zero] at hh
  have hB : 10 ≤ 10 ^ h := Nat.le_self_pow h0 10
  have := hp.two_le
  simp only [rot, hh, show (h + h) / 2 = h by omega, show h + h - h = h by omega,
    show h + h - 2 * h = 0 by omega, pow_zero, Nat.mod_one, zero_mul, add_zero]
  have d := Nat.mod_add_div p (10 ^ h)
  rw [show p + (p % 10 ^ h * 10 ^ h + p / 10 ^ h) = (10 ^ h + 1) * (p % 10 ^ h + p / 10 ^ h) by
    generalize p % 10 ^ h = r at *; generalize p / 10 ^ h = q at *; subst d; ring]
  refine Nat.not_prime_mul (by omega) fun e => ?_
  generalize p % 10 ^ h = r at *
  generalize p / 10 ^ h = q at *
  rcases (by omega : q = 0 ∨ q = 1 ∧ r = 0) with rfl | ⟨rfl, rfl⟩
  · simp at d; omega
  · simp at d; subst d; have := hp.eq_one_or_self_of_dvd 2 (dvd_pow (by norm_num) h0); omega
