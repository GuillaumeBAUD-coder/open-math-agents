import OMAStatements.S_oeis_a196200
import Mathlib

-- Disproof: n = 39270 = 2*3*5*7*11*17 has psi n = 124416 = 2^9 * 3^5,
-- and totient (2^9 * 3^5) = 41472 > 39270.

namespace OMA.A196200Disproof

theorem pf : (39270 : ℕ).primeFactors = {2, 3, 5, 7, 11, 17} := by
  have h : (39270 : ℕ) = 2 * 3 * 5 * 7 * 11 * 17 := by norm_num
  rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
  decide

theorem psi_val : OMA.S_oeis_a196200.psi 39270 = 2 ^ 9 * 3 ^ 5 := by
  unfold OMA.S_oeis_a196200.psi
  rw [pf]
  decide

theorem tot : (2 ^ 9 * 3 ^ 5 : ℕ).totient = 41472 := by
  rw [Nat.totient_mul (by norm_num), Nat.totient_prime_pow (by norm_num) (by norm_num),
    Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num

end OMA.A196200Disproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a196200.main) := by
  intro h
  have := h 39270 (by norm_num)
  rw [OMA.A196200Disproof.psi_val, OMA.A196200Disproof.tot] at this
  norm_num at this
