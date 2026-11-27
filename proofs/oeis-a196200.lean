import OMAStatements.S_oeis_a196200

-- Problem: OEIS A196200, Sandor inequality totient(psi(n)) <= n for n >= 2
-- Credit: @JamesSlash
-- Disproof: n = 39270 = 2*3*5*7*11*17 (counterexample credited to L. Toth in Sandor 2005).
-- psi(39270) = 3*4*6*8*12*18 = 2^9 * 3^5 = 124416 and totient(124416) = 2^8 * 2 * 3^4 = 41472 > 39270.

namespace OMA.A196200Proof

lemma pf : Nat.primeFactors 39270 = {2, 3, 5, 7, 11, 17} := by
  have h2 : Nat.Prime 2 := by norm_num
  have h3 : Nat.Prime 3 := by norm_num
  have h5 : Nat.Prime 5 := by norm_num
  have h7 : Nat.Prime 7 := by norm_num
  have h11 : Nat.Prime 11 := by norm_num
  have h17 : Nat.Prime 17 := by norm_num
  rw [show (39270 : ℕ) = 2 * 3 * 5 * 7 * 11 * 17 by norm_num]
  rw [Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    h2.primeFactors, h3.primeFactors, h5.primeFactors, h7.primeFactors,
    h11.primeFactors, h17.primeFactors]
  decide

lemma psi_val : OMA.S_oeis_a196200.psi 39270 = 2 ^ 9 * 3 ^ 5 := by
  unfold OMA.S_oeis_a196200.psi
  rw [pf]
  decide

lemma tot_val : Nat.totient (2 ^ 9 * 3 ^ 5) = 41472 := by
  rw [Nat.totient_mul (by norm_num), Nat.totient_prime_pow (by norm_num) (by norm_num),
    Nat.totient_prime_pow (by norm_num) (by norm_num)]
  norm_num

end OMA.A196200Proof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a196200.main) := by
  intro h
  have h1 := h 39270 (by norm_num)
  rw [OMA.A196200Proof.psi_val, OMA.A196200Proof.tot_val] at h1
  norm_num at h1
