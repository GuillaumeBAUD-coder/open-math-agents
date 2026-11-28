import OMAStatements.S_oeis_a009191
import Mathlib

open OMA.S_oeis_a009191 in
/-- Every positive integer occurs as `gcd(n, d(n))`. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a009191.main := by
  intro k hk
  let t := k.divisors.card
  have htpos : 0 < t := by
    rw [Finset.card_pos]
    exact ⟨1, Nat.one_mem_divisors.mpr (Nat.ne_of_gt hk)⟩
  obtain ⟨q, hqge, hqprime⟩ := Nat.exists_infinite_primes (k * t + 1)
  have hqgtk : k < q := by
    have hle : k ≤ k * t := by
      calc k = k * 1 := by rw [mul_one]
        _ ≤ k * t := Nat.mul_le_mul_left k htpos
    omega
  have hnotqk : ¬ q ∣ k := by
    intro hdiv
    have hqlek : q ≤ k := Nat.le_of_dvd hk hdiv
    omega
  have hqtt : t < q := by
    have hle : t ≤ k * t := by
      calc t = 1 * t := by rw [one_mul]
        _ ≤ k * t := Nat.mul_le_mul_right t hk
    omega
  have hnotqt : ¬ q ∣ t := by
    intro hdiv
    have hqlet : q ≤ t := Nat.le_of_dvd htpos hdiv
    omega
  have hcop_qpow_t : (q ^ (k - 1)).Coprime t :=
    (hqprime.coprime_iff_not_dvd.mpr hnotqt).pow_left (k - 1)
  have hcop_kqpow : k.Coprime (q ^ (k - 1)) :=
    (hqprime.coprime_iff_not_dvd.mpr hnotqk).symm.pow_right (k - 1)
  have hqcard : (q ^ (k - 1)).divisors.card = k := by
    rw [← ArithmeticFunction.sigma_zero_apply,
      ArithmeticFunction.sigma_zero_apply_prime_pow hqprime]
    omega
  refine ⟨k * q ^ (k - 1), ?_⟩
  unfold a
  rw [hcop_kqpow.card_divisors_mul, hqcard]
  rw [mul_comm k.divisors.card k, Nat.gcd_mul_left,
    hcop_qpow_t.gcd_eq_one, mul_one]

