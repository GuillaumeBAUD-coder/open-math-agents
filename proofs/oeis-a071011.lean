import OMAStatements.S_oeis_a071011

-- Problem: A071011, sigma(m) == 0 (mod 4) whenever m is not a sum of two squares.
-- Credit: @ShoQo
-- Proof: m has a prime q == 3 (mod 4) to an odd power 2k+1 (Nat.eq_sq_add_sq_iff), so
-- sigma(m) = sigma(q^(2k+1)) * sigma(r), and sigma(q^(2k+1)) = sum of (1 + q) q^(2i), 4 | 1 + q.

open ArithmeticFunction

namespace OMA_A071011_Proof

/-- Pairing consecutive powers: `q^(2i) + q^(2i+1) = q^(2i) * (1 + q)` and `4 ∣ 1 + q`. -/
lemma four_dvd_geom (q k : ℕ) (hq : q % 4 = 3) :
    4 ∣ ∑ i ∈ Finset.range (2 * k + 2), q ^ i := by
  induction k with
  | zero => simp [Finset.sum_range_succ]; omega
  | succ k ih =>
    rw [show 2 * (k + 1) + 2 = 2 * k + 2 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, add_assoc]
    refine dvd_add ih ?_
    rw [show q ^ (2 * k + 2) + q ^ (2 * k + 2 + 1) = q ^ (2 * k + 2) * (1 + q) by ring]
    exact Dvd.dvd.mul_left (by omega) _

end OMA_A071011_Proof

open OMA_A071011_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a071011.main := by
  intro m hm
  have hm0 : m ≠ 0 := by rintro rfl; exact hm ⟨0, 0, by simp⟩
  rw [Nat.eq_sq_add_sq_iff] at hm
  push Not at hm
  obtain ⟨q, hqmem, hq4, hodd⟩ := hm
  have hqp := Nat.prime_of_mem_primeFactors hqmem
  have := Fact.mk hqp
  obtain ⟨e, r, hndvd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 q hqp.one_lt.ne'
  have hr0 : r ≠ 0 := by rintro rfl; simp at hm0
  have he : padicValNat q (q ^ e * r) = e := by
    rw [padicValNat.mul (pow_ne_zero _ hqp.ne_zero) hr0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hndvd, add_zero]
  rw [he] at hodd
  obtain ⟨k, rfl⟩ := Nat.not_even_iff_odd.mp hodd
  have hcop : Nat.Coprime (q ^ (2 * k + 1)) r :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hqp).mpr hndvd)
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_apply_prime_pow hqp]
  exact Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right (four_dvd_geom q k hq4) _)
