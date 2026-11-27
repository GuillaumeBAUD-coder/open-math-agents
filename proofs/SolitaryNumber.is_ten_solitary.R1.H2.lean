import OMAReductions.R_SolitaryNumber_is_ten_solitary_R1

-- Step SolitaryNumber.is_ten_solitary.R1.H2: hypothesis H2 of reduction SolitaryNumber.is_ten_solitary.R1
-- Credit: @JamesSlash. 5 * sigma m = 9 * m is odd, so sigma m is odd, and an odd number with odd
-- sigma is a square. The lemma odd_square is copied from the merged proof
-- proofs/Erdos955.erdos_955.variants.empty_preimage.lean by @Halldon.

namespace OMASolitaryH2

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

lemma odd_square {n : ℕ} : Odd n → Odd (σ 1 n) → IsSquare n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => simp
  | prime_pow p k hp hk =>
    intro hn hσ
    have hpodd := (Nat.odd_pow_iff hk.ne').mp hn
    rw [sigma_one_apply_prime_pow hp, Finset.odd_sum_iff_odd_card_odd] at hσ
    have hOdd (i : ℕ) : Odd (p ^ i) := hpodd.pow
    simp [hOdd] at hσ
    have hEven : Even k := by
      rw [Nat.even_iff]
      have hmod := Nat.odd_iff.mp hσ
      omega
    obtain ⟨j, hj⟩ := hEven
    exact ⟨p ^ j, by rw [hj, pow_add]⟩
  | coprime a b ha hb hab ihA ihB =>
    intro hn hσ
    rw [isMultiplicative_sigma.map_mul_of_coprime hab] at hσ
    exact (ihA (Nat.odd_mul.mp hn).1 (Nat.odd_mul.mp hσ).1).mul
      (ihB (Nat.odd_mul.mp hn).2 (Nat.odd_mul.mp hσ).2)


end OMASolitaryH2

open ArithmeticFunction in
open scoped ArithmeticFunction.sigma in
theorem OMA.solution : OMA.R_SolitaryNumber_is_ten_solitary_R1.H2 := by
  intro m hm h
  apply OMASolitaryH2.odd_square hm
  rcases Nat.even_or_odd (σ 1 m) with he | ho
  · exfalso
    obtain ⟨r, hr⟩ := he
    obtain ⟨t, ht⟩ := hm
    omega
  · exact ho
