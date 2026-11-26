import FormalConjectures.OEIS.«107247»

/-! Prime and semiprime values among sums of squares of nonacci numbers. -/

open OeisA107247

namespace OMA.Nonacci

-- Lucas certificates for the two large primes in the last factorization.
lemma prime840848161 : Nat.Prime 840848161 := by
  apply lucas_primality _ 7 (by simp only [Nat.reduceSub]; reduce_mod_char)
  intro q hq hd
  rw [show 840848161 - 1 = 2 ^ 5 * (3 * (5 * 1751767)) by decide] at hd
  have htwo : q ∣ 2 ^ 5 ↔ q = 2 := by
    refine ⟨fun h => (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h), ?_⟩
    rintro rfl
    decide
  simp only [hq.dvd_mul, htwo] at hd
  have hlarge : Nat.Prime 1751767 := by norm_num
  rw [Nat.prime_dvd_prime_iff_eq hq Nat.prime_three,
      Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 5),
      Nat.prime_dvd_prime_iff_eq hq hlarge] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> simp only [Nat.reduceSub, Nat.reduceDiv] <;> reduce_mod_char <;> decide

lemma prime5045088967 : Nat.Prime 5045088967 := by
  apply lucas_primality _ 3 (by simp only [Nat.reduceSub]; reduce_mod_char)
  intro q hq hd
  rw [show 5045088967 - 1 = 2 * (3 * 840848161) by decide] at hd
  simp only [hq.dvd_mul, Nat.prime_dvd_prime_iff_eq hq Nat.prime_two,
    Nat.prime_dvd_prime_iff_eq hq Nat.prime_three,
    Nat.prime_dvd_prime_iff_eq hq prime840848161] at hd
  rcases hd with rfl | rfl | rfl <;> simp only [Nat.reduceSub, Nat.reduceDiv] <;> reduce_mod_char <;> decide

lemma semiprime_of_value {n p q : ℕ} (h : a n = p * q) (hp : p.Prime) (hq : q.Prime) :
    (a n).IsSemiprime := by
  rw [h]
  exact hp.mul_isAlmostPrime_two hq

end OMA.Nonacci

theorem OMA.solution : type_of% @OeisA107247.known_prime_and_semiprimes := by
  have h8 : a 8 = 2 := by decide +kernel
  refine ⟨by simpa only [h8] using Nat.prime_two, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact OMA.Nonacci.semiprime_of_value (p := 2) (q := 3) (by decide +kernel) (by norm_num) (by norm_num)
  · exact OMA.Nonacci.semiprime_of_value (p := 2) (q := 11) (by decide +kernel) (by norm_num) (by norm_num)
  · exact OMA.Nonacci.semiprime_of_value (p := 2) (q := 43) (by decide +kernel) (by norm_num) (by norm_num)
  · exact OMA.Nonacci.semiprime_of_value (p := 2) (q := 683) (by decide +kernel) (by norm_num) (by norm_num)
  · exact OMA.Nonacci.semiprime_of_value (p := 2) (q := 2731) (by decide +kernel) (by norm_num) (by norm_num)
  · exact OMA.Nonacci.semiprime_of_value (p := 2) (q := 43691) (by decide +kernel) (by norm_num) (by norm_num)
  · exact OMA.Nonacci.semiprime_of_value (p := 37) (q := 9419) (by decide +kernel) (by norm_num) (by norm_num)
  · exact OMA.Nonacci.semiprime_of_value (p := 71) (q := 5045088967) (by decide +kernel)
      (by norm_num) OMA.Nonacci.prime5045088967
