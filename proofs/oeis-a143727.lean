import OMAStatements.S_oeis_a143727

-- Problem: A143727, every near-prime number is a multiple of 15.
-- Credit: @bnb9001

namespace OMA_A143727_Proof

lemma eq_of_prime_dvd {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (h : q ∣ p) : q = p :=
  (Nat.prime_dvd_prime_iff_eq hq hp).1 h

end OMA_A143727_Proof

open OMA_A143727_Proof OMA.S_oeis_a143727 in
theorem OMA.solution : type_of% @OMA.S_oeis_a143727.main := by
  rintro n ⟨hm2, hp2, hm4, hp4, hm8, hp8⟩
  have hn : 10 ≤ n := by have := hm8.two_le; omega
  have h3 : 3 ∣ n := by
    have : 3 ∣ n ∨ 3 ∣ n + 2 ∨ 3 ∣ n - 2 := by omega
    rcases this with h | h | h
    · exact h
    · have := eq_of_prime_dvd Nat.prime_three hp2 h; omega
    · have := eq_of_prime_dvd Nat.prime_three hm2 h; omega
  have h5 : 5 ∣ n := by
    have : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
    rcases this with h | h | h | h | h
    · omega
    · have := eq_of_prime_dvd Nat.prime_five hp4 (by omega); omega
    · have := eq_of_prime_dvd Nat.prime_five hm2 (by omega); omega
    · have := eq_of_prime_dvd Nat.prime_five hp2 (by omega); omega
    · have := eq_of_prime_dvd Nat.prime_five hm4 (by omega); omega
  omega
