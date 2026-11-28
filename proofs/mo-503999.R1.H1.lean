import OMAReductions.R_mo_503999_R1

open Nat OMA.S_mo_503999 in
theorem OMA.solution : OMA.R_mo_503999_R1.H1 := by
  intro i h c
  have q j (d : 11 ∣ nth Nat.Prime j) : j = 4 := nth_injective infinite_setOfPred_prime <|
    ((prime_dvd_prime_iff_eq prime_eleven (prime_nth_prime j)).1 d).symm.trans nth_prime_four_eq_eleven.symm
  have a : nth Nat.Prime 5 = 13 := by rw [← show count Nat.Prime 13 = 5 by decide]; exact nth_count (by norm_num)
  have b : nth Nat.Prime 6 = 17 := by rw [← show count Nat.Prime 17 = 6 by decide]; exact nth_count (by norm_num)
  have : i = 2 ∨ i = 3 ∨ i = 4 := by
    rcases prime_eleven.dvd_mul.1 c with d | d
    · rcases prime_eleven.dvd_mul.1 d with d | d <;> have := q _ d <;> omega
    · have := q _ d; omega
  rcases this with rfl | rfl | rfl <;> revert h <;>
    norm_num [nth_prime_two_eq_five, nth_prime_three_eq_seven, nth_prime_four_eq_eleven, a, b, IsPalindrome]
