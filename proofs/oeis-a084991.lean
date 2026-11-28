import OMAStatements.S_oeis_a084991
import Mathlib

/-!
# OEIS A084991: palindromes that are a sum of two primes

* If `k = p + q` is odd, one of the primes is even, hence equal to `2`, and the other is
  `k - 2`. Conversely if `k - 2` is prime then `k = 2 + (k - 2)`.
* Assuming Goldbach, every even `k > 2` is a sum of two primes, so every even palindrome
  `k > 2` is a term.
-/

open OMA.S_oeis_a084991

theorem OMA.solution : type_of% @OMA.S_oeis_a084991.main := by
  constructor
  · intro k hpal hodd
    constructor
    · rintro ⟨-, p, q, hp, hq, hpq⟩
      obtain ⟨j, hj⟩ := hodd
      rcases hp.eq_two_or_odd with h2 | hp1
      · have : k - 2 = q := by omega
        rw [this]
        exact hq
      · rcases hq.eq_two_or_odd with h2 | hq1
        · have : k - 2 = p := by omega
          rw [this]
          exact hp
        · omega
    · intro h
      have h2 := h.two_le
      exact ⟨hpal, 2, k - 2, Nat.prime_two, h, by omega⟩
  · intro G k hpal hev hk
    exact ⟨hpal, G k hev hk⟩
