import Mathlib

/-!
# A061712: Smallest prime with Hamming weight n.

Source: https://oeis.org/A061712
Credit: @thatoneguy006

a(n) is the smallest prime with exactly n 1's when written in binary (offset 1):
2, 3, 7, 23, 31, 311, 127, ...

The conjecture stated here, from the entry:

  Conjecture: a(n) < 2^(n+3). - T. D. Noe, Mar 14 2008

Reading. It is not known that a prime of every Hamming weight exists: the entry records that
Drmota, Mauduit and Rivat prove that a(n) exists for n > N for some N. The conjecture uses a(n)
as a number, so it asserts in particular that a(n) exists. Since a(n) is the least prime of
weight n, the claim that a(n) exists and a(n) < 2^(n+3) is equivalent to: some prime of Hamming weight n is
less than 2^(n+3). That is the form stated here. (Writing a(n) as an `sInf` would make the
inequality hold vacuously for an n without such a prime, so that form is avoided.)

The Hamming weight of `p` is the number of digits equal to 1 in `Nat.digits 2 p`, A000120.
-/

namespace OMA.S_oeis_a061712

/-- The binary weight A000120: the number of 1's in the binary expansion. -/
def hammingWeight (m : ℕ) : ℕ := (Nat.digits 2 m).count 1

/-- Noe's conjecture: for every n ≥ 1 the least prime of Hamming weight n exists and is below
2^(n+3); equivalently some prime of Hamming weight n is below 2^(n+3). -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ hammingWeight p = n ∧ p < 2 ^ (n + 3) := by
  sorry

end OMA.S_oeis_a061712
