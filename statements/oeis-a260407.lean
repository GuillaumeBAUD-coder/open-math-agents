import Mathlib

/-!
# A260407: Numbers n such that (n-1)^2+1 divides 2^(n-1)-1.

Source: https://oeis.org/A260407
Credit: @xor2k

Jaroslav Krizek, in the comments of A260407:
  Conjecture: also numbers n such that ((2^k)^(n-1)-1) == 0 mod ((n-1)^2+1) for all k >= 1.

Only this conjecture of the entry is formalized. The other remark of the entry (that the Fermat
numbers 2^(2^k)+1 with k > 1 are exactly the intersection of this sequence and A260406) is not
part of the statement.

Conventions:
* The sequence (offset 1) consists of the positive integers `n` such that `(n-1)^2+1` divides
  `2^(n-1)-1`; it starts with 1, since for n = 1 the modulus is 1 and 2^0 - 1 = 0.
* The conjecture says that this set coincides with the set of positive integers `n` such that
  for every `k ≥ 1` the number `(2^k)^(n-1) - 1` is 0 modulo `(n-1)^2+1`. It is stated as an
  equivalence for every `n ≥ 1`.
* Everything is in `ℕ`. Since `n ≥ 1`, `n - 1` is the true difference, and since powers of 2 and
  of 2^k are at least 1, the subtractions `2^(n-1) - 1` and `(2^k)^(n-1) - 1` are the true
  differences as well. `x == 0 mod m` is written `m ∣ x`.

Numerical check: a Python copy of the definition gives 1, 17, 257, 8209, 65537 for the terms
below 200000, which are the first five terms of the DATA of the entry (1, 17, 257, 8209, 65537,
649801, 1382401, 4294967297), and the two conditions agree for all n < 3000 with k up to 39.
-/

namespace OMA.S_oeis_a260407

/-- For every `n ≥ 1`: `(n-1)^2+1 ∣ 2^(n-1)-1` if and only if
`(n-1)^2+1 ∣ (2^k)^(n-1)-1` for all `k ≥ 1`. -/
theorem main :
    ∀ n : ℕ, 0 < n → (((n - 1) ^ 2 + 1 ∣ 2 ^ (n - 1) - 1) ↔
      ∀ k : ℕ, 1 ≤ k → (n - 1) ^ 2 + 1 ∣ (2 ^ k) ^ (n - 1) - 1) := by
  sorry

end OMA.S_oeis_a260407
