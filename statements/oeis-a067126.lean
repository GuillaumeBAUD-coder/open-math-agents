import Mathlib

/-!
# A067126: Numbers for which phi(n) >= phi(k) for all k = 1 to n-1

Source: https://oeis.org/A067126
Credit: @niclorusso

Conjecture (in the comments of A067126): 4 and 9 are the only composite terms.

Conventions:
* phi is Euler's totient, Mathlib's `Nat.totient`.
* n is a term when phi(n) >= phi(k) for every k with 1 <= k <= n - 1 (the definition of A067126).
* A composite number is a natural number n > 1 that is not prime.
* "4 and 9 are the only composite terms" is stated as a set equality: the composite terms are
  exactly 4 and 9.
-/

namespace OMA.S_oeis_a067126

/-- `n` is a term of A067126: `phi(n) >= phi(k)` for all `k = 1, ..., n - 1`. -/
def IsTerm (n : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k < n → Nat.totient k ≤ Nat.totient n

/-- The conjecture on A067126: the only composite terms are `4` and `9`. -/
theorem main : {n : ℕ | 1 < n ∧ ¬ n.Prime ∧ IsTerm n} = {4, 9} := by
  sorry

end OMA.S_oeis_a067126
