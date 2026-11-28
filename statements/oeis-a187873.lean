import Mathlib

/-!
# A187873: Second smallest prime after n^2

Source: https://oeis.org/A187873
Credit: @xor2k

The entry's text is a remark (Robert Israel, Dec 18 2018):
Oppermann's conjecture implies a(n) < (n+1)^2 for n > 0.
For n > 1, a(n) >= n^2 + 3, with equality for n in A080149.

The first sentence only derives a consequence of Oppermann's conjecture (a famous open problem) and is
not formalized. Formalized is the precise claim of the second sentence: for every `n > 1`,
`a(n) ≥ n^2 + 3`, and `a(n) = n^2 + 3` holds exactly for the `n > 1` that lie in A080149.

Conventions:
* Offset 0. `a n` is the second smallest prime strictly greater than `n^2`, written as
  `Nat.nth (fun p => p.Prime ∧ n ^ 2 < p) 1` (`Nat.nth` counts from index 0, so index 1 is the
  second smallest element).
* A080149 is the set of natural numbers `k` such that `k^2 + 1` and `k^2 + 3` are both prime
  (for `k = 0` the number `1` is not prime, so the set agrees with the OEIS terms, offset 1).
* With equality for n in A080149 is read as: equality holds if and only if `n` is in A080149.
-/

namespace OMA.S_oeis_a187873

/-- A187873: the second smallest prime strictly greater than `n^2`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth (fun p => p.Prime ∧ n ^ 2 < p) 1

/-- A080149: numbers `k` such that `k^2 + 1` and `k^2 + 3` are both prime. -/
def A080149 : Set ℕ := {k | (k ^ 2 + 1).Prime ∧ (k ^ 2 + 3).Prime}

/-- For `n > 1`, `a(n) ≥ n^2 + 3`, with equality exactly when `n` is in A080149. -/
theorem main :
    (∀ n : ℕ, 1 < n → n ^ 2 + 3 ≤ a n) ∧
    (∀ n : ℕ, 1 < n → (a n = n ^ 2 + 3 ↔ n ∈ A080149)) := by
  sorry

end OMA.S_oeis_a187873
