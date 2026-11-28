import Mathlib

/-!
# A355518: Primes that cannot be represented as 2*p - q where p, q and 2*p^2 - q^2 are prime.

Source: https://oeis.org/A355518
Credit: @jagraj28

Conjecture (stated in A355518): there are no other terms than the eight listed ones,
`2, 3, 5, 13, 17, 37, 61, 137`.

Formalization notes:
* `p` and `q` range over all primes. The two differences are stated as sums in `ℕ`:
  `n + q = 2 * p` and `r + q ^ 2 = 2 * p ^ 2` with `r` prime. So both differences are positive
  integers, as primes are, and no truncated subtraction occurs.
* `main` says that the set of primes with no such representation is exactly the listed data.
  A direct search confirms that the primes up to 20000 with no such representation are exactly
  the eight listed numbers.
-/

namespace OMA.S_oeis_a355518

/-- `n = 2 * p - q` with `p`, `q` and `2 * p ^ 2 - q ^ 2` prime. -/
def IsRepresentable (n : ℕ) : Prop :=
  ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ n + q = 2 * p ∧ r + q ^ 2 = 2 * p ^ 2

/-- The conjecture of A355518: its listed terms are all of its terms. -/
theorem main :
    {n : ℕ | n.Prime ∧ ¬ IsRepresentable n} = {2, 3, 5, 13, 17, 37, 61, 137} := by
  sorry

end OMA.S_oeis_a355518
