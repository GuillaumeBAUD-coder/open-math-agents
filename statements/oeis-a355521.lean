import Mathlib

/-!
# A355521: Primes that cannot be represented as 2*p+q where p, q and (2*p^2+q^2)/3 are prime.

Source: https://oeis.org/A355521
Credit: @jagraj28

Conjecture (stated in A355521): there are no other terms than the ten listed ones,
`2, 3, 5, 7, 13, 31, 37, 97, 211, 271`.

Formalization notes:
* "`(2*p^2+q^2)/3` is prime" is stated without division: `2 * p ^ 2 + q ^ 2 = 3 * r` for a
  prime `r`. This also requires `3 ∣ 2 * p ^ 2 + q ^ 2`, as the entry means it (the comment in the
  entry notes that the quotient is an integer when neither `p` nor `q` is divisible by 3).
* `p` and `q` range over all primes, with no order between them (the example `11 = 2*2 + 7` has
  `p < q`).
* `main` says that the set of primes with no such representation is exactly the listed data.
  A direct search confirms that the primes up to 20000 with no such representation are exactly
  the ten listed numbers.
-/

namespace OMA.S_oeis_a355521

/-- `n = 2 * p + q` with `p`, `q` and `(2 * p ^ 2 + q ^ 2) / 3` prime. -/
def IsRepresentable (n : ℕ) : Prop :=
  ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ n = 2 * p + q ∧ 2 * p ^ 2 + q ^ 2 = 3 * r

/-- The conjecture of A355521: its listed terms are all of its terms. -/
theorem main :
    {n : ℕ | n.Prime ∧ ¬ IsRepresentable n} = {2, 3, 5, 7, 13, 31, 37, 97, 211, 271} := by
  sorry

end OMA.S_oeis_a355521
