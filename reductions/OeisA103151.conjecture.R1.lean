import FormalConjectures.OEIS.«103151»

-- Reduction OeisA103151.conjecture.R1 of Number of decompositions of $2n+1$ into $2p+q$, where $p$ and $q$ are both odd primes
-- Credit: @ihateSAS
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# A103151: the residue class of `2n + 1` modulo 3

`a n` counts the odd primes `p ≤ n` with `2p < 2n + 1` and `2n + 1 - 2p` again prime, i.e. the
number of ways to write `2n + 1 = 2p + q` with `p` and `q` odd primes.  The conjecture is that
this count is never zero for `n ≥ 4`.

The three cases below are the residue classes of `n` modulo `3`, and they are genuinely
different problems, because they decide whether the small prime `3` can be used at all:

* `n ≡ 1 (mod 3)`: then `2n + 1 ≡ 0 (mod 3)`, so neither `p` nor `q` may be `3`; a decomposition
  needs two odd primes `≢ 0 (mod 3)`, and the singular series is the smallest of the three
  classes.
* `n ≡ 2 (mod 3)`: then `2n + 1 ≡ 2 (mod 3)`, and taking `q = 3` leaves `p = n - 1`, which is
  `≡ 1 (mod 3)`; the class reduces to the primality of the single number `n - 1`.
* `n ≡ 0 (mod 3)`: then `2n + 1 ≡ 1 (mod 3)`, and taking `p = 3` leaves `q = 2n - 5 ≡ 1 (mod 3)`;
  the class reduces to the primality of the single number `2n - 5`.

So `H2` and `H3` are the two classes where the problem collapses to a binary statement about one
linear form, while `H1` is the class in which the prime `3` is unavailable.  All three are open.

The reduction's content is the case split on `n % 3`.

*References:*
- [A103151](https://oeis.org/A103151)
-/

namespace OMA.R_OeisA103151_conjecture_R1

open OeisA103151

/-- The class `n ≡ 1 (mod 3)`, where `2n + 1` is divisible by `3` and the prime `3` is not
available for either summand. -/
def H1 : Prop :=
  ∀ n : ℕ, 4 ≤ n → n % 3 = 1 → a n ≥ 1

/-- The class `n ≡ 2 (mod 3)`, where `q = 3` leaves `p = n - 1`. -/
def H2 : Prop :=
  ∀ n : ℕ, 4 ≤ n → n % 3 = 2 → a n ≥ 1

/-- The class `n ≡ 0 (mod 3)`, where `p = 3` leaves `q = 2n - 5`. -/
def H3 : Prop :=
  ∀ n : ℕ, 4 ≤ n → n % 3 = 0 → a n ≥ 1

theorem main : H1 → H2 → H3 → type_of% @OeisA103151.conjecture := by
  intro h1 h2 h3 n hn
  have hlt : n % 3 < 3 := Nat.mod_lt n (by decide)
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hcases with h | h | h
  · exact h3 n hn h
  · exact h1 n hn h
  · exact h2 n hn h

end OMA.R_OeisA103151_conjecture_R1
