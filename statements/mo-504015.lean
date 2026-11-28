import Mathlib

/-!
# For a prime, is there always a prime number for which it is a primitive root?

Source: https://mathoverflow.net/questions/504015 (CC BY-SA 4.0).

Artin's primitive root conjecture says that every integer `a ≠ ±1` that is not a square is a
primitive root modulo infinitely many primes; by Heath-Brown at most two primes `a` can fail it.
The question: is it known that for every prime `q` there is at least one prime `p > q` such that
`q` is a primitive root modulo `p`?

We state the affirmative answer.

Formalization notes:
* "`q` is a primitive root mod `p`" is `orderOf (q : ZMod p) = p - 1`, i.e. the class of `q`
  generates the multiplicative group of `ZMod p` (for `p > q` the class of `q` is nonzero).
* Checked numerically: for every prime `q < 2000` such a prime `p` exists.
-/

namespace OMA.S_mo_504015

/-- Every prime `q` is a primitive root modulo some prime `p > q`. -/
theorem main : ∀ q : ℕ, q.Prime → ∃ p : ℕ, p.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  sorry

end OMA.S_mo_504015
