import Mathlib

/-!
# The Gaussian-binomial period conjecture in OEIS A392059

Source: https://oeis.org/A392059
Original conjecture and sequence: Rick Zhou.

For `n ≥ 1`, `a n` is the product of the largest powers at most `n` of all
rational primes that ramify or remain inert in the Gaussian integers. These are
the prime `2` and the primes congruent to `3` modulo `4`.

The conjecture says that `a n` is the least positive integer `k` for which
`binomial (x + k i) n` and `binomial x n` are congruent modulo `1 + i` for every
integer `x`. Here `binomial z n` is the polynomial binomial coefficient, given
by the falling factorial at `z` divided by `n!`. We clear the common denominator
in the congruence, so the condition is that the difference of the two falling
factorials is divisible by `n! * (1 + i)` in the Gaussian integers. For integral
`x`, this also enforces integrality of the translated binomial coefficient.
-/

namespace OMA.S_oeis_a392059

/-- The Gaussian integer `i`. -/
def imaginaryUnit : GaussianInt := ⟨0, 1⟩

/-- The falling-factorial polynomial evaluated at a Gaussian integer. -/
def falling (z : GaussianInt) (n : ℕ) : GaussianInt :=
  ∏ j ∈ Finset.range n, (z - (j : GaussianInt))

/-- The product of the specified maximal prime powers. -/
def a (n : ℕ) : ℕ :=
  ∏ p ∈ n.primesLE.filter (fun p => p = 2 ∨ p % 4 = 3), p ^ Nat.log p n

/-- A positive vertical shift that preserves every `n`-th binomial residue. -/
def IsPeriod (n k : ℕ) : Prop :=
  0 < k ∧ ∀ x : ℤ,
    (n.factorial : GaussianInt) * (1 + imaginaryUnit) ∣
      falling ((x : GaussianInt) + (k : GaussianInt) * imaginaryUnit) n -
        falling (x : GaussianInt) n

theorem main : ∀ n : ℕ, 0 < n → IsLeast {k : ℕ | IsPeriod n k} (a n) := by
  sorry

end OMA.S_oeis_a392059
