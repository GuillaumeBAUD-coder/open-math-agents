import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Monotone.Defs

/-!
# The prime-gap conjecture for OEIS A031932

Jahangeer Kholdi and Farideh Firoozbakht, 29 November 2014, in
[OEIS A031932](https://oeis.org/A031932). Formalization by @pblivin0x.

The sequence enumerates the lower endpoints of consecutive-prime gaps of 14.
The OEIS offset is 1, so `a k` below represents term number `k + 1`.
All terms are positive. Raising the source inequality for term number `n`
to the positive power `n` gives the natural-power comparison in `main`.
-/

namespace OMA.S_oeis_a031932

/-- The next prime after `p` is `p + 14`, and `p` itself is prime. -/
def lowerEndpoint (p : ℕ) : Prop :=
  p.Prime ∧ (p + 14).Prime ∧ ∀ q : ℕ, p < q → q < p + 14 → ¬ q.Prime

/-- The endpoints form an infinite sequence whose successive roots strictly decrease. -/
theorem main :
    ∃ a : ℕ → ℕ, StrictMono a ∧
      (∀ p : ℕ, lowerEndpoint p ↔ ∃ k : ℕ, a k = p) ∧
      ∀ k : ℕ, a (k + 1) ^ (k + 1) < a k ^ (k + 2) := by
  sorry

end OMA.S_oeis_a031932
