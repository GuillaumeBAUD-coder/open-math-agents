import Mathlib

/-!
# Does the converse of Wolstenholme's theorem hold for all natural numbers?

Source: https://en.wikipedia.org/wiki/Wolstenholme%27s_theorem#The_converse_as_a_conjecture
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: Wolstenholme's theorem states that for a prime `p >= 5` the binomial coefficient
`choose (2 * p - 1) (p - 1)` is congruent to `1` modulo `p ^ 3`.  It is conjectured that the
converse holds, that is, that if `choose (2 * n - 1) (n - 1)` is congruent to `1` modulo `n ^ 3`
for a natural number `n > 1`, then `n` is prime.  No composite numbers satisfying the congruence
are known.

So the proposition formalized below is: every `n > 1` with
`choose (2 * n - 1) (n - 1) = 1` in `ZMod (n ^ 3)` is prime.
-/

namespace OMA.S_wp_does_the_converse_of_wolstenholme_s_theorem_hold_for_all_natural_numbers

-- definitions the statement needs (no sorry, no axiom)

/-- Does the converse of Wolstenholme's theorem hold? -/
theorem main : ∀ n : ℕ, 1 < n → Nat.ModEq (n ^ 3) (Nat.choose (2 * n - 1) (n - 1)) 1 → n.Prime := by
  sorry

end OMA.S_wp_does_the_converse_of_wolstenholme_s_theorem_hold_for_all_natural_numbers
