import Mathlib

/-!
# Does the converse of Wolstenholme's theorem hold for all natural numbers?

Source: https://en.wikipedia.org/wiki/Wolstenholme's_theorem#The_converse_as_a_conjecture
Credit: @mwhuss

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source ("The converse as a conjecture"): Wolstenholme's theorem says that for a prime p ≥ 5,
(2p−1 choose p−1) ≡ 1 (mod p³). The converse is conjectured: if (2n−1 choose n−1) ≡ 1 (mod n³)
(the source's condition (1) with k = 3), then n is prime. No composite n is known to satisfy it.

Reading decision: the congruence is trivially satisfied at n = 0 and n = 1 (modulus 0 and 1),
which are not prime, so the conjecture is stated for n ≥ 2, the range in which the source
discusses it (its k = 1, 2 analysis quantifies over prime powers and composites n ≥ 4).
-/

namespace OMA.S_wp_does_the_converse_of_wolstenholme_s_theorem_hold_for_all_natural_numbers

/--
The converse of Wolstenholme's theorem as conjectured on the source page:
if (2n−1 choose n−1) ≡ 1 (mod n³) for an integer n ≥ 2, then n is prime.
-/
theorem main :
    ∀ n : ℕ, 2 ≤ n → Nat.choose (2 * n - 1) (n - 1) ≡ 1 [MOD n ^ 3] → n.Prime := by
  sorry

end OMA.S_wp_does_the_converse_of_wolstenholme_s_theorem_hold_for_all_natural_numbers

