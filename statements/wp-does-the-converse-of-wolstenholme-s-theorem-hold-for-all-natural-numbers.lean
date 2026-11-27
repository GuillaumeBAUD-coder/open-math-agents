import Mathlib

/-!
# Does the converse of Wolstenholme's theorem hold for all natural numbers?

Source: https://en.wikipedia.org/wiki/Wolstenholme%27s_theorem
Credit: @John-A-McMahon

Source statement (Wikipedia, *Wolstenholme's theorem*, section on the converse): Wolstenholme's
theorem says that `binom(2p - 1, p - 1) ≡ 1 (mod p ^ 3)` for every prime `p ≥ 5`. It is
conjectured that the converse holds: if `binom(2n - 1, n - 1) ≡ 1 (mod n ^ 3)` then `n` is
prime. Stated here in that positive form for every natural number `n ≥ 2`; `n = 1` is excluded
since `binom(1, 0) = 1` satisfies the congruence trivially and 1 is not prime, so it cannot be
meant. (The weaker versions with `n` or `n ^ 2` in place of `n ^ 3` are not part of this
statement.)
-/

namespace OMA.S_wp_does_the_converse_of_wolstenholme_s_theorem_hold_for_all_natural_numbers

theorem main : ∀ n : ℕ, 2 ≤ n → (2 * n - 1).choose (n - 1) ≡ 1 [MOD n ^ 3] → n.Prime := by
  sorry

end OMA.S_wp_does_the_converse_of_wolstenholme_s_theorem_hold_for_all_natural_numbers
