import Mathlib

/-!
# Is `2` always a `p`-th power nonresidue modulo `2^p - 1`?

Source: https://mathoverflow.net/questions/111422 (2012).
Credit: @jagraj28

The post asks whether, for every prime `p` and every integer `x`, `x ^ p ≢ 2 (mod 2 ^ p - 1)`.
A comment proves it when some prime `q ∣ 2 ^ p - 1` has `q ≢ 1 (mod p ^ 2)` (in particular
when `p` is not a Wieferich prime), and leaves the general case open. The post has no answer.

Formalization notes:
* The congruence is stated in `ZMod (2 ^ p - 1)`: every integer `x` reduces to an element of it,
  and `x ^ p ≡ 2` holds there exactly when it holds for the integer.
* `main` states the affirmative answer. A brute-force search confirms it for every prime
  `p < 24`.
-/

namespace OMA.S_mo_111422

/-- For every prime `p`, `2` is not a `p`-th power modulo `2 ^ p - 1`. -/
theorem main : ∀ p : ℕ, p.Prime → ∀ x : ZMod (2 ^ p - 1), x ^ p ≠ 2 := by
  sorry

end OMA.S_mo_111422
