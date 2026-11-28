import Mathlib

/-!
# Two conjectures regarding `φ(n)`

Source: https://math.stackexchange.com/questions/1065941 (2014, edited version of the question).
Credit: @jagraj28

The post states two conjectures related to Lehmer's totient problem (`φ(n) ∣ n - 1` implies `n`
prime):
1. if `n` is odd and `φ(n) + 1 ∣ n`, then `n` is prime;
2. for odd `n`, `φ(n) + 1 ∣ n` if and only if `φ(n) ∣ n - 1`.
The one answer gives a counterexample (`n = 2p`) to the first version of the question; the
question was then restricted to odd `n`, and the post has no answer to the edited conjectures.

Formalization notes:
* `φ` is `Nat.totient`; `n - 1` is the true difference for `n ≥ 1`.
* Conjecture 2 is stated for odd `n > 1`. For `n = 1` it fails trivially (`φ(1) = 1` divides
  `0`, while `φ(1) + 1 = 2` does not divide `1`); the post is about Lehmer's problem, where
  `n > 1`. Conjecture 1 holds trivially at `n = 1` and is stated for all odd `n`.
* `main` is the conjunction of the two conjectures.
* A direct search confirms both for every odd `n` with `1 < n ≤ 10 ^ 7`.
-/

namespace OMA.S_mse_1065941

/-- The two conjectures of the post. -/
theorem main :
    (∀ n : ℕ, Odd n → Nat.totient n + 1 ∣ n → n.Prime) ∧
    (∀ n : ℕ, Odd n → 1 < n → (Nat.totient n + 1 ∣ n ↔ Nat.totient n ∣ n - 1)) := by
  sorry

end OMA.S_mse_1065941
