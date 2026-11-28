import Mathlib

/-!
# A234361: a(n) = |{0 < k < n: 2^{phi(k)/2}*3^{phi(n-k)/4} + 1 is prime}|, where phi(.) is Euler's totient function.

Source: https://oeis.org/A234361
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): a(n) > 0 for all n > 7.

Formalization notes:
* phi = `Nat.totient`.
* A power such as 2^(phi(k)/2) with phi(k) odd (k = 1, 2) is not an integer, and then the expression
  cannot be prime; so each halving (or quartering) of an exponent is stated as "phi(.) is even
  (divisible by 4) and the expression with phi(.)/2 (phi(.)/4) is prime".
* Controls (computed): a(1..25) = 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 6, 3, 6, 6, 5, 7,
  4, 6, as in the entry; a(n) > 0 for 7 < n < 150.
-/

namespace OMA.S_oeis_a234361

/-- A234361(n). -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ioo 0 n).filter fun k => Even (Nat.totient k) ∧ 4 ∣ Nat.totient (n - k) ∧
    (2 ^ (Nat.totient k / 2) * 3 ^ (Nat.totient (n - k) / 4) + 1).Prime).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    ∀ n : ℕ, 7 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a234361
