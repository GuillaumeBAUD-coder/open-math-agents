import Mathlib

/-!
# A067126: Numbers for which phi(n) >= phi(k) for all k = 1 to n-1.

Source: https://oeis.org/A067126
Credit: @eitanteperman

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a067126

/-- A067126: `n` is a term iff `n >= 1` and `φ(n) ≥ φ(k)` for all `k` with `1 ≤ k < n`
(`Nat.totient`; the extra value `k = 0` has `φ 0 = 0` and is harmless). -/
def IsTerm (n : ℕ) : Prop := 1 ≤ n ∧ ∀ k : ℕ, k < n → Nat.totient k ≤ Nat.totient n

/-- Conjecture (A067126): 4 and 9 are the only composite terms, i.e. a composite number `n`
(`1 < n` and not prime) is a term if and only if `n = 4` or `n = 9`. Checked below 3 * 10^5, and
OEIS notes no further composite term below 1.5e18. -/
theorem main : ∀ n : ℕ, (1 < n ∧ ¬ n.Prime ∧ IsTerm n) ↔ (n = 4 ∨ n = 9) := by
  sorry

end OMA.S_oeis_a067126
