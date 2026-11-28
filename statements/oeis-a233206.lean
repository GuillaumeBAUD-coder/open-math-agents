import Mathlib

/-!
# A233206: Number of ways to write n = k + m (0 < k <= m) with k! + prime(m) prime.

Source: https://oeis.org/A233206
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry; verified for n up to 10^7): a(n) > 0 for all n > 3.

Formalization notes:
* prime(m) = `Nat.nth Nat.Prime (m - 1)` (prime(1) = 2); m = n - k and k ≤ m is 2k ≤ n.
* Controls (computed): a(n) > 0 for 3 < n < 600.
-/

namespace OMA.S_oeis_a233206

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A233206(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 (n / 2)).filter fun k => (k.factorial + prime (n - k)).Prime).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    ∀ n : ℕ, 3 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a233206
