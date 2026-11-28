import Mathlib

/-!
# OEIS A275391: a(n) <= n-2 for n > 15, with equality infinitely often

Source: https://oeis.org/A275391
Credit: @LordMike

A275391: "Least k such that n divides sigma(k^k) (k > 0)." (offset 1)
Comment (Robert Israel): "Conjecture: a(n) <= n-2 for all n > 15, but a(n) = n-2 for infinitely many n."

Reading used here: a(n) = sInf {k | 0 < k ∧ n ∣ σ₁(k^k)}; the set is nonempty for n ≥ 1 (Israel's comment),
so sInf is not a junk value. The conjecture is the conjunction of both claims; n - 2 is genuine since n > 15.
-/

namespace OMA.S_oeis_a275391

/-- A275391: least `k > 0` such that `n ∣ σ(k^k)`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | 0 < k ∧ n ∣ ArithmeticFunction.sigma 1 (k ^ k)}

theorem main : (∀ n, 15 < n → a n ≤ n - 2) ∧ {n : ℕ | 15 < n ∧ a n = n - 2}.Infinite := by
  sorry

end OMA.S_oeis_a275391
