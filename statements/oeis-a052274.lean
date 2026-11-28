import Mathlib.Data.ZMod.Basic
import Mathlib.SetTheory.Cardinal.Finite

namespace OMA.S_oeis_a052274

/-- OEIS A052274: the number of distinct 5th powers modulo `n`. -/
noncomputable def a052274 (n : ℕ) : ℕ :=
  Nat.card (Set.range (fun x : ZMod n => x ^ 5))

/-- OEIS A052274 conjectures: formulas for `a(p^e)` at prime powers `p^e`:
1. `a(5^e) = 1 + ((5 - 1) * 5^(e + 3)) / (5^5 - 1)` when `e % 5 ≠ 1`,
   and `a(5^e) = 5 + ((5 - 1) * 5^(e + 3)) / (5^5 - 1)` when `e % 5 = 1`;
2. `a(p^e) = 1 + ((p - 1) * p^(e + 4)) / (Nat.gcd (p - 1) 5 * (p^5 - 1))`
   for every prime `p ≠ 5`. -/
theorem main :
    (∀ e : ℕ, e % 5 ≠ 1 → a052274 (5 ^ e) = 1 + (4 * 5 ^ (e + 3)) / (5 ^ 5 - 1)) ∧
    (∀ e : ℕ, e % 5 = 1 → a052274 (5 ^ e) = 5 + (4 * 5 ^ (e + 3)) / (5 ^ 5 - 1)) ∧
    (∀ p e : ℕ, p.Prime → p ≠ 5 →
      a052274 (p ^ e) = 1 + ((p - 1) * p ^ (e + 4)) / (Nat.gcd (p - 1) 5 * (p ^ 5 - 1))) := by
  sorry

end OMA.S_oeis_a052274
