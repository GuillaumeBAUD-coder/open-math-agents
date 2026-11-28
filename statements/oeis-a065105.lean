import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Nth

namespace OMA.S_oeis_a065105

/-- `IsFibProd m` holds if `m` is expressible as a (possibly empty) finite product of
Fibonacci numbers `Nat.fib k`. -/
inductive IsFibProd : ℕ → Prop
  | one : IsFibProd 1
  | mul {a k : ℕ} : IsFibProd a → IsFibProd (a * Nat.fib k)

/-- `a(n)` (OEIS A065105, 1-indexed): the `n`-th positive integer not expressible as a product
of Fibonacci numbers (`a(1) = 7, a(2) = 11, ...`). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth (fun m : ℕ => 0 < m ∧ ¬ IsFibProd m) (n - 1)

/-- Conjecture (OEIS A065105): `a(n + 1) - a(n) ≤ 5` for all `n ≥ 1`, and
`a(n + 1) - a(n) ≤ 3` for all `n ≥ 8`. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → a (n + 1) - a n ≤ 5) ∧
    (∀ n : ℕ, 8 ≤ n → a (n + 1) - a n ≤ 3) := by
  sorry

end OMA.S_oeis_a065105
