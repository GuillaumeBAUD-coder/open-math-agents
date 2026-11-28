import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Lattice.Nat

namespace OMA.S_oeis_a094802

/-- `a(n)` (OEIS A094802): the smallest `k` such that every integer `m` with `1 ≤ m ≤ n`
divides `k!`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ m : ℕ, 1 ≤ m → m ≤ n → m ∣ k.factorial}

/-- The largest prime `≤ n` (i.e. `n` if `n` is prime, or the previous prime otherwise). -/
noncomputable def largestPrimeLe (n : ℕ) : ℕ :=
  sSup {p : ℕ | p ≤ n ∧ p.Prime}

/-- Conjecture (OEIS A094802): for every `n > 4`, `a(n)` is prime and equals the largest
prime `≤ n` (`n` if `n` is prime, or the previous prime otherwise). -/
theorem main : ∀ n : ℕ, 4 < n → (a n).Prime ∧ a n = largestPrimeLe n := by
  sorry

end OMA.S_oeis_a094802
