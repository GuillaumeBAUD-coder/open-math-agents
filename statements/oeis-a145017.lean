import Mathlib

/-!
# A145017: squarefree k with k - floor(sqrt k)^2 a perfect square (Shevelev's conjecture)

Source: https://oeis.org/A145017
Credit: @LordMike

Sequence: "Squarefree positive integers k for which k-(floor(sqrt(k)))^2 is a perfect square."

Conjecture. For every n>=1 there exist infinitely many primes p of the form 4k+1 for which for a(n) > 1 we have
s*p-(floor(sqrt(s*p)))^2 is not a perfect square for s=1,...,a(n)-1 while a(n)*p-(floor(sqrt(a(n)*p)))^2 is a
perfect square.

Reading used here: a(n) is the n-th term (offset 1, terms 1, 2, 5, 10, 13, ...), via `Nat.nth` (0-indexed, so
`n - 1`). "For a(n) > 1" only qualifies the clause s=1..a(n)-1, which is empty (Finset.Ico 1 1) when a(n) = 1;
the case n = 1 (A145016) is kept. floor(sqrt m) is `Nat.sqrt m`; `m - Nat.sqrt m ^ 2` is
never truncated since `Nat.sqrt m ^ 2 ≤ m`.
-/

namespace OMA.S_oeis_a145017

/-- `m - floor(sqrt m)^2`. -/
def r (m : ℕ) : ℕ := m - Nat.sqrt m ^ 2

/-- `a n` is the n-th term (offset 1) of A145017. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun k => Squarefree k ∧ IsSquare (r k)) (n - 1)

theorem main : ∀ n ≥ 1, {p : ℕ | p.Prime ∧ p % 4 = 1 ∧
    (∀ s ∈ Finset.Ico 1 (a n), ¬ IsSquare (r (s * p))) ∧ IsSquare (r (a n * p))}.Infinite := by
  sorry

end OMA.S_oeis_a145017
