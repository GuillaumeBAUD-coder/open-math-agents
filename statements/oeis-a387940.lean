import Mathlib

/-!
# A387940: a(n) is the smallest squarefree semiprime k such that n^2 + k is a perfect square.

Source: https://oeis.org/A387940
Credit: @cjchaffin

Conjecture (stated on the OEIS page): `a(n)` always exists.

Conventions:
- The sequence has offset 1, so `n` runs over the positive integers (as in the b-file and the
  programs, which all start at `n = 1`).
- A squarefree semiprime is a product of two distinct primes: Mathlib's `Squarefree` together
  with `Nat.IsSemiprime` (exactly two prime factors counted with multiplicity). This is the
  same as OEIS A006881, cited on the page.
- "Always exists" is the statement that for every such `n` there is at least one squarefree
  semiprime `k` with `n^2 + k` a square. (The sequence then takes the smallest such `k`;
  the conjecture is only existence.)
-/

namespace OMA.S_oeis_a387940

theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ k : ℕ, Squarefree k ∧ k.IsSemiprime ∧ IsSquare (n ^ 2 + k) := by
  sorry

end OMA.S_oeis_a387940
