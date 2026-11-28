import Mathlib

/-!
# A088226: a(1)=0, a(2)=0, a(3)=1; for n>3, a(n) = abs(a(n-1) - a(n-2) - a(n-3)).

Source: https://oeis.org/A088226
Credit: @thatoneguy006

The conjecture recorded in the entry:

  Conjecture: a(n) = m/2 where m is the smallest even distance from n to a square.
  - Ralf Stephan, Sep 23 2013

Indexing. The entry has offset 1 (a(1) = 0, a(2) = 0, a(3) = 1, ...). Read literally with that
offset the conjecture fails at once: a(2) = 0, while the even distances from 2 to the squares
0, 1, 4, ... are 2, 2, ..., so m/2 = 1. The PARI program the same author gives with the
conjecture, a(n)=t=sqrtint(n);if((n-t*t)%2==0,(n-t*t)/2,((t+1)^2-n)/2), takes the value a(n+1)
at n (for example 0, 1, 1, 0, 2 at n = 1, ..., 5, which are a(2), ..., a(6)); it computes m/2
for the argument n - 1. The formulas of the entry, a(k^2 + 2*m + 1) = m and
a(k^2 + 2*m + 2) = k - m, say the same. So the conjecture is read with that shift:
a(n) = m(n - 1)/2 for n >= 1, where m(x) is the smallest even number of the form |x - s^2|.
This reading agrees with the recurrence for all n <= 5000.

Definitions.
* `a` is the recurrence of the name, in ℤ, with `a 1 = a 2 = 0`, `a 3 = 1`; `a 0` is not a term
  of the sequence and is set to 0.
* `m x` is the least `d` that is even and equal to `Nat.dist x (s^2)` for some `s`; such `d`
  exist (take `s = x`, as `x^2 - x` is even).
-/

namespace OMA.S_oeis_a088226

/-- A088226, offset 1 (the value at 0 is not a term). -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 1
  | (n + 4) => |a (n + 3) - a (n + 2) - a (n + 1)|

/-- The smallest even distance from `x` to a square. -/
noncomputable def m (x : ℕ) : ℕ := sInf {d : ℕ | Even d ∧ ∃ s : ℕ, d = Nat.dist x (s ^ 2)}

/-- Stephan's conjecture, with the index shift of his PARI program. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = ((m (n - 1) / 2 : ℕ) : ℤ) := by
  sorry

end OMA.S_oeis_a088226
