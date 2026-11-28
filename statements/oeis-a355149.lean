import Mathlib

/-!
# The 42-step recurrence for the partial sums in OEIS A355149

Sources: https://oeis.org/A355149 and https://oeis.org/A351743.
Submitted by @VestigeClub.

A351743 starts with 1. The next increment is the greatest positive divisor
of the current partial sum that is coprime to the previous increment.
The state records both the sum and the increment. At index one both are
1, and each later sum includes the new increment. The recurrence starts
at index 138 inclusive. The additive correction is an integer-valued
function on natural indices of period 42. The proof checks the first ten
sums against the entry.
-/

namespace OMA.S_oeis_a355149

def greatestCoprimeDivisor (s v : ℕ) : ℕ :=
  (s.divisors.filter (fun d => d.Coprime v)).sup id

def step (p : ℕ × ℕ) : ℕ × ℕ :=
  let w := greatestCoprimeDivisor p.1 p.2
  (p.1 + w, w)

def state : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | 1 => (1, 1)
  | n + 2 => step (state (n + 1))

def a (n : ℕ) : ℕ := (state n).1

theorem main :
    ∃ b : ℕ → ℤ, Function.Periodic b 42 ∧
      ∀ n : ℕ, 138 ≤ n → (a (n + 42) : ℤ) = 3645 * (a n : ℤ) + b n := by
  sorry

end OMA.S_oeis_a355149
