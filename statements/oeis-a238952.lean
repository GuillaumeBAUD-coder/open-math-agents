import Mathlib

/-!
# OEIS A238952: Hurt's divisor-sum formula for the arcs of the transitive closure of D(n)

Source: https://oeis.org/A238952 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Sung-Hyuk Cha, Mar 07 2014), offset 1: The size (the number of arcs) in the transitive
closure of divisor lattice D(n). The formula section states: Conjecture: a(n) = Sum_{i=1..floor(n/2)}
d(i) * (floor(n/i) - floor((n-1)/i)), where d(n) is the number of divisors of n. - Wesley Ivan
Hurt, Dec 21 2017

Formalization notes:
* The divisor lattice D(n) is the set of divisors of n ordered by divisibility; the arcs of its
  transitive closure are the pairs (d, e) of divisors of n with d dividing e and d /= e (no
  loops: a(1) = 0).
* d(i) is the number of divisors of i. Since floor(n/i) >= floor((n-1)/i), the difference is
  computed in N without truncation.
* Controls: the definition gives a(1..12) = 0, 1, 1, 3, 1, 5, 1, 6, 3, 5, 1, 12, as in the entry.
-/

namespace OMA.S_oeis_a238952

/-- A238952(n): the arcs `(d, e)`, `d ∣ e`, `d ≠ e`, among the divisors of `n`. -/
def a (n : ℕ) : ℕ :=
  ((n.divisors ×ˢ n.divisors).filter (fun p : ℕ × ℕ => p.1 ∣ p.2 ∧ p.1 ≠ p.2)).card

/-- Hurt's conjecture: a(n) = Sum_{i=1..floor(n/2)} d(i)(floor(n/i) - floor((n-1)/i)). -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    a n = ∑ i ∈ Finset.Icc 1 (n / 2), i.divisors.card * (n / i - (n - 1) / i) := by
  sorry

end OMA.S_oeis_a238952
