import Mathlib

/-!
# A010915: the Pisot sequence E(6,16) satisfies no linear recurrence

Source: https://oeis.org/A010915 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A010915 (offset 0): Pisot sequence E(6,16), a(n) = floor( a(n-1)^2/a(n-2) + 1/2 );
data 6, 16, 43, 116, 313, 845, 2281, 6157, 16619, ...

The entry records:

  Conjectured not to satisfy a linear recurrence.

Reading of the source:
* a(0) = 6, a(1) = 16, and for n ≥ 0, a(n+2) = floor(a(n+1)^2 / a(n) + 1/2). All terms are
  positive, and floor(x^2/y + 1/2) = floor((2x^2 + y) / (2y)), so the recurrence is computed
  exactly with natural division.
* "satisfies a linear recurrence": a homogeneous linear recurrence with constant coefficients,
  `a(n+d) = c_0 a(n) + ... + c_(d-1) a(n+d-1)` for some order `d ≥ 1` and rational `c_i`. For an
  integer sequence, rational coefficients are no restriction (a sequence of rationals satisfying
  a recurrence over ℂ satisfies one over ℚ). The recurrence is allowed to hold only from some
  index `N` on, so the conjecture is stated in its strong form: no linear recurrence holds even
  eventually.
-/

namespace OMA.S_oeis_a010915

/-- A010915: a(0) = 6, a(1) = 16, a(n+2) = floor(a(n+1)^2 / a(n) + 1/2). -/
def a : ℕ → ℕ
  | 0 => 6
  | 1 => 16
  | n + 2 => (2 * a (n + 1) ^ 2 + a n) / (2 * a n)

/-- No linear recurrence with constant rational coefficients holds, even from some index on. -/
theorem main :
    ¬ ∃ (d : ℕ) (c : Fin d → ℚ) (N : ℕ), 1 ≤ d ∧
      ∀ n, N ≤ n → (a (n + d) : ℚ) = ∑ i : Fin d, c i * a (n + i) := by
  sorry

end OMA.S_oeis_a010915
