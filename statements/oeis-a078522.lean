import Mathlib

/-!
# A078522: Numbers k such that (k+1)*(2*k+1) is a perfect square.

Source: https://oeis.org/A078522
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: let f(n) be a sequence of form x(n)*y(n)/2, of the ordered Pythagorean triples
(x(n), y(n) = x(n) + v, z(n)) with x(1)=0, y(1)=v, z(1)=0, f(1)=0, where v is an even number.
Then there exists such a subset p(i) that p(1) = 0, p(2) = 24*(v/2)^2, for any i > 2,
p(i) = 34*p(i-1) - p(i-2) + 24*(v/2)^2, and any p(i) is a term of the above sequence f(n).
-/

namespace OMA.S_oeis_a078522

/-- The recurrence `p(0) = 0`, `p(1) = 24*m^2`, `p(i+2) = 34*p(i+1) - p(i) + 24*m^2` where `v = 2*m`. -/
def p (m : ℕ) : ℕ → ℤ
  | 0 => 0
  | 1 => 24 * (m : ℤ) ^ 2
  | i + 2 => 34 * p m (i + 1) - p m i + 24 * (m : ℤ) ^ 2

theorem main :
    ∀ m i : ℕ, ∃ x z : ℕ,
      x ^ 2 + (x + 2 * m) ^ 2 = z ^ 2 ∧ ((x * (x + 2 * m) : ℕ) : ℤ) = 2 * p m i := by sorry

end OMA.S_oeis_a078522
