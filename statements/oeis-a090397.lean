import Mathlib

/-!
# A090397: Number of terms in simple continued fraction for (3/2)^n

Source: https://oeis.org/A090397
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Number of terms in the simple continued fraction for (3/2)^n.
Conjecture: a(n) is asymptotic to c * n where c = 12 * (log(2) / Pi)^2.
-/

namespace OMA.S_oeis_a090397

/-- Number of steps in the Euclidean algorithm for p / q (length of simple
continued fraction), bounded by fuel. -/
def cfLenAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, p, q =>
    if q = 0 then 0
    else if p % q = 0 then 1
    else 1 + cfLenAux fuel q (p % q)

/-- Number of terms in the simple continued fraction of (3/2)^n = 3^n / 2^n. -/
def a (n : ℕ) : ℕ :=
  cfLenAux (2 ^ n + 1) (3 ^ n) (2 ^ n)

theorem main :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ)) Filter.atTop
      (nhds (12 * (Real.log 2 / Real.pi) ^ 2)) := by
  sorry

end OMA.S_oeis_a090397
