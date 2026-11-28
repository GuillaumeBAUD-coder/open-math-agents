import Mathlib

/-!
# A083005: a(1)=1, a(n)=2a(n-1)+1 if a(n-1) is prime, a(n)=a(n-1)+1 otherwise.

Source: https://oeis.org/A083005
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture : limit n ->oo log(a(n))/sqrt(n)=c= 1.3....
-/

namespace OMA.S_oeis_a083005

def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    let prev := a (n + 1)
    if Nat.Prime prev then 2 * prev + 1 else prev + 1

theorem main :
    ∃ c : ℝ, 0 < c ∧
      Filter.Tendsto
        (fun n : ℕ => Real.log (a n : ℝ) / Real.sqrt (n : ℝ))
        Filter.atTop (nhds c) := by
  sorry

end OMA.S_oeis_a083005
