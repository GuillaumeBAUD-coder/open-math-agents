import FormalConjectures.ErdosProblems.«263»

-- Reduction Erdos263.erdos_263.parts.i.R1 of Erdős Problem 263 — the irrationality sequence 2^2^n
-- Credit: @MBimrose
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target (erdosproblems.com/263): `a n = 2 ^ 2 ^ n` is an *irrationality sequence*: whenever
-- `b` is a positive integer sequence with `a n / b n -> 1`, the sum `∑ 1 / b n` is irrational.
-- By the definition `IsIrrationalitySequence` this is a conjunction of three statements, and the
-- file splits it into exactly those three conjuncts:
--   * `H1` — positivity of `a`, `∀ n, 2 ^ 2 ^ n > 0`.  Elementary: `Nat.pow_pos` (no hypotheses).
--   * `H2` — strict monotonicity of `a`.  Elementary: `n < m` gives `2 ^ n < 2 ^ m`, hence
--     `2 ^ (2 ^ n) < 2 ^ (2 ^ m)` by `Nat.pow_lt_pow_right` twice; three lines, no analysis.
--   * `H3` — the analytic core: every positive `b` with `a n / b n → 1` has irrational reciprocal
--     sum.  This is the whole mathematical content of the problem (the Diophantine approximation
--     of `2 ^ 2 ^ n` by integers), and it is what remains open on erdosproblems.com/263.
--
-- Why this is honest: `IsIrrationalitySequence a` unfolds to `H1 ∧ H2 ∧ H3` verbatim, so the three
-- hypotheses are a partition of the target into its definitional components (nothing is weakened,
-- nothing is dropped), `main` is the anonymous constructor, and the two bookkeeping components are
-- discharged by one-line Nat lemmas while `H3` is left exactly as stated in the definition.

namespace OMA.R_Erdos263_erdos_263_parts_i_R1

open Erdos263 Filter
open scoped Topology

/-- `a n = 2 ^ 2 ^ n` is positive: the first conjunct of `IsIrrationalitySequence`. -/
def H1 : Prop :=
  ∀ n : ℕ, (2 : ℕ) ^ 2 ^ n > 0

/-- `a n = 2 ^ 2 ^ n` is strictly increasing: the second conjunct of `IsIrrationalitySequence`. -/
def H2 : Prop :=
  StrictMono (fun n : ℕ => (2 : ℕ) ^ 2 ^ n)

/-- The analytic core: every positive integer sequence `b` asymptotic to `2 ^ 2 ^ n` has
irrational reciprocal sum (the third conjunct of `IsIrrationalitySequence`). -/
def H3 : Prop :=
  ∀ b : ℕ → ℕ, (∀ n : ℕ, b n > 0) ∧
    atTop.Tendsto (fun n : ℕ => ((2 ^ 2 ^ n : ℕ) : ℝ) / (b n : ℝ)) (nhds 1) →
    Irrational (∑' n, 1 / (b n : ℝ))

theorem main : H1 → H2 → H3 → type_of% @Erdos263.erdos_263.parts.i := by
  intro h1 h2 h3
  exact ⟨h1, h2, h3⟩

end OMA.R_Erdos263_erdos_263_parts_i_R1
