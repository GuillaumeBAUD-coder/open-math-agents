import FormalConjectures.ErdosProblems.«967»
import Mathlib

-- Reduction Erdos967.erdos_967.variants.finite.R1 of Erdős Problem 967 — finite
-- Credit: @MBimrose
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target (Erdős–Ingham; erdosproblems.com/967): for `t = σ + it` on the line `σ = 1`, the
-- "truncated zeta" `1 + ∑_{n ∈ A} n^{-1-it}` never vanishes, for EVERY finite set `A ⊆ ℕ` of
-- integers `> 1`.  Yip [Yi25] refuted the infinite-sequence form, but the finite form is open and
-- Erdős–Ingham already singled out `A = {2, 3, 5}` as the smallest case they could not decide.
--
-- The two elementary cases are separated off here, so that each remaining H is a genuine core:
--   * `H1` — `A` has at most one element: `|n^{-1-it}| = n^{-1} ≤ 1/2`, so `|∑| ≤ 1/2 < 1` and
--     `1 + ∑ ≠ 0` for every `t`;
--   * `H2` — `t = 0`: every summand is the positive real `1/n`, so `1 + ∑ ≥ 1 > 0`;
--   * `H3` — the open core: at least two distinct integers and `t ≠ 0` (this is where `{2,3,5}`,
--     and every other non-trivial case, lives).

namespace OMA.R_Erdos967_erdos_967_variants_finite_R1

open Erdos967

/-- `A` has at most one element: the truncated sum has modulus `< 1`, so `1 + ∑ ≠ 0`. -/
def H1 : Prop :=
  ∀ A : Finset ℕ, (∀ n ∈ A, 1 < n) → A.card ≤ 1 → ∀ t : ℝ, 1 + (∑ n ∈ A, summand t n) ≠ 0

/-- The real line `t = 0`: every summand is the positive real `1 / n`, so `1 + ∑ > 0`. -/
def H2 : Prop :=
  ∀ A : Finset ℕ, (∀ n ∈ A, 1 < n) → 1 + (∑ n ∈ A, summand 0 n) ≠ 0

/-- The open core: at least two integers `> 1` in `A`, and `t ≠ 0`. -/
def H3 : Prop :=
  ∀ A : Finset ℕ, (∀ n ∈ A, 1 < n) → 2 ≤ A.card → ∀ t : ℝ, t ≠ 0 →
    1 + (∑ n ∈ A, summand t n) ≠ 0

theorem main : H1 → H2 → H3 → type_of% @Erdos967.erdos_967.variants.finite := by
  intro h1 h2 h3 A hA t
  rcases le_or_gt A.card 1 with h | h
  · exact h1 A hA h t
  · rcases eq_or_ne t 0 with ht0 | ht0
    · subst ht0
      exact h2 A hA
    · exact h3 A hA (by omega) t ht0

end OMA.R_Erdos967_erdos_967_variants_finite_R1
