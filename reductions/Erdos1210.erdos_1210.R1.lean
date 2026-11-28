import FormalConjectures.ErdosProblems.«1210»
import Mathlib

-- Reduction Erdos1210.erdos_1210.R1 of Erdős Problem 1210
-- Credit: @MBimrose
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target (erdosproblems.com/1210): for `A ⊆ [1, n)` with `a` coprime to `b` for all distinct
-- `a, b ∈ A`, one has `∑_{a ∈ A} 1/(n - a) ≤ ∑_{p < n} 1/p + O(1)`, i.e. a bound that is uniform
-- in `n` and in `A`.  The constant `C` is quantified in the statement itself, so the split below
-- has to exhibit one constant for the whole elementary range and keep a single existential
-- constant for the rest.
--
-- The split separates the trivial range of `n` from the core, so that nothing easy is left inside
-- the hard hypothesis:
--   * `H1` — `n ≤ 2`: this is a *finite* check.  `A ⊆ [1, n)` then forces `A ⊆ {1}`, hence `A = ∅`
--     (left side `0`) or `n = 2` and `A = {1}` (left side `1/(2 - 1) = 1`), while `∑_{p < n} 1/p`
--     is `0` for `n ≤ 2`.  So `H1` holds with the explicit constant `1`: it is elementary, decided
--     by the two cases `A = ∅` and `A = {1}`.
--   * `H2` — `3 ≤ n`, the open core: here the additive constant has to be uniform over all `n` and
--     all pairwise coprime `A ⊆ [1, n)`, which is the actual content of Erdős's question.
--
-- `main` glues the two: the constant for the whole range is `max C 1`, one existential constant
-- from `H2` for its range and the displayed `1` for the elementary range.

namespace OMA.R_Erdos1210_erdos_1210_R1

open Finset

/-- `n ≤ 2`: `A ⊆ [1, n)` is contained in `{1}`, so the left side is at most `1`; elementary. -/
def H1 : Prop :=
  ∀ n : ℕ, n ≤ 2 → ∀ A : Finset ℕ,
    (∀ a ∈ A, 1 ≤ a ∧ a < n) →
    (∀ a ∈ A, ∀ b ∈ A, a ≠ b → a.Coprime b) →
    ∑ a ∈ A, (1 / ((n : ℝ) - a)) ≤ (∑ p ∈ (range n).filter Prime, (1 / (p : ℝ))) + 1

/-- The open core: `3 ≤ n`, with an additive constant that is uniform in `n` and in `A`. -/
def H2 : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n → ∀ A : Finset ℕ,
    (∀ a ∈ A, 1 ≤ a ∧ a < n) →
    (∀ a ∈ A, ∀ b ∈ A, a ≠ b → a.Coprime b) →
    ∑ a ∈ A, (1 / ((n : ℝ) - a)) ≤ (∑ p ∈ (range n).filter Prime, (1 / (p : ℝ))) + C

theorem main : H1 → H2 → type_of% @Erdos1210.erdos_1210 := by
  intro h1 h2
  obtain ⟨C, hC⟩ := h2
  refine ⟨max C 1, ?_⟩
  intro n A hA hcop
  rcases lt_or_ge n 3 with h | h
  · have := h1 n (by omega) A hA hcop
    linarith [le_max_right C 1]
  · have := hC n h A hA hcop
    linarith [le_max_left C 1]

end OMA.R_Erdos1210_erdos_1210_R1
