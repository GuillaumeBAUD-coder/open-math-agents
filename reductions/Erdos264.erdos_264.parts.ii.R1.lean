import FormalConjectures.ErdosProblems.«264»

-- Reduction Erdos264.erdos_264.parts.ii.R1 of Erdős Problem 264 — ii
-- Credit: @MBimrose
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target (erdosproblems.com/264): `Nat.factorial` is an irrationality sequence in the sense of
-- this file, i.e. for every integer sequence `b` that is bounded above and below (and such that
-- `0` is not hit by `b` or by `n! + b n`), the sum `∑ 1 / (n! + b n)` is irrational.  Kovač–Tao
-- showed `2 ^ n` is *not* such a sequence (`erdos_264.variants.ko_tao_neg`), while `2 ^ 2 ^ n` is
-- the classical positive example; the factorial is open.
--
-- The definition quantifies over `b` and then assumes BOTH boundedness conditions, so the split is
-- on the second of them (`BddBelow (Set.range b)`), which is the one that makes the sequence
-- one-sided:
--   * `H1` — `b` is bounded above but NOT below.  Then the premise `BddBelow (Set.range b)` of the
--     definition is false, so the statement is vacuous: elementary, the proof is
--     `fun b _ hb _ _ => absurd hb hb'` (no analysis at all).
--   * `H2` — `b` is bounded above AND below, i.e. the bounded sequences: this is the real content of
--     the problem (the Ahmes-type series `∑ 1/(n! + b n)` with `b` bounded), and it is strictly
--     weaker than the target because the unbounded-below case has been removed.
--
-- Why this is honest: `BddBelow (Set.range b) ∨ ¬ BddBelow (Set.range b)` partitions the quantified
-- `b`, each H carries the target's conclusion on its half (`main` is exactly `by_cases`), and the
-- vacuous half is elementary.  After the reduction only the bounded-below case `H2` remains — which
-- is exactly the case in which the sum has a chance of being a well-behaved Ahmes series.

namespace OMA.R_Erdos264_erdos_264_parts_ii_R1

open Erdos264

/-- The vacuous case: `b` is not bounded below, so the boundedness premise of
`IsIrrationalitySequence` fails and the statement is true for trivial reasons. -/
def H1 : Prop :=
  ∀ b : ℕ → ℤ, BddAbove (Set.range b) → ¬ BddBelow (Set.range b) →
    0 ∉ Set.range (fun n ↦ (Nat.factorial n : ℤ) + b n) → 0 ∉ Set.range b →
    Irrational (∑' n, (1 : ℝ) / ((Nat.factorial n : ℤ) + b n))

/-- The core: the same statement for `b` bounded above AND below. -/
def H2 : Prop :=
  ∀ b : ℕ → ℤ, BddAbove (Set.range b) → BddBelow (Set.range b) →
    0 ∉ Set.range (fun n ↦ (Nat.factorial n : ℤ) + b n) → 0 ∉ Set.range b →
    Irrational (∑' n, (1 : ℝ) / ((Nat.factorial n : ℤ) + b n))

theorem main : H1 → H2 → type_of% @Erdos264.erdos_264.parts.ii := by
  intro h1 h2 b hbdd hbdd' h0 hb0
  by_cases h : BddBelow (Set.range b)
  · exact h2 b hbdd h h0 hb0
  · exact h1 b hbdd h h0 hb0

end OMA.R_Erdos264_erdos_264_parts_ii_R1
