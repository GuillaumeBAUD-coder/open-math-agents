import FormalConjectures.ErdosProblems.«963»
import Mathlib

-- Reduction Erdos963.erdos_963.variants.positive.R1 of Erdős Problem 963 — positive
-- Credit: @MBimrose
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target (erdosproblems.com/963, second part, with `Nat.log 2 A.card` for Erdős's
-- `⌊log_2 |A|⌋`): every finite set `A` of positive reals has a dissociated subset `B ⊆ A` of size
-- at least `Nat.log 2 A.card`.  Equivalently `f n ≥ Nat.log 2 n` for the function `f` of the
-- module, whose only known input upstream is `f n ≥ 2` for `n` large (`parts.ii`).
--
-- The split separates off the trivial cardinality range, so that what is left is the whole
-- difficulty and nothing else:
--   * `H1` — `A.card ≤ 1`: then `B := A` works.  A set with at most one element is dissociated
--     because the only two subset sums are `0` and the single element, which is nonzero by
--     `0 < a`; and `Nat.log 2 0 = Nat.log 2 1 = 0 ≤ A.card`.  So `H1` is elementary — no
--     arithmetic, just the definition of `AddDissociated` on a subsingleton and `Nat.log`.
--   * `H2` — `2 ≤ A.card`: the open core.  Already the smallest case in which the bound
--     `Nat.log 2 A.card ≥ 1` is not free, and the case `|A| = 32` (where `Nat.log 2 32 = 5`) is
--     the first one not settled by the signed-sum count that gives `f n ≥ 4` unconditionally.

namespace OMA.R_Erdos963_erdos_963_variants_positive_R1

/-- `A` has at most one element: taking `B = A` is dissociated and `Nat.log 2 A.card ≤ A.card`
holds trivially. -/
def H1 : Prop :=
  ∀ A : Finset ℝ, (∀ a ∈ A, 0 < a) → A.card ≤ 1 →
    ∃ B ⊆ A, Nat.log 2 A.card ≤ B.card ∧ AddDissociated (B : Set ℝ)

/-- The open core: `A` has at least two positive elements, so the dissociated subset has to be
extracted by a genuine argument. -/
def H2 : Prop :=
  ∀ A : Finset ℝ, (∀ a ∈ A, 0 < a) → 2 ≤ A.card →
    ∃ B ⊆ A, Nat.log 2 A.card ≤ B.card ∧ AddDissociated (B : Set ℝ)

theorem main : H1 → H2 → type_of% @Erdos963.erdos_963.variants.positive := by
  intro h1 h2 A hA
  rcases le_or_gt A.card 1 with h | h
  · exact h1 A hA h
  · exact h2 A hA (by omega)

end OMA.R_Erdos963_erdos_963_variants_positive_R1
