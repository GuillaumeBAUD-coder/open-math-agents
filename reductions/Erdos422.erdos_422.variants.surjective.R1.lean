import FormalConjectures.ErdosProblems.«422»

-- Reduction Erdos422.erdos_422.variants.surjective.R1 of Erdős Problem 422 — surjective
-- Credit: @MBimrose
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target (erdosproblems.com/422, OEIS A005185): Hofstadter's `Q`-sequence
-- `f(1) = f(2) = 1`, `f n = f (n - f (n - 1)) + f (n - f (n - 2))` for `n > 2`, is it surjective?
-- Whether such an `f` exists at all is a separate open question (`erdos_422.variants.well_defined`),
-- so the reduction quantifies over every `f` satisfying `IsHofstadterQ`, as the target does.
--
-- The split is on the value `y` whose preimage is asked for:
--   * `H1` — the case `y = 1`: it is solved *by the definition* of `IsHofstadterQ`, which contains
--     `f 1 = 1` as its first conjunct.  This is the elementary region (one projection, no induction).
--   * `H2` — the case `y ≠ 1`, i.e. `y ≥ 2`: every larger value must be hit.  Since `f 1 = f 2 = 1`
--     and the recurrence only ever adds positive values, `f` starts at `1` and the whole content of
--     surjectivity is that it comes back to every `y ≥ 2`; this is the open core.
--
-- Why this is honest: `y = 1 ∨ y ≠ 1` partitions the values `y : ℕ+` and each H states the target's
-- conclusion `∃ x, f x = y` on its half, so `main` is exactly `by_cases` and no case is lost.  The
-- region `H1` is closed by `hf.1`, so after this reduction only `H2` has to be attacked.

namespace OMA.R_Erdos422_erdos_422_variants_surjective_R1

open Erdos422

/-- The elementary case: `f 1 = 1` is the first conjunct of `IsHofstadterQ`, so `y = 1` is hit. -/
def H1 : Prop :=
  ∀ f : ℕ+ → ℕ+, IsHofstadterQ f → f 1 = 1

/-- The open core: every value `y ≠ 1` (equivalently `y ≥ 2`) is attained by `f`. -/
def H2 : Prop :=
  ∀ f : ℕ+ → ℕ+, IsHofstadterQ f → ∀ y : ℕ+, y ≠ 1 → ∃ x : ℕ+, f x = y

theorem main : H1 → H2 → type_of% @Erdos422.erdos_422.variants.surjective := by
  intro h1 h2 f hf y
  by_cases hy : y = 1
  · subst hy
    exact ⟨1, h1 f hf⟩
  · exact h2 f hf y hy

end OMA.R_Erdos422_erdos_422_variants_surjective_R1
