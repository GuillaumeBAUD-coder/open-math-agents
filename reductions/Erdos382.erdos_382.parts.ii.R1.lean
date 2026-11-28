import FormalConjectures.ErdosProblems.«382»

-- Reduction Erdos382.erdos_382.parts.ii.R1 of Erdős Problem 382 — ii
-- Credit: @MBimrose
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target (erdosproblems.com/382): for every `k` there are `u ≤ v` such that the largest prime
-- dividing `∏_{u ≤ m ≤ v} m` is repeated (`LargestPrimeRepeated u v`) and the interval is long,
-- `k ≤ v - u`.  This is the "arbitrarily long intervals in which the largest prime is repeated"
-- half of Erdős–Graham; the companion statement `erdos_382.parts.i` bounds those intervals from
-- above by `v ^ ε` on average, and the two together say the lengths are `v ^ o(1)`.
--
-- The split peels off the small values of `k`, for which an explicit witness is already available
-- in the module:
--   * `H1` — `k ≤ 2`.  The pair `(u, v) = (48, 50)` satisfies `LargestPrimeRepeated` — upstream
--     `Erdos382.largestPrimeRepeated_48_50`, a kernel-checked `decide` — and it has length
--     `50 - 48 = 2`.  So the region `k ≤ 2` is elementary: one witness, `Nat.zero_le`/`norm_num`.
--   * `H2` — `2 < k`.  The genuine content of the problem: intervals of every length `> 2`, where
--     no finite search can help.
--
-- Why this is honest: `k ≤ 2 ∨ 2 < k` partitions the quantified `k`, `main` is exactly that case
-- distinction, each H states the target's conclusion on its half, and `H1` is closed by the
-- module's own test lemma, so the remaining step `H2` is the core with the degenerate cases gone.

namespace OMA.R_Erdos382_erdos_382_parts_ii_R1

open Erdos382

/-- The elementary region `k ≤ 2`: the pair `(48, 50)` already has `LargestPrimeRepeated` and
length `2`, so it witnesses every `k ≤ 2`. -/
def H1 : Prop :=
  ∀ k : ℕ, k ≤ 2 → ∃ u v : ℕ, LargestPrimeRepeated u v ∧ k ≤ v - u

/-- The core `2 < k`: intervals of arbitrarily large length in which the largest prime is repeated. -/
def H2 : Prop :=
  ∀ k : ℕ, 2 < k → ∃ u v : ℕ, LargestPrimeRepeated u v ∧ k ≤ v - u

theorem main : H1 → H2 → type_of% @Erdos382.erdos_382.parts.ii := by
  intro h1 h2 k
  by_cases hk : k ≤ 2
  · exact h1 k hk
  · exact h2 k (by omega)

end OMA.R_Erdos382_erdos_382_parts_ii_R1
