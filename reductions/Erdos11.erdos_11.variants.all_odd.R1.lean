import FormalConjectures.ErdosProblems.«11»

-- Reduction Erdos11.erdos_11.variants.all_odd.R1 of Erdős Problem 11 — all odd
-- Credit: @MBimrose
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target (erdosproblems.com/11): every odd `n > 1` is `k + 2^l` with `k` squarefree.  This is
-- the strong ("a single exception refutes it") form of Erdős's question; the site score for
-- `n` large is `erdos_11`, and `eventually_of_all_odd` shows this form implies it.
--
-- The split is on the *witness* that the weakest possible choice of the power of two allows:
--   * `H1` — `n - 1` is squarefree.  Then `k = n - 1`, `l = 0` works, because `n = (n - 1) + 1`
--     and `2 ^ 0 = 1`; this is the elementary region (two lines, no hypotheses beyond `1 < n`).
--   * `H2` — `n - 1` is NOT squarefree.  Then `l = 0` is impossible (`k = n - 1` would have to be
--     squarefree), so any solution has `l ≥ 1` and `k = n - 2 ^ l`; this is the core, and it is
--     strictly stronger than the target on its region, since it forbids the trivial `l = 0`.
--
-- Why this is honest: the two hypotheses partition the domain (`Squarefree (n - 1) ∨ ¬ …`) and
-- carry exactly the target's conclusion on their half, so `main` is a case distinction and nothing
-- is lost.  The region `H1` covers all odd `n` with `n - 1` squarefree (e.g. `n = 2p + 1` for `p`
-- prime, `n = 3`, `n = 5`), which is a positive proportion of the odd numbers; the remaining
-- problem is the classical form of the conjecture.

namespace OMA.R_Erdos11_erdos_11_variants_all_odd_R1

/-- The elementary case: `n - 1` is squarefree, so `k = n - 1` and `l = 0` solve the equation. -/
def H1 : Prop :=
  ∀ n : ℕ, Odd n → 1 < n → Squarefree (n - 1) → ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l

/-- The core: `n - 1` is not squarefree, so the power of two in `n = k + 2 ^ l` has to be
non-trivial (`2 ^ l` is a proper divisor of `n - k`). -/
def H2 : Prop :=
  ∀ n : ℕ, Odd n → 1 < n → ¬ Squarefree (n - 1) → ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l

theorem main : H1 → H2 → type_of% @Erdos11.erdos_11.variants.all_odd := by
  intro h1 h2 n hn hn'
  by_cases hs : Squarefree (n - 1)
  · exact h1 n hn hn' hs
  · exact h2 n hn hn' hs

end OMA.R_Erdos11_erdos_11_variants_all_odd_R1
