import FormalConjectures.ErdosProblems.«885»
import Mathlib

-- Reduction Erdos885.erdos_885.R1 of Erdős Problem 885
-- Credit: @MBimrose
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target (erdosproblems.com/885): for every `k ≥ 1` there are positive integers `N₁ < … < N_k`
-- whose common difference-set `⋂ᵢ D(Nᵢ)` (`factorDifferenceSet N = {|a - b| : N = a * b}`) has at
-- least `k` elements.  The cases `k = 2` (Erdős–Rosenfeld [ErRo97]) and `k = 3` (Jiménez-Urroz
-- [Ji99]) are already proved in this very module as `erdos_885.variants.k_eq_2` and
-- `erdos_885.variants.k_eq_3`, so the honest split is the one along `k`.
--
--   * `H1` — `k ≤ 3`: the three cases are known.  `k = 2` and `k = 3` are immediate from the two
--     proved theorems above; `k = 1` is a one-liner, `Ns = {1}`, because
--     `factorDifferenceSet 1 = {|1 - 1|} = {0}` has `ncard = 1`.  So `H1` is elementary: nothing
--     beyond the definitions and citations already in the file.
--   * `H2` — `4 ≤ k`: the open core.  This is where the construction has to be made for a growing
--     number of integers at once, which no known argument does beyond `k = 3`.
--
-- `main` is the case split `k ≤ 3` / `3 < k`, so closing `H1` and `H2` closes the problem.

namespace OMA.R_Erdos885_erdos_885_R1

open Erdos885

/-- The settled cases `k ≤ 3`. -/
def H1 : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ 3 →
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = k ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ k

/-- The open core: `4 ≤ k`. -/
def H2 : Prop :=
  ∀ k : ℕ, 4 ≤ k →
    ∃ Ns : Finset ℕ,
      (∀ n ∈ Ns, 1 ≤ n) ∧
      Ns.card = k ∧
      (⋂ n ∈ Ns, factorDifferenceSet n).ncard ≥ k

theorem main : H1 → H2 → type_of% @Erdos885.erdos_885 := by
  intro h1 h2 k hk
  rcases le_or_gt k 3 with h | h
  · exact h1 k hk h
  · exact h2 k (by omega)

end OMA.R_Erdos885_erdos_885_R1
