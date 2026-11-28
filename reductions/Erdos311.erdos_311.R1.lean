import FormalConjectures.ErdosProblems.«311»
import Mathlib

-- Reduction Erdos311.erdos_311.R1 of Erdős Problem 311
-- Credit: @MBimrose
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
/-!
# Reduction of `Erdos311.erdos_311`

`delta N` is the least non-zero `|1 - ∑_{n ∈ A} 1/n|` over `A ⊆ {1,…,N}`, and the target asks for
`c ∈ (0,1)` with `-log (delta N) / N → c`. The three conjuncts of that sentence are exactly the
three steps below; the bridge is elementary (an eventual bound on a sequence that converges is a
bound on its limit):

* `H1` — the limit `-log (delta N) / N → c` exists for some real `c` (the sequence is not known to
  be monotone, so this is genuine content, not a definitional triviality).
* `H2` — the strict upper bound `-log (delta N) / N ≤ 1 - ε` eventually. This is the `c < 1` half.
  It is *nontrivial*: the in-repo textbook bound `Erdos311.delta_ge_exp`
  (`delta N ≥ exp (-(1+ε)N)`) gives only `-log (delta N) / N ≤ 1 + ε`, so `H2` asks for a
  genuine gain over the lcm bound `delta N ≥ 1/[1,…,N] = e^{-(1+o(1))N}`.
* `H3` — the strict lower bound `c₀ ≤ -log (delta N) / N` eventually. This is the `c > 0` half,
  i.e. `delta N ≤ e^{-c₀ N}`: a construction beating the trivial values `|1 - 1/n| ≥ 1/2`.
-/

namespace OMA.R_Erdos311_erdos_311_R1

open Filter Topology

/-- Step 1: the normalised logarithm of `delta` converges (the limit constant exists). -/
def H1 : Prop :=
  ∃ c : ℝ, Tendsto (fun N : ℕ => -Real.log (Erdos311.delta N) / (N : ℝ)) atTop (𝓝 c)

/-- Step 2 (`c < 1`): eventually `-log (delta N) / N ≤ 1 - ε`, beating the trivial lcm bound
`Erdos311.delta_ge_exp`, which only gives `≤ 1 + ε`. -/
def H2 : Prop :=
  ∃ ε > (0 : ℝ), ∀ᶠ N : ℕ in atTop, -Real.log (Erdos311.delta N) / (N : ℝ) ≤ 1 - ε

/-- Step 3 (`c > 0`): eventually `-log (delta N) / N` is bounded below by a positive constant,
i.e. `delta N ≤ exp (-c₀ N)` for some `c₀ > 0`. -/
def H3 : Prop :=
  ∃ c₀ > (0 : ℝ), ∀ᶠ N : ℕ in atTop, c₀ ≤ -Real.log (Erdos311.delta N) / (N : ℝ)

theorem main : H1 → H2 → H3 → type_of% @Erdos311.erdos_311 := by
  rintro ⟨c, hlim⟩ ⟨ε, hε0, hε⟩ ⟨c₀, hc₀0, hc₀⟩
  refine ⟨c, ⟨?_, ?_⟩, hlim⟩
  · -- `0 < c`: the limit is at least the eventual lower bound `c₀ > 0`.
    have hc₀c : c₀ ≤ c := ge_of_tendsto hlim hc₀
    linarith
  · -- `c < 1`: the limit is at most the eventual upper bound `1 - ε < 1`.
    have hc : c ≤ 1 - ε := le_of_tendsto hlim hε
    linarith

end OMA.R_Erdos311_erdos_311_R1
