import Mathlib

/-!
# arXiv:2606.18956 — A Combinatorial Generalization of a Random-Player Game

Author: Yehonatan Fridman.

We formalize all main results of this paper, resolving the open question of giving a direct
combinatorial explanation for the derangement winning probability `d_n / n!` and generalizing
it to the `q`-game where the deterministic player removes `q` elements per turn (or all
remaining elements if fewer than `q` remain):
1. **Theorem 1 (`thm:main-coupling`)**: Exact cycle-decomposition coupling — for all `q ≥ 1`
   and `n ≥ 1`, the random player's winning probability `RProb q n` equals the fraction of
   permutations `π ∈ Equiv.Perm (Fin n)` whose first cycle of length `≤ q` (in canonical cycle
   order, ordered by smallest element) is a fixed point.
2. **Corollary 1**: For `q = 1`, the deterministic player's winning probability `DProb 1 n`
   equals `d_n / n!` (the derangement probability).
3. **Section 7 (Exact Finite Expression)**: `RProb q n = (1 / n!) * ∑ π, (C_1(π) / M_q(π)) * 1_{M_q(π) > 0}`.
4. **Section 8 (Limiting Probabilities)**: As `n → ∞`, `RProb q n → ρ_q = exp(-H_q) * ∫_0^1 exp(P_q(x)) dx`
   and `DProb q n → 1 - ρ_q`.
5. **Corollary 2**: As `q → ∞`, `ρ_q → 0` and `1 - ρ_q → 1`.
-/

namespace OMA.S_arxiv_2606_18956

open scoped Classical

/-- Winning probability `R_n^{(q)}` of the random player `R` in the `q`-game starting from a pile
    of `n` elements (`R` moves first and removes a uniformly random `k ∈ {1, ..., n}`; if the
    pile is not empty, `D` removes `min(q, n - k)` elements). -/
noncomputable def RProb (q : ℕ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
    (1 / ((n + 1 : ℕ) : ℝ)) *
      ∑ j ∈ Finset.range (n + 1),
        if j = n then (1 : ℝ)
        else if n - j ≤ q then 0
        else RProb q (n - j - q)

/-- Winning probability `D_n^{(q)}` of the deterministic player `D` from `n` elements. -/
noncomputable def DProb (q n : ℕ) : ℝ :=
  1 - RProb q n

/-- Length of the cycle of `π : Equiv.Perm (Fin n)` containing `i : Fin n`. -/
noncomputable def cycleLen {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) : ℕ :=
  (Finset.univ.filter fun j : Fin n => π.SameCycle i j).card

/-- Event that the first cycle of `π` of length `≤ q` in canonical cycle order (ordered by
    smallest element) exists and is a fixed point. -/
def firstShortCycleIsFixed (q : ℕ) {n : ℕ} (π : Equiv.Perm (Fin n)) : Prop :=
  ∃ i : Fin n, cycleLen π i = 1 ∧ ∀ j : Fin n, j < i → q < cycleLen π j

/-- Number of fixed points `C_1(π)` of `π`. -/
noncomputable def fixedPointCount {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n => π i = i).card

/-- Number of elements `M_q(π)` lying in cycles of `π` of length at most `q`. -/
noncomputable def shortCycleElts (q : ℕ) {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i : Fin n => cycleLen π i ≤ q).card

/-- The `q`-th harmonic number `H_q = ∑_{j=1}^q 1/j`. -/
noncomputable def harmonicR (q : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 q, (1 / (j : ℝ))

/-- The truncated logarithm polynomial `P_q(x) = ∑_{j=1}^q x^j / j`. -/
noncomputable def truncLogPoly (q : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 q, x ^ j / (j : ℝ)

/-- Limiting random-player winning probability `ρ_q = exp(-H_q) * ∫_0^1 exp(P_q(x)) dx`. -/
noncomputable def rho (q : ℕ) : ℝ :=
  Real.exp (-harmonicR q) * ∫ x in (0 : ℝ)..1, Real.exp (truncLogPoly q x)

theorem main :
    (∀ (q n : ℕ), 1 ≤ q → 1 ≤ n →
      RProb q n =
        ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
          firstShortCycleIsFixed q π)).card : ℝ) /
          (Nat.factorial n : ℝ)) ∧
    (∀ (n : ℕ), 1 ≤ n →
      DProb 1 n = (numDerangements n : ℝ) / (Nat.factorial n : ℝ)) ∧
    (∀ (q n : ℕ), 1 ≤ q → 1 ≤ n →
      RProb q n =
        (1 / (Nat.factorial n : ℝ)) *
          ∑ π : Equiv.Perm (Fin n),
            if 0 < shortCycleElts q π then
              ((fixedPointCount π : ℝ) / (shortCycleElts q π : ℝ))
            else 0) ∧
    (∀ (q : ℕ), 1 ≤ q →
      Filter.Tendsto (fun n => RProb q n) Filter.atTop (nhds (rho q)) ∧
      Filter.Tendsto (fun n => DProb q n) Filter.atTop (nhds (1 - rho q))) ∧
    (Filter.Tendsto (fun q => rho q) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun q => 1 - rho q) Filter.atTop (nhds 1)) := by
  sorry

end OMA.S_arxiv_2606_18956
