import Mathlib

/-!
# Erdős Problem 301

Source: https://www.erdosproblems.com/301
Credit: @mgv27

Let $f(N)$ be the size of the largest $A\subseteq \{1,\ldots,N\}$ such that there are no
solutions to $\frac{1}{a} = \frac{1}{b_1}+\cdots+\frac{1}{b_k}$ with distinct
$a,b_1,\ldots,b_k\in A$. Estimate $f(N)$. In particular, is it true that
$f(N) = (\tfrac{1}{2}+o(1))N$?

Formalization notes:
* `main` states the specific question, as `f(N) / N → 1/2`.
* Distinct `b_1, …, b_k` form a nonempty finset `S ⊆ A` not containing `a`; `k ≥ 1` is
  arbitrary. (The case `k = 1` never gives a solution, since `a ≠ b_1`.)
* The source records `N/2 ≤ f(N) ≤ (25/28 + o(1)) N` (the lower bound from `(N/2, N]`).
-/

namespace OMA.S_erdos_301

open Filter Topology

/-- `A` contains no `a` and distinct `b_1, …, b_k` (all different from `a`) with
`1/a = 1/b_1 + ⋯ + 1/b_k`. -/
def NoSolution (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S : Finset ℕ, S ⊆ A → S.Nonempty → a ∉ S →
    (1 / (a : ℚ)) ≠ ∑ b ∈ S, 1 / (b : ℚ)

/-- `f(N)`: the size of the largest `A ⊆ {1, …, N}` with no solution. -/
noncomputable def f (N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ NoSolution A ∧ A.card = k}

/-- Erdős Problem 301: is it true that `f(N) = (1/2 + o(1)) N`? -/
theorem main : Tendsto (fun N : ℕ => (f N : ℝ) / (N : ℝ)) atTop (𝓝 (1 / 2)) := by
  sorry

end OMA.S_erdos_301
