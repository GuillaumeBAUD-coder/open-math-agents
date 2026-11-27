import Mathlib

/-!
# A discrete iteration related to Pierce expansions

Source: https://www.openproblemgarden.org/op/a_discrete_iteration_related_to_pierce_expansions
Credit: @Hyvok

Posed by Jeffrey O. Shallit (2008). Let `a > b > 0` be integers. Define `b₁ = b` and
`b_{i+1} = a mod b_i` (the source writes "for i ≥ 0", but its sequence starts at `b₁`). Each nonzero
term is smaller than the previous one, so eventually `b_{n+1} = 0`; set `P(a, b) = n`, the number of
nonzero terms. The source's example: `P(35, 22) = 7`, from 22, 13, 9, 8, 3, 2, 1, 0.

Problem: prove or disprove that `P(a, b) = O((log a)^2)`. The best known upper bound is
`P(a, b) = O(a^{1/3})` [P. Erdős and J. Shallit, New bounds on the length of finite Pierce and Engel
series, Sém. Théor. Nombres Bordeaux 3 (1991), 43–53].

Formalization notes:
* `steps a b` counts the nonzero terms of the sequence started at `b`, with `a` fixed throughout
  (each step reduces `a`, not the previous term, modulo the current term). `steps a 0 = 0`.
* `O((log a)^2)` is read uniformly in `b`: one constant `C` works for all `a > b > 0`. Since
  `a ≥ 2` forces `log a ≥ log 2 > 0`, this is the same as the bound holding for all large `a`.
* `main` states the bound itself (the "prove" direction of the question).
-/

namespace OMA.S_opg_a_discrete_iteration_related_to_pierce_expansions

/-- `steps a b`: the number of nonzero terms of `b₁ = b`, `b_{i+1} = a mod b_i`, i.e. `P(a, b)`. -/
def steps (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | b + 1 => steps a (a % (b + 1)) + 1
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos b)

/-- Shallit's question: is `P(a, b) = O((log a)^2)`, uniformly over `0 < b < a`? -/
theorem main :
    ∃ C : ℝ, ∀ a b : ℕ, 0 < b → b < a → (steps a b : ℝ) ≤ C * Real.log a ^ 2 := by
  sorry

end OMA.S_opg_a_discrete_iteration_related_to_pierce_expansions
