import FormalConjectures.ErdosProblems.«107»

-- Reduction Erdos107.erdos_107.R1 of Erdős Problem 107
-- Credit: @ihateSAS
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős–Szekeres: the two inequalities behind `f n = 2 ^ (n - 2) + 1`

The conjecture is the exact value of the least `N` such that any `N` points in the plane, no
three collinear, contain the vertices of a convex `n`-gon.  An equality of natural numbers is
the conjunction of its two inequalities, and the two inequalities are proved by completely
different methods.

* `H1` is the **upper bound** `f n ≤ 2 ^ (n - 2) + 1`: every set of `2 ^ (n - 2) + 1` points in
  general position contains a convex `n`-gon.  This is the open direction (the Happy Ending
  theorem gives existence of *some* bound, not this one).
* `H2` is the **lower bound** `2 ^ (n - 2) + 1 ≤ f n`: the Erdős–Szekeres construction of
  `2 ^ (n - 2)` points in general position with no convex `n`-gon shows that no smaller number
  can work.

The reduction's content is the antisymmetry assembly `le_antisymm H1 H2`.
-/

namespace OMA.R_Erdos107_erdos_107_R1

/-- The upper bound on `f`: `2 ^ (n - 2) + 1` points in general position always contain a
convex `n`-gon.  This is the open direction of the conjecture. -/
def H1 : Prop :=
  ∀ n ≥ 3, Erdos107.f n ≤ 2 ^ (n - 2) + 1

/-- The lower bound on `f`: the Erdős–Szekeres construction gives `2 ^ (n - 2)` points in
general position with no convex `n`-gon, so `f n` is at least `2 ^ (n - 2) + 1`. -/
def H2 : Prop :=
  ∀ n ≥ 3, 2 ^ (n - 2) + 1 ≤ Erdos107.f n

theorem main : H1 → H2 → type_of% @Erdos107.erdos_107 := by
  intro h1 h2 n hn
  exact le_antisymm (h1 n hn) (h2 n hn)

end OMA.R_Erdos107_erdos_107_R1
