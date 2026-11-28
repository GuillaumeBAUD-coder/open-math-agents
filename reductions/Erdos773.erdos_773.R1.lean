import FormalConjectures.ErdosProblems.«773»

-- Reduction Erdos773.erdos_773.R1 of Erdős Problem 773
-- Credit: @MBimrose
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 773: the threshold `ε = 1` is elementary

The question asks, for every `ε > 0`, whether the largest Sidon subset of the squares
`{1², 2², …, N²}` has size at least `N ^ (1 - ε)` for all large `N`. This reduction splits the
*parameter* `ε` at the explicit threshold `1`, and nothing else.

* `H1` is the region `ε ≥ 1`. It is **elementary** and holds for every `N`, not only eventually:
  `1 - ε ≤ 0`, so `N ^ (1 - ε) ≤ N ^ 0 = 1` for every `N ≥ 1` (`Real.rpow_nonpos`), while the
  largest Sidon subset has size at least `1` because the singleton `{1} = {1²}` is a Sidon subset
  of `{1², …, N²}` for `N ≥ 1` (a one-point set is Sidon: the only pairwise sums are `1 + 1`).
  For `N = 0` the left side is `0`. So the region `ε ≥ 1` of the statement is already settled
  unconditionally, by a positivity and a `rpow` inequality.
* `H2` is the region `0 < ε < 1`: the genuine open content of the problem.

The threshold is the exact edge of the elementary method, not a round number. The exponent
`1 - ε` exceeds `0` exactly when `ε < 1`, and it is there that the right-hand side has to grow
with `N`, i.e. exactly where the Sidon structure of the squares has to be used. At `ε = 1` the
bound is the constant `1`, which the trivial singleton satisfies; below `1` no fixed-size witness
can work. So `H2` is where the substance is, and `H1` can never be extended upward in ε beyond `1`
without proving the theorem.

Source: <https://www.erdosproblems.com/773>.
-/

namespace OMA.R_Erdos773_erdos_773_R1

open Filter Finset

/-- The statement on the elementary parameter range `ε ≥ 1`, where the exponent `1 - ε` is `≤ 0`. -/
def H1 : Prop :=
  ∀ ε : ℝ, ε > 0 → 1 ≤ ε → ∀ᶠ N : ℕ in atTop,
    (N : ℝ) ^ (1 - ε) ≤
      (Finset.maxSidonSubsetCard
        (Finset.image (fun n : ℕ => n ^ 2) (Finset.Icc 1 N)) : ℝ)

/-- The statement on the open parameter range `0 < ε < 1`, where the bound must grow. -/
def H2 : Prop :=
  ∀ ε : ℝ, ε > 0 → ε < 1 → ∀ᶠ N : ℕ in atTop,
    (N : ℝ) ^ (1 - ε) ≤
      (Finset.maxSidonSubsetCard
        (Finset.image (fun n : ℕ => n ^ 2) (Finset.Icc 1 N)) : ℝ)

theorem main : H1 → H2 → type_of% @Erdos773.erdos_773 := by
  intro hlarge hsmall ε hpos
  by_cases h : 1 ≤ ε
  · exact hlarge ε hpos h
  · exact hsmall ε hpos (not_le.mp h)

end OMA.R_Erdos773_erdos_773_R1
