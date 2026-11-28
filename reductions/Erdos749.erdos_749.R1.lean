import FormalConjectures.ErdosProblems.«749»

-- Reduction Erdos749.erdos_749.R1 of Erdős Problem 749
-- Credit: @MBimrose
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 749: the threshold `ε = 1/2` is elementary

The question asks, for every `ε > 0`, for a set `A ⊆ ℕ` whose sumset `A + A` has lower density at
least `1 - ε` while the representation function `1_A * 1_A` stays bounded. This reduction splits
the *parameter* `ε` at the explicit threshold `1/2`, and nothing else.

* `H1` is the region `ε ≥ 1/2`. It is **elementary**: the even numbers `A = 2ℕ` are an explicit
  witness. Sums of two even numbers are exactly the even numbers, so `A + A = 2ℕ` and
  `lowerDensity (2ℕ) = 1/2 ≥ 1 - ε`; and an even `n` has at most one representation
  `n = a + b` with `a, b ∈ 2ℕ` (namely `a = 0`), an odd `n` has none, so `1_A * 1_A ≤ 1`.
  Hence the region `ε ≥ 1/2` of the statement is already settled, unconditionally.
* `H2` is the region `0 < ε < 1/2`: the genuine open content of the problem.

The threshold is the exact edge of the elementary method, not a convenient round number. Every
arithmetic progression `A = Nℕ` has `A + A = Nℕ`, so `lowerDensity (A + A) = 1/N` and
`1_A * 1_A ≤ 1`; the condition `1/N ≥ 1 - ε` forces `N ≤ 1/(1 - ε)`, which for `ε < 1/2` forces
`N = 1`, and `A = ℕ` has an unbounded representation function. So no progression witness reaches
below `1/2`, and `H2` is where a new construction is required.

Source: <https://www.erdosproblems.com/749>.
-/

namespace OMA.R_Erdos749_erdos_749_R1

open Set Pointwise AdditiveCombinatorics

/-- The statement for the parameter range `ε ≥ 1/2`, where the even numbers are a witness. -/
def H1 : Prop :=
  ∀ ε : ℝ, ε > 0 → 1 / 2 ≤ ε →
    ∃ A : Set ℕ, 1 - ε ≤ lowerDensity (A + A) ∧
      ((Nat.cast (R := ℝ) ∘ sumRep A) ≪ (fun n => (1 : ℝ)))

/-- The statement for the parameter range `0 < ε < 1/2`: the open region. -/
def H2 : Prop :=
  ∀ ε : ℝ, ε > 0 → ε < 1 / 2 →
    ∃ A : Set ℕ, 1 - ε ≤ lowerDensity (A + A) ∧
      ((Nat.cast (R := ℝ) ∘ sumRep A) ≪ (fun n => (1 : ℝ)))

theorem main : H1 → H2 → type_of% @Erdos749.erdos_749 := by
  intro hhalf hsmall ε hpos
  by_cases hlt : ε < 1 / 2
  · exact hsmall ε hpos hlt
  · exact hhalf ε hpos (not_lt.mp hlt)

end OMA.R_Erdos749_erdos_749_R1
