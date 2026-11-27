import FormalConjectures.ErdosProblems.«338»

-- Reduction Erdos338.erdos_338.variants.squares.R1 of Erdős Problem 338 — squares
-- Credit: @luciusacarr
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The squares: order `4`, restricted order `5`

* `H1` is the classical part: the squares are a basis of order exactly `4` (Lagrange's
  four-square theorem, and `8k + 7` is never a sum of at most three squares).
* `H2` is Pall's theorem: every sufficiently large integer is a sum of at most `5` distinct
  squares.  This is the hard part.
* `H3` is the matching lower bound: infinitely many integers (for instance `2 * 4 ^ k`) are not
  sums of at most `4` distinct squares.
-/

namespace OMA.R_Erdos338_erdos_338_variants_squares_R1

open Erdos338

/-- The squares form a basis of order exactly `4`. -/
def H1 : Prop :=
  basisOrder (Set.range fun k : ℕ ↦ k ^ 2) = 4

/-- Pall: every sufficiently large integer is a sum of at most `5` distinct squares. -/
def H2 : Prop :=
  HasRestrictedOrder (Set.range fun k : ℕ ↦ k ^ 2) 5

/-- Not every sufficiently large integer is a sum of at most `4` distinct squares. -/
def H3 : Prop :=
  ¬ HasRestrictedOrder (Set.range fun k : ℕ ↦ k ^ 2) 4

lemma hasRestrictedOrder_mono {A : Set ℕ} {t t' : ℕ} (h : HasRestrictedOrder A t)
    (htt : t ≤ t') : HasRestrictedOrder A t' := by
  unfold HasRestrictedOrder at *
  filter_upwards [h] with m ⟨S, hS, hc, hs⟩
  exact ⟨S, hS, hc.trans htt, hs⟩

theorem main : H1 → H2 → H3 → type_of% @Erdos338.erdos_338.variants.squares := by
  intro h1 h2 h3
  refine ⟨h1, ?_⟩
  unfold restrictedOrder
  apply le_antisymm
  · exact iInf₂_le 5 h2
  · refine le_iInf₂ fun t ht => ?_
    by_contra hlt
    have ht4 : t ≤ 4 := by
      have : (t : ℕ∞) < 5 := lt_of_not_ge hlt
      exact_mod_cast Order.le_of_lt_succ (by exact_mod_cast this)
    exact h3 (hasRestrictedOrder_mono ht ht4)

end OMA.R_Erdos338_erdos_338_variants_squares_R1
