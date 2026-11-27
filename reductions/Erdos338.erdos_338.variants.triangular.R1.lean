import FormalConjectures.ErdosProblems.«338»

-- Reduction Erdos338.erdos_338.variants.triangular.R1 of Erdős Problem 338 — triangular
-- Credit: @luciusacarr
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The triangular numbers: order `3` and restricted order `3`

* `H1` is Schinzel's theorem: every sufficiently large integer is a sum of at most `3` distinct
  triangular numbers.  It also gives order at most `3` (distinct summands are in particular
  summands), so it carries Gauss's Eureka theorem for large integers.
* `H2` is the lower bound: the triangular numbers are not a basis of order `2` (for instance no
  integer `≡ 5 (mod 9)` is a sum of at most two triangular numbers).  This also rules out
  restricted order `2`.
-/

namespace OMA.R_Erdos338_erdos_338_variants_triangular_R1

open Erdos338

/-- Schinzel: every sufficiently large integer is a sum of at most `3` distinct triangular
numbers. -/
def H1 : Prop :=
  HasRestrictedOrder (Set.range fun k : ℕ ↦ k * (k + 1) / 2) 3

/-- The triangular numbers are not a basis of order `2`. -/
def H2 : Prop :=
  ¬ HasOrder (Set.range fun k : ℕ ↦ k * (k + 1) / 2) 2

lemma hasOrder_of_hasRestrictedOrder {A : Set ℕ} {t : ℕ} (h : HasRestrictedOrder A t) :
    HasOrder A t := by
  unfold HasRestrictedOrder HasOrder at *
  filter_upwards [h] with m ⟨S, hS, hc, hs⟩
  exact ⟨S.val, hS, hc, by rw [← hs, Finset.sum_eq_multiset_sum, Multiset.map_id']⟩

lemma hasOrder_mono {A : Set ℕ} {h h' : ℕ} (H : HasOrder A h) (hh : h ≤ h') :
    HasOrder A h' := by
  unfold HasOrder at *
  filter_upwards [H] with m ⟨S, hS, hc, hs⟩
  exact ⟨S, hS, hc.trans hh, hs⟩

theorem main : H1 → H2 → type_of% @Erdos338.erdos_338.variants.triangular := by
  intro h1 h2
  constructor
  · unfold basisOrder
    apply le_antisymm (iInf₂_le 3 (hasOrder_of_hasRestrictedOrder h1))
    refine le_iInf₂ fun t ht => ?_
    by_contra hlt
    have : t ≤ 2 := by
      have : (t : ℕ∞) < 3 := lt_of_not_ge hlt
      have : t < 3 := by exact_mod_cast this
      omega
    exact h2 (hasOrder_mono ht this)
  · unfold restrictedOrder
    apply le_antisymm (iInf₂_le 3 h1)
    refine le_iInf₂ fun t ht => ?_
    by_contra hlt
    have : t ≤ 2 := by
      have : (t : ℕ∞) < 3 := lt_of_not_ge hlt
      have : t < 3 := by exact_mod_cast this
      omega
    exact h2 (hasOrder_mono (hasOrder_of_hasRestrictedOrder ht) this)

end OMA.R_Erdos338_erdos_338_variants_triangular_R1
