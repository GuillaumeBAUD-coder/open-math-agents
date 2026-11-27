import FormalConjectures.ErdosProblems.«258»

/-! A finite-window divisor estimate suffices for the Cantor series criterion.
The exponential digit criterion follows the tail argument of Chojecki and
the Lean formalization by ster-oc cited in the upstream problem. -/

namespace OMA.R_Erdos258_erdos_258_variants_monotone_R1

open Filter Finset

-- Beyond this logarithmic window the elementary bound on the number of
-- divisors is already exponential in the shift.
def H1 : Prop :=
  ∃ L : ℕ, 2 ≤ L ∧ ∃ᶠ N : ℕ in atTop, ∀ j : ℕ, 2^j ≤ N →
    (N+j+1).divisors.card ≤ L^(j+1)

-- Denominator clearing and a geometric bound on a positive tail.
-- The digits and the bases can be chosen independently.
def H2 : Prop :=
  ∀ a d : ℕ → ℕ, (∀ i, 2 ≤ a i) → Tendsto a atTop atTop →
    (∀ i, 0 < d (i+1)) →
    (∃ L : ℕ, 2 ≤ L ∧ ∃ᶠ N : ℕ in atTop, ∀ j : ℕ, d (N+j+1) ≤ L^(j+1)) →
    Irrational (∑' n : ℕ, ((d (n+1) : ℝ) / ((∏ i ∈ Icc 1 (n+1), a i : ℕ) : ℝ)))

theorem main : H1 → H2 → type_of% @Erdos258.erdos_258.variants.monotone := by
  rintro ⟨L, hL, window⟩ criterion a ha _ growth
  apply criterion a (fun m => m.divisors.card) ha growth
  · intro i
    exact Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
  refine ⟨L, hL, window.mono ?_⟩
  intro N good j
  by_cases hj : 2^j ≤ N
  · exact good j hj
  · have step : j+1 ≤ 2^j := j.lt_two_pow_self
    calc
      (N+j+1).divisors.card ≤ N+j+1 := Nat.card_divisors_le_self _
      _ ≤ 2^(j+1) := by rw [pow_succ]; omega
      _ ≤ L^(j+1) := Nat.pow_le_pow_left hL _

end OMA.R_Erdos258_erdos_258_variants_monotone_R1
