import FormalConjectures.ErdosProblems.«91»

open EuclideanGeometry Erdos91

namespace OMA.R_Erdos91_erdos_91_test_wheelSeven_optimal_R1

-- Compute the distances in the displayed hexagon together with its center.
def H1 : Prop := wheelSeven.card = 7 ∧ distinctDistances wheelSeven = 3

-- A planar set with at most two distinct distances has at most six points.
-- The weaker bound of six suffices for the seven-point problem.
def H2 : Prop := ∀ S : Finset ℝ², distinctDistances S < 3 → S.card ≤ 6

theorem main : H1 → H2 → type_of% @Erdos91.erdos_91.test.wheelSeven_optimal := by
  rintro ⟨hc, hw⟩ hsmall
  refine ⟨hc, le_antisymm ?_ ?_⟩
  · rw [hw]
    unfold minimalDistinctDistances
    apply le_csInf
    · exact ⟨_, wheelSeven, hc, rfl⟩
    rintro d ⟨S, hs, hd⟩
    rw [← show distinctDistances S = d from by exact_mod_cast hd]
    by_contra! h
    have hle := hsmall S h
    omega
  · unfold minimalDistinctDistances
    exact Nat.sInf_le ⟨wheelSeven, hc, rfl⟩

end OMA.R_Erdos91_erdos_91_test_wheelSeven_optimal_R1
