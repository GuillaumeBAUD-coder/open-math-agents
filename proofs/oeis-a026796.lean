import OMAStatements.S_oeis_a026796
import Mathlib

namespace OMA.A026796Disproof

open OMA.S_oeis_a026796

theorem a_four : a 4 = 0 := by
  unfold a
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun ⟨p, h3, hall⟩ => ?_⟩
  obtain ⟨rest, hr⟩ := Multiset.exists_cons_of_mem h3
  have hs := p.parts_sum
  rw [hr, Multiset.sum_cons] at hs
  have hrs : rest.sum = 1 := by omega
  rcases Multiset.empty_or_exists_mem rest with h0 | ⟨x, hx⟩
  · rw [h0] at hrs
    simp at hrs
  · have hx3 : 3 ≤ x := hall x (by rw [hr]; exact Multiset.mem_cons_of_mem hx)
    have hle : x ≤ rest.sum := Multiset.le_sum_of_mem hx
    omega

theorem b_zero : b 0 ≠ 0 := by
  unfold b
  haveI : Nonempty (Balanced 0) := ⟨⟨⟨0, by simp, by simp⟩, by simp⟩⟩
  exact Fintype.card_ne_zero

end OMA.A026796Disproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a026796.main) := by
  intro h
  have := h 0
  rw [OMA.A026796Disproof.a_four] at this
  exact OMA.A026796Disproof.b_zero this.symm
