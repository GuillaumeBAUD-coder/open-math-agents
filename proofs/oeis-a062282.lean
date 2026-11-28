import OMAStatements.S_oeis_a062282
import Mathlib

namespace A062282
open OMA.S_oeis_a062282

lemma fixedPts_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) : fixedPts σ < n + 1 := by
  unfold fixedPts
  have h1 : (Finset.univ.filter fun i => σ i = i).card ≤ (Finset.univ : Finset (Fin n)).card :=
    Finset.card_filter_le _ _
  have h2 : (Finset.univ : Finset (Fin n)).card = n := by simp
  omega

lemma fiber (n k : ℕ) :
    ((Finset.univ.filter fun σ : Equiv.Perm (Fin n) => Even (fixedPts σ)).filter
        fun σ => fixedPts σ = k).card = T n k * chiEven k := by
  unfold T chiEven
  rw [Finset.filter_filter]
  rcases Nat.even_or_odd k with hk | hk
  · have h0 : k % 2 = 0 := Nat.even_iff.mp hk
    rw [h0, Nat.sub_zero, mul_one]
    congr 1
    apply Finset.filter_congr
    intro σ _
    constructor
    · rintro ⟨_, h⟩
      exact h
    · intro h
      exact ⟨h ▸ hk, h⟩
  · have h1 : k % 2 = 1 := Nat.odd_iff.mp hk
    rw [h1, Nat.sub_self, mul_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro σ _ ⟨h2, h3⟩
    rw [h3] at h2
    exact (Nat.not_even_iff_odd.mpr hk) h2

end A062282

theorem OMA.solution : type_of% @OMA.S_oeis_a062282.main := by
  intro n
  unfold OMA.S_oeis_a062282.a
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun σ : Equiv.Perm (Fin n) => OMA.S_oeis_a062282.fixedPts σ)
    (t := Finset.range (n + 1))]
  · apply Finset.sum_congr rfl
    intro k _
    exact A062282.fiber n k
  · intro σ _
    rw [Finset.mem_coe, Finset.mem_range]
    exact A062282.fixedPts_lt σ
