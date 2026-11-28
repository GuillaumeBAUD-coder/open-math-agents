import OMAStatements.S_oeis_a062282

namespace OMA.P_oeis_a062282

open OMA.S_oeis_a062282

lemma fixedPts_le {n : ℕ} (σ : Equiv.Perm (Fin n)) : fixedPts σ ≤ n := by
  unfold fixedPts
  calc _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

lemma term (n k : ℕ) :
    ((Finset.univ.filter fun σ : Equiv.Perm (Fin n) => Even (fixedPts σ)).filter
      fun σ => fixedPts σ = k).card = T n k * chiEven k := by
  unfold T chiEven
  rw [Finset.filter_filter]
  rcases Nat.even_or_odd k with hk | hk
  · have h0 : k % 2 = 0 := Nat.even_iff.mp hk
    rw [h0, Nat.sub_zero, Nat.mul_one]
    congr 1
    apply Finset.filter_congr
    intro σ _
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨h ▸ hk, h⟩
  · have h1 : k % 2 = 1 := Nat.odd_iff.mp hk
    rw [h1, Nat.sub_self, Nat.mul_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro σ _ h
    rw [h.2] at h
    exact (Nat.not_even_iff_odd.mpr hk) h.1

end OMA.P_oeis_a062282

theorem OMA.solution : type_of% @OMA.S_oeis_a062282.main := by
  intro n
  unfold OMA.S_oeis_a062282.a
  rw [Finset.card_eq_sum_card_fiberwise (f := OMA.S_oeis_a062282.fixedPts)
    (t := Finset.range (n + 1))]
  · exact Finset.sum_congr rfl fun k _ => OMA.P_oeis_a062282.term n k
  · intro σ _
    simpa [Finset.mem_range, Nat.lt_succ_iff] using OMA.P_oeis_a062282.fixedPts_le σ
