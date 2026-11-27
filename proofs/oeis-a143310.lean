import OMAStatements.S_oeis_a143310
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a143310.main := by
  intro n k hk1 hkn
  have hL : OMA.S_oeis_a143310.T n k
      = ∑ j ∈ (Finset.Icc 1 n).filter (fun j => k ∣ j), j := by
    unfold OMA.S_oeis_a143310.T
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_Icc] at hj
    unfold OMA.S_oeis_a143310.A000012 OMA.S_oeis_a143310.A127446
    rw [if_pos hj.2, one_mul]
    by_cases hd : k ∣ j
    · rw [if_pos ⟨hk1, Nat.le_of_dvd (by omega) hd, hd⟩, if_pos hd]
    · rw [if_neg (fun h => hd h.2.2), if_neg hd]
  have hR : (∑ i ∈ Finset.Icc 1 n, if i * k ≤ n then i * k else 0)
      = ∑ i ∈ (Finset.Icc 1 n).filter (fun i => i * k ≤ n), i * k :=
    (Finset.sum_filter _ _).symm
  rw [hL, hR]
  symm
  apply Finset.sum_nbij' (fun i => i * k) (fun j => j / k)
  · intro i hi
    rw [Finset.mem_filter, Finset.mem_Icc] at hi ⊢
    exact ⟨⟨Nat.mul_pos (by omega) (by omega), hi.2⟩, Dvd.intro_left _ rfl⟩
  · intro j hj
    rw [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
    obtain ⟨⟨hj1, hjn⟩, c, rfl⟩ := hj
    rw [Nat.mul_div_cancel_left _ (by omega)]
    have hc : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with rfl | h
      · omega
      · exact h
    have hck : c ≤ k * c := Nat.le_mul_of_pos_left c (by omega)
    refine ⟨⟨hc, by omega⟩, ?_⟩
    rw [Nat.mul_comm]
    exact hjn
  · intro i _
    exact Nat.mul_div_cancel _ (by omega)
  · intro j hj
    rw [Finset.mem_filter] at hj
    exact Nat.div_mul_cancel hj.2
  · intro i _
    rfl
