import OMAReductions.R_Green37_green_37_lower_bound_R1_H1_R1

-- Step Green37.green_37_lower_bound.R1.H1.R1.H3: hypothesis H3 of reduction Green37.green_37_lower_bound.R1.H1.R1
-- Credit: @ishaanzee
-- Proof: a cover for N2 also covers N1 (and covers exist: the union of {0, d, ..., (k-1)d}),
-- so m is monotone in N; the second part is Bertrand's postulate applied to N / 2.

namespace G37Aux

lemma ap_exists (k d : ℕ) (hd : 1 ≤ d) :
    ((((Finset.range k).image (fun n => n * d)) : Finset ℕ) : Set ℕ).IsAPOfLengthWith (k : ℕ∞) 0 d := by
  refine ⟨?_, ?_⟩
  · have hinj : Function.Injective (fun n : ℕ => n * d) := mul_left_injective₀ (by omega)
    rw [← Set.encard, Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ hinj,
      Finset.card_range]
  · ext x
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio, Set.mem_ofPred_eq,
      zero_add, smul_eq_mul, Nat.cast_lt, exists_prop]

lemma cover_exists (N k : ℕ) :
    ∃ A : Finset ℕ, Green37.IsAPCover (A : Set ℕ) N k := by
  refine ⟨(Finset.Icc 1 N).biUnion (fun d => (Finset.range k).image (fun n => n * d)), ?_⟩
  rintro d ⟨hd1, hdN⟩
  refine ⟨0, _, ?_, ap_exists k d hd1⟩
  intro x hx
  simp only [Finset.coe_biUnion, Finset.coe_Icc, Set.mem_iUnion, exists_prop]
  exact ⟨d, ⟨hd1, hdN⟩, hx⟩

lemma m_mono {N₁ N₂ : ℕ} (k : ℕ) (h : N₁ ≤ N₂) : Green37.m N₁ k ≤ Green37.m N₂ k := by
  have hne : {m | ∃ A : Finset ℕ, A.card = m ∧ Green37.IsAPCover (A : Set ℕ) N₂ k}.Nonempty := by
    obtain ⟨A, hA⟩ := cover_exists N₂ k
    exact ⟨A.card, A, rfl, hA⟩
  obtain ⟨A, hAc, hAcov⟩ := Nat.sInf_mem hne
  unfold Green37.m
  rw [← hAc]
  exact Nat.sInf_le ⟨A, rfl, fun d hd => hAcov d ⟨hd.1, le_trans hd.2 h⟩⟩

lemma bertrand (N : ℕ) (hN : 2 ≤ N) : ∃ p : ℕ, Nat.Prime p ∧ N ≤ 2 * p ∧ p ≤ N := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (N / 2) (by omega)
  exact ⟨p, hp, by omega, by omega⟩

end G37Aux

theorem OMA.solution : OMA.R_Green37_green_37_lower_bound_R1_H1_R1.H3 :=
  ⟨fun _ _ k h => G37Aux.m_mono k h, G37Aux.bertrand⟩
