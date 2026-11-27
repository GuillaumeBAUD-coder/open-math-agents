import OMAReductions.R_Erdos46_erdos_46_variants_positive_rat_R1

/-! If k colors occur, some color has at least n representatives in [kn,2kn)
for arbitrarily large n. Those intervals eventually lie beyond every cutoff. -/

open Filter Finset

theorem OMA.solution : OMA.R_Erdos46_erdos_46_variants_positive_rat_R1.H1 := by
  classical
  intro c hc
  let C := hc.toFinset
  have hC : C.Nonempty := ⟨c 0,hc.mem_toFinset.mpr ⟨0,rfl⟩⟩
  let k := C.card
  have hk : 0<k := card_pos.mpr hC
  let seg (n : ℕ) := Ico (k*n) (2*(k*n))
  have base (n : ℕ) : ∃ j ∈ C, n ≤ ((seg n).filter fun a => c a=j).card := by
    apply exists_le_card_fiber_of_mul_le_card_of_maps_to (fun a _ => hc.mem_toFinset.mpr ⟨a,rfl⟩) hC
    simp only [seg,Nat.card_Ico]
    change k*n ≤ 2*(k*n)-k*n
    omega
  obtain ⟨j,_,hj⟩ := (C.frequently_exists).mp ((Eventually.of_forall base).frequently (f:=atTop))
  refine ⟨j,?_⟩
  intro B
  let T : Set ℕ := {n | B<n ∧ c n=j}
  have low : 0 < (1:ℝ)/(2*k) := by positivity
  apply low.trans_le
  refine le_limsup_of_frequently_le (u:=fun n => T.partialDensity Set.univ n) ?_ ?_
  · rw [frequently_atTop] at hj ⊢
    intro N
    obtain ⟨n,hn,hfreq⟩ := hj (max N B+1)
    have hkn : n ≤ k*n := Nat.le_mul_of_pos_left _ hk
    have hN := le_max_left N B
    have hB := le_max_right N B
    refine ⟨2*(k*n),by omega,?_⟩
    let F := (seg n).filter fun a => c a=j
    have hsub : (↑F : Set ℕ) ⊆ T ∩ Set.Iio (2*(k*n)) := by
      intro a ha
      obtain ⟨hm,hc'⟩ := Finset.mem_filter.mp ha
      obtain ⟨ha1,ha2⟩ := Finset.mem_Ico.mp hm
      exact ⟨⟨by omega,hc'⟩,ha2⟩
    have hcnt : n ≤ (T ∩ Set.Iio (2*(k*n))).ncard := hfreq.trans
      (by simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub
            ((Set.finite_Iio _).subset Set.inter_subset_right))
    simp only [Set.partialDensity,Set.inter_univ,Set.univ_inter,Nat.ncard_Iio]
    push_cast
    have hn' : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0<n)
    have hk' : 0 < (k:ℝ) := by exact_mod_cast hk
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hreal : (n:ℝ) ≤ ((T ∩ Set.Iio (2*(k*n))).ncard:ℝ) := by exact_mod_cast hcnt
    nlinarith [mul_le_mul_of_nonneg_left hreal hk'.le]
  · exact ⟨1,eventually_map.mpr (Eventually.of_forall (Set.partialDensity_le_one T Set.univ))⟩

