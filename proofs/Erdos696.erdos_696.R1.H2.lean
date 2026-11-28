import OMAReductions.R_Erdos696_erdos_696_R1

theorem OMA.solution : OMA.R_Erdos696_erdos_696_R1.H2 := by
  intro S T δ hδ hT hD hS
  unfold Set.HasDensity at hT hS
  have hsum := hS.add hT
  have hle : ∀ᶠ b : ℕ in Filter.atTop, (S.partialDensity Set.univ b + T.partialDensity Set.univ b) ≤ 1 := by
    filter_upwards [Filter.eventually_gt_atTop 0] with b hb
    have hc : (Set.univ ∩ Set.Iio b).ncard = b := by simp
    have hbpos : (0:ℝ) < b := by exact_mod_cast hb
    unfold Set.partialDensity
    rw [hc, ← add_div, div_le_one hbpos]
    have hdisj : Disjoint ((S ∩ Set.univ) ∩ Set.Iio b) ((T ∩ Set.univ) ∩ Set.Iio b) :=
      Set.disjoint_left.2 (fun x hx hy => Set.disjoint_left.1 hD hx.1.1 hy.1.1)
    have hfin : ((Set.Iio b : Set ℕ)).Finite := Set.finite_Iio b
    rw [← Nat.cast_add, ← Set.ncard_union_eq hdisj (hfin.subset fun x hx => hx.2) (hfin.subset fun x hx => hx.2)]
    have : (S ∩ Set.univ ∩ Set.Iio b ∪ T ∩ Set.univ ∩ Set.Iio b).ncard ≤ (Set.Iio b).ncard :=
      Set.ncard_le_ncard (fun x hx => by rcases hx with hx | hx <;> exact hx.2) hfin
    have h2 : (Set.Iio b : Set ℕ).ncard = b := by simpa using hc
    exact_mod_cast h2 ▸ this
  have := le_of_tendsto hsum hle
  linarith
