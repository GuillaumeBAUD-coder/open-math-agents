import OMAReductions.R_Green72_no_k_in_line_big_R1

-- Step Green72.no_k_in_line_big.R1.H2
-- Credit: @caa1982

open Finset Green72

theorem OMA.solution : OMA.R_Green72_no_k_in_line_big_R1.H2 := by
  intro k N s hk hs hline
  refine ⟨fun i hi => ?_, fun t hts htc hcol => ?_⟩
  · have hmem := Finset.mem_product.mp (hs hi)
    exact ⟨Finset.mem_range.mp hmem.1, Finset.mem_range.mp hmem.2⟩
  · have h1 : 1 < t.card := by omega
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h1
    have hpN := Finset.mem_product.mp (hs (hts hp))
    have hqN := Finset.mem_product.mp (hs (hts hq))
    have hp1 : p.1 < N := Finset.mem_range.mp hpN.1
    have hp2 : p.2 < N := Finset.mem_range.mp hpN.2
    have hq1 : q.1 < N := Finset.mem_range.mp hqN.1
    have hq2 : q.2 < N := Finset.mem_range.mp hqN.2
    let a : ℤ := (q.2 : ℤ) - (p.2 : ℤ)
    let b : ℤ := (p.1 : ℤ) - (q.1 : ℤ)
    let c : ℤ := a * (p.1 : ℤ) + b * (p.2 : ℤ)
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra! h0
      apply hpq
      exact Prod.ext (by omega) (by omega)
    have ha1 : -(N : ℤ) < a := by omega
    have ha2 : a < (N : ℤ) := by omega
    have hb1 : -(N : ℤ) < b := by omega
    have hb2 : b < (N : ℤ) := by omega
    rw [collinear_iff_exists_forall_eq_smul_vadd] at hcol
    obtain ⟨p₀, v, hv⟩ := hcol
    obtain ⟨sp, hsp⟩ := hv ((p.1 : ℝ), (p.2 : ℝ)) ⟨p, hp, rfl⟩
    obtain ⟨sq, hsq⟩ := hv ((q.1 : ℝ), (q.2 : ℝ)) ⟨q, hq, rfl⟩
    have hsp1 : (p.1 : ℝ) = sp * v.1 + p₀.1 := congrArg Prod.fst hsp
    have hsp2 : (p.2 : ℝ) = sp * v.2 + p₀.2 := congrArg Prod.snd hsp
    have hsq1 : (q.1 : ℝ) = sq * v.1 + p₀.1 := congrArg Prod.fst hsq
    have hsq2 : (q.2 : ℝ) = sq * v.2 + p₀.2 := congrArg Prod.snd hsq
    have hsub : t ⊆ s.filter (fun i => a * (i.1 : ℤ) + b * (i.2 : ℤ) = c) := by
      intro i hi
      refine Finset.mem_filter.mpr ⟨hts hi, ?_⟩
      obtain ⟨si, hsi⟩ := hv ((i.1 : ℝ), (i.2 : ℝ)) ⟨i, hi, rfl⟩
      have hsi1 : (i.1 : ℝ) = si * v.1 + p₀.1 := congrArg Prod.fst hsi
      have hsi2 : (i.2 : ℝ) = si * v.2 + p₀.2 := congrArg Prod.snd hsi
      have hreal : ((q.2 : ℝ) - (p.2 : ℝ)) * (i.1 : ℝ) + ((p.1 : ℝ) - (q.1 : ℝ)) * (i.2 : ℝ) =
          ((q.2 : ℝ) - (p.2 : ℝ)) * (p.1 : ℝ) + ((p.1 : ℝ) - (q.1 : ℝ)) * (p.2 : ℝ) := by
        rw [hsp1, hsp2, hsq1, hsq2, hsi1, hsi2]
        ring
      have hint : ((a * (i.1 : ℤ) + b * (i.2 : ℤ) : ℤ) : ℝ) = ((c : ℤ) : ℝ) := by
        dsimp only [a, b, c]
        push_cast
        exact hreal
      exact_mod_cast hint
    have hcard := (Finset.card_le_card hsub).trans (hline a b c hab ha1 ha2 hb1 hb2)
    omega
