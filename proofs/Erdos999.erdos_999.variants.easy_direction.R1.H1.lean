import OMAReductions.R_Erdos999_erdos_999_variants_easy_direction_R1

/-! # A measure bound for neighborhoods of reduced fractions on the unit interval -/
-- Credit: @steveDOTdigital

open MeasureTheory

theorem OMA.solution : OMA.R_Erdos999_erdos_999_variants_easy_direction_R1.H1 := by
  classical
  intro f hf q
  by_cases hq : 0 < q
  · have hqr : (0 : ℝ) < q := by exact_mod_cast hq
    have hqz : (0 : ℤ) < q := by exact_mod_cast hq
    let δ := f q / q
    let E : Set ℝ := {x | 0 < q ∧ ∃ p : ℤ, Int.gcd p q = 1 ∧ |x - p / q| < δ}
    change (volume.restrict (Set.Icc (0 : ℝ) 1)) E ≤ _
    rw [Measure.restrict_apply' measurableSet_Icc, mul_div_assoc]
    by_cases hlarge : 1 ≤ δ
    · have ht : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
      have hprod : 1 ≤ (q.totient : ℝ) * δ := one_le_mul_of_one_le_of_one_le ht hlarge
      calc
        volume (E ∩ Set.Icc (0 : ℝ) 1) ≤ volume (Set.Icc (0 : ℝ) 1) :=
          measure_mono Set.inter_subset_right
        _ = ENNReal.ofReal 1 := by simp [Real.volume_Icc]
        _ ≤ _ := ENNReal.ofReal_le_ofReal (show 1 ≤ 6 * ((q.totient : ℝ) * δ) by linarith)
    · let R := (Finset.range q).filter (fun a => q.Coprime a)
      let K := Finset.Icc (-1 : ℤ) 1
      let indices := R ×ˢ K
      let center (t : ℕ × ℤ) : ℝ := (((t.1 : ℤ) + (q : ℤ) * t.2 : ℤ) : ℝ) / q
      let ball (t : ℕ × ℤ) := Set.Ioo (center t - δ) (center t + δ)
      have hcover : E ∩ Set.Icc (0 : ℝ) 1 ⊆ ⋃ t ∈ indices, ball t := by
        rintro x ⟨⟨_, p, hcop, hdist⟩, hxlo, hxhi⟩
        obtain ⟨hdlo, hdhi⟩ := abs_lt.mp hdist
        have hlo : (-1 : ℝ) < (p : ℝ) / q := by linarith
        have hhi : (p : ℝ) / q < 2 := by linarith
        have hloz : (-1 : ℤ) * q ≤ p := by
          exact_mod_cast (le_of_lt ((lt_div_iff₀ hqr).mp hlo))
        have hhiz : p < 2 * (q : ℤ) := by exact_mod_cast ((div_lt_iff₀ hqr).mp hhi)
        let a := (p % (q : ℤ)).toNat
        let k := p / (q : ℤ)
        have ha : (a : ℤ) = p % (q : ℤ) :=
          Int.toNat_of_nonneg (Int.emod_nonneg _ hqz.ne')
        have haq : a < q := by
          exact_mod_cast (show (a : ℤ) < q by rw [ha]; exact Int.emod_lt_of_pos _ hqz)
        have hgc : Int.gcd (a : ℤ) q = 1 := by rw [ha, Int.gcd_emod]; exact hcop
        have hac : q.Coprime a := (show Nat.Coprime a q from hgc).symm
        have hak : (a,k) ∈ indices := by
          refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr haq, hac⟩, ?_⟩
          exact Finset.mem_Icc.mpr ⟨(Int.le_ediv_iff_mul_le hqz).mpr hloz,
            by have hk : k < 2 := (Int.ediv_lt_iff_lt_mul hqz).mpr hhiz; omega⟩
        have hp : (a : ℤ) + (q : ℤ) * k = p := by rw [ha]; exact Int.emod_add_mul_ediv p q
        have hcenter : center (a,k) = (p : ℝ) / q := by
          change (((a : ℤ) + (q : ℤ) * k : ℤ) : ℝ) / q = _
          rw [hp]
        refine Set.mem_iUnion.mpr ⟨(a,k), Set.mem_iUnion.mpr ⟨hak, ?_⟩⟩
        change center (a,k) - δ < x ∧ x < center (a,k) + δ
        rw [hcenter]
        constructor <;> linarith
      have hvol (t : ℕ × ℤ) : volume (ball t) = ENNReal.ofReal (2 * δ) := by
        rw [show ball t = Set.Ioo (center t - δ) (center t + δ) from rfl, Real.volume_Ioo]
        congr 1
        ring
      calc
        volume (E ∩ Set.Icc (0 : ℝ) 1) ≤ volume (⋃ t ∈ indices, ball t) := measure_mono hcover
        _ ≤ ∑ t ∈ indices, volume (ball t) := measure_biUnion_finset_le _ _
        _ = indices.card • ENNReal.ofReal (2 * δ) := by simp [hvol]
        _ = _ := by
          have hcard : indices.card = q.totient * 3 := by
            change (R ×ˢ K).card = _
            rw [Finset.card_product, show R.card = q.totient from rfl, show K.card = 3 by decide]
          rw [hcard, ← ENNReal.ofReal_nsmul, nsmul_eq_mul]
          congr 1
          push_cast
          change _ = 6 * ((q.totient : ℝ) * δ)
          ring
  · have hz : q = 0 := by omega
    subst q
    simp
