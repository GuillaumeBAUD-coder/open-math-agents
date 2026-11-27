import OMAReductions.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1
import Mathlib.Data.Finset.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Leng, Sah and Sawhney, arXiv:2402.17995, Section 3.2, gives a
quantitative trichotomy for bounded functions on an interval. The first
hypothesis is its indicator-function specialization, using the count
of ordered start and difference pairs in `{0, ..., N}`. The second is
the elementary discrepancy between an AP-free set and its constant-density
model once the interval is large relative to the density.
-/

namespace OMA.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1_H1_R1

open Finset
open scoped Classical

private theorem no_positive_progression {A : Finset ℕ} {k a d : ℕ}
    (hfree : (A : Set ℕ).IsAPOfLengthFree k) (hk : 2 ≤ k) (hd : 0 < d)
    (hmem : ∀ i < k, a + i * d ∈ A) : False := by
  classical
  let T := (range k).image (fun i : ℕ => a + i * d)
  have hinj : Function.Injective (fun i : ℕ => a + i * d) := by
    intro i j he
    exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel he)
  have hcard : T.card = k := by
    simp only [T, card_image_of_injective _ hinj, card_range]
  have hsubset : (T : Set ℕ) ⊆ A := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    exact hmem i (mem_range.mp hi)
  have hp : (T : Set ℕ).IsAPOfLength k := by
    refine ⟨a, d, ?_, ?_⟩
    · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard, hcard]
    · ext x
      constructor
      · intro hx
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
        exact ⟨i, by exact_mod_cast (mem_range.mp hi), by simp⟩
      · rintro ⟨i, hi, rfl⟩
        exact mem_image.mpr ⟨i, mem_range.mpr (by exact_mod_cast hi), by simp⟩
  have h : k ≤ 1 := by exact_mod_cast hfree (T : Set ℕ) hsubset hp
  omega

private theorem free_affine_restriction {A : Finset ℕ} {k a d M : ℕ}
    (hfree : (A : Set ℕ).IsAPOfLengthFree k) (hd : 0 < d) :
    (((Icc 1 M).filter (fun i => a + (i - 1) * d ∈ A) : Finset ℕ) : Set ℕ).IsAPOfLengthFree k := by
  intro T hT hprogression
  by_contra! hlength
  have hk : 2 ≤ k := by exact_mod_cast hlength
  obtain ⟨first, diff, hcard, hset⟩ := hprogression
  have hdiff : 0 < diff := by
    by_contra! hzero
    have hz : diff = 0 := by omega
    have hsingle : T = {first} := by
      rw [hset, hz]
      ext x
      simp only [nsmul_zero, add_zero, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, hi, rfl⟩
        rfl
      · rintro rfl
        exact ⟨0, by exact_mod_cast (show 0 < k by omega), rfl⟩
    rw [hsingle] at hcard
    have hone : (k : ℕ∞) = 1 := by simpa using hcard.symm
    exact hlength.not_ge hone.le
  have hfirst : 1 ≤ first := by
    have ht : first ∈ T := by
      rw [hset]
      exact ⟨0, by exact_mod_cast (show 0 < k by omega), by simp⟩
    exact (mem_Icc.mp (mem_filter.mp (hT ht)).1).1
  apply no_positive_progression hfree hk (Nat.mul_pos hdiff hd)
    (a := a + (first - 1) * d)
  intro i hi
  have ht : first + i * diff ∈ T := by
    rw [hset]
    exact ⟨i, by exact_mod_cast hi, by simp⟩
  have hm := (mem_filter.mp (hT ht)).2
  have hshift : first + i * diff - 1 = (first - 1) + i * diff := by omega
  rw [hshift] at hm
  convert hm using 1
  ring

private theorem gap_drop_of_density_gain {N A M B gain : ℝ}
    (hN : 0 < N) (hA : 0 < A) (hM : 0 < M) (hB : 0 < B)
    (hgain : 0 < gain) (increase : gain * (A / N) ≤ B / M) :
    Real.log (M / B) ≤ Real.log (N / A) - Real.log gain := by
  have h := one_div_le_one_div_of_le (mul_pos hgain (div_pos hA hN)) increase
  have hl : 1 / (B / M) = M / B := one_div_div _ _
  have hr : 1 / (gain * (A / N)) = (N / A) / gain := by
    field_simp
  rw [hl, hr] at h
  have hb := Real.log_le_log (div_pos hM hB) h
  rwa [Real.log_div (div_ne_zero hN.ne' hA.ne') hgain.ne'] at hb

private theorem log_log_loss_of_progression_length {N M loss : ℝ}
    (hN : 1 < N) (hsize : N ^ Real.exp (-loss) ≤ M) :
    Real.log (Real.log N) ≤ Real.log (Real.log M) + loss := by
  have hn : 0 < N := zero_lt_one.trans hN
  have hfirst := Real.log_le_log (Real.rpow_pos_of_pos hn _) hsize
  rw [Real.log_rpow hn] at hfirst
  have hsecond := Real.log_le_log (mul_pos (Real.exp_pos _) (Real.log_pos hN)) hfirst
  rw [Real.log_mul (Real.exp_pos _).ne' (Real.log_pos hN).ne', Real.log_exp] at hsecond
  linarith

private theorem progression_length_ge_three {N M loss : ℝ}
    (hN : 1 < N)
    (large : Real.log (Real.log N) > Real.log (Real.log 3) + loss)
    (hsize : N ^ Real.exp (-loss) ≤ M) : 3 < M := by
  have hn : 0 < N := zero_lt_one.trans hN
  have hlogThree : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlarge : -loss + Real.log (Real.log N) > Real.log (Real.log 3) := by
    linarith
  rw [← Real.log_exp (-loss), ← Real.log_mul (Real.exp_pos _).ne' (Real.log_pos hN).ne'] at hlarge
  have hprod : Real.log 3 < Real.exp (-loss) * Real.log N :=
    (Real.log_lt_log_iff hlogThree (mul_pos (Real.exp_pos _) (Real.log_pos hN))).mp hlarge
  rw [← Real.log_rpow hn] at hprod
  exact ((Real.log_lt_log_iff (by norm_num) (Real.rpow_pos_of_pos hn _)).mp hprod).trans_le hsize

private theorem level_of_terminal_bound {N loss : ℝ}
    (hN : 1 < N) (hsmall : N ≤ Real.exp (Real.exp loss)) :
    Real.log (Real.log N) ≤ loss := by
  have hfirst := Real.log_le_log (zero_lt_one.trans hN) hsmall
  rw [Real.log_exp] at hfirst
  have hsecond := Real.log_le_log (Real.log_pos hN) hfirst
  rwa [Real.log_exp] at hsecond

private theorem count_threshold_from_log {N density : ℝ} {k : ℕ}
    (hN : 0 < N) (hdensity : 0 < density) (hk : 0 < k)
    (large : Real.log (128 * (k : ℝ)) + ((k - 1 : ℕ) : ℝ) * Real.log density⁻¹ ≤ Real.log N) :
    128 * (k : ℝ) ≤ N * density ^ (k - 1) := by
  have hK : 0 < (k : ℝ) := by exact_mod_cast hk
  apply (Real.log_le_log_iff (by positivity) (mul_pos hN (pow_pos hdensity _))).mp
  rw [Real.log_mul hN.ne' (pow_ne_zero _ hdensity.ne'), Real.log_pow]
  rw [Real.log_inv] at large
  linarith only [large]

private theorem enlarge_loss_polynomial {C slope offset gap : ℝ} (D : ℕ)
    (hC : 0 ≤ C) (hslope : 0 ≤ slope) (hoffset : 0 ≤ offset) (hgap : 0 ≤ gap) :
    C * (1 + gap) ^ D + slope * gap + offset ≤
      (C + slope + offset) * (1 + gap) ^ (D + 1) := by
  have hbase : 1 ≤ 1 + gap := by linarith
  have hone : 1 ≤ (1 + gap) ^ (D + 1) := one_le_pow₀ hbase
  have hpow : (1 + gap) ^ D ≤ (1 + gap) ^ (D + 1) :=
    pow_le_pow_right₀ hbase (Nat.le_succ _)
  have hgap' : gap ≤ (1 + gap) ^ (D + 1) := by
    calc
      gap ≤ 1 + gap := by linarith
      _ = (1 + gap) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hbase (by omega)
  calc
    _ ≤ C * (1 + gap) ^ (D + 1) + slope * (1 + gap) ^ (D + 1) +
        offset * (1 + gap) ^ (D + 1) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hpow hC)
        (mul_le_mul_of_nonneg_left hgap' hslope))
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hone hoffset)
    _ = _ := by ring

/-- The finite trichotomy for indicator functions of sets in an interval. -/
def H1 : Prop := ∀ k : ℕ, 5 ≤ k →
  ∃ gain C : ℝ, 1 < gain ∧ 0 < C ∧ ∃ D : ℕ,
    ∀ (N : ℕ) (A : Finset ℕ), 3 ≤ N → 0 < A.card → A ⊆ Icc 1 N →
      let count (B : Finset ℕ) :=
        ((range (N + 1) ×ˢ range (N + 1)).filter
          (fun p => ∀ i < k, p.1 + i * p.2 ∈ B)).card
      let δ := (A.card : ℝ) / N
      let loss := C * (1 + Real.log ((N : ℝ) / A.card)) ^ D
      let total := ((N : ℝ) + 1) ^ 2
      (N : ℝ) ≤ Real.exp (Real.exp loss) ∨
        |(count A : ℝ) / total - δ ^ k * count (Icc 1 N) / total| ≤ δ ^ k / (256 * k) ∨
        ∃ a d M : ℕ, 0 < d ∧
          (∀ i ∈ Icc 1 M, a + (i - 1) * d ∈ Icc 1 N) ∧
          (N : ℝ) ^ Real.exp (-loss) ≤ (M : ℝ) ∧
          gain * δ ≤ (((Icc 1 M).filter (fun i => a + (i - 1) * d ∈ A)).card : ℝ) / M

/-- Diagonal progressions in a free set are separated from the interval model. -/
def H2 : Prop := ∀ (N k : ℕ) (A : Finset ℕ), 2 ≤ k → 2 * k ≤ N →
  A ⊆ Icc 1 N → (A : Set ℕ).IsAPOfLengthFree k →
  let count (B : Finset ℕ) :=
    ((range (N + 1) ×ˢ range (N + 1)).filter
      (fun p => ∀ i < k, p.1 + i * p.2 ∈ B)).card
  let δ := (A.card : ℝ) / N
  let total := ((N : ℝ) + 1) ^ 2
  128 * (k : ℝ) ≤ N * δ ^ (k - 1) →
    δ ^ k / (128 * (k : ℝ)) ≤
      |(count A : ℝ) / total - δ ^ k * count (Icc 1 N) / total|

theorem main : H1 → H2 → OMA.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1.H1 := by
  intro trichotomy separation k hk
  obtain ⟨gain, C, hgain, hC, D, advance⟩ := trichotomy k hk
  have hkpos : 0 < k := by omega
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hkpos
  let slope : ℝ := ((k - 1 : ℕ) : ℝ)
  let offset := max (Real.log (128 * (k : ℝ))) 0 + max (Real.log (Real.log 3)) 0
  have hslope : 0 ≤ slope := Nat.cast_nonneg _
  have hoffset : 0 ≤ offset := add_nonneg (le_max_right _ _) (le_max_right _ _)
  have hcountOffset : Real.log (128 * (k : ℝ)) ≤ offset :=
    (le_max_left _ _).trans (le_add_of_nonneg_right (le_max_right _ _))
  have hlengthOffset : Real.log (Real.log 3) ≤ offset :=
    (le_max_left _ _).trans (le_add_of_nonneg_left (le_max_right _ _))
  refine ⟨Real.log gain, C + slope + offset, Real.log_pos hgain,
    add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hC hslope) hoffset, D + 1,
    fun N A hN hApos hsub hfree => ?_⟩
  intro gap level
  let δ := (A.card : ℝ) / N
  let loss := C * (1 + gap) ^ D
  let budget := (C + slope + offset) * (1 + gap) ^ (D + 1)
  have hNgt : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hNpos : 0 < (N : ℝ) := zero_lt_one.trans hNgt
  have hAreal : 0 < (A.card : ℝ) := by exact_mod_cast hApos
  have hcard : A.card ≤ N := by simpa using card_le_card hsub
  have hcardReal : (A.card : ℝ) ≤ N := by exact_mod_cast hcard
  have hδpos : 0 < δ := div_pos hAreal hNpos
  have hδle : δ ≤ 1 := (div_le_iff₀ hNpos).mpr (by simpa using hcardReal)
  have hinv : δ⁻¹ = (N : ℝ) / A.card := by dsimp [δ]; rw [inv_div]
  have hgap : 0 ≤ gap :=
    Real.log_nonneg ((le_div_iff₀ hAreal).mpr (by simpa using hcardReal))
  have hloss : 0 ≤ loss := mul_nonneg hC.le (pow_nonneg (by linarith) _)
  have hbudget : loss + slope * gap + offset ≤ budget :=
    enlarge_loss_polynomial D hC.le hslope hoffset hgap
  change level ≤ budget ∨ _
  by_cases small : level ≤ budget
  · exact Or.inl small
  have large : budget < level := lt_of_not_ge small
  have hlossBudget : loss ≤ budget := by nlinarith [mul_nonneg hslope hgap]
  rcases advance N A hN hApos hsub with terminal | close | ⟨a, d, M, hd, -, hsize, increase⟩
  · exact (small ((level_of_terminal_bound hNgt terminal).trans hlossBudget)).elim
  · have hLogN : level ≤ Real.log (N : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (Real.log_pos hNgt)
      dsimp [level]
      linarith
    have hLogThreshold : Real.log (128 * (k : ℝ)) + slope * Real.log δ⁻¹ ≤ Real.log (N : ℝ) := by
      rw [hinv]
      change Real.log (128 * (k : ℝ)) + slope * gap ≤ _
      linarith
    have threshold := count_threshold_from_log hNpos hδpos hkpos hLogThreshold
    have hNlarge : 2 * k ≤ N := by
      have hp : δ ^ (k - 1) ≤ 1 := pow_le_one₀ hδpos.le hδle
      have h := threshold.trans (mul_le_of_le_one_right hNpos.le hp)
      exact_mod_cast (show 2 * (k : ℝ) ≤ N by linarith)
    have apart := separation N k A (show 2 ≤ k by omega) hNlarge hsub hfree threshold
    have hstrict : δ ^ k / (256 * (k : ℝ)) < δ ^ k / (128 * (k : ℝ)) := by
      apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
      exact mul_lt_mul_of_pos_left (by linarith) (pow_pos hδpos _)
    exact (not_lt_of_ge (apart.trans close) hstrict).elim
  · let B := (Icc 1 M).filter (fun i => a + (i - 1) * d ∈ A)
    have hLargeLength : Real.log (Real.log 3) + loss < level := by
      nlinarith [mul_nonneg hslope hgap]
    have hMgt : (3 : ℝ) < (M : ℝ) :=
      progression_length_ge_three hNgt hLargeLength hsize
    have hMpos : 0 < (M : ℝ) := by linarith
    have hBreal : 0 < (B.card : ℝ) :=
      (div_pos_iff_of_pos_right hMpos).mp ((mul_pos (zero_lt_one.trans hgain) hδpos).trans_le increase)
    have hBpos : 0 < B.card := by exact_mod_cast hBreal
    refine Or.inr ⟨M, B, (show 3 ≤ M by exact_mod_cast hMgt.le), hBpos,
      filter_subset _ _, free_affine_restriction hfree hd, ?_, ?_⟩
    · exact gap_drop_of_density_gain hNpos hAreal hMpos hBreal (zero_lt_one.trans hgain) increase
    · exact (log_log_loss_of_progression_length hNgt hsize).trans
        (add_le_add_right hlossBudget _)

end OMA.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1_H1_R1
