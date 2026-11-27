import OMAReductions.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1
import Mathlib.NumberTheory.LSeries.ZetaZeros

-- Credit: @marcusbuffett
namespace OMA.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1_H1_R1

/-- Existence of one nonreal critical-strip zero. -/
def H1 : Prop := ∃ w : ℂ, 0 < w.re ∧ w.re < 1 ∧ w.im ≠ 0 ∧ riemannZeta w = 0

/-- The reflection symmetry from the zeta functional equation. -/
def H2 : Prop := ∀ w : ℂ, 0 < w.re → w.re < 1 → w.im ≠ 0 →
  riemannZeta w = 0 → riemannZeta (1 - w) = 0

theorem main : H1 → H2 → OMA.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1.H1 := by
  intro hex reflectZero
  obtain ⟨a,ha,ha',hai,haz⟩ := hex
  let S : Set ℂ := {z | 0 < z.re ∧ z.re < 1 ∧ z.im ≠ 0 ∧
    |z.im| ≤ |a.im| ∧ riemannZeta z = 0}
  have fin : S.Finite := by
    apply (isCompact_closedBall (0 : ℂ) (1 + |a.im|)).inter_riemannZetaZeros_finite.subset
    intro z hz
    obtain ⟨hp,hu,_,hb,hzero⟩ := hz
    refine ⟨?_, hzero⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (Complex.norm_le_abs_re_add_abs_im z).trans (by rw [abs_of_pos hp]; linarith)
  obtain ⟨b,hb,hm⟩ := Set.exists_min_image S (fun z => |z.im|) fin
    ⟨a,ha,ha',hai,le_rfl,haz⟩
  obtain ⟨bp,bu,bi,bb,bz⟩ := hb
  have orient : ∃ w : ℂ, 1/2 ≤ w.re ∧ w.re < 1 ∧ |w.im| = |b.im| ∧ riemannZeta w = 0 := by
    by_cases h : 1/2 ≤ b.re
    · exact ⟨b,h,bu,rfl,bz⟩
    · refine ⟨1-b, ?_, ?_, ?_, reflectZero b bp bu bi bz⟩ <;> simp <;> linarith
  obtain ⟨w,wl,wu,wi,wz⟩ := orient
  have hi : w.im ≠ 0 := by simpa [abs_eq_zero] using (wi.trans_ne (abs_ne_zero.mpr bi))
  refine ⟨w / 2, ?_, ?_, ?_, ?_⟩
  · simp [Complex.div_ofNat_re]; linarith
  · simpa [Complex.div_ofNat_im] using hi
  · convert wz using 2 <;> ring
  · intro hz
    have half : |(w / 2).im| < |b.im| := by
      rw [Complex.div_ofNat_im, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2), wi]
      linarith [abs_pos.mpr bi]
    have mem : w/2 ∈ S := by
      refine ⟨?_, ?_, ?_, half.le.trans bb, hz⟩
      · rw [Complex.div_ofNat_re]; linarith
      · rw [Complex.div_ofNat_re]; linarith
      · simpa [Complex.div_ofNat_im] using hi
    exact (not_lt_of_ge (hm _ mem)) half

end OMA.R_Erdos969_erdos_969_variants_evelyn_linfoot_R1_H1_R1
