import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R3_H2_R1
import Mathlib

/-!
Transfer of 4-term progressions from `ZMod M` back to the integers when `M > 2 N`.
Lift the four terms to `a₀, a₁, a₂, a₃ ∈ S ⊆ [1, N]`. Consecutive differences agree modulo `M` and
differ by less than `M` in absolute value, so they agree as integers. A positive common difference
gives a progression in `S`, a negative one gives the reversed progression, and zero gives `s = 0`.
-/

namespace OMA

theorem transfer4 : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R3_H2_R1.H2 := by
  intro M N S hM hS hfree t s h
  have get : ∀ j : ℕ, j < 4 → ∃ a ∈ S, (a : ZMod M) = t + (j : ZMod M) * s := by
    intro j hj
    obtain ⟨a, ha, e⟩ := Finset.mem_image.mp (h j hj)
    exact ⟨a, ha, e⟩
  obtain ⟨a0, ha0, e0⟩ := get 0 (by norm_num)
  obtain ⟨a1, ha1, e1⟩ := get 1 (by norm_num)
  obtain ⟨a2, ha2, e2⟩ := get 2 (by norm_num)
  obtain ⟨a3, ha3, e3⟩ := get 3 (by norm_num)
  have b0 := Finset.mem_Icc.mp (hS ha0)
  have b1 := Finset.mem_Icc.mp (hS ha1)
  have b2 := Finset.mem_Icc.mp (hS ha2)
  have b3 := Finset.mem_Icc.mp (hS ha3)
  push_cast at e0 e1 e2 e3
  have zero_of : ∀ x : ℤ, (x : ZMod M) = 0 → |x| < (M : ℤ) → x = 0 := by
    intro x hx hlt
    exact Int.eq_zero_of_abs_lt_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd x M).mp hx) hlt
  have hx : ((a1 : ℤ) - a0) - ((a2 : ℤ) - a1) = 0 := by
    apply zero_of
    · push_cast
      rw [e0, e1, e2]
      ring
    · rw [abs_lt]
      constructor <;> omega
  have hy : ((a2 : ℤ) - a1) - ((a3 : ℤ) - a2) = 0 := by
    apply zero_of
    · push_cast
      rw [e1, e2, e3]
      ring
    · rw [abs_lt]
      constructor <;> omega
  have hs : (((a1 : ℤ) - a0 : ℤ) : ZMod M) = s := by
    push_cast
    rw [e0, e1]
    ring
  rcases lt_trichotomy (a0 : ℤ) (a1 : ℤ) with hlt | heq | hgt
  · exfalso
    apply hfree
    refine ⟨a0, a1 - a0, by omega, ?_⟩
    intro i hi
    interval_cases i
    · simpa using ha0
    · have e : a0 + 1 * (a1 - a0) = a1 := by omega
      rw [e]; exact ha1
    · have e : a0 + 2 * (a1 - a0) = a2 := by omega
      rw [e]; exact ha2
    · have e : a0 + 3 * (a1 - a0) = a3 := by omega
      rw [e]; exact ha3
  · rw [← hs]
    have e : (a1 : ℤ) - a0 = 0 := by omega
    rw [e]
    simp
  · exfalso
    apply hfree
    refine ⟨a3, a0 - a1, by omega, ?_⟩
    intro i hi
    interval_cases i
    · simpa using ha3
    · have e : a3 + 1 * (a0 - a1) = a2 := by omega
      rw [e]; exact ha2
    · have e : a3 + 2 * (a0 - a1) = a1 := by omega
      rw [e]; exact ha1
    · have e : a3 + 3 * (a0 - a1) = a0 := by omega
      rw [e]; exact ha0

end OMA

theorem OMA.solution : OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H1_R3_H2_R1.H2 :=
  OMA.transfer4
