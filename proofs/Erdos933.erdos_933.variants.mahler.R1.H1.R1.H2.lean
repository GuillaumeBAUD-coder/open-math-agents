import OMAReductions.R_Erdos933_erdos_933_variants_mahler_R1_H1_R1
import Mathlib

-- Step Erdos933.erdos_933.variants.mahler.R1.H1.R1.H2: hypothesis H2 of reduction Erdos933.erdos_933.variants.mahler.R1.H1.R1
-- Credit: @ivillar. Two distinct points (n, n+1), (m, m+1) of W give (n - m, 0) and then (1, 0), (0, 1) in W, so W = ⊤; hence a proper W meets the line in at most one point.

/-! Step Erdos933.erdos_933.variants.mahler.R1.H1.R1.H2. -/

theorem P8Erdos933.line_finite : ∀ W : Submodule ℚ (ℚ × ℚ), W ≠ ⊤ →
    {n : ℕ | ((n : ℚ), (n : ℚ) + 1) ∈ W}.Finite := by
  intro W hW
  apply Set.Subsingleton.finite
  intro n hn m hm
  by_contra hnm
  apply hW
  have hn' : ((n : ℚ), (n : ℚ) + 1) ∈ W := hn
  have hm' : ((m : ℚ), (m : ℚ) + 1) ∈ W := hm
  have hnm' : (n : ℚ) - m ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hnm)
  have h10 : ((1 : ℚ), (0 : ℚ)) ∈ W := by
    have h1 := W.sub_mem (W.smul_mem ((m : ℚ) + 1) hn') (W.smul_mem ((n : ℚ) + 1) hm')
    have e : ((m : ℚ) + 1) • ((n : ℚ), (n : ℚ) + 1) - ((n : ℚ) + 1) • ((m : ℚ), (m : ℚ) + 1) =
        ((n : ℚ) - m, 0) := by
      simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_sub_mk, Prod.mk.injEq]
      constructor <;> ring
    rw [e] at h1
    have h2 := W.smul_mem ((n : ℚ) - m)⁻¹ h1
    have e2 : ((n : ℚ) - m)⁻¹ • ((n : ℚ) - m, (0 : ℚ)) = (1, 0) := by
      simp only [Prod.smul_mk, smul_eq_mul, mul_zero, inv_mul_cancel₀ hnm']
    rw [e2] at h2
    exact h2
  have h01 : ((0 : ℚ), (1 : ℚ)) ∈ W := by
    have h1 := W.sub_mem hn' (W.smul_mem (n : ℚ) h10)
    have e : ((n : ℚ), (n : ℚ) + 1) - (n : ℚ) • ((1 : ℚ), (0 : ℚ)) = (0, (n : ℚ) + 1) := by
      simp only [Prod.smul_mk, smul_eq_mul, Prod.mk_sub_mk, Prod.mk.injEq]
      constructor <;> ring
    rw [e] at h1
    have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
    have h2 := W.smul_mem ((n : ℚ) + 1)⁻¹ h1
    have e2 : ((n : ℚ) + 1)⁻¹ • ((0 : ℚ), (n : ℚ) + 1) = (0, 1) := by
      simp only [Prod.smul_mk, smul_eq_mul, mul_zero, inv_mul_cancel₀ hn1]
    rw [e2] at h2
    exact h2
  rw [eq_top_iff]
  rintro ⟨a, b⟩ -
  have e : ((a, b) : ℚ × ℚ) = a • ((1 : ℚ), (0 : ℚ)) + b • ((0 : ℚ), (1 : ℚ)) := by
    simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, Prod.mk_add_mk, add_zero, zero_add]
  rw [e]
  exact W.add_mem (W.smul_mem a h10) (W.smul_mem b h01)

theorem OMA.solution : OMA.R_Erdos933_erdos_933_variants_mahler_R1_H1_R1.H2 :=
  P8Erdos933.line_finite
