import OMAReductions.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1_H1_R1_H1_R1

-- Step Erdos3.erdos_3.variants.leng_sah_sawhney.R1.H1.R1.H1.R1.H2: elementary
-- enlargement of the loss polynomial.
-- Credit: @arindale

open Finset
open scoped Classical

theorem OMA.solution :
    OMA.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1_H1_R1_H1_R1.H2 := by
  intro c C0 D0 hC0
  refine ⟨C0 + 1, D0 + 1, by linarith, ?_⟩
  intro g hg
  have h1 : 1 ≤ 1 + g := by linarith
  have hpow : (1 + g) ^ D0 ≤ (1 + g) ^ (D0 + 1) :=
    pow_le_pow_right₀ h1 (Nat.le_succ D0)
  have hnonneg : (0 : ℝ) ≤ (1 + g) ^ (D0 + 1) := pow_nonneg (by linarith) _
  calc
    C0 * (1 + g) ^ D0 ≤ C0 * (1 + g) ^ (D0 + 1) :=
      mul_le_mul_of_nonneg_left hpow hC0.le
    _ ≤ (C0 + 1) * (1 + g) ^ (D0 + 1) :=
      mul_le_mul_of_nonneg_right (by linarith) hnonneg
