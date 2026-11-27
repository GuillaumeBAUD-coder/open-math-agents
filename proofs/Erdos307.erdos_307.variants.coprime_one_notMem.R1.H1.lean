import OMAReductions.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1
import Mathlib.Tactic

/-!
Proof of hypothesis `H1` for reduction `Erdos307.erdos_307.variants.coprime_one_notMem.R1`:
- Clearing denominators expresses `(∏ a ∈ A, a) * (∑ a ∈ A, a⁻¹)` as the cofactor sum `∑ a ∈ A, (∏ x ∈ A, x) / a`.
- Inserting a positive element `w ∉ A` updates the cofactor sum as `w * M' + M`.
-/

-- Step Erdos307.erdos_307.variants.coprime_one_notMem.R1.H1: hypothesis H1 of reduction Erdos307.erdos_307.variants.coprime_one_notMem.R1
-- Credit: @kenharimadesu

theorem OMA.solution : OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1.H1 := by
  intro A hA
  constructor
  · rw [Finset.mul_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl ?_
    intro a ha
    have ha_pos : 0 < a := hA a ha
    have ha_ne : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha_pos.ne'
    have hdvd : a ∣ ∏ x ∈ A, x := Finset.dvd_prod_of_mem (fun x => x) ha
    have hmul : (∏ x ∈ A, x) / a * a = ∏ x ∈ A, x := Nat.div_mul_cancel hdvd
    have hmulQ : (((∏ x ∈ A, x) / a : ℕ) : ℚ) * (a : ℚ) = ∏ x ∈ A, (x : ℚ) := by
      rw [← Nat.cast_mul, hmul, Nat.cast_prod]
    rw [← hmulQ, mul_inv_cancel_right₀ ha_ne]
  · intro w hw hwA
    rw [Finset.sum_insert hwA, Finset.prod_insert hwA, Nat.mul_div_cancel_left _ hw]
    have hsum :
        ∑ a ∈ A, (w * ∏ x ∈ A, x) / a = w * ∑ a ∈ A, (∏ x ∈ A, x) / a := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro a ha
      exact Nat.mul_div_assoc w (Finset.dvd_prod_of_mem (fun x => x) ha)
    rw [hsum, Nat.add_comm]
