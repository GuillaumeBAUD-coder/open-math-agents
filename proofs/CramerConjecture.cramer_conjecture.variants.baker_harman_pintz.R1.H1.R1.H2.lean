import OMAReductions.R_CramerConjecture_cramer_conjecture_variants_baker_harman_pintz_R1_H1_R1
import Mathlib

open Finset ArithmeticFunction
open OMA.R_CramerConjecture_cramer_conjecture_variants_baker_harman_pintz_R1

theorem OMA.solution : OMA.R_CramerConjecture_cramer_conjecture_variants_baker_harman_pintz_R1_H1_R1.H2 := by
  intro a h
  let b := a+2*h
  let S := Ico (a+h-h/2) (a+h+h/2)
  rw [truncate_sum (N := b) le_rfl, truncate_sum (N := b) (by omega),
    truncate_sum (n := a) (N := b) (by omega), mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  let W (k : ℕ) := max ((b : ℝ)-k) 0 - 2 * max (((a+h:ℕ) : ℝ)-k) 0 + max ((a:ℝ)-k) 0
  have pos (k : ℕ) : 0 ≤ W k := by
    dsimp [W,b]
    push_cast
    have := Nat.cast_nonneg (α := ℝ) h
    simp only [max_def]
    split_ifs <;> linarith
  have sub : S ⊆ range b := by
    intro k hk
    obtain ⟨_,hk'⟩ := mem_Ico.mp hk
    exact mem_range.mpr (by dsimp [b]; omega)
  calc
    _ ≤ ∑ k ∈ S, (Λ k : ℝ) * W k := by
      apply sum_le_sum
      intro k hk
      obtain ⟨lo,hi⟩ := mem_Ico.mp hk
      have l : 2*a+h ≤ 2*k := by omega
      have u : 2*k ≤ 2*a+3*h := by omega
      have lr : 2*(a:ℝ)+h ≤ 2*k := by exact_mod_cast l
      have ur : 2*(k:ℝ) ≤ 2*a+3*h := by exact_mod_cast u
      have weight : (h:ℝ)/2 ≤ W k := by
        dsimp [W,b]
        push_cast
        simp only [max_def]
        split_ifs <;> linarith
      simpa [mul_comm] using mul_le_mul_of_nonneg_left weight (vonMangoldt_nonneg (n := k))
    _ ≤ ∑ k ∈ range b, (Λ k : ℝ) * W k :=
      sum_le_sum_of_subset_of_nonneg sub (fun k _ _ => mul_nonneg vonMangoldt_nonneg (pos k))
    _ = _ := by apply sum_congr rfl; intro k _; dsimp [W]; ring
