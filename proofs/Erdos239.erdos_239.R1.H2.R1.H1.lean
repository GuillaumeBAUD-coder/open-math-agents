import OMAReductions.R_Erdos239_erdos_239_R1_H2_R1
import Mathlib

open Finset Real

theorem OMA.solution : OMA.R_Erdos239_erdos_239_R1_H2_R1.H1 := by
  classical
  intro f hf hdiv T B
  let g (p : Nat.Primes) (t : ℝ) := (1 - f p * cos (t * log p.val)) / p.val
  have hpos (p : Nat.Primes) (t : ℝ) : 0 ≤ g p t := by
    have hp := hf p p.property.one_le
    have hb : |f p * cos (t * log p.val)| ≤ 1 := by
      rw [abs_mul]
      exact mul_le_one₀ hp (abs_nonneg _) (abs_cos_le_one _)
    exact div_nonneg (sub_nonneg.mpr ((le_abs_self _).trans hb)) (Nat.cast_nonneg _)
  let U (S : Finset Nat.Primes) := {t : ℝ | B < ∑ p ∈ S, g p t}
  have hmono : Monotone U := by
    intro S R h t ht
    exact lt_of_lt_of_le ht (sum_le_sum_of_subset_of_nonneg h (fun p _ _ => hpos p t))
  apply isCompact_Icc.elim_directed_cover U
  · intro S
    apply isOpen_lt continuous_const
    apply continuous_finset_sum
    intro p _
    dsimp [g]
    fun_prop
  · intro t _
    apply Set.mem_iUnion.mpr
    by_contra! h
    apply hdiv t
    apply summable_of_sum_le (fun p => hpos p t) (c := B)
    intro S
    exact le_of_not_gt (h S)
  · exact hmono.directed_le
