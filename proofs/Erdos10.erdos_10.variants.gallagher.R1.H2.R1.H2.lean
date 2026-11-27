import OMAReductions.R_Erdos10_erdos_10_variants_gallagher_R1_H2_R1
import Mathlib

-- Step Erdos10.erdos_10.variants.gallagher.R1.H2.R1.H2: hypothesis H2 of reduction Erdos10.erdos_10.variants.gallagher.R1.H2.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Finset

/-! Expand the square. Each diagonal term is at most M^2 at every j < N. For an off-diagonal pair
with shifts a ≤ b, the product vanishes unless b ≤ j, and the substitution i = j - b bounds
its sum by the sum over i < N of v i * v (i + (b - a)). -/

theorem OMA.solution : OMA.R_Erdos10_erdos_10_variants_gallagher_R1_H2_R1.H2 := by
  intro v s N Q M hv hM hvM
  set f : ℕ → ℕ → ℝ := fun a j => if a ≤ j then v (j - a) else 0 with hf
  have f_nn : ∀ a j, 0 ≤ f a j := by
    intro a j; simp only [hf]; split_ifs
    · exact hv _
    · exact le_rfl
  have f_le : ∀ a j, j < N → f a j ≤ M := by
    intro a j hj; simp only [hf]; split_ifs with h
    · exact hvM _ (by omega)
    · exact hM
  have shift : ∀ a b : ℕ, a ≤ b →
      ∑ j ∈ range N, f a j * f b j ≤ ∑ j ∈ range N, v j * v (j + (b - a)) := by
    intro a b hab
    have e : ∀ j, f a j * f b j =
        if b ≤ j then v (j - b) * v (j - b + (b - a)) else 0 := by
      intro j
      by_cases hb : b ≤ j
      · have ha : a ≤ j := le_trans hab hb
        simp only [hf, if_pos ha, if_pos hb]
        rw [show j - a = j - b + (b - a) by omega]
        ring
      · simp [hf, hb]
    simp only [e]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have hfil : (range N).filter (fun j => b ≤ j) = Ico b N := by
      ext j; simp only [mem_filter, mem_range, mem_Ico]; omega
    rw [hfil, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    apply Finset.sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (Nat.sub_le N b))
    intro i _ _
    exact mul_nonneg (hv _) (hv _)
  have diag : ∀ a, ∑ j ∈ range N, f a j * f a j ≤ N * M^2 := by
    intro a
    calc ∑ j ∈ range N, f a j * f a j ≤ ∑ j ∈ range N, M^2 := by
          apply Finset.sum_le_sum
          intro j hj
          rw [← sq]
          exact pow_le_pow_left₀ (f_nn a j) (f_le a j (mem_range.mp hj)) 2
      _ = N * M^2 := by rw [Finset.sum_const, card_range, nsmul_eq_mul]
  have off : ∀ a b, ∑ j ∈ range N, f a j * f b j ≤ ∑ j ∈ range N, v j * v (j + Nat.dist a b) := by
    intro a b
    rcases le_total a b with h | h
    · rw [Nat.dist_eq_sub_of_le h]
      exact shift a b h
    · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h]
      simp only [mul_comm (f a _) (f b _)]
      exact shift b a h
  calc (∑ j ∈ range N, (∑ t ∈ Q, f (s t) j)^2)
      = ∑ j ∈ range N, ∑ t ∈ Q, ∑ u ∈ Q, f (s t) j * f (s u) j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [sq, Finset.sum_mul_sum]
    _ = ∑ t ∈ Q, ∑ u ∈ Q, ∑ j ∈ range N, f (s t) j * f (s u) j := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro t _
        rw [Finset.sum_comm]
    _ = ∑ t ∈ Q, (∑ j ∈ range N, f (s t) j * f (s t) j +
          ∑ u ∈ Q.erase t, ∑ j ∈ range N, f (s t) j * f (s u) j) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact (Finset.add_sum_erase Q (fun u => ∑ j ∈ range N, f (s t) j * f (s u) j) ht).symm
    _ ≤ ∑ t ∈ Q, (N * M^2 + ∑ u ∈ Q.erase t, ∑ j ∈ range N, v j * v (j + Nat.dist (s t) (s u))) := by
        apply Finset.sum_le_sum
        intro t _
        exact add_le_add (diag _) (Finset.sum_le_sum fun u _ => off _ _)
    _ = N*Q.card*M^2 + ∑ t ∈ Q, ∑ u ∈ Q.erase t, ∑ j ∈ range N, v j*v (j+Nat.dist (s t) (s u)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        ring
