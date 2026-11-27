import OMAReductions.R_OeisA262813_conjecture_2_R1

-- Step OeisA262813.conjecture_2.R1.H1: hypothesis H1 of reduction OeisA262813.conjecture_2.R1
-- Credit: @sebastianbachmaier
-- H1 := ∀ n : ℕ, n ∈ ({1, 9, 21, 35, 98, 152, 306} : Finset ℕ) → OeisA262813.a n = 1  /-- The open direction: count one happens only at the seven listed indices. -/

namespace OMAStepA262813

lemma tri_mono {a b : ℕ} (h : a ≤ b) : Nat.triangular a ≤ Nat.triangular b := by
  unfold Nat.triangular
  exact Nat.div_le_div_right (Nat.mul_le_mul h (Nat.add_le_add_right h 1))

lemma trunc (n X Y Z : ℕ) (hX : X ≤ n + 1) (hY : Y ≤ n + 1) (hZ : Z ≤ n + 1)
    (hX' : n < X ^ 3) (hY' : n < Y ^ 2) (hZ' : n < Nat.triangular Z) :
    OeisA262813.a n = ∑ x ∈ Finset.range X, ∑ y ∈ Finset.range Y, ∑ z ∈ Finset.Ico 1 Z,
      (if x ^ 3 + y ^ 2 + Nat.triangular z == n then 1 else 0) := by
  unfold OeisA262813.a
  have h1 : ∀ x y : ℕ, (∑ z ∈ Finset.Ico 1 (n + 1),
      (if x ^ 3 + y ^ 2 + Nat.triangular z == n then 1 else 0)) =
      ∑ z ∈ Finset.Ico 1 Z, (if x ^ 3 + y ^ 2 + Nat.triangular z == n then 1 else 0) := by
    intro x y
    symm
    apply Finset.sum_subset (Finset.Ico_subset_Ico_right hZ)
    intro z hz1 hz
    simp only [Finset.mem_Ico, not_and, not_lt] at hz hz1
    rw [if_neg]
    intro h
    rw [beq_iff_eq] at h
    have := tri_mono (hz hz1.1)
    omega
  simp_rw [h1]
  have h2 : ∀ x : ℕ, (∑ y ∈ Finset.range (n + 1), ∑ z ∈ Finset.Ico 1 Z,
      (if x ^ 3 + y ^ 2 + Nat.triangular z == n then 1 else 0)) =
      ∑ y ∈ Finset.range Y, ∑ z ∈ Finset.Ico 1 Z,
      (if x ^ 3 + y ^ 2 + Nat.triangular z == n then 1 else 0) := by
    intro x
    symm
    apply Finset.sum_subset (Finset.range_subset_range.mpr hY)
    intro y _ hy
    simp only [Finset.mem_range, not_lt] at hy
    apply Finset.sum_eq_zero
    intro z _
    rw [if_neg]
    intro h
    rw [beq_iff_eq] at h
    have := Nat.pow_le_pow_left hy 2
    omega
  simp_rw [h2]
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr hX)
  intro x _ hx
  simp only [Finset.mem_range, not_lt] at hx
  apply Finset.sum_eq_zero
  intro y _
  apply Finset.sum_eq_zero
  intro z _
  rw [if_neg]
  intro h
  rw [beq_iff_eq] at h
  have := Nat.pow_le_pow_left hx 3
  omega

end OMAStepA262813

theorem OMA.solution : OMA.R_OeisA262813_conjecture_2_R1.H1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [OMAStepA262813.trunc 1 2 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide)]
    decide +kernel
  · rw [OMAStepA262813.trunc 9 3 4 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide)]
    decide +kernel
  · rw [OMAStepA262813.trunc 21 3 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide)]
    decide +kernel
  · rw [OMAStepA262813.trunc 35 4 6 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide)]
    decide +kernel
  · rw [OMAStepA262813.trunc 98 5 10 14 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide)]
    decide +kernel
  · rw [OMAStepA262813.trunc 152 6 13 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide)]
    decide +kernel
  · rw [OMAStepA262813.trunc 306 7 18 25 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide)]
    decide +kernel
