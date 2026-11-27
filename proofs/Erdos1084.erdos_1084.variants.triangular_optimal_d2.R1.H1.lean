import OMAReductions.R_Erdos1084_erdos_1084_variants_triangular_optimal_d2_R1

-- Step Erdos1084.erdos_1084.variants.triangular_optimal_d2.R1.H1: hypothesis H1 of reduction Erdos1084.erdos_1084.variants.triangular_optimal_d2.R1
-- Credit: @ivillar
-- Count the hexagonal patch row by row: the row y has 2n+1-|y| points, and summing over
-- |y| <= n gives (2n+1)^2 - n(n+1) = 3n^2+3n+1.

open Finset

lemma fiber_card (n : ℕ) (y : ℤ) (hy : y ∈ Icc (-(n:ℤ)) n) :
    (((Icc (-(n:ℤ)) n).filter (fun x => x + y ∈ Icc (-(n:ℤ)) n)).card : ℤ) = 2*n+1 - |y| := by
  have e : (Icc (-(n:ℤ)) n).filter (fun x => x + y ∈ Icc (-(n:ℤ)) n) =
      Icc (max (-(n:ℤ)) (-n - y)) (min (n:ℤ) (n - y)) := by
    ext x; simp only [mem_filter, mem_Icc, max_le_iff, le_min_iff]; omega
  rw [e, Int.card_Icc]
  simp only [mem_Icc] at hy
  rcases le_total 0 y with h | h
  · rw [abs_of_nonneg h]; omega
  · rw [abs_of_nonpos h]; omega

lemma abs_sum (n : ℕ) : ∑ y ∈ Icc (-(n:ℤ)) n, |y| = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have e : Icc (-((k+1 : ℕ):ℤ)) ((k+1 : ℕ):ℤ) =
        insert (-((k:ℤ)+1)) (insert ((k:ℤ)+1) (Icc (-(k:ℤ)) k)) := by
      ext x; simp only [mem_insert, mem_Icc]; push_cast; omega
    rw [e, sum_insert (by simp only [mem_insert, mem_Icc]; omega),
      sum_insert (by simp only [mem_Icc]; omega), ih]
    rw [abs_of_nonpos (by omega), abs_of_nonneg (by omega)]
    push_cast; ring

theorem OMA.solution : OMA.R_Erdos1084_erdos_1084_variants_triangular_optimal_d2_R1.H1 := by
  intro n interval patch
  have hc : (patch.card : ℤ) = ∑ y ∈ interval, (((interval.filter (fun x => x + y ∈ interval)).card : ℕ) : ℤ) := by
    have : patch.card = ∑ y ∈ interval, (interval.filter (fun x => x + y ∈ interval)).card := by
      simp only [patch, card_filter]
      rw [sum_product_right]
    rw [this]; push_cast; rfl
  have hs : ∑ y ∈ interval, (((interval.filter (fun x => x + y ∈ interval)).card : ℕ) : ℤ) =
      ∑ y ∈ interval, ((2*n+1 : ℤ) - |y|) := by
    apply sum_congr rfl
    intro y hy
    exact fiber_card n y hy
  rw [hs, sum_sub_distrib, abs_sum, sum_const] at hc
  simp only [interval, Int.card_Icc, nsmul_eq_mul] at hc
  have h2 : ((n:ℤ) + 1 - -(n:ℤ)).toNat = 2*n+1 := by omega
  rw [h2] at hc
  push_cast at hc
  have : (patch.card : ℤ) = ((3*n^2+3*n+1 : ℕ) : ℤ) := by rw [hc]; push_cast; ring
  exact_mod_cast this
