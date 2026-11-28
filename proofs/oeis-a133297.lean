import OMAStatements.S_oeis_a133297
import Mathlib

namespace A133297Aux

lemma tail (N : ℕ) (x : ℝ) :
    (∑' k : ℕ, (-1 : ℝ) ^ k * x ^ (N + 1 + k) / ((N + 1 + k).factorial : ℝ)) =
      (-1 : ℝ) ^ (N + 1) *
        (Real.exp (-x) - ∑ m ∈ Finset.range (N + 1), (-x) ^ m / (m.factorial : ℝ)) := by
  have hs : Summable (fun m : ℕ => (-x) ^ m / (m.factorial : ℝ)) :=
    NormedSpace.expSeries_div_summable (-x)
  have he : ∑' m : ℕ, (-x) ^ m / (m.factorial : ℝ) = Real.exp (-x) := by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp (-x)).tsum_eq
  have h := hs.sum_add_tsum_nat_add (N + 1)
  rw [he] at h
  have e2 : ((-1 : ℝ) ^ (N + 1)) * (-1) ^ (N + 1) = 1 := by
    rw [← mul_pow]
    norm_num
  have h2 : (∑' k : ℕ, (-1 : ℝ) ^ k * x ^ (N + 1 + k) / ((N + 1 + k).factorial : ℝ)) =
      (-1 : ℝ) ^ (N + 1) *
        ∑' i : ℕ, (-x) ^ (i + (N + 1)) / ((i + (N + 1)).factorial : ℝ) := by
    rw [← tsum_mul_left]
    congr 1
    funext k
    rw [show k + (N + 1) = N + 1 + k from by ring, neg_pow, pow_add (-1 : ℝ)]
    linear_combination (-((-1 : ℝ) ^ k * x ^ (N + 1 + k) / ((N + 1 + k).factorial : ℝ))) * e2
  rw [h2, ← h]
  ring

end A133297Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a133297.main := by
  intro n hn
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hx : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have he : (-1 / Real.exp 1) ^ (N + 1) =
      (-1 : ℝ) ^ (N + 1) * Real.exp (-((N + 1 : ℕ) : ℝ)) := by
    rw [div_pow, Real.exp_neg, ← Real.exp_nat_mul, mul_one, div_eq_mul_inv]
  rw [A133297Aux.tail N ((N + 1 : ℕ) : ℝ), he]
  unfold OMA.S_oeis_a133297.a
  rw [Finset.mul_sum]
  have key : ∑ k ∈ Finset.Icc 1 (N + 1), ((N + 1).factorial : ℝ) *
      ((-1 : ℝ) ^ (k + 1) * ((N + 1 : ℕ) : ℝ) ^ (((N + 1 : ℕ) : ℤ) - (k : ℤ) - 1) /
        ((N + 1 - k).factorial : ℝ)) =
      ∑ m ∈ Finset.range (N + 1), (N.factorial : ℝ) * (-1) ^ N *
        ((-((N + 1 : ℕ) : ℝ)) ^ m / (m.factorial : ℝ)) := by
    refine Finset.sum_nbij' (fun k => N + 1 - k) (fun m => N + 1 - m) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      simp only [Finset.mem_range]
      omega
    · intro m hm
      simp only [Finset.mem_range] at hm
      simp only [Finset.mem_Icc]
      omega
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      omega
    · intro m hm
      simp only [Finset.mem_range] at hm
      omega
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      obtain ⟨m, hm⟩ : ∃ m, N + 1 = k + m := ⟨N + 1 - k, by omega⟩
      have e1 : N + 1 - k = m := by omega
      have e2 : ((N + 1 : ℕ) : ℤ) - (k : ℤ) - 1 = (m : ℤ) - 1 := by omega
      have e3 : ((N + 1 : ℕ) : ℝ) ^ ((m : ℤ) - 1) = ((N + 1 : ℕ) : ℝ) ^ m / ((N + 1 : ℕ) : ℝ) := by
        rw [zpow_sub_one₀ hx, zpow_natCast, div_eq_mul_inv]
      have e4 : ((N + 1).factorial : ℝ) = ((N + 1 : ℕ) : ℝ) * (N.factorial : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have e5 : (-1 : ℝ) ^ (k + 1) = (-1) ^ N * (-1) ^ m := by
        rw [← pow_add, neg_one_pow_eq_pow_mod_two (n := k + 1),
          neg_one_pow_eq_pow_mod_two (n := N + m)]
        congr 1
        omega
      rw [e1, e2, e3, e4, e5, neg_pow ((N + 1 : ℕ) : ℝ) m]
      field_simp
  rw [key, Nat.add_sub_cancel, ← Finset.mul_sum]
  ring
