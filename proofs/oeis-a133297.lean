import OMAStatements.S_oeis_a133297

open OMA.S_oeis_a133297 in
theorem OMA.solution : type_of% @OMA.S_oeis_a133297.main := by
  intro n hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have h1 := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (-(n : ℝ))
  rw [← Real.exp_eq_exp_ℝ] at h1
  have h2 := ((hasSum_nat_add_iff' n).mpr h1).mul_left ((-1 : ℝ) ^ n)
  have hsq : ∀ m : ℕ, ((-1 : ℝ) ^ m) * ((-1 : ℝ) ^ m) = 1 := by
    intro m; rw [← mul_pow]; norm_num
  have h3 : (fun k : ℕ => (-1 : ℝ) ^ n * ((-(n : ℝ)) ^ (k + n) / ((k + n).factorial : ℝ)))
      = (fun k : ℕ => (-1 : ℝ) ^ k * (n : ℝ) ^ (n + k) / ((n + k).factorial : ℝ)) := by
    funext k
    have e0 : (-1 : ℝ) ^ n * (-1) ^ (k + n) = (-1) ^ k := by
      rw [pow_add, mul_comm ((-1 : ℝ) ^ k), ← mul_assoc, hsq, one_mul]
    rw [neg_pow (n : ℝ) (k + n), add_comm n k, ← e0]
    ring
  rw [h3] at h2
  rw [h2.tsum_eq]
  have h4 : (-1 / Real.exp 1) ^ n = (-1) ^ n * Real.exp (-(n : ℝ)) := by
    rw [div_pow, ← Real.exp_nat_mul, mul_one, Real.exp_neg]; ring
  rw [h4, a]
  have h5 : ∑ k ∈ Finset.Icc 1 n,
      (-1 : ℝ) ^ (k + 1) * (n : ℝ) ^ ((n : ℤ) - (k : ℤ) - 1) / ((n - k).factorial : ℝ)
      = ∑ i ∈ Finset.range n, (-1 : ℝ) ^ (n - i + 1) * (n : ℝ) ^ ((i : ℤ) - 1) / (i.factorial : ℝ) := by
    refine Finset.sum_nbij' (fun k => n - k) (fun i => n - i) ?_ ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_Icc, Finset.mem_range] at *; omega
    · intro k hk; simp only [Finset.mem_Icc, Finset.mem_range] at *; omega
    · intro k hk; simp only [Finset.mem_Icc, Finset.mem_range] at *; omega
    · intro k hk; simp only [Finset.mem_Icc, Finset.mem_range] at *; omega
    · intro k hk
      simp only [Finset.mem_Icc] at hk
      have e1 : n - (n - k) = k := by omega
      have e2 : ((n - k : ℕ) : ℤ) - 1 = (n : ℤ) - (k : ℤ) - 1 := by
        rw [Nat.cast_sub hk.2]
      rw [e1, e2]
  rw [h5]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.factorial_succ, Nat.add_sub_cancel]
  have h6 : ∀ i ∈ Finset.range (m + 1),
      (-1 : ℝ) ^ (m + 1 - i + 1) * ((m + 1 : ℕ) : ℝ) ^ ((i : ℤ) - 1) / (i.factorial : ℝ)
      = -((-1 : ℝ) ^ (m + 1) * ((-((m + 1 : ℕ) : ℝ)) ^ i / (i.factorial : ℝ))) / ((m + 1 : ℕ) : ℝ) := by
    intro i hi
    have hi' : i ≤ m + 1 := by
      have := Finset.mem_range.mp hi; omega
    have e : (-1 : ℝ) ^ (m + 1 - i) * (-1) ^ i = (-1) ^ (m + 1) := by
      rw [← pow_add]; congr 1; omega
    have := hsq i
    rw [zpow_sub_one₀ hn0, zpow_natCast, neg_pow ((m + 1 : ℕ) : ℝ) i, ← e,
      pow_succ (-1 : ℝ) (m + 1 - i)]
    linear_combination ((-1 : ℝ) ^ (m + 1 - i) * ((m + 1 : ℕ) : ℝ) ^ i / (i.factorial : ℝ)
      / ((m + 1 : ℕ) : ℝ)) * this
  rw [Finset.sum_congr rfl h6, ← Finset.sum_div, Finset.sum_neg_distrib, ← Finset.mul_sum]
  push_cast
  field_simp
  ring

