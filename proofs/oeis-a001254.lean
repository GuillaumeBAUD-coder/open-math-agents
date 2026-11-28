import OMAStatements.S_oeis_a001254

-- Problem: A001254: Squares of Lucas numbers.
-- Upstream: formal-conjectures statements/oeis-a001254.lean:0 (declaration OMA.S_oeis_a001254.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)

open Real Filter Topology Finset

namespace OMA.A1254

abbrev luc := OMA.S_oeis_a001254.lucas

theorem luc_eq (n : ℕ) : (luc n : ℝ) = goldenRatio ^ n + goldenConj ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => show ((2 : ℕ) : ℝ) = _; norm_num
  | one => show ((1 : ℕ) : ℝ) = _; rw [pow_one, pow_one, goldenRatio_add_goldenConj]; norm_num
  | more n ih1 ih2 =>
    have h : luc (n + 2) = luc (n + 1) + luc n := rfl
    rw [h]; push_cast; rw [ih1, ih2]
    have h1 := goldenRatio_sq
    have h2 := goldenConj_sq
    linear_combination (-goldenRatio ^ n) * h1 + (-goldenConj ^ n) * h2

theorem luc_pos (n : ℕ) : 0 < luc n := by
  induction n using Nat.twoStepInduction with
  | zero => show 0 < 2; norm_num
  | one => show 0 < 1; norm_num
  | more n ih1 ih2 =>
    have h : luc (n + 2) = luc (n + 1) + luc n := rfl
    omega

theorem luc_succ (n : ℕ) : luc (n + 1) = Nat.fib n + Nat.fib (n + 2) := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih1 ih2 =>
    have h : luc (n + 3) = luc (n + 2) + luc (n + 1) := rfl
    have ih2' : luc (n + 2) = Nat.fib (n + 1) + Nat.fib (n + 3) := ih2
    have a1 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    have a2 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
    have a3 : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := Nat.fib_add_two
    show luc (n + 3) = Nat.fib (n + 2) + Nat.fib (n + 4)
    rw [h, ih1, ih2']
    omega

theorem psi_pow (n : ℕ) : goldenConj ^ n = (-1 : ℝ) ^ n / goldenRatio ^ n := by
  have h : goldenConj = -goldenRatio⁻¹ := by rw [inv_goldenRatio]; ring
  rw [h, neg_pow, inv_pow, div_eq_mul_inv]

theorem den_aux (r d : ℕ) :
    goldenRatio ^ r * goldenConj ^ (r + d) + goldenConj ^ r * goldenRatio ^ (r + d) ≠ 0 := by
  have h : goldenRatio ^ r * goldenConj ^ (r + d) + goldenConj ^ r * goldenRatio ^ (r + d)
      = (goldenRatio * goldenConj) ^ r * (luc d : ℝ) := by
    rw [luc_eq, mul_pow, pow_add, pow_add]; ring
  rw [h, goldenRatio_mul_goldenConj]
  have hp : (0 : ℝ) < (luc d : ℝ) := by exact_mod_cast luc_pos d
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hp.ne'

theorem den_ne (r j : ℕ) :
    goldenRatio ^ r * goldenConj ^ j + goldenConj ^ r * goldenRatio ^ j ≠ 0 := by
  rcases le_total r j with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    exact den_aux r d
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have h1 := den_aux j d
    intro h0
    apply h1
    rw [← h0]; ring

/-- the telescoping function -/
noncomputable def e (j r : ℕ) : ℝ :=
  -(-1 : ℝ) ^ r * (goldenRatio ^ r * goldenConj ^ j - goldenConj ^ r * goldenRatio ^ j) /
    (goldenRatio ^ r * goldenConj ^ j + goldenConj ^ r * goldenRatio ^ j)

theorem key (A B C D s : ℝ) (hA : A ≠ 0) (hC : C ≠ 0) (hs : s = 1 ∨ s = -1)
    (hB : B = s / A) (hD : D = -1 / C) :
    2 * (C * C - D * D) * (A * D + B * C) * (A * C * C * D + B * D * D * C) =
      ((A + B) ^ 2 - s * (C - D) ^ 2) *
        (-s * (A * C * C * D - B * D * D * C) * (A * D + B * C) +
          s * (A * D - B * C) * (A * C * C * D + B * D * D * C)) := by
  subst hB hD
  rcases hs with rfl | rfl <;> field_simp <;> ring

theorem K_pos (j : ℕ) (hj : j ≠ 0) :
    0 < goldenRatio ^ j * goldenRatio ^ j - goldenConj ^ j * goldenConj ^ j := by
  have h1 : 1 < goldenRatio ^ j := one_lt_pow₀ one_lt_goldenRatio hj
  have h2 : |goldenConj ^ j| < 1 := by
    rw [abs_pow]
    apply pow_lt_one₀ (abs_nonneg _) _ hj
    rw [abs_lt]
    exact ⟨neg_one_lt_goldenConj, by linarith [goldenConj_neg]⟩
  have h3 := abs_lt.1 h2
  nlinarith [h3.1, h3.2]

theorem term_eq (j m : ℕ) (hj : Odd j) :
    1 / ((luc m : ℝ) ^ 2 - 5 * (-1 : ℝ) ^ m * (Nat.fib j : ℝ) ^ 2) =
      (e j (m + 2 * j) - e j m) / (2 * (goldenRatio ^ j * goldenRatio ^ j -
        goldenConj ^ j * goldenConj ^ j)) := by
  have hA : goldenRatio ^ m ≠ 0 := pow_ne_zero _ goldenRatio_pos.ne'
  have hC : goldenRatio ^ j ≠ 0 := pow_ne_zero _ goldenRatio_pos.ne'
  have hs := neg_one_pow_eq_or ℝ m
  have hB : goldenConj ^ m = (-1 : ℝ) ^ m / goldenRatio ^ m := psi_pow m
  have hD : goldenConj ^ j = -1 / goldenRatio ^ j := by rw [psi_pow j, hj.neg_one_pow]
  have hfib : 5 * (-1 : ℝ) ^ m * (Nat.fib j : ℝ) ^ 2 =
      (-1 : ℝ) ^ m * (goldenRatio ^ j - goldenConj ^ j) ^ 2 := by
    rw [coe_fib_eq, div_pow, Real.sq_sqrt (by norm_num)]; ring
  have e1 : goldenRatio ^ (m + 2 * j) = goldenRatio ^ m * goldenRatio ^ j * goldenRatio ^ j := by
    rw [pow_add, two_mul, pow_add]; ring
  have e2 : goldenConj ^ (m + 2 * j) = goldenConj ^ m * goldenConj ^ j * goldenConj ^ j := by
    rw [pow_add, two_mul, pow_add]; ring
  have e3 : (-1 : ℝ) ^ (m + 2 * j) = (-1) ^ m := by
    rw [pow_add, pow_mul]; norm_num
  have hP := den_ne m j
  have hQ := den_ne (m + 2 * j) j
  rw [e1, e2] at hQ
  have hK := K_pos j hj.pos.ne'
  unfold e
  rw [luc_eq, hfib, e1, e2, e3]
  have hkey := key (goldenRatio ^ m) (goldenConj ^ m) (goldenRatio ^ j) (goldenConj ^ j)
    ((-1 : ℝ) ^ m) hA hC hs hB hD
  generalize goldenRatio ^ m = A at *
  generalize goldenConj ^ m = B at *
  generalize goldenRatio ^ j = C at *
  generalize goldenConj ^ j = D at *
  generalize (-1 : ℝ) ^ m = s at *
  have h2K : 2 * (C * C - D * D) ≠ 0 := by positivity
  have hΔ : (A + B) ^ 2 - s * (C - D) ^ 2 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hkey
    exact (mul_ne_zero (mul_ne_zero h2K hP) hQ) hkey
  rw [eq_div_iff h2K, div_sub_div _ _ hQ hP, div_mul_eq_mul_div, div_eq_div_iff hΔ (mul_ne_zero hQ hP)]
  linear_combination hkey

theorem e_refl (j r r' : ℕ) (h : r + r' = 2 * j) : e j r' = -e j r := by
  have hσ : (-1 : ℝ) ^ r' = (-1) ^ r := by
    have h3 : (-1 : ℝ) ^ r * (-1) ^ r' = 1 := by rw [← pow_add, h, pow_mul]; norm_num
    rcases neg_one_pow_eq_or ℝ r with h1 | h1 <;> rw [h1] at h3 ⊢ <;> linarith
  have h1 : goldenRatio ^ r * goldenRatio ^ r' = goldenRatio ^ j * goldenRatio ^ j := by
    rw [← pow_add, h, two_mul, pow_add]
  have h2 : goldenConj ^ r * goldenConj ^ r' = goldenConj ^ j * goldenConj ^ j := by
    rw [← pow_add, h, two_mul, pow_add]
  have hP := den_ne r j
  have hP' := den_ne r' j
  unfold e
  rw [hσ]
  generalize goldenRatio ^ r = a at *
  generalize goldenRatio ^ r' = a' at *
  generalize goldenConj ^ r = b at *
  generalize goldenConj ^ r' = b' at *
  generalize goldenRatio ^ j = C at *
  generalize goldenConj ^ j = D at *
  generalize (-1 : ℝ) ^ r = s at *
  rw [eq_neg_iff_add_eq_zero, div_add_div _ _ hP' hP, div_eq_zero_iff]
  left
  linear_combination (-s * 2 * D ^ 2) * h1 + (s * 2 * C ^ 2) * h2

theorem W0 (j : ℕ) (hj : Odd j) :
    ∑ i ∈ range (2 * j), e j (0 + 1 + i) = e j (2 * j) := by
  obtain ⟨t, ht⟩ : ∃ t, 2 * j = t + 1 := ⟨2 * j - 1, by have := hj.pos; omega⟩
  rw [ht, sum_range_succ]
  have hz : ∑ i ∈ range t, e j (0 + 1 + i) = 0 := by
    have hr : ∑ i ∈ range t, e j (0 + 1 + (t - 1 - i)) = ∑ i ∈ range t, e j (0 + 1 + i) :=
      Finset.sum_range_reflect (fun i => e j (0 + 1 + i)) t
    have hc : ∑ i ∈ range t, e j (0 + 1 + (t - 1 - i)) = ∑ i ∈ range t, -e j (0 + 1 + i) := by
      apply sum_congr rfl
      intro i hi
      have hi' := mem_range.1 hi
      exact e_refl j (0 + 1 + i) (0 + 1 + (t - 1 - i)) (by omega)
    rw [hc, sum_neg_distrib] at hr
    linarith
  rw [hz, zero_add]
  congr 1
  omega

theorem tele (j N : ℕ) :
    ∑ n ∈ range N, (e j (n + 1 + 2 * j) - e j (n + 1)) =
      ∑ i ∈ range (2 * j), e j (N + 1 + i) - ∑ i ∈ range (2 * j), e j (0 + 1 + i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    have h1 : ∑ i ∈ range (2 * j + 1), e j (N + 1 + i) =
        ∑ i ∈ range (2 * j), e j (N + 1 + i) + e j (N + 1 + 2 * j) :=
      Finset.sum_range_succ (fun i => e j (N + 1 + i)) (2 * j)
    have h2 : ∑ i ∈ range (2 * j + 1), e j (N + 1 + i) =
        ∑ i ∈ range (2 * j), e j (N + 1 + (i + 1)) + e j (N + 1) :=
      Finset.sum_range_succ' (fun i => e j (N + 1 + i)) (2 * j)
    have h3 : ∑ i ∈ range (2 * j), e j (N + 1 + 1 + i) =
        ∑ i ∈ range (2 * j), e j (N + 1 + (i + 1)) := by
      apply sum_congr rfl
      intro i _
      congr 1
      omega
    rw [h3]
    linarith

theorem alt_sum (j : ℕ) : ∑ i ∈ range (2 * j), (-1 : ℝ) ^ i = 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
    rw [h, sum_range_succ, sum_range_succ, ih, pow_succ, pow_mul]
    norm_num

theorem delta_tendsto (j : ℕ) :
    Tendsto (fun r => e j r + (-1 : ℝ) ^ r) atTop (𝓝 0) := by
  have hφ := goldenRatio_pos
  have hD : goldenConj ^ j ≠ 0 := pow_ne_zero _ goldenConj_neg.ne
  have hq : |goldenConj / goldenRatio| < 1 := by
    rw [abs_div, abs_of_pos hφ, div_lt_one hφ]
    have h1 : |goldenConj| < 1 := by
      rw [abs_lt]
      exact ⟨neg_one_lt_goldenConj, by linarith [goldenConj_neg]⟩
    linarith [one_lt_goldenRatio]
  have hq0 := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq
  have hlim : Tendsto (fun r : ℕ => 2 * (goldenConj / goldenRatio) ^ r * goldenRatio ^ j /
      (goldenConj ^ j + (goldenConj / goldenRatio) ^ r * goldenRatio ^ j)) atTop (𝓝 0) := by
    have h := ((tendsto_const_nhds (x := (2 : ℝ))).mul hq0).mul
      (tendsto_const_nhds (x := goldenRatio ^ j))
    have h' := (tendsto_const_nhds (x := goldenConj ^ j)).add
      (hq0.mul (tendsto_const_nhds (x := goldenRatio ^ j)))
    have h'' := h.div h' (by simpa using hD)
    have h3 : (2 * (0 : ℝ) * goldenRatio ^ j) / (goldenConj ^ j + 0 * goldenRatio ^ j) = 0 := by simp
    rw [h3] at h''
    exact h''
  have habs := hlim.abs
  rw [abs_zero] at habs
  apply squeeze_zero_norm _ habs
  intro r
  have hP := den_ne r j
  have hr : goldenRatio ^ r ≠ 0 := pow_ne_zero _ hφ.ne'
  have heq : e j r + (-1 : ℝ) ^ r = (-1 : ℝ) ^ r * (2 * (goldenConj / goldenRatio) ^ r * goldenRatio ^ j /
      (goldenConj ^ j + (goldenConj / goldenRatio) ^ r * goldenRatio ^ j)) := by
    rw [div_pow]
    unfold e
    generalize goldenRatio ^ r = X at *
    generalize goldenConj ^ r = Y at *
    generalize goldenRatio ^ j = C at *
    generalize goldenConj ^ j = D at *
    generalize (-1 : ℝ) ^ r = s at *
    have hden : D + Y / X * C = (X * D + Y * C) / X := by field_simp
    rw [hden]
    field_simp
    ring
  rw [heq, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs]

theorem W_tendsto (j : ℕ) :
    Tendsto (fun N => ∑ i ∈ range (2 * j), e j (N + 1 + i)) atTop (𝓝 0) := by
  have hδ := delta_tendsto j
  have h1 : ∀ N, ∑ i ∈ range (2 * j), e j (N + 1 + i) =
      ∑ i ∈ range (2 * j), (e j (N + 1 + i) + (-1 : ℝ) ^ (N + 1 + i)) := by
    intro N
    rw [sum_add_distrib]
    have : ∑ i ∈ range (2 * j), (-1 : ℝ) ^ (N + 1 + i) = 0 := by
      simp_rw [pow_add (-1 : ℝ) (N + 1)]
      rw [← mul_sum, alt_sum, mul_zero]
    rw [this, add_zero]
  simp_rw [h1]
  have h2 : Tendsto (fun N => ∑ i ∈ range (2 * j), (e j (N + 1 + i) + (-1 : ℝ) ^ (N + 1 + i)))
      atTop (𝓝 (∑ i ∈ range (2 * j), (0 : ℝ))) := by
    apply tendsto_finsetSum
    intro i _
    exact hδ.comp (tendsto_atTop_mono (fun N => (by omega : N ≤ N + 1 + i)) tendsto_id)
  simpa using h2

theorem nonneg_term (j n : ℕ) :
    0 ≤ 1 / ((luc (n + j + 1) : ℝ) ^ 2 - 5 * (-1 : ℝ) ^ (n + j + 1) * (Nat.fib j : ℝ) ^ 2) := by
  have h3 : 3 * Nat.fib j ≤ luc (n + j + 1) := by
    rw [luc_succ]
    have a1 := Nat.fib_mono (show j ≤ n + j by omega)
    have a2 := Nat.fib_mono (show j + 2 ≤ n + j + 2 by omega)
    have a3 := Nat.fib_add_two (n := j)
    have a4 := Nat.fib_le_fib_succ (n := j)
    omega
  have h3' : (3 : ℝ) * Nat.fib j ≤ luc (n + j + 1) := by exact_mod_cast h3
  have hF : (0 : ℝ) ≤ Nat.fib j := Nat.cast_nonneg _
  apply one_div_nonneg.2
  rcases neg_one_pow_eq_or ℝ (n + j + 1) with h | h <;> rw [h] <;> nlinarith

theorem final_val (j : ℕ) (hj : Odd j) :
    (0 - e j (2 * j)) / (2 * (goldenRatio ^ j * goldenRatio ^ j - goldenConj ^ j * goldenConj ^ j)) =
      1 / (2 * (luc j : ℝ) ^ 2) := by
  have hK := K_pos j hj.pos.ne'
  have hL : (0 : ℝ) < (luc j : ℝ) := by exact_mod_cast luc_pos j
  rw [luc_eq] at hL ⊢
  have hC : 0 < goldenRatio ^ j := pow_pos goldenRatio_pos _
  have hD : goldenConj ^ j ≠ 0 := pow_ne_zero _ goldenConj_neg.ne
  have e4 : goldenRatio ^ (2 * j) = goldenRatio ^ j * goldenRatio ^ j := by rw [two_mul, pow_add]
  have e5 : goldenConj ^ (2 * j) = goldenConj ^ j * goldenConj ^ j := by rw [two_mul, pow_add]
  have e6 : (-1 : ℝ) ^ (2 * j) = 1 := by rw [pow_mul]; norm_num
  unfold e
  rw [e4, e5, e6]
  generalize goldenRatio ^ j = C at *
  generalize goldenConj ^ j = D at *
  have hCD : C - D ≠ 0 := by
    intro h0
    have : C * C - D * D = (C - D) * (C + D) := by ring
    rw [this, h0, zero_mul] at hK
    exact lt_irrefl _ hK
  have hden : C * C * D + D * D * C ≠ 0 := by
    have : C * C * D + D * D * C = C * D * (C + D) := by ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero hC.ne' hD) hL.ne'
  have hK' : C * C - D * D = (C - D) * (C + D) := by ring
  rw [hK']
  have hnum : -1 * (C * C * D - D * D * C) / (C * C * D + D * D * C) = -(C - D) / (C + D) := by
    rw [div_eq_div_iff hden hL.ne']; ring
  rw [hnum]
  field_simp
  ring

end OMA.A1254

open OMA.A1254 in
theorem OMA.solution : type_of% @OMA.S_oeis_a001254.main := by
  intro k
  have hj : Odd (2 * k + 1) := ⟨k, rfl⟩
  generalize 2 * k + 1 = j at hj ⊢
  have hf : ∀ n : ℕ, (1 : ℝ) / ((OMA.S_oeis_a001254.a (n + 1) : ℝ) -
      5 * (-1 : ℝ) ^ (n + 1) * (Nat.fib j : ℝ) ^ 2) =
      (e j (n + 1 + 2 * j) - e j (n + 1)) / (2 * (goldenRatio ^ j * goldenRatio ^ j -
        goldenConj ^ j * goldenConj ^ j)) := by
    intro n
    rw [← term_eq j (n + 1) hj]
    have : (OMA.S_oeis_a001254.a (n + 1) : ℝ) = (luc (n + 1) : ℝ) ^ 2 := by
      unfold OMA.S_oeis_a001254.a; push_cast; rfl
    rw [this]
  have hS : ∀ N : ℕ, ∑ n ∈ range N, (1 : ℝ) / ((OMA.S_oeis_a001254.a (n + 1) : ℝ) -
      5 * (-1 : ℝ) ^ (n + 1) * (Nat.fib j : ℝ) ^ 2) =
      (∑ i ∈ range (2 * j), e j (N + 1 + i) - e j (2 * j)) / (2 * (goldenRatio ^ j * goldenRatio ^ j -
        goldenConj ^ j * goldenConj ^ j)) := by
    intro N
    simp_rw [hf]
    rw [← sum_div, tele, W0 j hj]
  rw [← hasSum_nat_add_iff' j]
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · have hpart : ∀ N : ℕ, ∑ i ∈ range N, (1 : ℝ) / ((OMA.S_oeis_a001254.a (i + j + 1) : ℝ) -
        5 * (-1 : ℝ) ^ (i + j + 1) * (Nat.fib j : ℝ) ^ 2) =
        (∑ i ∈ range (2 * j), e j (j + N + 1 + i) - e j (2 * j)) / (2 * (goldenRatio ^ j * goldenRatio ^ j -
          goldenConj ^ j * goldenConj ^ j)) - ∑ i ∈ range j, (1 : ℝ) / ((OMA.S_oeis_a001254.a (i + 1) : ℝ) -
        5 * (-1 : ℝ) ^ (i + 1) * (Nat.fib j : ℝ) ^ 2) := by
      intro N
      rw [← hS (j + N), sum_range_add]
      have : ∀ x, j + x + 1 = x + j + 1 := fun x => by ring
      simp_rw [this]
      ring
    simp_rw [hpart]
    apply Tendsto.sub_const
    have hval := final_val j hj
    have ha : (OMA.S_oeis_a001254.a j : ℝ) = (luc j : ℝ) ^ 2 := by
      unfold OMA.S_oeis_a001254.a; push_cast; rfl
    rw [ha, ← hval]
    apply Tendsto.div_const
    apply Tendsto.sub_const
    have hW := W_tendsto j
    exact hW.comp (tendsto_atTop_mono (fun N => (by omega : N ≤ j + N)) tendsto_id)
  · intro n
    have h := nonneg_term j n
    have ha : (OMA.S_oeis_a001254.a (n + j + 1) : ℝ) = (luc (n + j + 1) : ℝ) ^ 2 := by
      unfold OMA.S_oeis_a001254.a; push_cast; rfl
    rw [ha]
    exact h
