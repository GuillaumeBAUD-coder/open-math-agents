import OMAStatements.S_oeis_a203751

namespace OMA.S_oeis_a203751

lemma pair_prod (h : ℕ → ℕ) : ∀ m : ℕ,
    ∏ j ∈ Finset.Icc 1 (2 * m + 1), h (j / 2) = h 0 * (∏ i ∈ Finset.Icc 1 m, h i) ^ 2 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have e : 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 := by ring
    rw [e, Finset.prod_Icc_succ_top (a := 1) (b := 2 * m + 1 + 1) (by omega),
      Finset.prod_Icc_succ_top (a := 1) (b := 2 * m + 1) (by omega), ih,
      Finset.prod_Icc_succ_top (a := 1) (b := m) (by omega)]
    have e1 : (2 * m + 1 + 1 + 1) / 2 = m + 1 := by omega
    have e2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    rw [e1, e2]
    ring

lemma fact_prod (m : ℕ) : ∏ i ∈ Finset.Icc 1 m, i = m.factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_Icc_succ_top (a := 1) (b := m) (by omega), ih, Nat.factorial_succ]
    ring

lemma refl_prod (m : ℕ) :
    ∏ k ∈ Finset.Icc 1 m, ((m + 1 : ℝ) - (k : ℝ)) = (m.factorial : ℝ) := by
  rw [← fact_prod, Nat.cast_prod]
  apply Finset.prod_nbij' (fun k => m + 1 - k) (fun k => m + 1 - k)
  · intro a ha
    simp only [Finset.mem_Icc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha ⊢
    omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring

lemma v_pos (n : ℕ) : 0 < v n := by
  unfold v
  apply Finset.prod_pos
  intro k hk
  apply Finset.prod_pos
  intro j _
  simp only [Finset.mem_Icc] at hk
  have h1 : 1 ≤ k / 2 := by omega
  have h2 : 0 < (k / 2) ^ 2 := pow_pos h1 2
  exact Nat.lt_of_lt_of_le h2 (Nat.le_add_left _ _)

lemma inner_eq (m : ℕ) :
    ∏ j ∈ Finset.Icc 1 (2 * (m + 1) + 1 - 1),
        ((j / 2) ^ 2 + (j / 2) * ((2 * (m + 1) + 1) / 2) + ((2 * (m + 1) + 1) / 2) ^ 2)
      = 3 * ((m + 1) ^ 2 * ∏ i ∈ Finset.Icc 1 m, (i ^ 2 + i * (m + 1) + (m + 1) ^ 2)) ^ 2 := by
  have e1 : (2 * (m + 1) + 1) / 2 = m + 1 := by omega
  have e2 : 2 * (m + 1) + 1 - 1 = 2 * m + 1 + 1 := by omega
  have hp := pair_prod (fun i => i ^ 2 + i * (m + 1) + (m + 1) ^ 2) m
  beta_reduce at hp
  rw [e1, e2, Finset.prod_Icc_succ_top (a := 1) (b := 2 * m + 1) (by omega), hp]
  have e3 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  rw [e3]
  ring

theorem bala_formula : ∀ n : ℕ, 1 ≤ n →
    a n = (n : ℝ) ^ 2 / ((n - 1).factorial : ℝ) *
      ∏ k ∈ Finset.Icc 1 (n - 1), ((n : ℝ) ^ 3 - (k : ℝ) ^ 3) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hv : v (2 * (m + 1) + 1) = v (2 * (m + 1)) *
      (3 * ((m + 1) ^ 2 * ∏ i ∈ Finset.Icc 1 m, (i ^ 2 + i * (m + 1) + (m + 1) ^ 2)) ^ 2) := by
    unfold v
    rw [Finset.prod_Icc_succ_top (a := 2) (b := 2 * (m + 1)) (by omega)]
    exact congrArg _ (inner_eq m)
  have hpos : (0 : ℝ) < (v (2 * (m + 1)) : ℝ) := by exact_mod_cast v_pos _
  set X : ℕ := (m + 1) ^ 2 * ∏ i ∈ Finset.Icc 1 m, (i ^ 2 + i * (m + 1) + (m + 1) ^ 2) with hX
  unfold a
  rw [hv]
  have h1 : ((v (2 * (m + 1)) * (3 * X ^ 2) : ℕ) : ℝ) / (3 * (v (2 * (m + 1)) : ℝ))
      = (X : ℝ) ^ 2 := by
    rw [div_eq_iff (mul_pos (by norm_num) hpos).ne']
    push_cast
    ring
  rw [h1, Real.sqrt_sq (Nat.cast_nonneg _)]
  have h2 : ∏ k ∈ Finset.Icc 1 (m + 1 - 1), (((m + 1 : ℕ) : ℝ) ^ 3 - (k : ℝ) ^ 3)
      = ∏ k ∈ Finset.Icc 1 m, (((m + 1 : ℝ) - (k : ℝ)) *
          ((k : ℝ) ^ 2 + (k : ℝ) * (m + 1) + (m + 1) ^ 2)) := by
    rw [Nat.add_sub_cancel]
    apply Finset.prod_congr rfl
    intro k _
    push_cast
    ring
  rw [h2, Finset.prod_mul_distrib, refl_prod, Nat.add_sub_cancel, hX]
  have hf : (m.factorial : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

end OMA.S_oeis_a203751

theorem OMA.solution : type_of% @OMA.S_oeis_a203751.main := OMA.S_oeis_a203751.bala_formula
