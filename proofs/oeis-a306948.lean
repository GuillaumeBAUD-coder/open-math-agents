import OMAStatements.S_oeis_a306948

section Proof

open PowerSeries

private noncomputable def dPs (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((n + 1 : ℕ) : ℚ) * coeff (n + 1) f

private lemma coeff_dPs (f : PowerSeries ℚ) (n : ℕ) :
    coeff n (dPs f) = ((n + 1 : ℕ) : ℚ) * coeff (n + 1) f := by
  simp [dPs]

private lemma dPs_C (c : ℚ) : dPs (C c) = 0 := by
  ext n
  simp [coeff_dPs]

private lemma dPs_one : dPs (1 : PowerSeries ℚ) = 0 := by
  rw [← map_one C]
  exact dPs_C 1

private lemma dPs_X : dPs (X : PowerSeries ℚ) = 1 := by
  ext n
  simp only [coeff_dPs, coeff_X, coeff_one]
  cases n <;> simp

private lemma dPs_add (f g : PowerSeries ℚ) : dPs (f + g) = dPs f + dPs g := by
  ext n
  simp only [coeff_dPs, map_add]
  ring

private lemma dPs_mul (f g : PowerSeries ℚ) : dPs (f * g) = dPs f * g + f * dPs g := by
  ext n
  rw [coeff_dPs, map_add, coeff_mul, coeff_mul, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => coeff i f * coeff j g) (n + 1),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => coeff i (dPs f) * coeff j g) n,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => coeff i f * coeff j (dPs g)) n,
    Finset.mul_sum]
  have hsplit :
      ∑ k ∈ Finset.range (n + 2),
          ((n + 1 : ℕ) : ℚ) * (coeff k f * coeff (n + 1 - k) g) =
        ∑ k ∈ Finset.range (n + 2),
          (((k : ℚ) * coeff k f) * coeff (n + 1 - k) g +
            coeff k f * (((n + 1 - k : ℕ) : ℚ) * coeff (n + 1 - k) g)) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk_le : k ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hnat : (k : ℚ) + ((n + 1 - k : ℕ) : ℚ) = ((n + 1 : ℕ) : ℚ) := by
      exact_mod_cast Nat.add_sub_of_le hk_le
    rw [← hnat]
    ring
  rw [hsplit, Finset.sum_add_distrib]
  have h1 :
      ∑ k ∈ Finset.range (n + 2), ((k : ℚ) * coeff k f) * coeff (n + 1 - k) g =
        ∑ k ∈ Finset.range (n + 1), coeff k (dPs f) * coeff (n - k) g := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coeff_dPs, Nat.succ_sub_succ]
  have h2 :
      ∑ k ∈ Finset.range (n + 2),
          coeff k f * (((n + 1 - k : ℕ) : ℚ) * coeff (n + 1 - k) g) =
        ∑ k ∈ Finset.range (n + 1), coeff k f * coeff (n - k) (dPs g) := by
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, mul_zero, add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [coeff_dPs, Nat.sub_add_comm hk_le]
  rw [h1, h2]

private lemma dPs_exp : dPs (exp ℚ) = exp ℚ := by
  ext n
  rw [coeff_dPs, coeff_exp, coeff_exp, Nat.factorial_succ]
  push_cast
  have hfac : (n.factorial : ℚ) ≠ 0 := by positivity
  have hn : (n : ℚ) + 1 ≠ 0 := by positivity
  field_simp

private lemma dPs_log_eq : dPs (log ℚ) = PowerSeries.mk fun n => (-1 : ℚ) ^ n := by
  ext n
  rw [coeff_dPs, coeff_log, coeff_mk]
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Algebra.algebraMap_self,
    RingHom.id_apply]
  have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ hn]
  simp only [pow_add, pow_one]
  ring

private lemma mul_dPs_log : (1 + (X : PowerSeries ℚ)) * dPs (log ℚ) = 1 := by
  ext n
  rw [add_mul, one_mul, map_add]
  cases n with
  | zero => simp [dPs_log_eq]
  | succ k =>
    rw [coeff_succ_X_mul, coeff_one]
    simp [dPs_log_eq, pow_succ]

private lemma coeff_mul_X_succ (f : PowerSeries ℚ) (m : ℕ) :
    coeff (m + 1) (f * X) = coeff m f := by
  simp

private lemma egf_ode :
    dPs OMA.S_oeis_a306948.egf + dPs OMA.S_oeis_a306948.egf * X -
      C (2 : ℚ) * OMA.S_oeis_a306948.egf - OMA.S_oeis_a306948.egf * X =
      exp ℚ + exp ℚ * X := by
  have hlog : dPs ((1 + (X : PowerSeries ℚ)) * log ℚ) = 1 + log ℚ := by
    rw [dPs_mul, dPs_add, dPs_one, dPs_X, zero_add, one_mul, mul_dPs_log, add_comm]
  have hegf :
      dPs OMA.S_oeis_a306948.egf =
        OMA.S_oeis_a306948.egf + (1 + log ℚ) * exp ℚ := by
    unfold OMA.S_oeis_a306948.egf
    rw [dPs_mul, dPs_exp, hlog, add_comm]
  have hmul :
      (1 + (X : PowerSeries ℚ)) * ((1 + log ℚ) * exp ℚ) =
        OMA.S_oeis_a306948.egf + exp ℚ + exp ℚ * X := by
    unfold OMA.S_oeis_a306948.egf
    ring
  have hC2 : C (2 : ℚ) = 2 :=
    map_ofNat (C : ℚ →+* PowerSeries ℚ) 2
  rw [hC2]
  linear_combination (1 + (X : PowerSeries ℚ)) * hegf + hmul

private lemma rec1 (m : ℕ) :
    OMA.S_oeis_a306948.a (m + 2) + ((m : ℚ) - 1) * OMA.S_oeis_a306948.a (m + 1) -
      ((m : ℚ) + 1) * OMA.S_oeis_a306948.a m = (m : ℚ) + 2 := by
  have hcoeff := congrArg (coeff (m + 1)) egf_ode
  simp only [map_add, map_sub, coeff_dPs, coeff_mul_X_succ, coeff_C_mul, coeff_exp] at hcoeff
  have hfac1 : ((m + 1).factorial : ℚ) ≠ 0 := by positivity
  have hfac0 : (m.factorial : ℚ) ≠ 0 := by positivity
  have hmul := congrArg (fun t : ℚ => ((m + 1).factorial : ℚ) * t) hcoeff
  dsimp at hmul
  have hf1 : ((m + 2).factorial : ℚ) = ((m + 1).factorial : ℚ) * ((m : ℚ) + 2) := by
    rw [Nat.factorial_succ (m + 1)]
    push_cast
    ring
  have hf0 : ((m + 1).factorial : ℚ) = ((m : ℚ) + 1) * (m.factorial : ℚ) := by
    rw [Nat.factorial_succ m]
    push_cast
    ring
  have hrhs :
      ((m + 1).factorial : ℚ) * (1 / ((m + 1).factorial : ℚ) + 1 / (m.factorial : ℚ)) =
        (m : ℚ) + 2 := by
    rw [mul_add, mul_one_div_cancel hfac1, hf0, mul_assoc, mul_one_div_cancel hfac0]
    ring
  rw [hrhs] at hmul
  unfold OMA.S_oeis_a306948.a
  rw [hf1, show ((m : ℚ) + 1) * ((m.factorial : ℚ) * coeff m OMA.S_oeis_a306948.egf) =
      ((m + 1).factorial : ℚ) * coeff m OMA.S_oeis_a306948.egf by rw [hf0]; ring]
  push_cast at hmul
  rw [show m + 1 + 1 = m + 2 by rfl] at hmul
  linear_combination hmul

end Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a306948.main := by
  intro n hn
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have hr0 := rec1 r
  have hr1 := rec1 (r + 1)
  have hr2 := rec1 (r + 2)
  push_cast at hr0 hr1 hr2 ⊢
  linear_combination hr2 - 2 * hr1 + hr0
