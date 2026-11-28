import OMAStatements.S_oeis_a111779

namespace OMA.P111779

open PowerSeries OMA.S_oeis_a111779

/-- Sum over the even indices as a weighted sum over all indices. -/
lemma even_sum (F : ℕ → ℚ) (n : ℕ) :
    ∑ k ∈ Finset.range (n / 2 + 1), F (2 * k)
      = ∑ j ∈ Finset.range (n + 1), (1 + (-1 : ℚ) ^ j) / 2 * F j := by
  induction n with
  | zero => simp
  | succ n ih =>
    conv_rhs => rw [Finset.sum_range_succ]
    rw [← ih]
    rcases Nat.even_or_odd' n with ⟨t, rfl | rfl⟩
    · have e1 : (2 * t + 1) / 2 = t := by omega
      have e2 : 2 * t / 2 = t := by omega
      have e3 : (-1 : ℚ) ^ (2 * t + 1) = -1 := by
        rw [pow_succ, pow_mul]
        norm_num
      rw [e1, e2, e3]
      ring
    · have e1 : (2 * t + 1 + 1) / 2 = t + 1 := by omega
      have e2 : (2 * t + 1) / 2 = t := by omega
      have e3 : (-1 : ℚ) ^ (2 * t + 1 + 1) = 1 := by
        rw [pow_succ, pow_succ, pow_mul]
        norm_num
      have e4 : 2 * (t + 1) = 2 * t + 1 + 1 := by ring
      rw [e1, e2, e3, Finset.sum_range_succ _ (t + 1), e4]
      ring

lemma cb_succ (m : ℕ) : ((2 * (m + 1)).choose (m + 1) : ℚ)
    = 2 * (2 * (m : ℚ) + 1) * ((2 * m).choose m : ℚ) / ((m : ℚ) + 1) := by
  have h := Nat.succ_mul_centralBinom_succ m
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
  have hq : ((m : ℚ) + 1) * ((2 * (m + 1)).choose (m + 1) : ℚ)
      = 2 * (2 * (m : ℚ) + 1) * ((2 * m).choose m : ℚ) := by
    exact_mod_cast h
  have p1 : (m : ℚ) + 1 ≠ 0 := by positivity
  rw [eq_div_iff p1]
  linear_combination hq

/-- The coefficients of 1/sqrt(1-x^2): binomial(i,i/2)/2^i for even i and 0 for odd i. -/
def u (i : ℕ) : ℚ := (1 + (-1 : ℚ) ^ i) / 2 * (i.choose (i / 2) : ℚ) / (2 : ℚ) ^ i

/-- The coefficients of (x/(1-x))^5: binomial(j-1,4). -/
def v (j : ℕ) : ℚ := ((j - 1).choose 4 : ℚ)

lemma u_succ (i : ℕ) : ((i : ℚ) + 2) * u (i + 2) = ((i : ℚ) + 1) * u i := by
  unfold u
  rcases Nat.even_or_odd' i with ⟨k, rfl | rfl⟩
  · have e0 : 2 * k + 2 = 2 * (k + 1) := by ring
    have e1 : 2 * (k + 1) / 2 = k + 1 := by omega
    have e2 : 2 * k / 2 = k := by omega
    have e3 : (-1 : ℚ) ^ (2 * (k + 1)) = 1 := by
      rw [pow_mul]
      norm_num
    have e4 : (-1 : ℚ) ^ (2 * k) = 1 := by
      rw [pow_mul]
      norm_num
    rw [e0, e1, e2, e3, e4, cb_succ]
    have p1 : (k : ℚ) + 1 ≠ 0 := by positivity
    have p2 : (2 : ℚ) ^ (2 * k) ≠ 0 := by positivity
    have e5 : (2 : ℚ) ^ (2 * (k + 1)) = 4 * (2 : ℚ) ^ (2 * k) := by ring
    rw [e5]
    push_cast
    field_simp
    ring
  · have e3 : (-1 : ℚ) ^ (2 * k + 1 + 2) = -1 := by
      rw [pow_succ, pow_succ, pow_succ, pow_mul]
      norm_num
    have e4 : (-1 : ℚ) ^ (2 * k + 1) = -1 := by
      rw [pow_succ, pow_mul]
      norm_num
    rw [e3, e4]
    ring

lemma v_succ (j : ℕ) : ((j : ℚ) - 4) * v (j + 1) = (j : ℚ) * v j := by
  unfold v
  rcases j with _ | i
  · simp
  · have e1 : i + 1 + 1 - 1 = i + 1 := by omega
    have e2 : i + 1 - 1 = i := by omega
    rw [e1, e2]
    by_cases h : 4 ≤ i + 1
    · have hc := Nat.choose_mul_succ_eq i 4
      have hq : ((i.choose 4 : ℕ) : ℚ) * ((i : ℚ) + 1)
          = (((i + 1).choose 4 : ℕ) : ℚ) * (((i + 1 - 4 : ℕ) : ℕ) : ℚ) := by
        exact_mod_cast hc
      rw [Nat.cast_sub h] at hq
      push_cast at hq ⊢
      linear_combination -hq
    · have h1 : (i + 1).choose 4 = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have h2 : i.choose 4 = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [h1, h2]
      simp

lemma coeff_theta (f : PowerSeries ℚ) (n : ℕ) :
    coeff n (X * d⁄dX ℚ f) = (n : ℚ) * coeff n f := by
  rcases n with _ | m
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

/-- The differential equation of the series of 1/sqrt(1-x^2). -/
lemma odeU :
    X * d⁄dX ℚ (PowerSeries.mk u)
      = X * (X * (X * d⁄dX ℚ (PowerSeries.mk u))) + X * (X * PowerSeries.mk u) := by
  have u1 : u 1 = 0 := by
    unfold u
    norm_num
  ext n
  rcases n with _ | _ | i
  · simp
  · simp only [map_add, coeff_succ_X_mul, coeff_zero_X_mul, coeff_derivative, coeff_mk]
    norm_num [u1]
  · have h := u_succ i
    simp only [map_add, coeff_theta, coeff_succ_X_mul, coeff_derivative, coeff_mk]
    push_cast
    linear_combination h

/-- The differential equation of the series of (x/(1-x))^5. -/
lemma odeV :
    X * d⁄dX ℚ (PowerSeries.mk v)
      = X * (X * d⁄dX ℚ (PowerSeries.mk v)) + C (5 : ℚ) * PowerSeries.mk v := by
  have v0 : v 0 = 0 := by
    unfold v
    simp
  ext n
  rcases n with _ | j
  · simp only [map_add, coeff_zero_X_mul, coeff_C_mul, coeff_mk]
    rw [v0]
    simp
  · have h := v_succ j
    simp only [map_add, coeff_theta, coeff_succ_X_mul, coeff_derivative, coeff_C_mul, coeff_mk]
    push_cast
    linear_combination h

/-- The differential equation of the product. -/
lemma odeA :
    X * d⁄dX ℚ (PowerSeries.mk u * PowerSeries.mk v)
      = X * (X * (X * d⁄dX ℚ (PowerSeries.mk u * PowerSeries.mk v)))
        + X * (X * (PowerSeries.mk u * PowerSeries.mk v))
        + C (5 : ℚ) * (PowerSeries.mk u * PowerSeries.mk v)
        + C (5 : ℚ) * (X * (PowerSeries.mk u * PowerSeries.mk v)) := by
  have hU := odeU
  have hV := odeV
  simp only [Derivation.leibniz, smul_eq_mul, map_ofNat] at hU hV ⊢
  linear_combination (PowerSeries.mk v) * hU + (1 + X) * (PowerSeries.mk u) * hV

/-- The coefficients of the product. -/
noncomputable def c (m : ℕ) : ℚ := coeff m (PowerSeries.mk u * PowerSeries.mk v)

lemma recC (m : ℕ) :
    ((m : ℚ) - 2) * c (m + 3) = 5 * c (m + 2) + ((m : ℚ) + 2) * c (m + 1) := by
  have hc := congrArg (coeff (m + 3)) odeA
  simp only [map_add, coeff_C_mul, coeff_succ_X_mul, coeff_derivative] at hc
  push_cast at hc
  unfold c
  linear_combination hc

lemma a_eq (n : ℕ) : a n = (n.factorial : ℚ) / (Nat.factorial 5 : ℚ) * c n := by
  unfold a c
  congr 1
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_mk]
  have h1 : ∑ k ∈ Finset.range ((n - 5) / 2 + 1),
        ((2 * k).choose k : ℚ) * ((n - 2 * k - 1).choose 4 : ℚ) / (4 : ℚ) ^ k
      = ∑ k ∈ Finset.range (n / 2 + 1),
        ((2 * k).choose k : ℚ) * ((n - 2 * k - 1).choose 4 : ℚ) / (4 : ℚ) ^ k := by
    apply Finset.sum_subset
    · intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    · intro x hx hnx
      rw [Finset.mem_range] at hx hnx
      have h0 : (n - 2 * x - 1).choose 4 = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [h0]
      simp
  have h2 : ∑ k ∈ Finset.range (n / 2 + 1),
        ((2 * k).choose k : ℚ) * ((n - 2 * k - 1).choose 4 : ℚ) / (4 : ℚ) ^ k
      = ∑ k ∈ Finset.range (n / 2 + 1),
        (fun j : ℕ => (j.choose (j / 2) : ℚ) * ((n - j - 1).choose 4 : ℚ) / (2 : ℚ) ^ j)
          (2 * k) := by
    apply Finset.sum_congr rfl
    intro k _
    have e : 2 * k / 2 = k := by omega
    have e4 : (2 : ℚ) ^ (2 * k) = (4 : ℚ) ^ k := by
      rw [pow_mul]
      norm_num
    beta_reduce
    rw [e, e4]
  have h3 := even_sum
    (fun j : ℕ => (j.choose (j / 2) : ℚ) * ((n - j - 1).choose 4 : ℚ) / (2 : ℚ) ^ j) n
  rw [h1, h2]
  refine h3.trans ?_
  apply Finset.sum_congr rfl
  intro j _
  beta_reduce
  unfold u v
  ring

end OMA.P111779

open OMA.S_oeis_a111779 OMA.P111779 in
theorem OMA.solution : type_of% @OMA.S_oeis_a111779.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  have e1 : m + 7 - 1 = m + 6 := by omega
  have e2 : m + 7 - 2 = m + 5 := by omega
  rw [e1, e2, a_eq, a_eq, a_eq]
  have h := recC (m + 4)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h
  have e7 : (m + 7).factorial = (m + 7) * ((m + 6) * (m + 5).factorial) := by
    rw [Nat.factorial_succ (m + 6), Nat.factorial_succ (m + 5)]
  have e6 : (m + 6).factorial = (m + 6) * (m + 5).factorial := Nat.factorial_succ (m + 5)
  rw [e7, e6]
  push_cast at h ⊢
  linear_combination
    (-((m : ℚ) + 7) * ((m : ℚ) + 6) * (((m + 5).factorial : ℚ) / (Nat.factorial 5 : ℚ))) * h
