import OMAStatements.S_oeis_a267884

-- Credit: @Dariusthedoggie
-- Proof: Rule 233 becomes uniformly ON at stage 4 and stays ON forever, so offCount vanishes from stage 4 onward and a(n) = 6 for n > 2

namespace OMA.P267884

open OMA.S_oeis_a267884 PowerSeries

private lemma state1 (x : ℤ) : state 233 1 x = decide (x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1) := by
  change step 233 (state 233 0) x = _
  unfold step state
  by_cases h1 : x = -1 <;> by_cases h2 : x = 0 <;> by_cases h3 : x = 1 <;>
    simp_all [show ∀ a b : ℤ, a - 1 = b ↔ a = b + 1 by omega,
              show ∀ a b : ℤ, a + 1 = b ↔ a = b - 1 by omega] <;> decide

private lemma state2 (x : ℤ) : state 233 2 x = decide (x ≠ -1 ∧ x ≠ 1) := by
  change step 233 (state 233 1) x = _
  unfold step
  rw [state1, state1, state1]
  by_cases h1 : x = -2 <;> by_cases h2 : x = -1 <;> by_cases h3 : x = 0 <;>
    by_cases h4 : x = 1 <;> by_cases h5 : x = 2 <;>
    simp_all [show ∀ a b : ℤ, a - 1 = b ↔ a = b + 1 by omega,
              show ∀ a b : ℤ, a + 1 = b ↔ a = b - 1 by omega] <;> decide

private lemma state3 (x : ℤ) : state 233 3 x = decide (x ≠ 0) := by
  change step 233 (state 233 2) x = _
  unfold step
  rw [state2, state2, state2]
  by_cases h1 : x = -2 <;> by_cases h2 : x = -1 <;> by_cases h3 : x = 0 <;>
    by_cases h4 : x = 1 <;> by_cases h5 : x = 2 <;>
    simp_all [show ∀ a b : ℤ, a - 1 = b ↔ a = b + 1 by omega,
              show ∀ a b : ℤ, a + 1 = b ↔ a = b - 1 by omega] <;> decide

private lemma state4 (x : ℤ) : state 233 4 x = true := by
  change step 233 (state 233 3) x = _
  unfold step
  rw [state3, state3, state3]
  by_cases h1 : x = -1 <;> by_cases h2 : x = 0 <;> by_cases h3 : x = 1 <;>
    simp_all [show ∀ a b : ℤ, a - 1 = b ↔ a = b + 1 by omega,
              show ∀ a b : ℤ, a + 1 = b ↔ a = b - 1 by omega] <;> decide

private lemma state_ge4 (k : ℕ) (hk : 4 ≤ k) (x : ℤ) : state 233 k x = true := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 4 := ⟨k - 4, by omega⟩
  clear hk
  induction m generalizing x with
  | zero => exact state4 x
  | succ m ih =>
    have h4 : m + 1 + 4 = (m + 4) + 1 := by omega
    rw [h4, state, step, ih, ih, ih]
    rfl

private lemma offCount_ge4 (k : ℕ) (hk : 4 ≤ k) : offCount (state 233 k) k = 0 := by
  unfold offCount
  apply Finset.sum_eq_zero
  intro i _
  rw [state_ge4 k hk]
  rfl

private lemma a_val : a 0 = 0 ∧ a 1 = 3 ∧ a 2 = 5 ∧ a 3 = 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

private lemma a_ge3 (n : ℕ) (hn : 2 < n) : a n = 6 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  clear hn
  induction m with
  | zero => exact a_val.2.2.2
  | succ m ih =>
    have hstep : a (m + 1 + 3) = a (m + 3) + offCount (state 233 (m + 4)) (m + 4) := by
      unfold a
      rw [show m + 1 + 3 + 1 = (m + 3 + 1) + 1 by omega, Finset.sum_range_succ]
    rw [hstep, ih, offCount_ge4 (m + 4) (by omega), add_zero]

private lemma A_mul_one_sub_X :
    A * (1 - X) = (X * (3 + 2 * X + X ^ 2) : ℚ⟦X⟧) := by
  ext n
  have h1 : coeff n (A * (1 - X)) = coeff n A - (if n = 0 then 0 else coeff (n - 1) A) := by
    rw [mul_sub, mul_one, map_sub]
    congr 1
    cases n with
    | zero => simp
    | succ k =>
      have := PowerSeries.coeff_mul_X_pow' (n := k + 1) (d := 1) A
      simp at this ⊢
  have h2 : coeff n ((X * (3 + 2 * X + X ^ 2)) : ℚ⟦X⟧) =
      if n = 1 then 3 else if n = 2 then 2 else if n = 3 then 1 else 0 := by
    have hexp : (X * (3 + 2 * X + X ^ 2) : ℚ⟦X⟧) = C 3 * X + C 2 * X ^ 2 + X ^ 3 := by
      simp [map_ofNat]; ring
    rw [hexp]
    simp only [map_add, coeff_C_mul, coeff_X, coeff_X_pow]
    rcases n with _ | _ | _ | _ | k <;> simp
  rw [h1, h2]
  simp only [A, PowerSeries.coeff_mk]
  rcases n with _ | _ | _ | _ | k
  · simp [a_val.1]
  · simp [a_val.1, a_val.2.1]
  · simp [a_val.2.1, a_val.2.2.1]; norm_num
  · simp [a_val.2.2.1, a_val.2.2.2]; norm_num
  · have ha1 : a (k + 4) = 6 := a_ge3 (k + 4) (by omega)
    have ha2 : a (k + 3) = 6 := a_ge3 (k + 3) (by omega)
    simp [ha1, ha2]

theorem main_proof :
    (∀ n : ℕ, 2 < n → a n = 6) ∧
    (∀ n : ℕ, 3 < n → a n = a (n - 1)) ∧
    A = X * (3 + 2 * X + X ^ 2) * (1 - X)⁻¹ := by
  refine ⟨a_ge3, ?_, ?_⟩
  · intro n hn
    rw [a_ge3 n (by omega), a_ge3 (n - 1) (by omega)]
  · have hmul : (1 - X : ℚ⟦X⟧) * (1 - X)⁻¹ = 1 :=
      PowerSeries.mul_inv_cancel (1 - X) (by simp)
    calc A = A * ((1 - X) * (1 - X)⁻¹) := by rw [hmul, mul_one]
      _ = (A * (1 - X)) * (1 - X)⁻¹ := by rw [mul_assoc]
      _ = X * (3 + 2 * X + X ^ 2) * (1 - X)⁻¹ := by rw [A_mul_one_sub_X]

end OMA.P267884

theorem OMA.solution : type_of% @OMA.S_oeis_a267884.main := OMA.P267884.main_proof
