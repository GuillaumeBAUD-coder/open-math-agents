import OMAStatements.S_oeis_a220902

/-!
Proof of OEIS A220902: from the Catalan ratio identity
(m + 2) * catalan (m + 1) = (4 * m + 2) * catalan m, expressing a(k+5), ..., a(k+2)
over Q in terms of catalan k reduces Mathar's order-3 linear recurrence to an algebraic identity.
-/

private lemma catalan_ratio_nat (m : ℕ) :
    (m + 2) * catalan (m + 1) = (4 * m + 2) * catalan m := by
  have h1 := succ_mul_catalan_eq_centralBinom (m + 1)
  have h2 := Nat.succ_mul_centralBinom_succ m
  have h3 := succ_mul_catalan_eq_centralBinom m
  have hmul : (m + 1) * ((m + 2) * catalan (m + 1)) = (m + 1) * ((4 * m + 2) * catalan m) := by
    calc
      (m + 1) * ((m + 2) * catalan (m + 1))
          = (m + 1) * (m + 1).centralBinom := by rw [← h1]
      _ = 2 * (2 * m + 1) * m.centralBinom := h2
      _ = 2 * (2 * m + 1) * ((m + 1) * catalan m) := by rw [← h3]
      _ = (m + 1) * ((4 * m + 2) * catalan m) := by ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos m) hmul

private lemma catalan_step_rat (m : ℕ) :
    (catalan (m + 1) : ℚ) = (4 * (m : ℚ) + 2) / ((m : ℚ) + 2) * (catalan m : ℚ) := by
  have h : ((m : ℚ) + 2) * (catalan (m + 1) : ℚ) = (4 * (m : ℚ) + 2) * (catalan m : ℚ) := by
    exact_mod_cast catalan_ratio_nat m
  have hden : (m : ℚ) + 2 ≠ 0 := by positivity
  field_simp [hden]
  linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a220902.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have hq :
      (((((k + 5 : ℕ) : ℤ) + 1) * OMA.S_oeis_a220902.a (k + 5) +
          (-5 * ((k + 5 : ℕ) : ℤ) + 3) * OMA.S_oeis_a220902.a (k + 5 - 1) +
          (5 * ((k + 5 : ℕ) : ℤ) - 13) * OMA.S_oeis_a220902.a (k + 5 - 2) +
          2 * (-2 * ((k + 5 : ℕ) : ℤ) + 9) * OMA.S_oeis_a220902.a (k + 5 - 3) : ℤ) : ℚ) = 0 := by
    simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
      show k + 5 - 3 = k + 2 by omega]
    unfold OMA.S_oeis_a220902.a
    simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
      show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
      show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
      show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
    push_cast
    rw [catalan_step_rat (k + 4), catalan_step_rat (k + 3), catalan_step_rat (k + 2),
      catalan_step_rat (k + 1), catalan_step_rat k]
    push_cast
    have hd2 : (k : ℚ) + 2 ≠ 0 := by positivity
    have hd3 : (k : ℚ) + 1 + 2 ≠ 0 := by positivity
    have hd4 : (k : ℚ) + 2 + 2 ≠ 0 := by positivity
    have hd5 : (k : ℚ) + 3 + 2 ≠ 0 := by positivity
    have hd6 : (k : ℚ) + 4 + 2 ≠ 0 := by positivity
    field_simp
    ring
  exact_mod_cast hq
