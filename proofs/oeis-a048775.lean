import OMAStatements.S_oeis_a048775

/-!
Proof of OEIS A048775: from the binomial ratio
(m + 2) * choose (2*m + 3) (m + 2) = 2 * (2*m + 3) * choose (2*m + 1) (m + 1),
expressing a(k+5), ..., a(k+2) over Q in terms of choose (2*k + 3) (k + 2)
reduces Mathar's order-4 recurrence to an exact rational identity.
-/

private lemma binom_ratio_nat (m : ℕ) :
    (m + 2) * (2 * m + 3).choose (m + 2) = 2 * (2 * m + 3) * (2 * m + 1).choose (m + 1) := by
  have hsymm : (2 * m + 1).choose (m + 1) = (2 * m + 1).choose m := by
    rw [← Nat.choose_symm (by omega : m + 1 ≤ 2 * m + 1)]
    congr 1
    omega
  have h1 := Nat.add_one_mul_choose_eq (2 * m + 1) m
  have h2 := Nat.add_one_mul_choose_eq (2 * m + 2) (m + 1)
  have hmul : ((m + 2) * (2 * m + 3).choose (m + 2)) * (m + 1) =
      (2 * (2 * m + 3) * (2 * m + 1).choose (m + 1)) * (m + 1) := by
    calc
      ((m + 2) * (2 * m + 3).choose (m + 2)) * (m + 1)
          = ((2 * m + 3).choose (m + 2) * (m + 2)) * (m + 1) := by ring
      _ = ((2 * m + 3) * (2 * m + 2).choose (m + 1)) * (m + 1) := by
          rw [show 2 * m + 3 = (2 * m + 2) + 1 by omega,
            show m + 2 = (m + 1) + 1 by omega, ← h2]
      _ = (2 * m + 3) * ((2 * m + 2).choose (m + 1) * (m + 1)) := by ring
      _ = (2 * m + 3) * ((2 * m + 2) * (2 * m + 1).choose m) := by
          rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, ← h1]
      _ = (2 * (2 * m + 3) * (2 * m + 1).choose (m + 1)) * (m + 1) := by
          rw [hsymm]
          ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.succ_pos m) hmul

private lemma binom_step_rat (m : ℕ) :
    (((2 * (m + 1) + 1).choose (m + 2) : ℕ) : ℚ) =
      2 * (2 * (m : ℚ) + 3) / ((m : ℚ) + 2) * (((2 * m + 1).choose (m + 1) : ℕ) : ℚ) := by
  have h : ((m : ℚ) + 2) * (((2 * (m + 1) + 1).choose (m + 2) : ℕ) : ℚ) =
      2 * (2 * (m : ℚ) + 3) * (((2 * m + 1).choose (m + 1) : ℕ) : ℚ) := by
    rw [show 2 * (m + 1) + 1 = 2 * m + 3 by omega]
    exact_mod_cast binom_ratio_nat m
  have hden : (m : ℚ) + 2 ≠ 0 := by positivity
  field_simp [hden]
  linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a048775.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have hq :
      (((((k + 5 : ℕ) : ℤ) + 1) * OMA.S_oeis_a048775.a (k + 5) +
          (-7 * ((k + 5 : ℕ) : ℤ) - 2) * OMA.S_oeis_a048775.a (k + 5 - 1) +
          3 * (5 * ((k + 5 : ℕ) : ℤ) - 3) * OMA.S_oeis_a048775.a (k + 5 - 2) +
          (-13 * ((k + 5 : ℕ) : ℤ) + 20) * OMA.S_oeis_a048775.a (k + 5 - 3) +
          2 * (2 * ((k + 5 : ℕ) : ℤ) - 5) * OMA.S_oeis_a048775.a (k + 5 - 4) : ℤ) : ℚ) = 0 := by
    simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
      show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega]
    unfold OMA.S_oeis_a048775.a
    push_cast
    rw [binom_step_rat (k + 4), binom_step_rat (k + 3), binom_step_rat (k + 2),
      binom_step_rat (k + 1)]
    push_cast
    have hd3 : (k : ℚ) + 1 + 2 ≠ 0 := by positivity
    have hd4 : (k : ℚ) + 2 + 2 ≠ 0 := by positivity
    have hd5 : (k : ℚ) + 3 + 2 ≠ 0 := by positivity
    have hd6 : (k : ℚ) + 4 + 2 ≠ 0 := by positivity
    field_simp
    ring
  exact_mod_cast hq
