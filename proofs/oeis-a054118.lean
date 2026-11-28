import OMAStatements.S_oeis_a054118

namespace OMA.P_oeis_a054118

open OMA.S_oeis_a054118

/-- The row sum `r(h)`. -/
def R (h : ℕ) : ℕ := ∑ j ∈ Finset.range (h + 1), T h j

lemma T_zero_left (k : ℕ) : T 0 k = 1 := by
  rw [T]

lemma T_succ_zero (n : ℕ) : T (n + 1) 0 = 1 := by
  rw [T]

lemma T_succ_one (n : ℕ) : T (n + 1) 1 = R n := by
  rw [T, R]

lemma T_succ_add_two (n k : ℕ) :
    T (n + 1) (k + 2) = T (n + 1) (k + 1) + R (n + 1 - (k + 2)) := by
  rw [T, R]

/-- `T(m+2, k+2) = r(m+1) + T(m+1, k+1)`. -/
lemma key (m k : ℕ) : T (m + 2) (k + 2) = R (m + 1) + T (m + 1) (k + 1) := by
  induction k with
  | zero =>
    rw [T_succ_add_two, T_succ_one, T_succ_one]
    congr 2
  | succ k ih =>
    rw [T_succ_add_two, ih, T_succ_add_two (m) k]
    have : m + 1 + 1 - (k + 1 + 2) = m + 1 - (k + 2) := by omega
    rw [this]
    ring

lemma R_succ_succ (m : ℕ) : R (m + 2) = (m + 3) * R (m + 1) := by
  have h1 : R (m + 2) = T (m + 2) 0 + T (m + 2) 1 +
      ∑ k ∈ Finset.range (m + 1), T (m + 2) (k + 2) := by
    rw [R, Finset.sum_range_succ', Finset.sum_range_succ']
    ring
  have h2 : R (m + 1) = T (m + 1) 0 + ∑ k ∈ Finset.range (m + 1), T (m + 1) (k + 1) := by
    rw [R, Finset.sum_range_succ']
    ring
  rw [h1]
  simp only [key, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  rw [T_succ_zero, T_succ_one]
  rw [T_succ_zero] at h2
  nlinarith [h2]

lemma a_step (n : ℕ) (hn : 5 ≤ n) : a n = a (n - 1) + R (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have e1 : a (m + 5) = T (m + 3 + 2) (m + 2) := by
    unfold a; congr 1
  have e2 : a (m + 5 - 1) = T (m + 3 + 1) (m + 1) := by
    unfold a; congr 1
  rw [e1, e2, show m + 3 + 2 = (m + 3) + 2 from rfl, key]
  have : m + 5 - 1 = m + 3 + 1 := by omega
  rw [this]
  ring

end OMA.P_oeis_a054118

theorem OMA.solution : type_of% @OMA.S_oeis_a054118.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have h1 := OMA.P_oeis_a054118.a_step (m + 6) (by omega)
  have h2 := OMA.P_oeis_a054118.a_step (m + 5) (by omega)
  have h3 := OMA.P_oeis_a054118.R_succ_succ (m + 3)
  have e1 : m + 6 - 1 = m + 5 := by omega
  have e2 : m + 6 - 2 = m + 4 := by omega
  have e3 : m + 5 - 1 = m + 4 := by omega
  rw [e1] at h1 ⊢
  rw [e2]
  rw [e3] at h2
  rw [show m + 3 + 2 = m + 5 from rfl, show m + 3 + 1 = m + 4 from rfl] at h3
  rw [h1, h3]
  have h2' : (OMA.S_oeis_a054118.a (m + 5) : ℤ) =
      OMA.S_oeis_a054118.a (m + 4) + OMA.P_oeis_a054118.R (m + 4) := by
    exact_mod_cast h2
  push_cast
  rw [h2']
  ring
