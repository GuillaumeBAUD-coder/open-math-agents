import OMAStatements.S_oeis_a126477

-- Credit: @Dariusthedoggie
-- Proof: transfer matrix; the vectors M ^ n *ᵥ 1 satisfy the g.f. recurrence (checked by decide +kernel at the base).

namespace OMA.P126477

open OMA.S_oeis_a126477 PowerSeries Matrix

/-- Adjacent digits are close in the word `x`. -/
def good {n : ℕ} (x : Fin n → Fin 9) : Prop :=
  ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → close (x i) (x j)

instance {n : ℕ} (x : Fin n → Fin 9) : Decidable (good x) := by
  unfold good
  infer_instance

lemma good_cons {m : ℕ} (b : Fin 9) (y : Fin (m + 1) → Fin 9) :
    good (Fin.cons b y : Fin (m + 2) → Fin 9) ↔ close b (y 0) ∧ good y := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h 0 1 (by simp)
      simpa using this
    · intro i j hij
      have := h i.succ j.succ (by simp [hij])
      simpa using this
  · rintro ⟨h0, hy⟩ i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        have hj : j = 0 := by ext; simp at hij; omega
        subst hj
        simpa using h0
    | succ i =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        simp only [Fin.cons_succ]
        exact hy i j (by simp at hij; omega)

/-- The transfer matrix. -/
def M : Matrix (Fin 9) (Fin 9) ℤ := Matrix.of fun d e => if close d e then 1 else 0

def ones : Fin 9 → ℤ := fun _ => 1

/-- The vectors `M ^ n *ᵥ ones`, computed step by step. -/
def w : ℕ → Fin 9 → ℤ
  | 0 => ones
  | n + 1 => M *ᵥ w n

lemma w_eq (n : ℕ) : w n = M ^ n *ᵥ ones := by
  induction n with
  | zero => simp [w]
  | succ n ih => rw [w, ih, pow_succ', Matrix.mulVec_mulVec]

/-- Good words of length `n + 1` starting with `d`. -/
def W (n : ℕ) (d : Fin 9) : ℤ :=
  ∑ y : Fin (n + 1) → Fin 9, if y 0 = d ∧ good y then 1 else 0

lemma sum_cons {m : ℕ} (f : (Fin (m + 2) → Fin 9) → ℤ) :
    ∑ x, f x = ∑ b : Fin 9, ∑ y : Fin (m + 1) → Fin 9, f (Fin.cons b y) := by
  rw [← (Fin.consEquiv (fun _ => Fin 9)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma fiber (m : ℕ) (g : (Fin (m + 1) → Fin 9) → ℤ) :
    ∑ y, g y = ∑ c : Fin 9, ∑ y : Fin (m + 1) → Fin 9, if y 0 = c then g y else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_ite_eq]
  simp

lemma W_zero : W 0 = ones := by
  funext d
  unfold W ones good
  fin_cases d <;> decide

lemma W_succ (n : ℕ) : W (n + 1) = M *ᵥ W n := by
  funext d
  unfold W
  rw [sum_cons]
  simp only [Fin.cons_zero, good_cons]
  rw [Finset.sum_eq_single d (by intro b' _ hb'; simp [hb']) (by simp)]
  simp only [true_and]
  rw [fiber]
  simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : y 0 = c
  · subst hy
    by_cases hc : close d (y 0) <;> simp [hc]
  · simp [hy]

lemma W_eq (n : ℕ) : W n = M ^ n *ᵥ ones := by
  induction n with
  | zero => simp [W_zero]
  | succ n ih => rw [W_succ, ih, pow_succ', Matrix.mulVec_mulVec]

lemma a_succ (n : ℕ) : (a (n + 1) : ℤ) = ∑ d, (M ^ n *ᵥ ones) d := by
  rw [← W_eq]
  unfold W a
  rw [Finset.card_filter]
  push_cast
  rw [fiber]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro y _
  unfold good
  by_cases hy : y 0 = c <;> simp [hy]

lemma a_w (k : ℕ) : (a (k + 1) : ℤ) = ∑ x, w k x := by
  rw [a_succ, w_eq]

lemma a_succ' (m k : ℕ) : (a (m + k + 1) : ℤ) = ∑ x, (M ^ m *ᵥ w k) x := by
  rw [a_succ, w_eq, Matrix.mulVec_mulVec, pow_add]

lemma base_rel : w 4 = (7 : ℤ) • w 3 + (-6 : ℤ) • w 2 + (-2 : ℤ) • w 1 + (2 : ℤ) • w 0 := by
  decide +kernel

lemma sum_rel (m : ℕ) : ∑ x, (M ^ m *ᵥ w 4) x =
      7 * ∑ x, (M ^ m *ᵥ w 3) x +
      -6 * ∑ x, (M ^ m *ᵥ w 2) x +
      -2 * ∑ x, (M ^ m *ᵥ w 1) x +
      2 * ∑ x, (M ^ m *ᵥ w 0) x := by
  rw [base_rel]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, Finset.mul_sum]

lemma rec_all (n : ℕ) (hn : 5 ≤ n) : (a n : ℤ) = 7 * a (n - 1) - 6 * a (n - 2) - 2 * a (n - 3) + 2 * a (n - 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 + 1 := ⟨n - 5, by omega⟩
  rw [show m + 4 + 1 - 1 = m + 3 + 1 by omega,
      show m + 4 + 1 - 2 = m + 2 + 1 by omega,
      show m + 4 + 1 - 3 = m + 1 + 1 by omega,
      show m + 4 + 1 - 4 = m + 0 + 1 by omega]
  rw [a_succ' m 4, a_succ' m 3, a_succ' m 2, a_succ' m 1, a_succ' m 0]
  linear_combination sum_rel m

lemma v0 : a 0 = 1 := by decide

lemma v1 : a 1 = 9 := by
  have h : ∑ x, w 0 x = 9 := by decide +kernel
  exact_mod_cast (a_w 0).trans h

lemma v2 : a 2 = 51 := by
  have h : ∑ x, w 1 x = 51 := by decide +kernel
  exact_mod_cast (a_w 1).trans h

lemma v3 : a 3 = 301 := by
  have h : ∑ x, w 2 x = 301 := by decide +kernel
  exact_mod_cast (a_w 2).trans h

lemma v4 : a 4 = 1787 := by
  have h : ∑ x, w 3 x = 1787 := by decide +kernel
  exact_mod_cast (a_w 3).trans h

lemma hrec : ∀ n : ℕ, 4 < n → (a n : ℤ) = 7 * a (n - 1) - 6 * a (n - 2) - 2 * a (n - 3) + 2 * a (n - 4) := by
  intro n hn
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> simp [v0, v1, v2, v3, v4]
  · exact rec_all n h

lemma gf : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 7 * X + 6 * X ^ 2 + 2 * X ^ 3 - 2 * X ^ 4) =
    1 + 2 * X - 6 * X ^ 2 + 2 * X ^ 4 := by
  set S := PowerSeries.mk (fun n => (a n : ℚ)) with hS
  have hl : S * (1 - 7 * X + 6 * X ^ 2 + 2 * X ^ 3 - 2 * X ^ 4) =
      S + C (-7 : ℚ) * (S * X ^ 1) + C (6 : ℚ) * (S * X ^ 2) + C (2 : ℚ) * (S * X ^ 3) + C (-2 : ℚ) * (S * X ^ 4) := by
    simp only [map_neg, map_ofNat, map_one]; ring
  have hr : (1 + 2 * X - 6 * X ^ 2 + 2 * X ^ 4 : PowerSeries ℚ) =
      C (1 : ℚ) + C (2 : ℚ) * X ^ 1 + C (-6 : ℚ) * X ^ 2 + C (2 : ℚ) * X ^ 4 := by
    simp only [map_neg, map_ofNat, map_one]; ring
  rw [hl, hr]
  ext n
  simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C_mul_X_pow, coeff_C, hS, coeff_mk]
  rcases Nat.lt_or_ge n 5 with hn | hn
  · interval_cases n <;> simp [v0, v1, v2, v3, v4] <;> norm_num
  · have hq : (a n : ℚ) = 7 * a (n - 1) - 6 * a (n - 2) - 2 * a (n - 3) + 2 * a (n - 4) := by
      exact_mod_cast rec_all n (by omega)
    have c1 : 1 ≤ n := by omega
    have c2 : 2 ≤ n := by omega
    have c3 : 3 ≤ n := by omega
    have c4 : 4 ≤ n := by omega
    have d0 : n ≠ 0 := by omega
    have d1 : n ≠ 1 := by omega
    have d2 : n ≠ 2 := by omega
    have d3 : n ≠ 3 := by omega
    have d4 : n ≠ 4 := by omega
    have e1 : n - 1 ≠ 0 := by omega
    have e2 : n - 2 ≠ 0 := by omega
    have e3 : n - 3 ≠ 0 := by omega
    have e4 : n - 4 ≠ 0 := by omega
    simp only [c1, c2, c3, c4, d0, d1, d2, d3, d4, e1, e2, e3, e4, if_true, if_false]
    linear_combination hq

theorem main_proof :
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 7 * X + 6 * X ^ 2 + 2 * X ^ 3 - 2 * X ^ 4) =
      1 + 2 * X - 6 * X ^ 2 + 2 * X ^ 4) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 7 * a (n - 1) - 6 * a (n - 2) - 2 * a (n - 3) + 2 * a (n - 4)) :=
  ⟨gf, hrec⟩

end OMA.P126477

theorem OMA.solution : type_of% @OMA.S_oeis_a126477.main := OMA.P126477.main_proof
