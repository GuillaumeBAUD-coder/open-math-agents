import OMAStatements.S_oeis_a269822

-- Problem: A269822, n X 1 arrays over 0..4 with exactly one adjacent pair totalling four.
-- Credit: @Dariusthedoggie
-- Proof idea: every entry has exactly one partner totalling four. Fixing the first entry b,
-- Z m b = 4^m columns have no such pair and 4 * O m b = m * 4^m have exactly one (induction
-- by prepending an entry), so 4 * a(m+1) = 5 * m * 4^m.

namespace OMA.P269822

open OMA.S_oeis_a269822 PowerSeries

lemma sum_cons {m : ℕ} (f : (Fin (m + 2) → Fin 5) → ℕ) :
    ∑ x, f x = ∑ b : Fin 5, ∑ y : Fin (m + 1) → Fin 5, f (Fin.cons b y) := by
  rw [← (Fin.consEquiv (fun _ => Fin 5)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma pairs_cons (m : ℕ) (b : Fin 5) (y : Fin (m + 1) → Fin 5) :
    pairsTotallingFour (m + 1) (Fin.cons b y) =
      (if (b : ℕ) + (y 0 : ℕ) = 4 then 1 else 0) + pairsTotallingFour m y := by
  unfold pairsTotallingFour
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.succ_zero_eq_one, Fin.cons_one]
  congr 1

/-- Columns starting with `b` and no adjacent pair totalling four. -/
def Z (m : ℕ) (b : Fin 5) : ℕ :=
  ∑ y : Fin (m + 1) → Fin 5, if y 0 = b ∧ pairsTotallingFour m y = 0 then 1 else 0

/-- Columns starting with `b` and exactly one adjacent pair totalling four. -/
def O (m : ℕ) (b : Fin 5) : ℕ :=
  ∑ y : Fin (m + 1) → Fin 5, if y 0 = b ∧ pairsTotallingFour m y = 1 then 1 else 0

lemma fiber (m : ℕ) (g : (Fin (m + 1) → Fin 5) → ℕ) :
    ∑ y, g y = ∑ c : Fin 5, ∑ y : Fin (m + 1) → Fin 5, if y 0 = c then g y else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_ite_eq]
  simp

lemma count_ne (b : Fin 5) :
    ∑ c : Fin 5, (if (b : ℕ) + (c : ℕ) = 4 then 0 else 1) = 4 := by
  fin_cases b <;> decide

lemma count_eq (b : Fin 5) :
    ∑ c : Fin 5, (if (b : ℕ) + (c : ℕ) = 4 then 1 else 0) = 1 := by
  fin_cases b <;> decide

lemma Z_zero (b : Fin 5) : Z 0 b = 1 := by
  unfold Z pairsTotallingFour
  fin_cases b <;> decide

lemma O_zero (b : Fin 5) : O 0 b = 0 := by
  unfold O pairsTotallingFour
  fin_cases b <;> decide

lemma Z_succ (m : ℕ) (b : Fin 5) :
    Z (m + 1) b = ∑ c : Fin 5, (if (b : ℕ) + (c : ℕ) = 4 then 0 else Z m c) := by
  unfold Z
  rw [sum_cons]
  simp only [Fin.cons_zero, pairs_cons]
  rw [Finset.sum_eq_single b (by intro b' _ hb'; simp [hb']) (by simp)]
  simp only [true_and]
  rw [fiber]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs with hbc
  · apply Finset.sum_eq_zero
    intro y _
    by_cases hy : y 0 = c <;> simp [hy, hbc]
  · apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y 0 = c <;> simp [hy, hbc]

lemma O_succ (m : ℕ) (b : Fin 5) :
    O (m + 1) b = ∑ c : Fin 5, (if (b : ℕ) + (c : ℕ) = 4 then Z m c else O m c) := by
  unfold O Z
  rw [sum_cons]
  simp only [Fin.cons_zero, pairs_cons]
  rw [Finset.sum_eq_single b (by intro b' _ hb'; simp [hb']) (by simp)]
  simp only [true_and]
  rw [fiber]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs with hbc
  · apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y 0 = c <;> simp [hy, hbc]
  · apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y 0 = c <;> simp [hy, hbc]

lemma Z_eq (m : ℕ) (b : Fin 5) : Z m b = 4 ^ m := by
  induction m generalizing b with
  | zero => exact Z_zero b
  | succ m ih =>
    rw [Z_succ]
    simp only [ih]
    have h : ∀ c : Fin 5, (if (b : ℕ) + (c : ℕ) = 4 then 0 else 4 ^ m) =
        4 ^ m * (if (b : ℕ) + (c : ℕ) = 4 then 0 else 1) := by
      intro c; split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun c _ => h c), ← Finset.mul_sum, count_ne, pow_succ]

lemma O_eq (m : ℕ) (b : Fin 5) : 4 * O m b = m * 4 ^ m := by
  induction m generalizing b with
  | zero => simp [O_zero]
  | succ m ih =>
    rw [O_succ, Finset.mul_sum]
    have h : ∀ c : Fin 5, 4 * (if (b : ℕ) + (c : ℕ) = 4 then Z m c else O m c) =
        4 ^ (m + 1) * (if (b : ℕ) + (c : ℕ) = 4 then 1 else 0) +
          m * 4 ^ m * (if (b : ℕ) + (c : ℕ) = 4 then 0 else 1) := by
      intro c
      split_ifs
      · rw [Z_eq, pow_succ]; ring
      · rw [ih c]; ring
    rw [Finset.sum_congr rfl (fun c _ => h c), Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, count_eq, count_ne, pow_succ]
    push_cast
    ring

lemma a_succ (m : ℕ) : 4 * a (m + 1) = 5 * (m * 4 ^ m) := by
  have : a (m + 1) = ∑ c : Fin 5, O m c := by
    show (Finset.univ.filter (fun x : Fin (m + 1) → Fin 5 => pairsTotallingFour m x = 1)).card = _
    unfold O
    rw [Finset.card_filter, fiber]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro y _
    rw [ite_and]
  rw [this, Finset.mul_sum]
  simp only [O_eq]
  simp

lemma a_formula (n : ℕ) (hn : 2 ≤ n) : a n = 5 * 4 ^ (n - 2) * (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have h := a_succ (k + 1)
  rw [show k + 2 - 2 = k by omega, show k + 2 - 1 = k + 1 by omega]
  rw [pow_succ] at h
  push_cast at h
  have : 4 * a (k + 1 + 1) = 4 * (5 * 4 ^ k * (k + 1)) := by rw [h]; ring
  have := Nat.eq_of_mul_eq_mul_left (by norm_num) this
  simpa using this

lemma a_one : a 1 = 0 := by
  unfold a pairsTotallingFour
  decide

lemma a_zero : a 0 = 0 := rfl

lemma rec3 (n : ℕ) (hn : 3 ≤ n) : (a n : ℤ) = 8 * a (n - 1) - 16 * a (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega]
  rw [a_formula (k + 3) (by omega), a_formula (k + 2) (by omega)]
  rcases k with _ | k
  · rw [a_one]; norm_num
  · rw [a_formula (k + 1 + 1) (by omega)]
    rw [show k + 1 + 3 - 2 = k + 2 by omega, show k + 1 + 2 - 2 = k + 1 by omega,
      show k + 1 + 1 - 2 = k by omega]
    push_cast
    ring

theorem main_proof :
    (∀ n : ℕ, 3 ≤ n → (a n : ℤ) = 8 * a (n - 1) - 16 * a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 4 * X) ^ 2 = 5 * X ^ 2) ∧
    (∀ n : ℕ, 1 ≤ n → a n = 5 * 4 ^ (n - 2) * (n - 1)) := by
  refine ⟨rec3, ?_, fun n hn => ?_⟩
  swap
  · rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain rfl : n = 1 := by omega
      simp [a_one]
    · exact a_formula n h2
  have hl : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 4 * X) ^ 2 =
      PowerSeries.mk (fun n => (a n : ℚ)) - C (8 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1) +
        C (16 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2) := by
    simp only [map_ofNat]; ring
  have hr : (5 : PowerSeries ℚ) * X ^ 2 = C (5 : ℚ) * X ^ 2 := by simp only [map_ofNat]
  rw [hl, hr]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C_mul_X_pow, coeff_C, coeff_mk]
  have v2 : a 2 = 5 := by rw [a_formula 2 (le_refl _)]; norm_num
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> simp [a_zero, a_one, v2]
  · have hq : (a n : ℚ) = 8 * a (n - 1) - 16 * a (n - 2) := by exact_mod_cast rec3 n hn
    have c1 : 1 ≤ n := by omega
    have c2 : 2 ≤ n := by omega
    have d2 : n ≠ 2 := by omega
    have e2 : n - 2 ≠ 0 := by omega
    simp only [c1, c2, d2, e2, if_true, if_false]
    rw [hq]; ring

end OMA.P269822

theorem OMA.solution : type_of% @OMA.S_oeis_a269822.main := OMA.P269822.main_proof
