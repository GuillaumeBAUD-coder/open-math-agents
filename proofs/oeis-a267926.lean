import OMAStatements.S_oeis_a267926

-- Credit: @Dariusthedoggie
-- Proof: explicit rule-246 pattern by induction (cell off iff i = t + 1 mod 4 or outside the cone), then a(n+2) = 16 a(n) + 7.

namespace OMA.P267926

open OMA.S_oeis_a267926 PowerSeries

lemma rule246 (l c r : Bool) :
    ruleOut 246 l c r = !((!l && !c && !r) || (!l && c && r)) := by
  cases l <;> cases c <;> cases r <;> decide

/-- The explicit pattern of rule 246. -/
def P (t : ℕ) (i : ℤ) : Bool :=
  decide (-(t : ℤ) ≤ i ∧ i ≤ t ∧ (i - t - 1) % 4 ≠ 0)

lemma cell_eq (t : ℕ) : ∀ i : ℤ, cell 246 t i = P t i := by
  induction t with
  | zero =>
    intro i
    simp only [cell, P]
    by_cases h : i = 0
    · subst h; decide
    · simp only [h, decide_false]
      symm
      simp only [decide_eq_false_iff_not]
      omega
  | succ t ih =>
    intro i
    simp only [cell, ih, rule246]
    rw [Bool.eq_iff_iff]
    simp only [P, Bool.not_eq_true', Bool.or_eq_false_iff, Bool.and_eq_false_imp,
      Bool.not_eq_false', Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true,
      decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_eq_eq_not, Bool.not_true,
      Bool.not_false]
    push_cast
    constructor
    · intro h
      omega
    · intro h
      omega

lemma a_eq (n : ℕ) : a n = ∑ j ∈ Finset.range (2 * n + 1),
    if ((j : ℤ) - 2 * n - 1) % 4 = 0 then 0 else (2 : ℤ) ^ (2 * n - j) := by
  unfold a
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [cell_eq]
  unfold P
  by_cases h : ((j : ℤ) - 2 * n - 1) % 4 = 0
  · rw [if_pos h, if_neg]
    simp only [decide_eq_true_eq]
    omega
  · rw [if_neg h, if_pos]
    simp only [decide_eq_true_eq]
    omega

lemma a_step (n : ℕ) : a (n + 2) = 16 * a n + 7 := by
  rw [a_eq, a_eq, show 2 * (n + 2) + 1 = 2 * n + 1 + 1 + 1 + 1 + 1 by ring]
  have hs : ∑ j ∈ Finset.range (2 * n + 1),
      (if ((j : ℤ) - 2 * ((n + 2 : ℕ) : ℤ) - 1) % 4 = 0 then 0 else (2 : ℤ) ^ (2 * (n + 2) - j)) =
      16 * ∑ j ∈ Finset.range (2 * n + 1),
        (if ((j : ℤ) - 2 * n - 1) % 4 = 0 then 0 else (2 : ℤ) ^ (2 * n - j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have hc : (((j : ℤ) - 2 * ((n + 2 : ℕ) : ℤ) - 1) % 4 = 0) ↔ (((j : ℤ) - 2 * n - 1) % 4 = 0) := by
      push_cast; omega
    by_cases h : ((j : ℤ) - 2 * n - 1) % 4 = 0
    · rw [if_pos (hc.2 h), if_pos h]; ring
    · rw [if_neg (fun h' => h (hc.1 h')), if_neg h,
        show 2 * (n + 2) - j = (2 * n - j) + 4 by omega, pow_add]
      ring
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, hs]
  have x1 : 2 * (n + 2) - (2 * n + 1 + 1) = 2 := by omega
  have x2 : 2 * (n + 2) - (2 * n + 1 + 1 + 1) = 1 := by omega
  have x3 : 2 * (n + 2) - (2 * n + 1 + 1 + 1 + 1) = 0 := by omega
  rw [x1, x2, x3]
  split_ifs <;> first | (exfalso; push_cast at *; omega) | ring

lemma v0 : a 0 = 1 := by decide +kernel
lemma v1 : a 1 = 7 := by decide +kernel
lemma v2 : a 2 = 23 := by decide +kernel

lemma rec_all (n : ℕ) (hn : 3 ≤ n) : (a n : ℚ) = a (n - 1) + 16 * a (n - 2) - 16 * a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  have h1 := a_step (m + 1)
  have h2 := a_step m
  have h1' : (a (m + 3) : ℚ) = 16 * a (m + 1) + 7 := by exact_mod_cast h1
  have h2' : (a (m + 2) : ℚ) = 16 * a m + 7 := by exact_mod_cast h2
  linear_combination h1' - h2'

lemma gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 4 * X) * (1 + 4 * X) : PowerSeries ℚ) =
    1 + 6 * X := by
  set S := PowerSeries.mk (fun n => (a n : ℚ)) with hS
  have hl : S * ((1 - X) * (1 - 4 * X) * (1 + 4 * X) : PowerSeries ℚ) =
      S + C (-1 : ℚ) * (S * X ^ 1) + C (-16 : ℚ) * (S * X ^ 2) + C (16 : ℚ) * (S * X ^ 3) := by
    simp only [map_neg, map_ofNat, map_one]; ring
  have hr : (1 + 6 * X : PowerSeries ℚ) = C (1 : ℚ) + C (6 : ℚ) * X ^ 1 := by
    simp only [map_ofNat, map_one]; ring
  rw [hl, hr]
  ext n
  simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C_mul_X_pow, coeff_C, hS, coeff_mk]
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> simp [v0, v1, v2] <;> norm_num
  · have hq := rec_all n hn
    have c1 : 1 ≤ n := by omega
    have c2 : 2 ≤ n := by omega
    have c3 : 3 ≤ n := by omega
    have d0 : n ≠ 0 := by omega
    have d1 : n ≠ 1 := by omega
    have e1 : n - 1 ≠ 0 := by omega
    simp only [c1, c2, c3, d0, d1, e1, if_true, if_false]
    linear_combination hq

theorem main_proof :
    (∀ n : ℕ, 3 ≤ n → (a n : ℚ) = a (n - 1) + 16 * a (n - 2) - 16 * a (n - 3)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 4 * X) * (1 + 4 * X) : PowerSeries ℚ) = 1 + 6 * X) :=
  ⟨rec_all, gf⟩

end OMA.P267926

theorem OMA.solution : type_of% @OMA.S_oeis_a267926.main := OMA.P267926.main_proof
