import OMAStatements.S_oeis_a291515

namespace OMA.S_oeis_a291515

open PowerSeries





lemma ceil_div (m d q : ℕ) (hd : 0 < d) (h1 : (q : ℤ) * d < m + d) (h2 : (m : ℤ) ≤ q * d) :
    ⌈(m : ℚ) / d⌉ = q := by
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  rw [Int.ceil_eq_iff]
  constructor
  · rw [lt_div_iff₀ hdq]
    have : ((q : ℤ) : ℚ) * d < (m : ℚ) + d := by exact_mod_cast h1
    push_cast at this ⊢
    linarith
  · rw [div_le_iff₀ hdq]
    have : ((m : ℤ) : ℚ) ≤ ((q : ℤ) : ℚ) * d := by exact_mod_cast h2
    push_cast at this ⊢
    linarith

/-- The closed values c(d). -/
def cv (d : ℕ) : ℤ :=
  if d = 1 then -17 else if d = 2 then -17 else if d = 3 then -19 else if d = 4 then -16 else if d = 5 then -15 else if d = 6 then -17 else -2 * d

lemma val_eq (n d : ℕ) (hd : 1 ≤ d) : val n 3 6 d = min (n : ℤ) (cv d) := by
  rcases Nat.lt_or_ge d 7 with hlt | hge
  · interval_cases d
    · rw [val, ceil_div 3 1 3 (by norm_num) (by norm_num) (by norm_num),
        ceil_div 6 1 6 (by norm_num) (by norm_num) (by norm_num)]
      norm_num [delta, cv]
    · rw [val, ceil_div 3 2 2 (by norm_num) (by norm_num) (by norm_num),
        ceil_div 6 2 3 (by norm_num) (by norm_num) (by norm_num)]
      norm_num [delta, cv]
    · rw [val, ceil_div 3 3 1 (by norm_num) (by norm_num) (by norm_num),
        ceil_div 6 3 2 (by norm_num) (by norm_num) (by norm_num)]
      norm_num [delta, cv]
    · rw [val, ceil_div 3 4 1 (by norm_num) (by norm_num) (by norm_num),
        ceil_div 6 4 2 (by norm_num) (by norm_num) (by norm_num)]
      norm_num [delta, cv]
    · rw [val, ceil_div 3 5 1 (by norm_num) (by norm_num) (by norm_num),
        ceil_div 6 5 2 (by norm_num) (by norm_num) (by norm_num)]
      norm_num [delta, cv]
    · rw [val, ceil_div 3 6 1 (by norm_num) (by norm_num) (by norm_num),
        ceil_div 6 6 1 (by norm_num) (by norm_num) (by norm_num)]
      norm_num [delta, cv]
  · have hd' : (7 : ℤ) ≤ d := by exact_mod_cast hge
    rw [val, ceil_div 3 d 1 (by omega) (by push_cast; omega) (by push_cast; omega),
      ceil_div 6 d 1 (by omega) (by push_cast; omega) (by push_cast; omega)]
    have hcv : cv d = -2 * d := by
      unfold cv
      simp only [show d ≠ 1 by omega, show d ≠ 2 by omega, show d ≠ 3 by omega, show d ≠ 4 by omega, show d ≠ 5 by omega, show d ≠ 6 by omega, if_false]
    rw [hcv, if_neg (by push_cast; omega)]
    unfold delta
    rw [if_neg (by push_cast; omega), if_pos (by push_cast; omega)]
    congr 1
    push_cast
    ring

lemma uhat_eq (n : ℕ) :
    a n = (Nat.divisors n).fold min (n : ℤ) (fun d => min (n : ℤ) (cv d)) := by
  unfold a uhat
  apply Finset.fold_congr
  intro d hd
  exact val_eq n d (Nat.pos_of_mem_divisors hd)

lemma cv_ge (d : ℕ) : -2 * (d : ℤ) ≤ cv d ∨ -19 ≤ cv d := by
  unfold cv
  split_ifs <;> omega

/-- a(n) = -2n for n >= 10. -/
lemma a_big (n : ℕ) (hn : 10 ≤ n) : a n = -2 * n := by
  rw [uhat_eq]
  apply le_antisymm
  · rw [Finset.fold_min_le]
    right
    refine ⟨n, Nat.mem_divisors_self n (by omega), ?_⟩
    have : cv n = -2 * n := by
      unfold cv
      simp only [show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega, if_false]
    rw [this]
    omega
  · rw [Finset.le_fold_min]
    refine ⟨by omega, fun d hd => ?_⟩
    have hdn : d ≤ n := Nat.divisor_le hd
    have hdn' : (d : ℤ) ≤ n := by exact_mod_cast hdn
    rcases cv_ge d with h | h <;> omega

lemma values : a 1 = -17 ∧ a 2 = -17 ∧ a 3 = -19 ∧ a 4 = -17 ∧ a 5 = -17 ∧ a 6 = -19 ∧ a 7 = -17 ∧ a 8 = -17 ∧ a 9 = -19 := by
  simp only [uhat_eq]
  decide

/-- Wu's recurrence, for n > 11. -/
theorem recurrence (n : ℕ) (hn : 11 < n) : a n = 2 * a (n - 1) - a (n - 2) := by
  rw [a_big n (by omega), a_big (n - 1) (by omega), a_big (n - 2) (by omega)]
  push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega]
  ring

/-- Wu's g.f., as A(x) D(x) = N(x) in Z[[x]] (D has constant term -1 or 1, a unit). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * ((X - 1) ^ 2) =
    X * (-X ^ 10 + X ^ 9 - 2 * X ^ 8 - 2 * X ^ 7 + 4 * X ^ 6 - 2 * X ^ 5 - 2 * X ^ 4 + 4 * X ^ 3 -
      2 * X ^ 2 + 17 * X - 17) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * ((X - 1) ^ 2) =
      A - C 2 * (A * X ^ 1) + A * X ^ 2 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (-X ^ 10 + X ^ 9 - 2 * X ^ 8 - 2 * X ^ 7 + 4 * X ^ 6 - 2 * X ^ 5 - 2 * X ^ 4 +
    4 * X ^ 3 - 2 * X ^ 2 + 17 * X - 17) : ℤ⟦X⟧) =
      - X ^ 1 * C 17 + X ^ 2 * C 17 - X ^ 3 * C 2 + X ^ 4 * C 4 - X ^ 5 * C 2 - X ^ 6 * C 2 +
        X ^ 7 * C 4 - X ^ 8 * C 2 - X ^ 9 * C 2 + X ^ 10 - X ^ 11 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_mul_C, coeff_X_pow,
    coeff_mul_X_pow', hc]
  have v := values
  have w10 := a_big 10 (by norm_num)
  have w11 := a_big 11 (by norm_num)
  rcases Nat.lt_or_ge n 12 with hn | hn
  · interval_cases n <;> simp_all [w10, w11] <;> decide
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 12 := ⟨n - 12, by omega⟩
    have h := recurrence (q + 12) (by omega)
    simp only [show q + 12 - 1 = q + 11 by omega, show q + 12 - 2 = q + 10 by omega] at h ⊢
    simp only [show ¬ q + 12 = 0 by omega, show ¬ q + 11 = 0 by omega, show ¬ q + 10 = 0 by omega, show 1 ≤ q + 12 by omega, show 2 ≤ q + 12 by omega, show ¬ q + 12 = 1 by omega, show ¬ q + 12 = 2 by omega, show ¬ q + 12 = 3 by omega, show ¬ q + 12 = 4 by omega, show ¬ q + 12 = 5 by omega, show ¬ q + 12 = 6 by omega, show ¬ q + 12 = 7 by omega, show ¬ q + 12 = 8 by omega, show ¬ q + 12 = 9 by omega, show ¬ q + 12 = 10 by omega, show ¬ q + 12 = 11 by omega, if_true, if_false]
    rw [h]
    ring

/-- Controls: the entry's data a(1..70). -/
theorem controls : ∀ n : ℕ, 1 ≤ n → n ≤ 70 → a n = ([-17, -17, -19, -17, -17, -19, -17, -17, -19, -20, -22, -24, -26, -28, -30, -32, -34, -36, -38, -40, -42, -44, -46, -48, -50, -52, -54, -56, -58, -60, -62, -64, -66, -68, -70, -72, -74, -76, -78, -80, -82, -84, -86, -88, -90, -92, -94, -96, -98, -100, -102, -104, -106, -108, -110, -112, -114, -116, -118, -120, -122, -124, -126, -128, -130, -132, -134, -136, -138, -140] : List ℤ).getD (n - 1) 0 := by
  intro n h1 h2
  rcases Nat.lt_or_ge n 10 with hlt | hge
  · have v := values
    interval_cases n <;> simp only [v] <;> decide
  · rw [a_big n hge]
    have key : ∀ n : ℕ, 10 ≤ n → n ≤ 70 → (-2 : ℤ) * n = ([-17, -17, -19, -17, -17, -19, -17, -17, -19, -20, -22, -24, -26, -28, -30, -32, -34, -36, -38, -40, -42, -44, -46, -48, -50, -52, -54, -56, -58, -60, -62, -64, -66, -68, -70, -72, -74, -76, -78, -80, -82, -84, -86, -88, -90, -92, -94, -96, -98, -100, -102, -104, -106, -108, -110, -112, -114, -116, -118, -120, -122, -124, -126, -128, -130, -132, -134, -136, -138, -140] : List ℤ).getD (n - 1) 0 := by
      decide
    exact key n hge h2

/-- Both of Wu's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 11 < n → a n = 2 * a (n - 1) - a (n - 2)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * ((X - 1) ^ 2) =
      X * (-X ^ 10 + X ^ 9 - 2 * X ^ 8 - 2 * X ^ 7 + 4 * X ^ 6 - 2 * X ^ 5 - 2 * X ^ 4 + 4 * X ^ 3 -
        2 * X ^ 2 + 17 * X - 17) :=
  ⟨recurrence, gf⟩

end OMA.S_oeis_a291515

theorem OMA.solution : type_of% @OMA.S_oeis_a291515.main :=
  OMA.S_oeis_a291515.conjecture
