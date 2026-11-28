import OMAStatements.S_oeis_a291514

namespace OMA.S_oeis_a291514

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
  if d = 1 then -9 else if d = 2 then -9 else if d = 3 then -9 else if d = 4 then -8 else if d = 5 then -9 else -1 * d

lemma val_eq (n d : ℕ) (hd : 1 ≤ d) : val n 3 5 d = min (n : ℤ) (cv d) := by
  rcases Nat.lt_or_ge d 6 with hlt | hge
  · interval_cases d
    · rw [val, ceil_div 3 1 3 (by norm_num) (by norm_num) (by norm_num),
        ceil_div 5 1 5 (by norm_num) (by norm_num) (by norm_num)]
      norm_num [delta, cv]
    · rw [val, ceil_div 3 2 2 (by norm_num) (by norm_num) (by norm_num),
        ceil_div 5 2 3 (by norm_num) (by norm_num) (by norm_num)]
      norm_num [delta, cv]
    · rw [val, ceil_div 3 3 1 (by norm_num) (by norm_num) (by norm_num),
        ceil_div 5 3 2 (by norm_num) (by norm_num) (by norm_num)]
      norm_num [delta, cv]
    · rw [val, ceil_div 3 4 1 (by norm_num) (by norm_num) (by norm_num),
        ceil_div 5 4 2 (by norm_num) (by norm_num) (by norm_num)]
      norm_num [delta, cv]
    · rw [val, ceil_div 3 5 1 (by norm_num) (by norm_num) (by norm_num),
        ceil_div 5 5 1 (by norm_num) (by norm_num) (by norm_num)]
      norm_num [delta, cv]
  · have hd' : (6 : ℤ) ≤ d := by exact_mod_cast hge
    rw [val, ceil_div 3 d 1 (by omega) (by push_cast; omega) (by push_cast; omega),
      ceil_div 5 d 1 (by omega) (by push_cast; omega) (by push_cast; omega)]
    have hcv : cv d = -1 * d := by
      unfold cv
      simp only [show d ≠ 1 by omega, show d ≠ 2 by omega, show d ≠ 3 by omega, show d ≠ 4 by omega, show d ≠ 5 by omega, if_false]
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

lemma cv_ge (d : ℕ) : -1 * (d : ℤ) ≤ cv d ∨ -9 ≤ cv d := by
  unfold cv
  split_ifs <;> omega

/-- a(n) = -1n for n >= 9. -/
lemma a_big (n : ℕ) (hn : 9 ≤ n) : a n = -1 * n := by
  rw [uhat_eq]
  apply le_antisymm
  · rw [Finset.fold_min_le]
    right
    refine ⟨n, Nat.mem_divisors_self n (by omega), ?_⟩
    have : cv n = -1 * n := by
      unfold cv
      simp only [show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, if_false]
    rw [this]
    omega
  · rw [Finset.le_fold_min]
    refine ⟨by omega, fun d hd => ?_⟩
    have hdn : d ≤ n := Nat.divisor_le hd
    have hdn' : (d : ℤ) ≤ n := by exact_mod_cast hdn
    rcases cv_ge d with h | h <;> omega

lemma values : a 1 = -9 ∧ a 2 = -9 ∧ a 3 = -9 ∧ a 4 = -9 ∧ a 5 = -9 ∧ a 6 = -9 ∧ a 7 = -9 ∧ a 8 = -9 := by
  simp only [uhat_eq]
  decide

/-- Wu's recurrence, for n > 10. -/
theorem recurrence (n : ℕ) (hn : 10 < n) : a n = 2 * a (n - 1) - a (n - 2) := by
  rw [a_big n (by omega), a_big (n - 1) (by omega), a_big (n - 2) (by omega)]
  push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega]
  ring

/-- Wu's g.f., as A(x) D(x) = N(x) in Z[[x]] (D has constant term -1 or 1, a unit). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * ((X - 1) ^ 2) =
    X * (-X ^ 9 + 9 * X - 9) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * ((X - 1) ^ 2) =
      A - C 2 * (A * X ^ 1) + A * X ^ 2 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (-X ^ 9 + 9 * X - 9) : ℤ⟦X⟧) =
      - X ^ 1 * C 9 + X ^ 2 * C 9 - X ^ 10 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_mul_C, coeff_X_pow,
    coeff_mul_X_pow', hc]
  have v := values
  have w9 := a_big 9 (by norm_num)
  have w10 := a_big 10 (by norm_num)
  rcases Nat.lt_or_ge n 11 with hn | hn
  · interval_cases n <;> simp_all [w9, w10] <;> decide
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 11 := ⟨n - 11, by omega⟩
    have h := recurrence (q + 11) (by omega)
    simp only [show q + 11 - 1 = q + 10 by omega, show q + 11 - 2 = q + 9 by omega] at h ⊢
    simp only [show ¬ q + 11 = 0 by omega, show ¬ q + 10 = 0 by omega, show ¬ q + 9 = 0 by omega, show 1 ≤ q + 11 by omega, show 2 ≤ q + 11 by omega, show ¬ q + 11 = 1 by omega, show ¬ q + 11 = 2 by omega, show ¬ q + 11 = 10 by omega, if_true, if_false]
    rw [h]
    ring

/-- Controls: the entry's data a(1..70). -/
theorem controls : ∀ n : ℕ, 1 ≤ n → n ≤ 70 → a n = ([-9, -9, -9, -9, -9, -9, -9, -9, -9, -10, -11, -12, -13, -14, -15, -16, -17, -18, -19, -20, -21, -22, -23, -24, -25, -26, -27, -28, -29, -30, -31, -32, -33, -34, -35, -36, -37, -38, -39, -40, -41, -42, -43, -44, -45, -46, -47, -48, -49, -50, -51, -52, -53, -54, -55, -56, -57, -58, -59, -60, -61, -62, -63, -64, -65, -66, -67, -68, -69, -70] : List ℤ).getD (n - 1) 0 := by
  intro n h1 h2
  rcases Nat.lt_or_ge n 9 with hlt | hge
  · have v := values
    interval_cases n <;> simp only [v] <;> decide
  · rw [a_big n hge]
    have key : ∀ n : ℕ, 9 ≤ n → n ≤ 70 → (-1 : ℤ) * n = ([-9, -9, -9, -9, -9, -9, -9, -9, -9, -10, -11, -12, -13, -14, -15, -16, -17, -18, -19, -20, -21, -22, -23, -24, -25, -26, -27, -28, -29, -30, -31, -32, -33, -34, -35, -36, -37, -38, -39, -40, -41, -42, -43, -44, -45, -46, -47, -48, -49, -50, -51, -52, -53, -54, -55, -56, -57, -58, -59, -60, -61, -62, -63, -64, -65, -66, -67, -68, -69, -70] : List ℤ).getD (n - 1) 0 := by
      decide
    exact key n hge h2

/-- Both of Wu's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 10 < n → a n = 2 * a (n - 1) - a (n - 2)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * ((X - 1) ^ 2) =
      X * (-X ^ 9 + 9 * X - 9) :=
  ⟨recurrence, gf⟩

end OMA.S_oeis_a291514

theorem OMA.solution : type_of% @OMA.S_oeis_a291514.main :=
  OMA.S_oeis_a291514.conjecture
