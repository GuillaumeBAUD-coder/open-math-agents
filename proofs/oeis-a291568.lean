import OMAStatements.S_oeis_a291568

namespace OMA.S_oeis_a291568

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
  if d = 1 then 1 else if d = 2 then 1 else if d = 3 then 1 else if d = 4 then 1 else if d = 5 then -3 else 1

lemma val_eq (n d : ℕ) (hd : 1 ≤ d) : val n 5 5 d = min (n : ℤ) (cv d) := by
  rcases Nat.lt_or_ge d 6 with hlt | hge
  · interval_cases d
    · rw [val, ceil_div 5 1 5 (by norm_num) (by norm_num) (by norm_num)]
      norm_num [delta, cv]
    · rw [val, ceil_div 5 2 3 (by norm_num) (by norm_num) (by norm_num)]
      norm_num [delta, cv]
    · rw [val, ceil_div 5 3 2 (by norm_num) (by norm_num) (by norm_num)]
      norm_num [delta, cv]
    · rw [val, ceil_div 5 4 2 (by norm_num) (by norm_num) (by norm_num)]
      norm_num [delta, cv]
    · rw [val, ceil_div 5 5 1 (by norm_num) (by norm_num) (by norm_num)]
      norm_num [delta, cv]
  · have hd' : (6 : ℤ) ≤ d := by exact_mod_cast hge
    rw [val, ceil_div 5 d 1 (by omega) (by push_cast; omega) (by push_cast; omega)]
    have hcv : cv d = 1 := by
      unfold cv
      simp only [show d ≠ 1 by omega, show d ≠ 2 by omega, show d ≠ 3 by omega, show d ≠ 4 by omega, show d ≠ 5 by omega, if_false]
    rw [hcv, if_pos (by push_cast; omega)]
    congr 1
    push_cast
    omega

lemma uhat_eq (n : ℕ) :
    a n = (Nat.divisors n).fold min (n : ℤ) (fun d => min (n : ℤ) (cv d)) := by
  unfold a uhat
  apply Finset.fold_congr
  intro d hd
  exact val_eq n d (Nat.pos_of_mem_divisors hd)

/-- The value from the small divisors. -/
def F (n : ℕ) : ℤ := if 5 ∣ n then -3 else 1

lemma a_form (n : ℕ) (hn : 6 ≤ n) : a n = F n := by
  rw [uhat_eq]
  apply le_antisymm
  · rw [Finset.fold_min_le]
    right
    unfold F
    by_cases h5 : 5 ∣ n
    · refine ⟨5, Nat.mem_divisors.2 ⟨h5, by omega⟩, ?_⟩
      simp only [h5, if_true, cv]
      norm_num
      all_goals omega
    simp only [h5, if_false]
    refine ⟨n, Nat.mem_divisors_self n (by omega), ?_⟩
    have : cv n = 1 := by
      unfold cv
      simp only [show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, if_false]
    rw [this]
    omega
  · rw [Finset.le_fold_min]
    have hF : F n ≤ 1 := by unfold F; split_ifs <;> norm_num
    refine ⟨by omega, fun d hd => ?_⟩
    have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
    rcases Nat.lt_or_ge d 6 with hlt | hge
    · interval_cases d <;> unfold F cv <;> simp only [hdvd, if_true] <;> split_ifs <;> omega
    · have : cv d = 1 := by
        unfold cv
        simp only [show d ≠ 1 by omega, show d ≠ 2 by omega, show d ≠ 3 by omega, show d ≠ 4 by omega, show d ≠ 5 by omega, if_false]
      rw [this]
      omega

lemma values : a 1 = 1 ∧ a 2 = 1 ∧ a 3 = 1 ∧ a 4 = 1 ∧ a 5 = -3 := by
  simp only [uhat_eq]
  decide

/-- Wu's recurrence, for n > 5. -/
theorem recurrence (n : ℕ) (hn : 5 < n) : a n = a (n - 5) := by
  rcases Nat.lt_or_ge (n - 5) 6 with hlt | hge
  · have v := values
    have hn' : n < 11 := by omega
    rw [a_form n (by omega)]
    interval_cases n <;> simp only [v, F] <;> decide
  · rw [a_form n (by omega), a_form (n - 5) hge]
    unfold F
    obtain ⟨q, rfl⟩ : ∃ q, n = q + 5 := ⟨n - 5, by omega⟩
    rw [show q + 5 - 5 = q by omega]
    have e : (5 ∣ q + 5 ↔ 5 ∣ q) := by
      omega
    simp only [e]

/-- Wu's g.f., as A(x) D(x) = N(x) in Z[[x]] (D has constant term -1 or 1, a unit). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (X ^ 5 - 1) =
    X * (3 * X ^ 4 - X ^ 3 - X ^ 2 - X - 1) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (X ^ 5 - 1) =
      - A + A * X ^ 5 := by
    ring
  have e2 : (X * (3 * X ^ 4 - X ^ 3 - X ^ 2 - X - 1) : ℤ⟦X⟧) =
      - X ^ 1 - X ^ 2 - X ^ 3 - X ^ 4 + X ^ 5 * C 3 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_mul_C, coeff_X_pow,
    coeff_mul_X_pow', hc]
  have v := values
  rcases Nat.lt_or_ge n 6 with hn | hn
  · interval_cases n <;> simp_all <;> decide
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 6 := ⟨n - 6, by omega⟩
    have h := recurrence (q + 6) (by omega)
    simp only [show q + 6 - 1 = q + 5 by omega, show q + 6 - 2 = q + 4 by omega, show q + 6 - 3 = q + 3 by omega, show q + 6 - 4 = q + 2 by omega, show q + 6 - 5 = q + 1 by omega] at h ⊢
    simp only [show ¬ q + 6 = 0 by omega, show ¬ q + 5 = 0 by omega, show ¬ q + 4 = 0 by omega, show ¬ q + 3 = 0 by omega, show ¬ q + 2 = 0 by omega, show ¬ q + 1 = 0 by omega, show 5 ≤ q + 6 by omega, show ¬ q + 6 = 1 by omega, show ¬ q + 6 = 2 by omega, show ¬ q + 6 = 3 by omega, show ¬ q + 6 = 4 by omega, show ¬ q + 6 = 5 by omega, if_true, if_false]
    rw [h]
    ring

/-- Controls: the entry's data a(1..70). -/
theorem controls : ∀ n : ℕ, 1 ≤ n → n ≤ 70 → a n = ([1, 1, 1, 1, -3, 1, 1, 1, 1, -3, 1, 1, 1, 1, -3, 1, 1, 1, 1, -3, 1, 1, 1, 1, -3, 1, 1, 1, 1, -3, 1, 1, 1, 1, -3, 1, 1, 1, 1, -3, 1, 1, 1, 1, -3, 1, 1, 1, 1, -3, 1, 1, 1, 1, -3, 1, 1, 1, 1, -3, 1, 1, 1, 1, -3, 1, 1, 1, 1, -3] : List ℤ).getD (n - 1) 0 := by
  intro n h1 h2
  rcases Nat.lt_or_ge n 6 with hlt | hge
  · have v := values
    interval_cases n <;> simp only [v] <;> decide
  · rw [a_form n hge]
    have key : ∀ n : ℕ, 6 ≤ n → n ≤ 70 → F n = ([1, 1, 1, 1, -3, 1, 1, 1, 1, -3, 1, 1, 1, 1, -3, 1, 1, 1, 1, -3, 1, 1, 1, 1, -3, 1, 1, 1, 1, -3, 1, 1, 1, 1, -3, 1, 1, 1, 1, -3, 1, 1, 1, 1, -3, 1, 1, 1, 1, -3, 1, 1, 1, 1, -3, 1, 1, 1, 1, -3, 1, 1, 1, 1, -3, 1, 1, 1, 1, -3] : List ℤ).getD (n - 1) 0 := by
      decide
    exact key n hge h2

/-- Both of Wu's conjectures. -/
theorem conjecture :
    (∀ n : ℕ, 5 < n → a n = a (n - 5)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (X ^ 5 - 1) =
      X * (3 * X ^ 4 - X ^ 3 - X ^ 2 - X - 1) :=
  ⟨recurrence, gf⟩

end OMA.S_oeis_a291568

theorem OMA.solution : type_of% @OMA.S_oeis_a291568.main :=
  OMA.S_oeis_a291568.conjecture
