import OMAStatements.S_oeis_a128957

namespace OMA.A128957aux

open OMA.S_oeis_a128957

theorem count (N : ℕ) :
    ((Finset.Icc 1 N).filter (fun m => (¬ 2 ∣ m ∨ ¬ 5 ∣ m) ∧ (¬ 3 ∣ m ∨ ¬ 7 ∣ m))).card
      + N / 10 + N / 21 = N + N / 210 := by
  have hI : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hI]
  have h10 := Nat.Ioc_filter_dvd_card_eq_div N 10
  have h21 := Nat.Ioc_filter_dvd_card_eq_div N 21
  have h210 := Nat.Ioc_filter_dvd_card_eq_div N 210
  have hS : (Finset.Ioc 0 N).card = N := by simp
  have e1 : (Finset.Ioc 0 N).filter (fun m => (¬ 2 ∣ m ∨ ¬ 5 ∣ m) ∧ (¬ 3 ∣ m ∨ ¬ 7 ∣ m))
      = (Finset.Ioc 0 N).filter (fun m => ¬ (10 ∣ m ∨ 21 ∣ m)) := by
    apply Finset.filter_congr
    intro x _
    omega
  have e2 : (Finset.Ioc 0 N).filter (fun m => 10 ∣ m) ∩ (Finset.Ioc 0 N).filter (fun m => 21 ∣ m)
      = (Finset.Ioc 0 N).filter (fun m => 210 ∣ m) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h, h1⟩, _, h2⟩
      exact ⟨h, by omega⟩
    · rintro ⟨h, h1⟩
      exact ⟨⟨h, by omega⟩, h, by omega⟩
  have e3 := Finset.card_filter_add_card_filter_not (s := Finset.Ioc 0 N)
    (fun m => 10 ∣ m ∨ 21 ∣ m)
  have e4 := Finset.card_union_add_card_inter ((Finset.Ioc 0 N).filter (fun m => 10 ∣ m))
    ((Finset.Ioc 0 N).filter (fun m => 21 ∣ m))
  rw [← Finset.filter_or, e2] at e4
  rw [e1]
  omega

theorem a_succ (m : ℕ) :
    a (m + 1) + 10 ^ m + 10 ^ (m + 1) / 21 = 10 ^ (m + 1) + 10 ^ m / 21 := by
  have h := count (10 ^ (m + 1))
  have h1 : 10 ^ (m + 1) / 10 = 10 ^ m := by
    rw [pow_succ]
    exact Nat.mul_div_cancel _ (by norm_num)
  have h2 : 10 ^ (m + 1) / 210 = 10 ^ m / 21 := by
    rw [show (210 : ℕ) = 10 * 21 from rfl, ← Nat.div_div_eq_div_mul, h1]
  rw [h1, h2] at h
  exact h

theorem f6 (m : ℕ) : 10 ^ (m + 6) / 21 = 10 ^ m / 21 + 47619 * 10 ^ m := by
  have h : 10 ^ (m + 6) = 10 ^ m + 21 * (47619 * 10 ^ m) := by ring
  rw [h, Nat.add_mul_div_left _ _ (by norm_num : 0 < 21)]

theorem rec8 (k : ℕ) :
    a (k + 8) = 9 * a (k + 7) + 9 * a (k + 6) + 9 * a (k + 5) + 9 * a (k + 4) + 9 * a (k + 3)
      + 10 * a (k + 2) := by
  have h1 : a (k + 2) + 10 ^ (k + 1) + 10 ^ (k + 2) / 21 = 10 ^ (k + 2) + 10 ^ (k + 1) / 21 :=
    a_succ (k + 1)
  have h2 : a (k + 3) + 10 ^ (k + 2) + 10 ^ (k + 3) / 21 = 10 ^ (k + 3) + 10 ^ (k + 2) / 21 :=
    a_succ (k + 2)
  have h3 : a (k + 4) + 10 ^ (k + 3) + 10 ^ (k + 4) / 21 = 10 ^ (k + 4) + 10 ^ (k + 3) / 21 :=
    a_succ (k + 3)
  have h4 : a (k + 5) + 10 ^ (k + 4) + 10 ^ (k + 5) / 21 = 10 ^ (k + 5) + 10 ^ (k + 4) / 21 :=
    a_succ (k + 4)
  have h5 : a (k + 6) + 10 ^ (k + 5) + 10 ^ (k + 6) / 21 = 10 ^ (k + 6) + 10 ^ (k + 5) / 21 :=
    a_succ (k + 5)
  have h6 : a (k + 7) + 10 ^ (k + 6) + 10 ^ (k + 7) / 21 = 10 ^ (k + 7) + 10 ^ (k + 6) / 21 :=
    a_succ (k + 6)
  have h7 : a (k + 8) + 10 ^ (k + 7) + 10 ^ (k + 8) / 21 = 10 ^ (k + 8) + 10 ^ (k + 7) / 21 :=
    a_succ (k + 7)
  have g6 : 10 ^ (k + 7) / 21 = 10 ^ (k + 1) / 21 + 47619 * 10 ^ (k + 1) := f6 (k + 1)
  have g7 : 10 ^ (k + 8) / 21 = 10 ^ (k + 2) / 21 + 47619 * 10 ^ (k + 2) := f6 (k + 2)
  have p2 : 10 ^ (k + 2) = 10 * 10 ^ (k + 1) := by ring
  have p3 : 10 ^ (k + 3) = 100 * 10 ^ (k + 1) := by ring
  have p4 : 10 ^ (k + 4) = 1000 * 10 ^ (k + 1) := by ring
  have p5 : 10 ^ (k + 5) = 10000 * 10 ^ (k + 1) := by ring
  have p6 : 10 ^ (k + 6) = 100000 * 10 ^ (k + 1) := by ring
  have p7 : 10 ^ (k + 7) = 1000000 * 10 ^ (k + 1) := by ring
  have p8 : 10 ^ (k + 8) = 10000000 * 10 ^ (k + 1) := by ring
  omega

theorem a2 : a 2 = 86 := by
  have h := a_succ 1
  norm_num at h
  linarith

theorem a3 : a 3 = 857 := by
  have h := a_succ 2
  norm_num at h
  linarith

theorem a4 : a 4 = 8571 := by
  have h := a_succ 3
  norm_num at h
  linarith

theorem a5 : a 5 = 85715 := by
  have h := a_succ 4
  norm_num at h
  linarith

theorem a6 : a 6 = 857142 := by
  have h := a_succ 5
  norm_num at h
  linarith

theorem a7 : a 7 = 8571429 := by
  have h := a_succ 6
  norm_num at h
  linarith

open PowerSeries in
theorem coeffL (g : ℕ → ℤ) (n : ℕ) :
    coeff n (mk g * ((1 + X) * (1 - 10 * X) * (1 - X + X ^ 2) * (1 + X + X ^ 2) : PowerSeries ℤ)) =
      g n - 9 * (if 1 ≤ n then g (n - 1) else 0) - 9 * (if 2 ≤ n then g (n - 2) else 0)
        - 9 * (if 3 ≤ n then g (n - 3) else 0) - 9 * (if 4 ≤ n then g (n - 4) else 0)
        - 9 * (if 5 ≤ n then g (n - 5) else 0) - 10 * (if 6 ≤ n then g (n - 6) else 0) := by
  have h9 : (C 9 : PowerSeries ℤ) = 9 := by simp
  have h10 : (C 10 : PowerSeries ℤ) = 10 := by simp
  have hD : mk g * ((1 + X) * (1 - 10 * X) * (1 - X + X ^ 2) * (1 + X + X ^ 2) : PowerSeries ℤ)
      = mk g - C 9 * (mk g * X ^ 1) - C 9 * (mk g * X ^ 2) - C 9 * (mk g * X ^ 3)
        - C 9 * (mk g * X ^ 4) - C 9 * (mk g * X ^ 5) - C 10 * (mk g * X ^ 6) := by
    rw [h9, h10]
    ring
  rw [hD]
  simp only [map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_mk]

open PowerSeries in
theorem coeffR (n : ℕ) :
    coeff n (X ^ 2 * (86 + 83 * X + 84 * X ^ 2 + 89 * X ^ 3 + 81 * X ^ 4 + 90 * X ^ 5) :
        PowerSeries ℤ) =
      (if n = 2 then 86 else 0) + (if n = 3 then 83 else 0) + (if n = 4 then 84 else 0)
        + (if n = 5 then 89 else 0) + (if n = 6 then 81 else 0) + (if n = 7 then 90 else 0) := by
  have h86 : (C 86 : PowerSeries ℤ) = 86 := by simp
  have h83 : (C 83 : PowerSeries ℤ) = 83 := by simp
  have h84 : (C 84 : PowerSeries ℤ) = 84 := by simp
  have h89 : (C 89 : PowerSeries ℤ) = 89 := by simp
  have h81 : (C 81 : PowerSeries ℤ) = 81 := by simp
  have h90 : (C 90 : PowerSeries ℤ) = 90 := by simp
  have hR : (X ^ 2 * (86 + 83 * X + 84 * X ^ 2 + 89 * X ^ 3 + 81 * X ^ 4 + 90 * X ^ 5) :
        PowerSeries ℤ)
      = C 86 * X ^ 2 + C 83 * X ^ 3 + C 84 * X ^ 4 + C 89 * X ^ 5 + C 81 * X ^ 6
        + C 90 * X ^ 7 := by
    rw [h86, h83, h84, h89, h81, h90]
    ring
  rw [hR]
  simp only [map_add, coeff_C_mul_X_pow]

end OMA.A128957aux

open OMA.A128957aux OMA.S_oeis_a128957 in
theorem OMA.solution : type_of% @OMA.S_oeis_a128957.main := by
  have hrec : ∀ n : ℕ, 7 < n → (a n : ℤ) = 9 * a (n - 1) + 9 * a (n - 2) + 9 * a (n - 3)
      + 9 * a (n - 4) + 9 * a (n - 5) + 10 * a (n - 6) := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
    have e1 : k + 8 - 1 = k + 7 := by omega
    have e2 : k + 8 - 2 = k + 6 := by omega
    have e3 : k + 8 - 3 = k + 5 := by omega
    have e4 : k + 8 - 4 = k + 4 := by omega
    have e5 : k + 8 - 5 = k + 3 := by omega
    have e6 : k + 8 - 6 = k + 2 := by omega
    rw [e1, e2, e3, e4, e5, e6]
    have h := rec8 k
    omega
  refine ⟨hrec, ?_⟩
  ext n
  rw [coeffL, coeffR]
  rcases Nat.lt_or_ge n 8 with h | h
  · interval_cases n <;> simp [a2, a3, a4, a5, a6, a7]
  · have hr := hrec n (by omega)
    rw [if_neg (by omega : ¬ n < 2), if_pos (by omega : 1 ≤ n), if_neg (by omega : ¬ n - 1 < 2),
      if_pos (by omega : 2 ≤ n), if_neg (by omega : ¬ n - 2 < 2),
      if_pos (by omega : 3 ≤ n), if_neg (by omega : ¬ n - 3 < 2),
      if_pos (by omega : 4 ≤ n), if_neg (by omega : ¬ n - 4 < 2),
      if_pos (by omega : 5 ≤ n), if_neg (by omega : ¬ n - 5 < 2),
      if_pos (by omega : 6 ≤ n), if_neg (by omega : ¬ n - 6 < 2),
      if_neg (by omega : ¬ n = 2), if_neg (by omega : ¬ n = 3), if_neg (by omega : ¬ n = 4),
      if_neg (by omega : ¬ n = 5), if_neg (by omega : ¬ n = 6), if_neg (by omega : ¬ n = 7)]
    linarith
