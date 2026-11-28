import OMAStatements.S_oeis_a263245

namespace OMA.A263245Proof
open OMA.S_oeis_a263245 PowerSeries

def P (t : ℕ) (x : ℤ) : Bool :=
  if t = 0 then (if x = 0 then true else false)
  else if t % 2 = 1 then (if x = 1 - t then false else true)
  else (if x = 1 - t ∨ x = 2 - t then false else true)

theorem S (t : ℕ) : ∀ x, cell 155 t x = P t x := by
  induction t with
  | zero => intro x; simp [cell, P]
  | succ t ih =>
    intro x
    simp only [cell, ruleOut, ih, P]
    push_cast
    split_ifs <;> first | rfl | (exfalso; omega)

theorem T (N : ℕ) : ∑ k ∈ Finset.range (N + 1), (2 : ℚ) ^ (N - k) = 2 ^ (N + 1) - 1 := by
  have := Finset.sum_range_reflect (fun k => (2 : ℚ) ^ k) (N + 1)
  simp only [Nat.add_sub_cancel] at this
  rw [this, geom_sum_eq (by norm_num)]
  norm_num

theorem V (n : ℕ) : (a n : ℚ) = ∑ j ∈ Finset.range (2 * n + 1), if P n ((j : ℤ) - n) then (2 : ℚ) ^ (2 * n - j) else 0 := by
  simp only [a, S]
  push_cast
  rfl

theorem O (n : ℕ) (h : n % 2 = 1) : (a n : ℚ) = 3 * 2 ^ (2 * n - 1) - 1 := by
  rw [V, Finset.sum_congr rfl (g := fun j => (2 : ℚ) ^ (2 * n - j) - if j = 1 then 2 ^ (2 * n - j) else 0),
    Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (by simp; omega), T,
    show 2 * n + 1 = 2 * n - 1 + 2 by omega, pow_add]
  · ring
  · intro j _
    by_cases hj : j = 1
    · subst hj; simp [P, h, show n ≠ 0 by omega]
    · simp [P, h, hj, show n ≠ 0 by omega, show ¬ ((j : ℤ) - n = 1 - n) by omega]

theorem E (n : ℕ) (h : n % 2 = 0) (hn : 0 < n) : (a n : ℚ) = 5 * 2 ^ (2 * n - 2) - 1 := by
  rw [V, Finset.sum_congr rfl (g := fun j => (2 : ℚ) ^ (2 * n - j) - (if j = 1 then 2 ^ (2 * n - j) else 0) -
      if j = 2 then 2 ^ (2 * n - j) else 0),
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos (by simp; omega),
    if_pos (by simp; omega), T, show 2 * n + 1 = 2 * n - 2 + 3 by omega, show 2 * n - 1 = 2 * n - 2 + 1 by omega,
    pow_add, pow_add]
  · ring
  · intro j _
    by_cases hj : j = 1
    · subst hj; simp [P, h, show n ≠ 0 by omega]
    by_cases hj2 : j = 2
    · subst hj2; simp [P, h, show n ≠ 0 by omega]
    · simp [P, h, hj, hj2, show n ≠ 0 by omega, show ¬ ((j : ℤ) = 2) by omega, show ¬ ((j : ℤ) = 1) by omega]

theorem F (n : ℕ) (hn : 0 < n) : (a n : ℚ) = -1 + 11 / 8 * 4 ^ n - 1 / 8 * (-4) ^ n := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  rcases Nat.even_or_odd p with h | h
  · rw [O _ (by have := Nat.even_iff.1 h; omega), (h.add_one).neg_pow, show 2 * (p + 1) - 1 = 2 * p + 1 by omega,
      show (4 : ℚ) ^ (p + 1) = 2 ^ (2 * p + 2) by rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf]
    ring
  · rw [E _ (by have := Nat.odd_iff.1 h; omega) (by omega), (h.add_one).neg_pow, show 2 * (p + 1) - 2 = 2 * p by omega,
      show (4 : ℚ) ^ (p + 1) = 2 ^ (2 * p + 2) by rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf]
    ring

theorem R (n : ℕ) (hn : n > 3) : a n = a (n - 1) + 16 * a (n - 2) - 16 * a (n - 3) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 4 := ⟨n - 4, by omega⟩
  have h : (a (p + 4) : ℚ) = a (p + 3) + 16 * a (p + 2) - 16 * a (p + 1) := by
    rw [F _ (by omega), F _ (by omega), F _ (by omega), F _ (by omega)]; ring
  rw [show p + 4 - 1 = p + 3 by omega, show p + 4 - 2 = p + 2 by omega, show p + 4 - 3 = p + 1 by omega]
  exact_mod_cast h

theorem a0 : (a 0 : ℚ) = 1 := by norm_num [V, P]

theorem Z1 (n : ℕ) (h : Odd n) : (a n : ℚ) = 3 * (4 : ℚ) ^ (((n : ℤ) - 1) / 2) * (2 : ℚ) ^ (n : ℤ) - 1 := by
  obtain ⟨m, rfl⟩ := h
  rw [O _ (by omega), show (((2 * m + 1 : ℕ) : ℤ) - 1) / 2 = (m : ℤ) by omega, zpow_natCast, zpow_natCast,
    show 2 * (2 * m + 1) - 1 = 4 * m + 1 by omega, show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul]
  ring

theorem Z2 (n : ℕ) (hn : n > 0) (h : Even n) : (a n : ℚ) = 5 * (4 : ℚ) ^ ((n : ℤ) / 2 - 1) * (2 : ℚ) ^ (n : ℤ) - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * (m + 1) := ⟨n / 2 - 1, by have := Nat.even_iff.1 h; omega⟩
  rw [E _ (by omega) (by omega), show ((2 * (m + 1) : ℕ) : ℤ) / 2 - 1 = (m : ℤ) by omega, zpow_natCast, zpow_natCast,
    show 2 * (2 * (m + 1)) - 2 = 4 * m + 2 by omega, show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul]
  ring
theorem G : (PowerSeries.mk (fun n => (a n : ℚ))) * ((1 - X) * (1 - 4 * X) * (1 + 4 * X)) = 1 + 4 * X - 2 * X ^ 2 + 12 * X ^ 3 := by
  have k : (PowerSeries.mk (fun n => (a n : ℚ))) * ((1 - X) * (1 - 4 * X) * (1 + 4 * X)) = 1 + 4 * X - 2 * X ^ 2 + 12 * X ^ 3 := by
    rw [show (PowerSeries.mk (fun n => (a n : ℚ))) * ((1 - X) * (1 - 4 * X) * (1 + 4 * X)) = C (1 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ))) + C (-1 : ℚ) * ((PowerSeries.mk (fun n => (a n : ℚ))) * X ^ 1) + C (-16 : ℚ) * ((PowerSeries.mk (fun n => (a n : ℚ))) * X ^ 2) + C (16 : ℚ) * ((PowerSeries.mk (fun n => (a n : ℚ))) * X ^ 3) by simp only [map_neg, map_ofNat, map_one]; ring,
      show (1 + 4 * X - 2 * X ^ 2 + 12 * X ^ 3 : ℚ⟦X⟧) = C (1 : ℚ) + C (4 : ℚ) * X ^ 1 + C (-2 : ℚ) * X ^ 2 + C (12 : ℚ) * X ^ 3 by simp only [map_neg, map_ofNat, map_one]; ring]
    ext n
    simp only [map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk, coeff_C]
    rcases Nat.lt_or_ge n 4 with hn | hn
    · interval_cases n <;> norm_num [F, a0]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      simp only [show 1 ≤ m + 4 by omega, show 2 ≤ m + 4 by omega, show 3 ≤ m + 4 by omega, show m + 4 ≠ 0 by omega, show m + 3 ≠ 0 by omega, show m + 2 ≠ 0 by omega, show m + 1 ≠ 0 by omega, show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega, ↓reduceIte]
      rw [F (m + 4) (by omega), F (m + 3) (by omega), F (m + 2) (by omega), F (m + 1) (by omega)]
      ring
  exact k

end OMA.A263245Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a263245.main := ⟨OMA.A263245Proof.R, OMA.A263245Proof.G, OMA.A263245Proof.Z1, OMA.A263245Proof.Z2⟩
