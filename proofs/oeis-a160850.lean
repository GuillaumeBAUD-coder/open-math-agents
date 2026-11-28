import OMAStatements.S_oeis_a160850
import Mathlib

/-!
Proof of Colin Barker's conjectures (g.f. and recurrence for n > 21) for OEIS A160850, in the
form stated in the statement file.

* By the definition of `counts`, `a (k+4) = 2 a (k+3) - a (k+2) + secondDiff (k+3)`, so the
  second difference of `a` is `secondDiff`.
* `secondDiff t` is twice a sum of nine terms, one for each height `y = 1..9`; the term for `y`
  has period `2 y` in `t`. The polynomial `P = (1-X)(1+X)(1-X+X^2)(1+X^2)(1+X+X^2)
  (1+X+...+X^4)(1+X+...+X^6)` kills each term: this is a finite check over one period per `y`
  (kernel computation), extended to all `t` by periodicity.
* The denominator of the g.f. is `(1-X)^2 P`, so it kills `a` from index 22 on: this is the
  recurrence. The first 22 coefficients of the product are checked from the values a(0..21).
-/


namespace OMA.Helpers

open OMA.S_oeis_a160850 PowerSeries

/-- One summand of `secondDiff`: the term for the height `y`. -/
def a160850_c (y t : ℕ) : ℤ :=
  (if Nat.Coprime y (t % y) then ((10 - y : ℕ) : ℤ) else 0) -
    (if t % 2 = 0 ∧ Nat.Coprime y ((t / 2) % y) then ((10 - 2 * y : ℕ) : ℤ) else 0)

theorem a160850_sd_eq (t : ℕ) :
    secondDiff t = 2 * ∑ i : Fin 9, a160850_c (i.val + 1) t := rfl

/-- Each summand has period `2 y` in `t`. -/
theorem a160850_c_period (y s : ℕ) : a160850_c y (s + 2 * y) = a160850_c y s := by
  unfold a160850_c
  rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_left,
    Nat.add_mul_div_left _ _ (by norm_num : 0 < 2), Nat.add_mod_right]

/-- Coefficients of the annihilator `(1-X)(1+X)(1-X+X^2)(1+X^2)(1+X+X^2)(1+...+X^4)(1+...+X^6)`,
lowest shift first. -/
def a160850_pc (i : ℕ) : ℤ :=
  ([-1, -2, -4, -6, -8, -9, -9, -7, -4, 0, 4, 7, 9, 9, 8, 6, 4, 2, 1] : List ℤ).getD i 0

/-- The annihilator applied to the summand of height `y`. -/
def a160850_G (y t : ℕ) : ℤ := ∑ i ∈ Finset.range 19, a160850_pc i * a160850_c y (t + i)

theorem a160850_G_period (y t : ℕ) : a160850_G y (t + 2 * y) = a160850_G y t := by
  unfold a160850_G
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show t + 2 * y + i = (t + i) + 2 * y by ring, a160850_c_period]

theorem a160850_G_shift (y r q : ℕ) : a160850_G y (r + 2 * y * q) = a160850_G y r := by
  induction q with
  | zero => simp
  | succ q ih => rw [show r + 2 * y * (q + 1) = (r + 2 * y * q) + 2 * y by ring,
      a160850_G_period, ih]

theorem a160850_G_small : ∀ y, y < 10 → 0 < y → ∀ r, r < 2 * y → a160850_G y r = 0 := by
  decide +kernel

theorem a160850_G_zero (y t : ℕ) (hy0 : 0 < y) (hy : y < 10) : a160850_G y t = 0 := by
  have h := a160850_G_shift y (t % (2 * y)) (t / (2 * y))
  rw [Nat.mod_add_div] at h
  rw [h]
  exact a160850_G_small y hy hy0 _ (Nat.mod_lt _ (by omega))

theorem a160850_H (t : ℕ) :
    ∑ i ∈ Finset.range 19, a160850_pc i * secondDiff (t + i) = 0 := by
  simp only [a160850_sd_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  calc ∑ i ∈ Finset.range 19, a160850_pc i * (2 * a160850_c (j.val + 1) (t + i))
      = 2 * a160850_G (j.val + 1) t := by
        unfold a160850_G
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
    _ = 0 := by rw [a160850_G_zero _ _ (by omega) (by omega)]; ring

theorem a160850_counts (k : ℕ) : counts k = (a (k + 2), a (k + 3)) := by
  apply Prod.ext <;> rfl

theorem a160850_rec (k : ℕ) :
    a (k + 4) = 2 * a (k + 3) - a (k + 2) + secondDiff (k + 3) := by
  have h1 : a (k + 4) = (counts (k + 1)).2 := rfl
  have h2 : counts (k + 1) =
      ((counts k).2, 2 * (counts k).2 - (counts k).1 + secondDiff (k + 3)) := rfl
  rw [h1, h2, a160850_counts]

theorem a160850_vals : a 0 = 0 ∧ a 1 = 1 ∧ a 2 = 102 ∧ a 3 = 203 ∧ a 4 = 370 ∧ a 5 = 563 ∧
    a 6 = 836 ∧ a 7 = 1111 ∧ a 8 = 1470 ∧ a 9 = 1855 ∧ a 10 = 2306 ∧ a 11 = 2757 ∧
    a 12 = 3298 ∧ a 13 = 3857 ∧ a 14 = 4506 ∧ a 15 = 5159 ∧ a 16 = 5868 ∧ a 17 = 6603 ∧
    a 18 = 7428 ∧ a 19 = 8255 ∧ a 20 = 9172 ∧ a 21 = 10105 := by
  decide +kernel

theorem a160850_H' (t : ℕ) :
    -secondDiff t - 2 * secondDiff (t + 1) - 4 * secondDiff (t + 2) - 6 * secondDiff (t + 3) - 8 * secondDiff (t + 4) - 9 * secondDiff (t + 5) - 9 * secondDiff (t + 6) - 7 * secondDiff (t + 7) - 4 * secondDiff (t + 8) + 4 * secondDiff (t + 10) + 7 * secondDiff (t + 11) + 9 * secondDiff (t + 12) + 9 * secondDiff (t + 13) + 8 * secondDiff (t + 14) + 6 * secondDiff (t + 15) + 4 * secondDiff (t + 16) + 2 * secondDiff (t + 17) + secondDiff (t + 18) = 0 := by
  have h := a160850_H t
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, a160850_pc] at h
  norm_num at h
  linear_combination h

theorem a160850_recur (n : ℕ) (hn : 21 < n) : a n = - a (n-2) + a (n-5) + a (n-6) + 2*a (n-7) + a (n-8) + a (n-9) - a (n-11) - a (n-12) - 2*a (n-13) - a (n-14) - a (n-15) + a (n-18) + a (n-20) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 22 := ⟨n - 22, by omega⟩
  rw [show k + 22 - 2 = k + 20 by omega, show k + 22 - 5 = k + 17 by omega, show k + 22 - 6 = k + 16 by omega, show k + 22 - 7 = k + 15 by omega, show k + 22 - 8 = k + 14 by omega, show k + 22 - 9 = k + 13 by omega, show k + 22 - 11 = k + 11 by omega, show k + 22 - 12 = k + 10 by omega, show k + 22 - 13 = k + 9 by omega, show k + 22 - 14 = k + 8 by omega, show k + 22 - 15 = k + 7 by omega, show k + 22 - 18 = k + 4 by omega, show k + 22 - 20 = k + 2 by omega]
  have hH := a160850_H' (k + 3)
  simp only [add_assoc, Nat.reduceAdd] at hH
  have h0 := a160850_rec (k + 18)
  simp only [add_assoc, Nat.reduceAdd] at h0
  have h1 := a160850_rec (k + 17)
  simp only [add_assoc, Nat.reduceAdd] at h1
  have h2 := a160850_rec (k + 16)
  simp only [add_assoc, Nat.reduceAdd] at h2
  have h3 := a160850_rec (k + 15)
  simp only [add_assoc, Nat.reduceAdd] at h3
  have h4 := a160850_rec (k + 14)
  simp only [add_assoc, Nat.reduceAdd] at h4
  have h5 := a160850_rec (k + 13)
  simp only [add_assoc, Nat.reduceAdd] at h5
  have h6 := a160850_rec (k + 12)
  simp only [add_assoc, Nat.reduceAdd] at h6
  have h7 := a160850_rec (k + 11)
  simp only [add_assoc, Nat.reduceAdd] at h7
  have h8 := a160850_rec (k + 10)
  simp only [add_assoc, Nat.reduceAdd] at h8
  have h9 := a160850_rec (k + 9)
  simp only [add_assoc, Nat.reduceAdd] at h9
  have h10 := a160850_rec (k + 8)
  simp only [add_assoc, Nat.reduceAdd] at h10
  have h11 := a160850_rec (k + 7)
  simp only [add_assoc, Nat.reduceAdd] at h11
  have h12 := a160850_rec (k + 6)
  simp only [add_assoc, Nat.reduceAdd] at h12
  have h13 := a160850_rec (k + 5)
  simp only [add_assoc, Nat.reduceAdd] at h13
  have h14 := a160850_rec (k + 4)
  simp only [add_assoc, Nat.reduceAdd] at h14
  have h15 := a160850_rec (k + 3)
  simp only [add_assoc, Nat.reduceAdd] at h15
  have h16 := a160850_rec (k + 2)
  simp only [add_assoc, Nat.reduceAdd] at h16
  have h17 := a160850_rec (k + 1)
  simp only [add_assoc, Nat.reduceAdd] at h17
  have h18 := a160850_rec k
  linear_combination (1) * h0 + (2) * h1 + (4) * h2 + (6) * h3 + (8) * h4 + (9) * h5 + (9) * h6 + (7) * h7 + (4) * h8 + (-4) * h10 + (-7) * h11 + (-9) * h12 + (-9) * h13 + (-8) * h14 + (-6) * h15 + (-4) * h16 + (-2) * h17 + (-1) * h18 + hH

set_option maxHeartbeats 1600000 in
theorem a160850_gf :
    mk a * ((1-X)^3*(1+X)*(1-X+X^2)*(1+X^2)*(1+X+X^2)*(1+X+X^2+X^3+X^4)*(1+X+X^2+X^3+X^4+X^5+X^6)) = X*(1 + 102*X + 204*X^2 + 472*X^3 + 766*X^4 + 1205*X^5 + 1571*X^6 + 1999*X^7 + 2188*X^8 + 2334*X^9 + 2168*X^10 + 1959*X^11 + 1531*X^12 + 1165*X^13 + 746*X^14 + 462*X^15 + 214*X^16 + 112*X^17 + 21*X^18 + 10*X^19 + 10*X^20) := by
  have e1 : mk a * ((1-X)^3*(1+X)*(1-X+X^2)*(1+X^2)*(1+X+X^2)*(1+X+X^2+X^3+X^4)*(1+X+X^2+X^3+X^4+X^5+X^6)) =
      mk a + (mk a * X ^ 2) - (mk a * X ^ 5) - (mk a * X ^ 6) - C (2 : ℤ) * (mk a * X ^ 7) - (mk a * X ^ 8) - (mk a * X ^ 9) + (mk a * X ^ 11) + (mk a * X ^ 12) + C (2 : ℤ) * (mk a * X ^ 13) + (mk a * X ^ 14) + (mk a * X ^ 15) - (mk a * X ^ 18) - (mk a * X ^ 20) := by
    simp only [map_ofNat]
    ring
  have e2 : (X*(1 + 102*X + 204*X^2 + 472*X^3 + 766*X^4 + 1205*X^5 + 1571*X^6 + 1999*X^7 + 2188*X^8 + 2334*X^9 + 2168*X^10 + 1959*X^11 + 1531*X^12 + 1165*X^13 + 746*X^14 + 462*X^15 + 214*X^16 + 112*X^17 + 21*X^18 + 10*X^19 + 10*X^20) : PowerSeries ℤ) =
      C (1 : ℤ) * X ^ 1 + C (102 : ℤ) * X ^ 2 + C (204 : ℤ) * X ^ 3 + C (472 : ℤ) * X ^ 4 + C (766 : ℤ) * X ^ 5 + C (1205 : ℤ) * X ^ 6 + C (1571 : ℤ) * X ^ 7 + C (1999 : ℤ) * X ^ 8 + C (2188 : ℤ) * X ^ 9 + C (2334 : ℤ) * X ^ 10 + C (2168 : ℤ) * X ^ 11 + C (1959 : ℤ) * X ^ 12 + C (1531 : ℤ) * X ^ 13 + C (1165 : ℤ) * X ^ 14 + C (746 : ℤ) * X ^ 15 + C (462 : ℤ) * X ^ 16 + C (214 : ℤ) * X ^ 17 + C (112 : ℤ) * X ^ 18 + C (21 : ℤ) * X ^ 19 + C (10 : ℤ) * X ^ 20 + C (10 : ℤ) * X ^ 21 := by
    simp only [map_ofNat, map_one]
    ring
  rw [e1, e2]
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul_X_pow]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk]
  have hrec := a160850_recur
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19,
    v20, v21⟩ := a160850_vals
  generalize a = q at hrec v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 ⊢
  by_cases hk : k < 22
  · interval_cases k <;> simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15,
      v16, v17, v18, v19, v20, v21]
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 22 := ⟨k - 22, by omega⟩
    have hr := hrec (m + 22) (by omega)
    rw [if_pos (show 2 ≤ m + 22 by omega), if_pos (show 5 ≤ m + 22 by omega), if_pos (show 6 ≤ m + 22 by omega), if_pos (show 7 ≤ m + 22 by omega), if_pos (show 8 ≤ m + 22 by omega), if_pos (show 9 ≤ m + 22 by omega), if_pos (show 11 ≤ m + 22 by omega), if_pos (show 12 ≤ m + 22 by omega), if_pos (show 13 ≤ m + 22 by omega), if_pos (show 14 ≤ m + 22 by omega), if_pos (show 15 ≤ m + 22 by omega), if_pos (show 18 ≤ m + 22 by omega), if_pos (show 20 ≤ m + 22 by omega)]
    rw [if_neg (show ¬ (m + 22 = 1) by omega), if_neg (show ¬ (m + 22 = 2) by omega), if_neg (show ¬ (m + 22 = 3) by omega), if_neg (show ¬ (m + 22 = 4) by omega), if_neg (show ¬ (m + 22 = 5) by omega), if_neg (show ¬ (m + 22 = 6) by omega), if_neg (show ¬ (m + 22 = 7) by omega), if_neg (show ¬ (m + 22 = 8) by omega), if_neg (show ¬ (m + 22 = 9) by omega), if_neg (show ¬ (m + 22 = 10) by omega), if_neg (show ¬ (m + 22 = 11) by omega), if_neg (show ¬ (m + 22 = 12) by omega), if_neg (show ¬ (m + 22 = 13) by omega), if_neg (show ¬ (m + 22 = 14) by omega), if_neg (show ¬ (m + 22 = 15) by omega), if_neg (show ¬ (m + 22 = 16) by omega), if_neg (show ¬ (m + 22 = 17) by omega), if_neg (show ¬ (m + 22 = 18) by omega), if_neg (show ¬ (m + 22 = 19) by omega), if_neg (show ¬ (m + 22 = 20) by omega), if_neg (show ¬ (m + 22 = 21) by omega)]
    rw [show m + 22 - 2 = m + 20 by omega, show m + 22 - 5 = m + 17 by omega, show m + 22 - 6 = m + 16 by omega, show m + 22 - 7 = m + 15 by omega, show m + 22 - 8 = m + 14 by omega, show m + 22 - 9 = m + 13 by omega, show m + 22 - 11 = m + 11 by omega, show m + 22 - 12 = m + 10 by omega, show m + 22 - 13 = m + 9 by omega, show m + 22 - 14 = m + 8 by omega, show m + 22 - 15 = m + 7 by omega, show m + 22 - 18 = m + 4 by omega, show m + 22 - 20 = m + 2 by omega] at hr ⊢
    linear_combination hr

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a160850.main :=
  ⟨OMA.Helpers.a160850_gf, OMA.Helpers.a160850_recur⟩
