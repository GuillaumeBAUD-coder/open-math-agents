import OMAStatements.S_oeis_a160850
import Mathlib

-- Problem: oeis-a160850 (Barker's g.f. and recurrence)
-- Credit: @Aijy0264561
-- a has second difference secondDiff, which has period 840 (the truncated (10 - 2y : ℕ) coefficients
-- vanish for y >= 5, and gcd(9, x) = 1 only depends on x mod 3). The denominator is (1 - X)^2 Q with
-- Q of degree 18; Q annihilates secondDiff (checked on one period by decide, then extended by
-- periodicity), which gives the recurrence; the g.f. follows coefficientwise from it and 22 values.

namespace OMA.A160850proof

open OMA.S_oeis_a160850 PowerSeries

def qc : Fin 19 → ℤ := ![1, 2, 4, 6, 8, 9, 9, 7, 4, 0, -4, -7, -9, -9, -8, -6, -4, -2, -1]

def DQ (m : ℕ) : ℤ := (1) * secondDiff (m + 21) + (2) * secondDiff (m + 20) + (4) * secondDiff (m + 19) + (6) * secondDiff (m + 18) + (8) * secondDiff (m + 17) + (9) * secondDiff (m + 16) + (9) * secondDiff (m + 15) + (7) * secondDiff (m + 14) + (4) * secondDiff (m + 13) + (0) * secondDiff (m + 12) + (-4) * secondDiff (m + 11) + (-7) * secondDiff (m + 10) + (-9) * secondDiff (m + 9) + (-9) * secondDiff (m + 8) + (-8) * secondDiff (m + 7) + (-6) * secondDiff (m + 6) + (-4) * secondDiff (m + 5) + (-2) * secondDiff (m + 4) + (-1) * secondDiff (m + 3)

lemma sd_per (t : ℕ) : secondDiff (t + 840) = secondDiff t := by
  have h2 : (t + 840) % 2 = t % 2 := by omega
  have hd : (t + 840) / 2 = t / 2 + 420 := by omega
  have h9 : Nat.Coprime 9 ((t + 840) % 9) ↔ Nat.Coprime 9 (t % 9) := by
    rw [show (t + 840) % 9 = (t % 9 + 3) % 9 by omega]
    have : t % 9 < 9 := Nat.mod_lt _ (by norm_num)
    generalize t % 9 = r at this ⊢
    interval_cases r <;> decide
  simp only [secondDiff, Fin.sum_univ_succ, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
  simp only [show (t + 840) % 1 = t % 1 by omega, show (t + 840) % 2 = t % 2 by omega, show (t + 840) % 3 = t % 3 by omega, show (t + 840) % 4 = t % 4 by omega, show (t + 840) % 5 = t % 5 by omega, show (t + 840) % 6 = t % 6 by omega, show (t + 840) % 7 = t % 7 by omega, show (t + 840) % 8 = t % 8 by omega, h9, h2, hd, show (t / 2 + 420) % 1 = t / 2 % 1 by omega, show (t / 2 + 420) % 2 = t / 2 % 2 by omega, show (t / 2 + 420) % 3 = t / 2 % 3 by omega, show (t / 2 + 420) % 4 = t / 2 % 4 by omega]
  norm_num
  simp only [show (t + 840) % 1 = t % 1 by omega, show (t + 840) % 2 = t % 2 by omega, show (t + 840) % 3 = t % 3 by omega, show (t + 840) % 4 = t % 4 by omega, show (t + 840) % 5 = t % 5 by omega, show (t + 840) % 6 = t % 6 by omega, show (t + 840) % 7 = t % 7 by omega, show (t + 840) % 8 = t % 8 by omega, h9, show (t / 2 + 420) % 1 = t / 2 % 1 by omega, show (t / 2 + 420) % 2 = t / 2 % 2 by omega, show (t / 2 + 420) % 3 = t / 2 % 3 by omega, show (t / 2 + 420) % 4 = t / 2 % 4 by omega]
  try norm_num

lemma DQ_per (m : ℕ) : DQ (m + 840) = DQ m := by
  unfold DQ
  simp only [show ∀ c : ℕ, m + 840 + c = (m + c) + 840 from fun c => by ring, sd_per]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma DQ_small : ∀ m < 840, DQ m = 0 := by unfold DQ; decide

lemma DQ_zero (m : ℕ) : DQ m = 0 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge m 840 with h | h
    · exact DQ_small m h
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 840 := ⟨m - 840, by omega⟩
      rw [DQ_per]; exact ih k (by omega)

lemma rel (k : ℕ) : a (k + 4) = 2 * a (k + 3) - a (k + 2) + secondDiff (k + 3) := rfl

lemma rec0 (m : ℕ) :
    a (m + 22) + a (m + 20) - a (m + 17) - a (m + 16) - 2 * a (m + 15) - a (m + 14) - a (m + 13) +
      a (m + 11) + a (m + 10) + 2 * a (m + 9) + a (m + 8) + a (m + 7) - a (m + 4) - a (m + 2) = 0 := by
  have r0 : a (m + 22) = 2 * a (m + 21) - a (m + 20) + secondDiff (m + 21) := rel (m + 18)
  have r1 : a (m + 21) = 2 * a (m + 20) - a (m + 19) + secondDiff (m + 20) := rel (m + 17)
  have r2 : a (m + 20) = 2 * a (m + 19) - a (m + 18) + secondDiff (m + 19) := rel (m + 16)
  have r3 : a (m + 19) = 2 * a (m + 18) - a (m + 17) + secondDiff (m + 18) := rel (m + 15)
  have r4 : a (m + 18) = 2 * a (m + 17) - a (m + 16) + secondDiff (m + 17) := rel (m + 14)
  have r5 : a (m + 17) = 2 * a (m + 16) - a (m + 15) + secondDiff (m + 16) := rel (m + 13)
  have r6 : a (m + 16) = 2 * a (m + 15) - a (m + 14) + secondDiff (m + 15) := rel (m + 12)
  have r7 : a (m + 15) = 2 * a (m + 14) - a (m + 13) + secondDiff (m + 14) := rel (m + 11)
  have r8 : a (m + 14) = 2 * a (m + 13) - a (m + 12) + secondDiff (m + 13) := rel (m + 10)
  have r9 : a (m + 13) = 2 * a (m + 12) - a (m + 11) + secondDiff (m + 12) := rel (m + 9)
  have r10 : a (m + 12) = 2 * a (m + 11) - a (m + 10) + secondDiff (m + 11) := rel (m + 8)
  have r11 : a (m + 11) = 2 * a (m + 10) - a (m + 9) + secondDiff (m + 10) := rel (m + 7)
  have r12 : a (m + 10) = 2 * a (m + 9) - a (m + 8) + secondDiff (m + 9) := rel (m + 6)
  have r13 : a (m + 9) = 2 * a (m + 8) - a (m + 7) + secondDiff (m + 8) := rel (m + 5)
  have r14 : a (m + 8) = 2 * a (m + 7) - a (m + 6) + secondDiff (m + 7) := rel (m + 4)
  have r15 : a (m + 7) = 2 * a (m + 6) - a (m + 5) + secondDiff (m + 6) := rel (m + 3)
  have r16 : a (m + 6) = 2 * a (m + 5) - a (m + 4) + secondDiff (m + 5) := rel (m + 2)
  have r17 : a (m + 5) = 2 * a (m + 4) - a (m + 3) + secondDiff (m + 4) := rel (m + 1)
  have r18 : a (m + 4) = 2 * a (m + 3) - a (m + 2) + secondDiff (m + 3) := rel (m + 0)
  have hq := DQ_zero m
  unfold DQ at hq
  linear_combination (1) * r0 + (2) * r1 + (4) * r2 + (6) * r3 + (8) * r4 + (9) * r5 + (9) * r6 + (7) * r7 + (4) * r8 + (0) * r9 + (-4) * r10 + (-7) * r11 + (-9) * r12 + (-9) * r13 + (-8) * r14 + (-6) * r15 + (-4) * r16 + (-2) * r17 + (-1) * r18 + hq

lemma v0 : a 0 = 0 := by decide
lemma v1 : a 1 = 1 := by decide
lemma v2 : a 2 = 102 := by decide
lemma v3 : a 3 = 203 := by decide
lemma v4 : a 4 = 370 := by decide
lemma v5 : a 5 = 563 := by decide
lemma v6 : a 6 = 836 := by decide
lemma v7 : a 7 = 1111 := by decide
lemma v8 : a 8 = 1470 := by decide
lemma v9 : a 9 = 1855 := by decide
lemma v10 : a 10 = 2306 := by decide
lemma v11 : a 11 = 2757 := by decide
lemma v12 : a 12 = 3298 := by decide
lemma v13 : a 13 = 3857 := by decide
lemma v14 : a 14 = 4506 := by decide
lemma v15 : a 15 = 5159 := by decide
lemma v16 : a 16 = 5868 := by decide
lemma v17 : a 17 = 6603 := by decide
lemma v18 : a 18 = 7428 := by decide
lemma v19 : a 19 = 8255 := by decide
lemma v20 : a 20 = 9172 := by decide
lemma v21 : a 21 = 10105 := by decide

lemma denom_eq : ((1-X)^3*(1+X)*(1-X+X^2)*(1+X^2)*(1+X+X^2)*(1+X+X^2+X^3+X^4)*
    (1+X+X^2+X^3+X^4+X^5+X^6) : PowerSeries ℤ) =
    1 + X^2 - X^5 - X^6 - C 2 * X^7 - X^8 - X^9 + X^11 + X^12 + C 2 * X^13 + X^14 + X^15 - X^18 - X^20 := by
  simp only [map_ofNat]; ring

lemma numer_eq : (X*(1 + 102*X + 204*X^2 + 472*X^3 + 766*X^4 + 1205*X^5 + 1571*X^6 + 1999*X^7 + 2188*X^8 + 2334*X^9 + 2168*X^10 + 1959*X^11 + 1531*X^12 + 1165*X^13 + 746*X^14 + 462*X^15 + 214*X^16 + 112*X^17 + 21*X^18 + 10*X^19 + 10*X^20) : PowerSeries ℤ) =
    X^1 + C 102 * X^2 + C 204 * X^3 + C 472 * X^4 + C 766 * X^5 + C 1205 * X^6 + C 1571 * X^7 + C 1999 * X^8 + C 2188 * X^9 + C 2334 * X^10 + C 2168 * X^11 + C 1959 * X^12 + C 1531 * X^13 + C 1165 * X^14 + C 746 * X^15 + C 462 * X^16 + C 214 * X^17 + C 112 * X^18 + C 21 * X^19 + C 10 * X^20 + C 10 * X^21 := by
  simp only [map_ofNat]; ring

lemma coeff_mul_X1 (φ : PowerSeries ℤ) (n : ℕ) :
    coeff n (φ * X) = if 1 ≤ n then coeff (n - 1) φ else 0 := by
  simpa using coeff_mul_X_pow' φ 1 n

theorem a160850 : type_of% @OMA.S_oeis_a160850.main := by
  have hrec : ∀ n : ℕ, 21 < n → a n = - a (n-2) + a (n-5) + a (n-6) + 2*a (n-7) + a (n-8) + a (n-9) - a (n-11) - a (n-12) - 2*a (n-13) - a (n-14) - a (n-15) + a (n-18) + a (n-20) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 22 := ⟨n - 22, by omega⟩
    have := rec0 m
    simp only [show m + 22 - 1 = m + 21 by omega, show m + 22 - 2 = m + 20 by omega, show m + 22 - 3 = m + 19 by omega, show m + 22 - 4 = m + 18 by omega, show m + 22 - 5 = m + 17 by omega, show m + 22 - 6 = m + 16 by omega, show m + 22 - 7 = m + 15 by omega, show m + 22 - 8 = m + 14 by omega, show m + 22 - 9 = m + 13 by omega, show m + 22 - 10 = m + 12 by omega, show m + 22 - 11 = m + 11 by omega, show m + 22 - 12 = m + 10 by omega, show m + 22 - 13 = m + 9 by omega, show m + 22 - 14 = m + 8 by omega, show m + 22 - 15 = m + 7 by omega, show m + 22 - 16 = m + 6 by omega, show m + 22 - 17 = m + 5 by omega, show m + 22 - 18 = m + 4 by omega, show m + 22 - 19 = m + 3 by omega, show m + 22 - 20 = m + 2 by omega]
    linarith
  refine ⟨?_, hrec⟩
  rw [denom_eq, numer_eq]
  ext n
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, mul_left_comm (mk _) (C _),
    coeff_C_mul, coeff_mul_X_pow', coeff_mul_X1, coeff_mk, coeff_X_pow, coeff_C]
  rcases Nat.lt_or_ge n 22 with h | h
  · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21]
  · have := hrec n (by omega)
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega, show 8 ≤ n by omega, show 9 ≤ n by omega, show 10 ≤ n by omega, show 11 ≤ n by omega, show 12 ≤ n by omega, show 13 ≤ n by omega, show 14 ≤ n by omega, show 15 ≤ n by omega, show 16 ≤ n by omega, show 17 ≤ n by omega, show 18 ≤ n by omega, show 19 ≤ n by omega, show 20 ≤ n by omega, if_true, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega, show n ≠ 8 by omega, show n ≠ 9 by omega, show n ≠ 10 by omega, show n ≠ 11 by omega, show n ≠ 12 by omega, show n ≠ 13 by omega, show n ≠ 14 by omega, show n ≠ 15 by omega, show n ≠ 16 by omega, show n ≠ 17 by omega, show n ≠ 18 by omega, show n ≠ 19 by omega, show n ≠ 20 by omega, show n ≠ 21 by omega, if_false, Nat.sub_eq_zero_iff_le, show ¬ n ≤ 0 by omega, show ¬ n ≤ 1 by omega, show ¬ n ≤ 2 by omega, show ¬ n ≤ 3 by omega, show ¬ n ≤ 4 by omega, show ¬ n ≤ 5 by omega, show ¬ n ≤ 6 by omega, show ¬ n ≤ 7 by omega, show ¬ n ≤ 8 by omega, show ¬ n ≤ 9 by omega, show ¬ n ≤ 10 by omega, show ¬ n ≤ 11 by omega, show ¬ n ≤ 12 by omega, show ¬ n ≤ 13 by omega, show ¬ n ≤ 14 by omega, show ¬ n ≤ 15 by omega, show ¬ n ≤ 16 by omega, show ¬ n ≤ 17 by omega, show ¬ n ≤ 18 by omega, show ¬ n ≤ 19 by omega, show ¬ n ≤ 20 by omega, show ¬ n ≤ 21 by omega, ite_self]
    linarith

end OMA.A160850proof

theorem OMA.solution : type_of% @OMA.S_oeis_a160850.main := OMA.A160850proof.a160850
