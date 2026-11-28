import OMAStatements.S_oeis_a212836
import Mathlib

/-! Proof for OEIS A212836: write an array as `(x, y, z)` and sum over the middle entry `y`; the
first and last entries are then independent, and each avoids exactly one value (`n` or `0`) when
`y ∈ {0, n}` and nothing otherwise. Hence `a(n) = 2n^2 + (n-1)(n+1)^2 = n^3 + 3n^2 - n - 1` for
`n ≥ 1`, and the g.f. and the recurrence follow by comparing coefficients.
Credit: Sudharsan Rajendiran -/

namespace OMA.P212836
open Finset OMA.S_oeis_a212836

/-- arrays of length 3 as triples -/
def e (n : ℕ) : Fin (n + 1) × Fin (n + 1) × Fin (n + 1) ≃ (Fin 3 → Fin (n + 1)) where
  toFun t := ![t.1, t.2.1, t.2.2]
  invFun f := (f 0, f 1, f 2)
  left_inv t := rfl
  right_inv f := by funext i; fin_cases i <;> rfl

/-- the number of values in `0..n` not forming a bad pair with `y` -/
def c (n y : ℕ) : ℕ := if y = 0 ∨ y = n then n else n + 1

lemma cnt_left (n : ℕ) (hn : 1 ≤ n) (y : ℕ) (hy : y < n + 1) :
    ∑ x ∈ range (n + 1), (if ¬ adj n x y then 1 else 0) = c n y := by
  rw [Finset.sum_boole, Nat.cast_id]
  unfold c adj
  by_cases h0 : y = 0
  · subst h0
    rw [if_pos (Or.inl rfl)]
    have : (range (n + 1)).filter (fun x => ¬((x = 0 ∧ 0 = n) ∨ (x = n ∧ 0 = 0))) =
        (range (n + 1)).erase n := by
      ext x; simp only [mem_filter, mem_erase, mem_range, and_true, true_and]
      constructor <;> intro h <;> omega
    rw [this, card_erase_of_mem (by simp), card_range]; rfl
  · by_cases hn' : y = n
    · subst hn'
      rw [if_pos (Or.inr rfl)]
      have : (range (y + 1)).filter (fun x => ¬((x = 0 ∧ y = y) ∨ (x = y ∧ y = 0))) =
          (range (y + 1)).erase 0 := by
        ext x; simp only [mem_filter, mem_erase, mem_range, and_true, true_and]
        constructor <;> intro h <;> omega
      rw [this, card_erase_of_mem (by simp), card_range]; rfl
    · rw [if_neg (by tauto)]
      have : (range (n + 1)).filter (fun x => ¬((x = 0 ∧ y = n) ∨ (x = n ∧ y = 0))) =
          range (n + 1) := by
        ext x; simp only [mem_filter, mem_range]; omega
      rw [this, card_range]

lemma cnt_right (n : ℕ) (hn : 1 ≤ n) (y : ℕ) (hy : y < n + 1) :
    ∑ z ∈ range (n + 1), (if ¬ adj n y z then 1 else 0) = c n y := by
  rw [← cnt_left n hn y hy]
  apply Finset.sum_congr rfl
  intro x _
  unfold adj
  congr 1
  apply propext; omega

lemma a_eq (n : ℕ) (hn : 1 ≤ n) : a n = ∑ y ∈ range (n + 1), c n y * c n y := by
  unfold a
  rw [Finset.card_filter, ← (e n).sum_comp]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  have step : ∀ y : Fin (n + 1),
      (∑ x : Fin (n + 1), ∑ z : Fin (n + 1), (if good n ((e n) (x, y, z)) then 1 else 0)) =
        c n y * c n y := by
    intro y
    have hg : ∀ x z : Fin (n + 1), (if good n ((e n) (x, y, z)) then 1 else 0) =
        (if ¬ adj n (x : ℕ) y then 1 else 0) * (if ¬ adj n (y : ℕ) z then 1 else 0) := by
      intro x z
      show (if (¬ adj n (x : ℕ) y ∧ ¬ adj n (y : ℕ) z) then 1 else 0) = _
      split_ifs <;> simp_all
    simp only [hg]
    rw [← Finset.sum_mul_sum]
    rw [Fin.sum_univ_eq_sum_range (fun x => if ¬ adj n x y then 1 else 0) (n + 1),
      Fin.sum_univ_eq_sum_range (fun z => if ¬ adj n y z then 1 else 0) (n + 1),
      cnt_left n hn y y.isLt, cnt_right n hn y y.isLt]
  simp only [step]
  exact Fin.sum_univ_eq_sum_range (fun y => c n y * c n y) (n + 1)

lemma closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℤ) = (n : ℤ) ^ 3 + 3 * (n : ℤ) ^ 2 - n - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a_eq _ hn, Finset.sum_range_succ, Finset.sum_range_succ']
  have hmid : ∀ i ∈ range m, c (m + 1) (i + 1) * c (m + 1) (i + 1) = (m + 2) * (m + 2) := by
    intro i hi
    rw [mem_range] at hi
    unfold c; rw [if_neg (by omega)]
  rw [Finset.sum_congr rfl hmid, Finset.sum_const, card_range]
  unfold c
  simp only [true_or, or_true, if_true, smul_eq_mul]
  push_cast
  ring

open PowerSeries in
lemma gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 4 =
    X * (2 + 9 * X - 6 * X ^ 2 + X ^ 3) := by
  ext m
  have hX : ((1 - X) ^ 4 : PowerSeries ℚ) = C (1 : ℚ) * X ^ 0 + C (-4 : ℚ) * X ^ 1 +
      C (6 : ℚ) * X ^ 2 + C (-4 : ℚ) * X ^ 3 + C (1 : ℚ) * X ^ 4 := by
    simp only [map_neg, map_one, map_ofNat]; ring
  have hN : (X * (2 + 9 * X - 6 * X ^ 2 + X ^ 3) : PowerSeries ℚ) = C (2 : ℚ) * X ^ 1 +
      C (9 : ℚ) * X ^ 2 + C (-6 : ℚ) * X ^ 3 + C (1 : ℚ) * X ^ 4 := by
    simp only [map_neg, map_one, map_ofNat]; ring
  rw [hX, hN]
  simp only [mul_add, map_add, coeff_mk, mul_left_comm _ (C _), coeff_C_mul, coeff_mul_X_pow',
    coeff_X_pow, coeff_C]
  have hq : ∀ k : ℕ, 1 ≤ k → (a k : ℚ) = (k : ℚ) ^ 3 + 3 * (k : ℚ) ^ 2 - k - 1 := by
    intro k hk; exact_mod_cast closed k hk
  rcases Nat.lt_or_ge m 5 with hm | hm
  · interval_cases m <;> simp [hq] <;> norm_num
  · obtain ⟨p, rfl⟩ : ∃ p, m = p + 5 := ⟨m - 5, by omega⟩
    simp only [show p + 5 - 1 = p + 4 by omega, show p + 5 - 2 = p + 3 by omega,
      show p + 5 - 3 = p + 2 by omega, show p + 5 - 4 = p + 1 by omega,
      show 1 ≤ p + 5 by omega, show 2 ≤ p + 5 by omega, show 3 ≤ p + 5 by omega,
      show 4 ≤ p + 5 by omega, show 0 ≤ p + 5 by omega, if_true, Nat.sub_zero,
      show p + 5 ≠ 0 by omega, show p + 4 ≠ 0 by omega, show p + 3 ≠ 0 by omega,
      show p + 2 ≠ 0 by omega, show p + 1 ≠ 0 by omega, show p + 5 ≠ 1 by omega,
      show p + 5 ≠ 2 by omega, show p + 5 ≠ 3 by omega, show p + 5 ≠ 4 by omega, if_false]
    rw [hq _ (by omega), hq _ (by omega), hq _ (by omega), hq _ (by omega), hq _ (by omega)]
    push_cast
    ring

lemma rec (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 5 := ⟨n - 5, by omega⟩
  simp only [show p + 5 - 1 = p + 4 by omega, show p + 5 - 2 = p + 3 by omega,
    show p + 5 - 3 = p + 2 by omega, show p + 5 - 4 = p + 1 by omega]
  rw [closed _ (by omega), closed _ (by omega), closed _ (by omega), closed _ (by omega),
    closed _ (by omega)]
  push_cast
  ring

end OMA.P212836

theorem OMA.solution : type_of% @OMA.S_oeis_a212836.main :=
  ⟨OMA.P212836.closed, OMA.P212836.gf, OMA.P212836.rec⟩
