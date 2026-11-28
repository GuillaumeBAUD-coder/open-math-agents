import OMAStatements.S_oeis_a267539
import Mathlib

namespace A267539Aux

/-- the closed form of the rows: row 0 is the single cell, row 1 has one OFF cell at position 1,
and for `t ≥ 2` every cell is ON except the cells at positions `2 - t` and `3 - t` -/
def p (t : ℕ) (i : ℤ) : Bool :=
  decide ((t = 0 ∧ i = 0) ∨ (t = 1 ∧ i ≠ 1) ∨ (2 ≤ t ∧ i ≠ 2 - (t : ℤ) ∧ i ≠ 3 - (t : ℤ)))

lemma tr (t : ℕ) (i : ℤ) (l c r : Bool) (hl : p t (i - 1) = l) (hc : p t i = c)
    (hr : p t (i + 1) = r) :
    p (t + 1) i = Nat.testBit 143 (4 * l.toNat + 2 * c.toNat + r.toNat) := by
  cases l <;> cases c <;> cases r <;>
    simp only [p, decide_eq_true_eq, decide_eq_false_iff_not, Bool.toNat_true, Bool.toNat_false,
      Nat.testBit_eq_decide_div_mod_eq] at hl hc hr ⊢ <;>
    norm_num <;> push_cast <;> omega

open OMA.S_oeis_a267539 in
lemma rowP (t : ℕ) : ∀ i, row t i = p t i := by
  induction t with
  | zero =>
    intro i
    show decide (i = 0) = p 0 i
    unfold p
    apply decide_eq_decide.mpr
    constructor <;> intro h <;> omega
  | succ k ih =>
    intro i
    show rule (row k (i - 1)) (row k i) (row k (i + 1)) = p (k + 1) i
    rw [ih, ih, ih]
    exact (tr k i _ _ _ rfl rfl rfl).symm

open OMA.S_oeis_a267539 in
lemma a_succ (n : ℕ) : a (n + 1) = 2 * a n + (if row (n + 1) 0 then 1 else 0) := by
  unfold a
  rw [Finset.sum_range_succ, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun t ht => ?_)
    have ht' := Finset.mem_range.mp ht
    rw [show n + 1 - t = (n - t) + 1 by omega, pow_succ]
    split_ifs <;> ring
  · simp

open OMA.S_oeis_a267539 in
lemma col_one (t : ℕ) (ht : 4 ≤ t) : row t 0 = true := by
  rw [rowP]
  unfold p
  rw [decide_eq_true_eq]
  omega

open OMA.S_oeis_a267539 in
lemma a0 : a 0 = 1 := by decide

open OMA.S_oeis_a267539 in
lemma a1 : a 1 = 3 := by decide

open OMA.S_oeis_a267539 in
lemma a2 : a 2 = 6 := by decide

open OMA.S_oeis_a267539 in
lemma a3 : a 3 = 12 := by decide

open OMA.S_oeis_a267539 in
lemma aN (n : ℕ) : a (n + 3) + 1 = 13 * 2 ^ n := by
  induction n with
  | zero => rw [a3]; norm_num
  | succ k ih =>
    rw [show k + 1 + 3 = (k + 3) + 1 by ring, a_succ, col_one (k + 3 + 1) (by omega), pow_succ]
    simp only [if_true]
    omega

open OMA.S_oeis_a267539 in
lemma aZ (n : ℕ) : (a (n + 3) : ℤ) = 13 * 2 ^ n - 1 := by
  have h := aN n
  have h2 : ((a (n + 3) : ℕ) : ℤ) + 1 = 13 * 2 ^ n := by exact_mod_cast h
  linarith

open PowerSeries in
lemma coeff_term (f : ℕ → ℤ) (c : ℤ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A267539Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a267539 A267539Aux PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a267539.main := by
  refine ⟨?_, ?_, a0, a1, a2, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega]
    have f5 := aZ (m + 2)
    have f4 := aZ (m + 1)
    have f3 := aZ m
    rw [show m + 2 + 3 = m + 5 by ring] at f5
    rw [show m + 1 + 3 = m + 4 by ring] at f4
    rw [f5, f4, f3]
    ring
  · have hD : ((1 - X) * (1 - 2 * X) : PowerSeries ℤ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-3) * PowerSeries.X ^ 1 +
        PowerSeries.C 2 * PowerSeries.X ^ 2 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 - X ^ 2 + X ^ 4 : PowerSeries ℤ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-1) * PowerSeries.X ^ 2 +
        PowerSeries.C 1 * PowerSeries.X ^ 4 := by
      simp only [map_one, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    have e0 : (a 0 : ℤ) = 1 := by rw [a0]; norm_num
    have e1 : (a 1 : ℤ) = 3 := by rw [a1]; norm_num
    have e2 : (a 2 : ℤ) = 6 := by rw [a2]; norm_num
    have e3 : (a 3 : ℤ) = 12 := by rw [a3]; norm_num
    have e4 : (a 4 : ℤ) = 25 := by have := aZ 1; norm_num at this; exact this
    rcases n with _ | _ | _ | _ | _ | n
    · norm_num [e0]
    · norm_num [e0, e1]
    · norm_num [e0, e1, e2]
    · norm_num [e1, e2, e3]
    · norm_num [e2, e3, e4]
    · have f5 := aZ (n + 2)
      have f4 := aZ (n + 1)
      have f3 := aZ n
      rw [show n + 2 + 3 = n + 5 by ring] at f5
      rw [show n + 1 + 3 = n + 4 by ring] at f4
      simp [show n + 5 - 1 = n + 4 by omega, show n + 5 - 2 = n + 3 by omega, f5, f4, f3]
      ring
  · intro n
    have h := aN n
    unfold A198274
    omega
