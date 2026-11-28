import OMAStatements.S_oeis_a277799

/-!
# Proof of OEIS A277799 (Rule 1 2D von Neumann cellular automaton)

We prove all three conjectures in `OMA.S_oeis_a277799.main`:
1. Exact period-2 state classification of `cell 1 t i j`:
   - `t % 2 = 0`: ON iff `(i, j) = (0, 0)`.
   - `t % 2 = 1`: ON iff `2 ≤ i.natAbs + j.natAbs`.
2. Exact closed form of `a n`: `a (2 * m) = 1` and `a (2 * m + 1) = 2 ^ (2 * m + 2) - 4`,
   which equals `-3 / 2 - (-2) ^ n + 5 * (-1) ^ n / 2 + 2 ^ n` over `ℚ`.
3. Recurrence `a n = 5 * a (n - 2) - 4 * a (n - 4)` for `n ≥ 4` and the rational
   generating function `(1 - 4 * X ^ 2 + 12 * X ^ 3) / ((1 - X)(1 + X)(1 - 2 * X)(1 + 2 * X))`.
-/

namespace OMA.OeisA277799

open OMA.S_oeis_a277799 PowerSeries
open scoped BigOperators

private lemma testBit_one (m : ℕ) : (1 : ℕ).testBit m = decide (m = 0) := by
  cases m with
  | zero => rfl
  | succ k => simp [Nat.testBit_succ]

private lemma five_bool_sum_eq_zero (b0 b1 b2 b3 b4 : Bool) :
    b0.toNat + 2 * (b1.toNat + b2.toNat + b3.toNat + b4.toNat) = 0 ↔
      b0 = false ∧ b1 = false ∧ b2 = false ∧ b3 = false ∧ b4 = false := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> decide

private lemma cell_one (t : ℕ) (i j : ℤ) :
    cell 1 t i j =
      if t % 2 = 0 then decide (i = 0 ∧ j = 0)
      else decide (2 ≤ i.natAbs + j.natAbs) := by
  induction t generalizing i j with
  | zero => rfl
  | succ t ih =>
    simp only [cell, testBit_one, ih]
    by_cases ht : t % 2 = 0
    · have ht1 : (t + 1) % 2 ≠ 0 := by omega
      simp only [ht, ht1, ↓reduceIte]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, five_bool_sum_eq_zero, decide_eq_false_iff_not]
      omega
    · have ht1 : (t + 1) % 2 = 0 := by omega
      simp only [ht, ht1, ↓reduceIte]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, five_bool_sum_eq_zero, decide_eq_false_iff_not]
      omega

private lemma a_even (m : ℕ) : a (2 * m) = 1 := by
  dsimp [a]
  have hmod : (2 * m) % 2 = 0 := by omega
  simp only [cell_one, hmod, ↓reduceIte]
  rw [Finset.sum_eq_single (2 * m)]
  · simp
  · intro k hk hkne
    rw [if_neg (by simp; omega)]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (by omega))).elim

private lemma sum_pow_two_sub (m : ℕ) :
    (∑ k ∈ Finset.range (2 * m), (2 : ℤ) ^ (2 * m + 1 - k)) = (2 : ℤ) ^ (2 * m + 2) - 4 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have hsplit : ∑ k ∈ Finset.range (2 * (m + 1)), (2 : ℤ) ^ (2 * (m + 1) + 1 - k) =
        (∑ k ∈ Finset.range (2 * m), (2 : ℤ) ^ (2 * (m + 1) + 1 - k)) +
        (2 : ℤ) ^ (2 * (m + 1) + 1 - (2 * m)) +
        (2 : ℤ) ^ (2 * (m + 1) + 1 - (2 * m + 1)) := by
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [hsplit]
    have hscale : (∑ k ∈ Finset.range (2 * m), (2 : ℤ) ^ (2 * (m + 1) + 1 - k)) =
        4 * ∑ k ∈ Finset.range (2 * m), (2 : ℤ) ^ (2 * m + 1 - k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkl : k < 2 * m := Finset.mem_range.mp hk
      rw [show 2 * (m + 1) + 1 - k = (2 * m + 1 - k) + 2 by omega, pow_add]
      ring
    rw [hscale, ih]
    have h1 : 2 * (m + 1) + 1 - 2 * m = 3 := by omega
    have h2 : 2 * (m + 1) + 1 - (2 * m + 1) = 2 := by omega
    have h3 : 2 * (m + 1) + 2 = (2 * m + 2) + 2 := by omega
    rw [h1, h2, h3, pow_add]
    ring

private lemma a_odd (m : ℕ) : a (2 * m + 1) = (2 : ℤ) ^ (2 * m + 2) - 4 := by
  dsimp [a]
  have hmod : (2 * m + 1) % 2 ≠ 0 := by omega
  simp only [cell_one, hmod, ↓reduceIte]
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  rw [if_neg (by simp), if_neg (by simp), add_zero, add_zero]
  have hcongr : (∑ k ∈ Finset.range (2 * m),
      if decide (2 ≤ ((k : ℤ) - ((2 * m + 1 : ℕ) : ℤ)).natAbs + (0 : ℤ).natAbs) then
        (2 : ℤ) ^ (2 * m + 1 - k) else 0) =
      ∑ k ∈ Finset.range (2 * m), (2 : ℤ) ^ (2 * m + 1 - k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkl : k < 2 * m := Finset.mem_range.mp hk
    have htrue : 2 ≤ ((k : ℤ) - ((2 * m + 1 : ℕ) : ℤ)).natAbs + (0 : ℤ).natAbs := by omega
    rw [if_pos (decide_eq_true htrue)]
  push_cast at hcongr
  simp only [Int.natAbs_zero]
  rw [hcongr, sum_pow_two_sub]

lemma a_closed (n : ℕ) :
    (a n : ℚ) = -3 / 2 - (-2 : ℚ) ^ n + 5 * (-1 : ℚ) ^ n / 2 + (2 : ℚ) ^ n := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · have h2m : m + m = 2 * m := by omega
    rw [h2m, a_even]
    have hneg2 : (-2 : ℚ) ^ (2 * m) = (2 : ℚ) ^ (2 * m) := by
      rw [pow_mul, pow_mul]; norm_num
    have hneg1 : (-1 : ℚ) ^ (2 * m) = 1 := by
      rw [pow_mul]; norm_num
    rw [hneg2, hneg1]
    ring
  · rw [a_odd]
    push_cast
    have hneg2 : (-2 : ℚ) ^ (2 * m + 1) = -(2 : ℚ) ^ (2 * m + 1) := by
      calc
        (-2 : ℚ) ^ (2 * m + 1) = ((-2 : ℚ) ^ 2) ^ m * (-2) := by rw [pow_succ, pow_mul]
        _ = ((2 : ℚ) ^ 2) ^ m * (-2) := by norm_num
        _ = -(2 : ℚ) ^ (2 * m + 1) := by
          rw [pow_succ (2 : ℚ) (2 * m), pow_mul (2 : ℚ) 2 m]; ring
    have hneg1 : (-1 : ℚ) ^ (2 * m + 1) = -1 := by
      rw [pow_succ, pow_mul]; norm_num
    have hpow : (2 : ℚ) ^ (2 * m + 2) = 2 * (2 : ℚ) ^ (2 * m + 1) := by
      rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, pow_succ]; ring
    rw [hneg2, hneg1, hpow]
    ring

lemma a_rec (n : ℕ) (hn : 4 ≤ n) :
    (a n : ℚ) = 5 * a (n - 2) - 4 * a (n - 4) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h1 : 4 + k - 2 = k + 2 := by omega
  have h2 : 4 + k - 4 = k := by omega
  have h3 : 4 + k = k + 4 := by omega
  rw [h1, h2, h3, a_closed (k + 4), a_closed (k + 2), a_closed k]
  rw [pow_add (-2 : ℚ) k 4, pow_add (-2 : ℚ) k 2,
    pow_add (-1 : ℚ) k 4, pow_add (-1 : ℚ) k 2,
    pow_add (2 : ℚ) k 4, pow_add (2 : ℚ) k 2]
  ring

lemma gf_eq :
    PowerSeries.mk (fun n => (a n : ℚ)) *
        ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) : PowerSeries ℚ) =
      1 - 4 * X ^ 2 + 12 * X ^ 3 := by
  set P : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))
  have hfac : ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) : PowerSeries ℚ) =
      1 - 5 * X ^ 2 + 4 * X ^ 4 := by ring
  rw [hfac]
  have hexp : P * (1 - 5 * X ^ 2 + 4 * X ^ 4) =
      P - C (5 : ℚ) * (P * X ^ 2) + C (4 : ℚ) * (P * X ^ 4) := by
    have h5 : C (5 : ℚ) = (5 : PowerSeries ℚ) := map_ofNat C 5
    have h4 : C (4 : ℚ) = (4 : PowerSeries ℚ) := map_ofNat C 4
    rw [h5, h4]; ring
  rw [hexp]
  have hrhs : (1 - 4 * X ^ 2 + 12 * X ^ 3 : PowerSeries ℚ) =
      1 - C (4 : ℚ) * X ^ 2 + C (12 : ℚ) * X ^ 3 := by
    have h4 : C (4 : ℚ) = (4 : PowerSeries ℚ) := map_ofNat C 4
    have h12 : C (12 : ℚ) = (12 : PowerSeries ℚ) := map_ofNat C 12
    rw [h4, h12]
  rw [hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_one, PowerSeries.coeff_X_pow, PowerSeries.coeff_C, PowerSeries.coeff_mk, P]
  have ha0 : (a 0 : ℚ) = 1 := by simpa using congrArg (Int.cast (R := ℚ)) (a_even 0)
  have ha1 : (a 1 : ℚ) = 0 := by simpa using congrArg (Int.cast (R := ℚ)) (a_odd 0)
  have ha2 : (a 2 : ℚ) = 1 := by simpa using congrArg (Int.cast (R := ℚ)) (a_even 1)
  have ha3 : (a 3 : ℚ) = 12 := by simpa using congrArg (Int.cast (R := ℚ)) (a_odd 1)
  match n with
  | 0 => simp [ha0]
  | 1 => simp [ha1]
  | 2 => simp [ha2, ha0]; norm_num
  | 3 => simp [ha3, ha1]
  | n + 4 =>
    have hge4 : 4 ≤ n + 4 := by omega
    have hge3 : 3 ≤ n + 4 := by omega
    have hge2 : 2 ≤ n + 4 := by omega
    have hne0 : n + 4 ≠ 0 := by omega
    have hne2 : n + 4 ≠ 2 := by omega
    have hne3 : n + 4 ≠ 3 := by omega
    have hne2' : n + 4 - 2 ≠ 0 := by omega
    have hne3' : n + 4 - 3 ≠ 0 := by omega
    simp only [hge4, hge3, hge2, hne0, hne2, hne3, hne2', hne3', ↓reduceIte, mul_zero, sub_zero, add_zero]
    linarith [a_rec (n + 4) hge4]

end OMA.OeisA277799

theorem OMA.solution : type_of% @OMA.S_oeis_a277799.main :=
  ⟨OMA.OeisA277799.gf_eq, OMA.OeisA277799.a_rec, OMA.OeisA277799.a_closed⟩
