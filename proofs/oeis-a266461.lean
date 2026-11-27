import OMAStatements.S_oeis_a266461
import Mathlib

namespace A266461aux

open OMA.S_oeis_a266461 in
/-- Rule 27 as a function of the three neighbouring cells. -/
def r27 (l c r : Bool) : Bool := Nat.testBit 27 (4 * l.toNat + 2 * c.toNat + r.toNat)

open OMA.S_oeis_a266461 in
lemma step_eq (s : ℤ → Bool) (x : ℤ) :
    step 27 s x = r27 (s (x - 1)) (s x) (s (x + 1)) := rfl

open OMA.S_oeis_a266461 in
lemma stepE (j : ℤ) :
    step 27 (fun x : ℤ => decide (x = j)) = fun x : ℤ => decide (x ≠ j) := by
  funext x
  rw [step_eq]
  show r27 (decide (x - 1 = j)) (decide (x = j)) (decide (x + 1 = j)) = decide (x ≠ j)
  cases hb1 : decide (x - 1 = j) <;> cases hb2 : decide (x = j) <;>
    cases hb3 : decide (x + 1 = j) <;> cases hb4 : decide (x ≠ j) <;>
    first
      | decide
      | (exfalso
         simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hb1 hb2 hb3 hb4
         omega)

open OMA.S_oeis_a266461 in
lemma stepO (j : ℤ) :
    step 27 (fun x : ℤ => decide (x ≠ j)) = fun x : ℤ => decide (x = j + 1) := by
  funext x
  rw [step_eq]
  show r27 (decide (x - 1 ≠ j)) (decide (x ≠ j)) (decide (x + 1 ≠ j)) = decide (x = j + 1)
  cases hb1 : decide (x - 1 ≠ j) <;> cases hb2 : decide (x ≠ j) <;>
    cases hb3 : decide (x + 1 ≠ j) <;> cases hb4 : decide (x = j + 1) <;>
    first
      | decide
      | (exfalso
         simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hb1 hb2 hb3 hb4
         omega)

open OMA.S_oeis_a266461 in
lemma state_succ (n : ℕ) : state 27 (n + 1) = step 27 (state 27 n) := rfl

open OMA.S_oeis_a266461 in
lemma st (j : ℕ) : state 27 (2 * j) = (fun x : ℤ => decide (x = (j : ℤ))) ∧
    state 27 (2 * j + 1) = (fun x : ℤ => decide (x ≠ (j : ℤ))) := by
  induction j with
  | zero =>
    have h0 : state 27 (2 * 0) = (fun x : ℤ => decide (x = ((0 : ℕ) : ℤ))) := by
      funext x
      simp [state]
    refine ⟨h0, ?_⟩
    rw [state_succ, h0]
    exact stepE _
  | succ j ih =>
    have h2 : state 27 (2 * (j + 1)) = (fun x : ℤ => decide (x = ((j + 1 : ℕ) : ℤ))) := by
      rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, state_succ, ih.2, stepO, Nat.cast_add_one]
    refine ⟨h2, ?_⟩
    rw [state_succ, h2]
    exact stepE _

open OMA.S_oeis_a266461 in
lemma aE (j : ℕ) : a (2 * j) = 2 ^ j := by
  unfold a rowValue
  rw [(st j).1]
  show ∑ i ∈ Finset.range (2 * (2 * j) + 1),
    (decide ((((2 * j : ℕ) : ℤ) - (i : ℤ)) = (j : ℤ))).toNat * 2 ^ i = 2 ^ j
  have hf : ∀ i ∈ Finset.range (2 * (2 * j) + 1),
      (decide ((((2 * j : ℕ) : ℤ) - (i : ℤ)) = (j : ℤ))).toNat * 2 ^ i
        = if i = j then 2 ^ i else 0 := by
    intro i _
    by_cases h : i = j
    · rw [h, if_pos rfl]
      have h' : (((2 * j : ℕ) : ℤ) - (j : ℤ)) = (j : ℤ) := by
        push_cast
        ring
      rw [decide_eq_true h']
      simp
    · rw [if_neg h]
      have h' : ¬ ((((2 * j : ℕ) : ℤ) - (i : ℤ)) = (j : ℤ)) := by
        push_cast
        omega
      rw [decide_eq_false h']
      simp
  rw [Finset.sum_congr rfl hf, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]

open OMA.S_oeis_a266461 in
lemma geo (N : ℕ) : ∑ i ∈ Finset.range N, 2 ^ i + 1 = 2 ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

open OMA.S_oeis_a266461 in
lemma aO (j : ℕ) : a (2 * j + 1) + 2 ^ (j + 1) + 1 = 2 ^ (4 * j + 3) := by
  unfold a rowValue
  rw [(st j).2]
  show ∑ i ∈ Finset.range (2 * (2 * j + 1) + 1),
    (decide ((((2 * j + 1 : ℕ) : ℤ) - (i : ℤ)) ≠ (j : ℤ))).toNat * 2 ^ i
      + 2 ^ (j + 1) + 1 = 2 ^ (4 * j + 3)
  have hf : ∀ i ∈ Finset.range (2 * (2 * j + 1) + 1),
      (decide ((((2 * j + 1 : ℕ) : ℤ) - (i : ℤ)) ≠ (j : ℤ))).toNat * 2 ^ i
        + (if i = j + 1 then 2 ^ i else 0) = 2 ^ i := by
    intro i _
    by_cases h : i = j + 1
    · rw [h, if_pos rfl]
      have h' : ¬ ((((2 * j + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ)) ≠ (j : ℤ)) := by
        push_cast
        omega
      rw [decide_eq_false h']
      simp
    · rw [if_neg h]
      have h' : (((2 * j + 1 : ℕ) : ℤ) - (i : ℤ)) ≠ (j : ℤ) := by
        push_cast
        omega
      rw [decide_eq_true h']
      simp
  have hs : ∑ i ∈ Finset.range (2 * (2 * j + 1) + 1),
      ((decide ((((2 * j + 1 : ℕ) : ℤ) - (i : ℤ)) ≠ (j : ℤ))).toNat * 2 ^ i
        + (if i = j + 1 then 2 ^ i else 0))
      = ∑ i ∈ Finset.range (2 * (2 * j + 1) + 1), 2 ^ i := Finset.sum_congr rfl hf
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq',
    if_pos (Finset.mem_range.mpr (by omega))] at hs
  have hg := geo (2 * (2 * j + 1) + 1)
  rw [show 2 * (2 * j + 1) + 1 = 4 * j + 3 by ring] at hg hs ⊢
  generalize ∑ i ∈ Finset.range (4 * j + 3), 2 ^ i = S at hg hs
  omega

open OMA.S_oeis_a266461 in
lemma aO' (j : ℕ) : (a (2 * j + 1) : ℤ) = 2 ^ (4 * j + 3) - 2 ^ (j + 1) - 1 := by
  have h := aO j
  have h' : ((a (2 * j + 1) + 2 ^ (j + 1) + 1 : ℕ) : ℤ) = ((2 ^ (4 * j + 3) : ℕ) : ℤ) := by
    rw [h]
  push_cast at h'
  linarith

open OMA.S_oeis_a266461 in
lemma rec6 (m : ℕ) : (a (m + 6) : ℤ) = 19 * a (m + 4) - 50 * a (m + 2) + 32 * a m := by
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' m
  · rw [show 2 * i + 6 = 2 * (i + 3) by ring, show 2 * i + 4 = 2 * (i + 2) by ring,
      show 2 * i + 2 = 2 * (i + 1) by ring, aE, aE, aE, aE]
    push_cast
    ring
  · rw [show 2 * i + 1 + 6 = 2 * (i + 3) + 1 by ring,
      show 2 * i + 1 + 4 = 2 * (i + 2) + 1 by ring,
      show 2 * i + 1 + 2 = 2 * (i + 1) + 1 by ring,
      aO' (i + 3), aO' (i + 2), aO' (i + 1), aO' i]
    ring

open OMA.S_oeis_a266461 in
lemma a0 : a 0 = 1 := by
  have h := aE 0
  simpa using h
open OMA.S_oeis_a266461 in
lemma a2 : a 2 = 2 := by
  have h := aE 1
  simpa using h
open OMA.S_oeis_a266461 in
lemma a4 : a 4 = 4 := by
  have h := aE 2
  simpa using h
open OMA.S_oeis_a266461 in
lemma a1 : a 1 = 5 := by
  have h := aO 0
  norm_num at h
  omega
open OMA.S_oeis_a266461 in
lemma a3 : a 3 = 123 := by
  have h := aO 1
  norm_num at h
  omega
open OMA.S_oeis_a266461 in
lemma a5 : a 5 = 2039 := by
  have h := aO 2
  norm_num at h
  omega

open OMA.S_oeis_a266461 in
lemma gf : A = (1 + 5 * PowerSeries.X - 17 * PowerSeries.X ^ 2 + 28 * PowerSeries.X ^ 3
      + 16 * PowerSeries.X ^ 4 - 48 * PowerSeries.X ^ 5) *
    ((1 - PowerSeries.X) * (1 + PowerSeries.X) * (1 - 4 * PowerSeries.X)
      * (1 + 4 * PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2))⁻¹ := by
  have hD : PowerSeries.constantCoeff
      ((1 - PowerSeries.X) * (1 + PowerSeries.X) * (1 - 4 * PowerSeries.X)
        * (1 + 4 * PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2) : PowerSeries ℚ) ≠ 0 := by
    simp
  rw [PowerSeries.eq_mul_inv_iff_mul_eq hD]
  have h5 : (5 : PowerSeries ℚ) = PowerSeries.C (5 : ℚ) := (map_ofNat _ 5).symm
  have h16 : (16 : PowerSeries ℚ) = PowerSeries.C (16 : ℚ) := (map_ofNat _ 16).symm
  have h17 : (17 : PowerSeries ℚ) = PowerSeries.C (17 : ℚ) := (map_ofNat _ 17).symm
  have h19 : (19 : PowerSeries ℚ) = PowerSeries.C (19 : ℚ) := (map_ofNat _ 19).symm
  have h28 : (28 : PowerSeries ℚ) = PowerSeries.C (28 : ℚ) := (map_ofNat _ 28).symm
  have h32 : (32 : PowerSeries ℚ) = PowerSeries.C (32 : ℚ) := (map_ofNat _ 32).symm
  have h48 : (48 : PowerSeries ℚ) = PowerSeries.C (48 : ℚ) := (map_ofNat _ 48).symm
  have h50 : (50 : PowerSeries ℚ) = PowerSeries.C (50 : ℚ) := (map_ofNat _ 50).symm
  have hL : A * ((1 - PowerSeries.X) * (1 + PowerSeries.X) * (1 - 4 * PowerSeries.X)
        * (1 + 4 * PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2))
      = A - PowerSeries.C (19 : ℚ) * (PowerSeries.X ^ 2 * A)
        + PowerSeries.C (50 : ℚ) * (PowerSeries.X ^ 4 * A)
        - PowerSeries.C (32 : ℚ) * (PowerSeries.X ^ 6 * A) := by
    rw [← h19, ← h50, ← h32]
    ring
  have hR : (1 + 5 * PowerSeries.X - 17 * PowerSeries.X ^ 2 + 28 * PowerSeries.X ^ 3
        + 16 * PowerSeries.X ^ 4 - 48 * PowerSeries.X ^ 5 : PowerSeries ℚ)
      = 1 + PowerSeries.C (5 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (17 : ℚ) * PowerSeries.X ^ 2
        + PowerSeries.C (28 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (16 : ℚ) * PowerSeries.X ^ 4
        - PowerSeries.C (48 : ℚ) * PowerSeries.X ^ 5 := by
    rw [← h5, ← h17, ← h28, ← h16, ← h48]
    ring
  rw [hL, hR]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow, PowerSeries.coeff_one, A, PowerSeries.coeff_mk]
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | h
  · norm_num [a0]
  · norm_num [a1]
  · norm_num [a0, a2]
  · norm_num [a1, a3]
  · norm_num [a0, a2, a4]
  · norm_num [a1, a3, a5]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega)]
    rw [show m + 6 - 2 = m + 4 by omega, show m + 6 - 4 = m + 2 by omega,
      show m + 6 - 6 = m by omega]
    have hr : (a (m + 6) : ℚ) = 19 * (a (m + 4) : ℚ) - 50 * (a (m + 2) : ℚ) + 32 * (a m : ℚ) := by
      exact_mod_cast rec6 m
    linarith

end A266461aux

theorem OMA.solution : type_of% @OMA.S_oeis_a266461.main := by
  refine ⟨?_, A266461aux.gf, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    rw [show m + 6 - 2 = m + 4 by omega, show m + 6 - 4 = m + 2 by omega,
      show m + 6 - 6 = m by omega]
    exact A266461aux.rec6 m
  · intro n hn
    obtain ⟨j, rfl⟩ := hn
    rw [A266461aux.aO' j, show (2 * j + 1) / 2 = j by omega,
      show (4 : ℤ) ^ (2 * j + 1) = 2 ^ (2 * (2 * j + 1)) by rw [pow_mul]; norm_num]
    ring
  · intro n hn
    obtain ⟨j, rfl⟩ := hn
    rw [show j + j = 2 * j by ring, A266461aux.aE j,
      Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
