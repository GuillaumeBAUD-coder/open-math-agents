import OMAStatements.S_oeis_a265225
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Rule 54 from one cell: row 2k is ON exactly at 
-- i
--  <= 2k with i+2k divisible by 4,
-- row 2k+1 is ON at 
-- i
--  <= 2k+1 except where i+2k+1 = 3 mod 4 (both by induction on k).
-- Hence onCount(2k) = k+1, onCount(2k+1) = 3(k+1); the closed forms, recurrence and g.f. follow.

namespace OMA.S_oeis_a265225_Proof

open OMA.S_oeis_a265225
open PowerSeries in

lemma rule_dec (p q r : Prop) [Decidable p] [Decidable q] [Decidable r] :
    ruleOut (decide p) (decide q) (decide r) = decide ((q ∧ ¬p ∧ ¬r) ∨ (¬q ∧ (p ∨ r))) := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;> simp [hp, hq, hr] <;> decide

lemma cell_shape (k : ℕ) :
    (∀ i : ℤ, cell (2*k) i = decide (-(2*k:ℤ) ≤ i ∧ i ≤ 2*k ∧ (i + 2*k) % 4 = 0)) ∧
    (∀ i : ℤ, cell (2*k+1) i = decide (-(2*k+1:ℤ) ≤ i ∧ i ≤ 2*k+1 ∧ (i + 2*k+1) % 4 ≠ 3)) := by
  induction k with
  | zero =>
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [cell]; rw [Bool.eq_iff_iff]; simp; omega
    · simp only [cell, rule_dec, decide_eq_decide]; omega
  | succ k ih =>
    have h0 : ∀ i : ℤ, cell (2*(k+1)) i = decide (-(((2*(k+1):ℕ):ℤ)) ≤ i ∧ i ≤ ((2*(k+1):ℕ):ℤ) ∧ (i + ((2*(k+1):ℕ):ℤ)) % 4 = 0) := by
      intro i
      rw [show 2*(k+1) = (2*k+1)+1 by ring, cell]
      simp only [ih.2, rule_dec, decide_eq_decide]; push_cast; omega
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rw [h0]; push_cast; rfl
    · rw [cell]; simp only [h0, rule_dec, decide_eq_decide]; push_cast; omega

lemma S0 (k : ℕ) : ∑ j ∈ Finset.range (4*k+1), (if (j:ℤ) % 4 = 0 then (1:ℤ) else 0) = k+1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 4*(k+1)+1 = 4*k+1+1+1+1+1 by ring]
    simp only [Finset.sum_range_succ, ih]
    push_cast
    have e1 : ((4*k+1 : ℤ)) % 4 = 1 := by omega
    have e2 : ((4*k+1+1 : ℤ)) % 4 = 2 := by omega
    have e3 : ((4*k+1+1+1 : ℤ)) % 4 = 3 := by omega
    have e4 : ((4*k+1+1+1+1 : ℤ)) % 4 = 0 := by omega
    simp [e1, e2, e3, e4]

lemma S1 (k : ℕ) : ∑ j ∈ Finset.range (4*k+3), (if (j:ℤ) % 4 ≠ 3 then (1:ℤ) else 0) = 3*(k+1) := by
  induction k with
  | zero => simp [Finset.sum_range_succ]
  | succ k ih =>
    rw [show 4*(k+1)+3 = 4*k+3+1+1+1+1 by ring]
    simp only [Finset.sum_range_succ, ih]
    push_cast
    have e1 : ((4*k+3 : ℤ)) % 4 = 3 := by omega
    have e2 : ((4*k+3+1 : ℤ)) % 4 = 0 := by omega
    have e3 : ((4*k+3+1+1 : ℤ)) % 4 = 1 := by omega
    have e4 : ((4*k+3+1+1+1 : ℤ)) % 4 = 2 := by omega
    simp [e1, e2, e3, e4]; ring

lemma onE (k : ℕ) : onCount (2*k) = k+1 := by
  rw [onCount, show 2*(2*k)+1 = 4*k+1 by ring, ← S0 k]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [(cell_shape k).1]
  simp only [Finset.mem_range] at hj
  congr 1
  simp only [decide_eq_true_eq, eq_iff_iff]
  push_cast; omega

lemma onO (k : ℕ) : onCount (2*k+1) = 3*(k+1) := by
  rw [onCount, show 2*(2*k+1)+1 = 4*k+3 by ring, ← S1 k]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [(cell_shape k).2]
  simp only [Finset.mem_range] at hj
  congr 1
  simp only [decide_eq_true_eq, eq_iff_iff]
  push_cast; omega

lemma aEO (k : ℕ) : a (2*k) = (2*k+1)*(k+1) ∧ a (2*k+1) = (2*k+2)*(k+2) := by
  induction k with
  | zero =>
    have h0 := onE 0
    have h1 := onO 0
    simp only [mul_zero, zero_add, mul_one] at h0 h1
    refine ⟨?_, ?_⟩ <;> simp [a, Finset.sum_range_succ, h0, h1] <;> norm_num
  | succ k ih =>
    have h1 : a (2*(k+1)) = (2*((k+1):ℕ)+1)*(((k+1):ℕ)+1) := by
      rw [a, show 2*(k+1)+1 = (2*k+1)+1+1 by ring, Finset.sum_range_succ, ← a, ih.2,
        show 2*k+1+1 = 2*(k+1) by ring, onE]; push_cast; ring
    refine ⟨h1, ?_⟩
    rw [a, Finset.sum_range_succ, ← a, h1, onO]; push_cast; ring

lemma aE (k : ℕ) : a (2*k) = (2*k+1)*(k+1) := (aEO k).1
lemma aO (k : ℕ) : a (2*k+1) = (2*k+2)*(k+2) := (aEO k).2

lemma aZ (n : ℕ) : a n = (n : ℤ)+1+((n : ℤ)+1)*(((n+1)/2 : ℕ) : ℤ) := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [aE, show (2*k+1)/2 = k by omega]; push_cast; ring
  · rw [aO, show (2*k+1+1)/2 = k+1 by omega]; push_cast; ring

lemma rec5 (n : ℕ) : a (n+5) = a (n+4) + 2*a (n+3) - 2*a (n+2) - a (n+1) + a n := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [show 2*k+5 = 2*(k+2)+1 by ring, show 2*k+4 = 2*(k+2) by ring,
      show 2*k+3 = 2*(k+1)+1 by ring, show 2*k+2 = 2*(k+1) by ring, aE, aO, aE, aO, aE, aO]
    push_cast; ring
  · rw [show 2*k+1+5 = 2*(k+3) by ring, show 2*k+1+4 = 2*(k+2)+1 by ring,
      show 2*k+1+3 = 2*(k+2) by ring, show 2*k+1+2 = 2*(k+1)+1 by ring,
      show 2*k+1+1 = 2*(k+1) by ring, aE, aO, aE, aO, aE, aO]
    push_cast; ring

open PowerSeries in

theorem solution_main : type_of% @OMA.S_oeis_a265225.main := by
  refine ⟨fun n => ?_, fun n hn => ?_, ?_, aZ, fun n => ?_⟩
  · rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · rw [aE]; push_cast; rw [pow_mul]; norm_num <;> ring
    · rw [aO]; push_cast; rw [pow_succ, pow_mul]; norm_num <;> ring
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    rw [rec5, show m+5-1 = m+4 by omega, show m+5-2 = m+3 by omega, show m+5-3 = m+2 by omega,
      show m+5-4 = m+1 by omega, show m+5-5 = m by omega]
  · have hc : ∀ k, coeff k ((1:ℚ⟦X⟧) + 3*X) = if k = 0 then 1 else if k = 1 then 3 else 0 := by
      intro k
      rw [show (3:ℚ⟦X⟧) = C (3:ℚ) from (map_ofNat C 3).symm, map_add, coeff_one, coeff_C_mul, coeff_X]
      rcases k with _ | _ | k <;> simp
    rw [show PowerSeries.mk (fun n => (a n : ℚ)) * ((1-X)^3*(1+X)^2 : ℚ⟦X⟧) =
        PowerSeries.mk (fun n => (a n : ℚ)) - PowerSeries.mk (fun n => (a n : ℚ)) * X^1
        - C (2:ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X^2)
        + C (2:ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * X^3)
        + PowerSeries.mk (fun n => (a n : ℚ)) * X^4 - PowerSeries.mk (fun n => (a n : ℚ)) * X^5 by
      simp only [map_ofNat]; ring]
    ext k
    rw [hc]
    simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
    have v0 : a 0 = 1 := by simpa using aE 0
    have v1 : a 1 = 4 := by simpa using aO 0
    have v2 : a 2 = 6 := by simpa using aE 1
    have v3 : a 3 = 12 := by simpa using aO 1
    have v4 : a 4 = 15 := by simpa using aE 2
    rcases k with _ | _ | _ | _ | _ | k
    · simp [v0]
    · simp [v0, v1]; norm_num
    · simp [v0, v1, v2]; norm_num
    · simp [v0, v1, v2, v3]; norm_num
    · simp [v0, v1, v2, v3, v4]; norm_num
    · have r := rec5 k
      simp only [show k+1+1+1+1+1 = k+5 by ring, show k+5-1 = k+4 by omega, show k+5-2 = k+3 by omega,
        show k+5-3 = k+2 by omega, show k+5-4 = k+1 by omega, show k+5-5 = k by omega]
      simp
      rw [show (a (k+5) : ℚ) = ((a (k+4) + 2*a (k+3) - 2*a (k+2) - a (k+1) + a k : ℤ) : ℚ) by rw [r]]
      push_cast; ring
  · rw [aZ, a093353]
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · rw [show (2*k+1)/2 = k by omega, show 2*k + 2*k%2 = 2*k by omega,
        show 2*k*(2*k+1)/2 = k*(2*k+1) by rw [mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]]
      push_cast; ring
    · rw [show (2*k+1+1)/2 = k+1 by omega, show 2*k+1 + (2*k+1)%2 = 2*(k+1) by omega,
        show 2*(k+1)*(2*k+1+1)/2 = (k+1)*(2*k+2) by rw [mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]]
      push_cast; ring


end OMA.S_oeis_a265225_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a265225.main := OMA.S_oeis_a265225_Proof.solution_main
