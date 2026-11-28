import OMAStatements.S_oeis_a379907
import Mathlib

namespace A379907Proof

open Finset OMA.S_oeis_a379907

/-- The ballot number binomial(k + 2 i, i) (k + 1) / (k + 1 + i). -/
def b (k i : ℕ) : ℚ := (Nat.choose (k + 2 * i) i : ℚ) * ((k : ℚ) + 1) / ((k : ℚ) + 1 + (i : ℚ))

/-- The unsigned-prefactor form of the sum. -/
def U (m k : ℕ) : ℚ := ∑ i ∈ range (m + 1), (-1 : ℚ) ^ i * (Nat.choose m i : ℚ) * b k i

theorem T_eq (m k : ℕ) : T (k + m) k = (-1 : ℚ) ^ m * U m k := by
  unfold T U
  rw [Nat.add_sub_cancel_left, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hs : (-1 : ℚ) ^ (m - i) = (-1) ^ m * (-1) ^ i := by
    have h1 : (-1 : ℚ) ^ m = (-1) ^ (m - i) * (-1) ^ i := by
      rw [← pow_add, Nat.sub_add_cancel hi']
    have h2 : ((-1 : ℚ) ^ i) * (-1) ^ i = 1 := by
      rw [← mul_pow]; norm_num
    rw [h1, mul_assoc, h2, mul_one]
  rw [hs]
  unfold b
  ring

theorem U_succ (m k : ℕ) :
    U (m + 1) k - U m k = -∑ j ∈ range (m + 1), (-1 : ℚ) ^ j * (Nat.choose m j : ℚ) * b k (j + 1) := by
  have h1 : U (m + 1) k = ∑ j ∈ range (m + 1),
      (-1 : ℚ) ^ (j + 1) * (Nat.choose (m + 1) (j + 1) : ℚ) * b k (j + 1) + b k 0 := by
    unfold U
    rw [Finset.sum_range_succ']
    simp
  have h2 : U m k = ∑ j ∈ range (m + 1),
      (-1 : ℚ) ^ (j + 1) * (Nat.choose m (j + 1) : ℚ) * b k (j + 1) + b k 0 := by
    unfold U
    rw [Finset.sum_range_succ', Finset.sum_range_succ]
    simp
  rw [h1, h2, add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.choose_succ_succ]
  push_cast
  ring

theorem b_rec (K j : ℕ) : b (K + 1) (j + 1) - b K (j + 1) = b (K + 2) j := by
  unfold b
  have e1 : K + 1 + 2 * (j + 1) = (K + 2 * j + 2) + 1 := by ring
  have e2 : K + 2 * (j + 1) = K + 2 * j + 2 := by ring
  have e3 : K + 2 + 2 * j = K + 2 * j + 2 := by ring
  rw [e1, e2, e3, Nat.choose_succ_succ]
  have h := Nat.choose_succ_right_eq (K + 2 * j + 2) j
  have hsub : K + 2 * j + 2 - j = K + j + 2 := by omega
  rw [hsub] at h
  have hq : (Nat.choose (K + 2 * j + 2) (j + 1) : ℚ) * ((j : ℚ) + 1)
      = (Nat.choose (K + 2 * j + 2) j : ℚ) * ((K : ℚ) + (j : ℚ) + 2) := by
    exact_mod_cast h
  have hj : ((j : ℚ) + 1) ≠ 0 := by positivity
  have hc : (Nat.choose (K + 2 * j + 2) (j + 1) : ℚ)
      = (Nat.choose (K + 2 * j + 2) j : ℚ) * ((K : ℚ) + (j : ℚ) + 2) / ((j : ℚ) + 1) := by
    rw [eq_div_iff hj]; exact hq
  push_cast
  rw [hc]
  have d1 : ((K : ℚ) + 1 + 1 + ((j : ℚ) + 1)) ≠ 0 := by positivity
  have d2 : ((K : ℚ) + 1 + ((j : ℚ) + 1)) ≠ 0 := by positivity
  have d3 : ((K : ℚ) + 2 + 1 + (j : ℚ)) ≠ 0 := by positivity
  field_simp
  ring

theorem key (m K : ℕ) :
    T (K + 2 + m) (K + 2) = T (K + 2 + m) (K + 1) + T (K + 1 + m) (K + 1)
      - T (K + 1 + m) K - T (K + m) K := by
  have a1 : T (K + 2 + m) (K + 1) = (-1 : ℚ) ^ (m + 1) * U (m + 1) (K + 1) := by
    rw [← T_eq]; congr 1; ring
  have a2 : T (K + 1 + m) K = (-1 : ℚ) ^ (m + 1) * U (m + 1) K := by
    rw [← T_eq]; congr 1; ring
  rw [a1, a2, T_eq, T_eq, T_eq]
  have u1 := U_succ m (K + 1)
  have u2 := U_succ m K
  have hU : U m (K + 2) = ∑ j ∈ range (m + 1), (-1 : ℚ) ^ j * (Nat.choose m j : ℚ) * b (K + 1) (j + 1)
      - ∑ j ∈ range (m + 1), (-1 : ℚ) ^ j * (Nat.choose m j : ℚ) * b K (j + 1) := by
    unfold U
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← b_rec]; ring
  rw [hU]
  rw [pow_succ]
  linear_combination ((-1 : ℚ) ^ m) * (u1 - u2)

end A379907Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a379907.main := by
  intro n k hk hkn
  obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le hk
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hkn
  have h := A379907Proof.key m K
  have e1 : 2 + K + m = K + 2 + m := by ring
  have e2 : 2 + K = K + 2 := by ring
  rw [e1, e2]
  have f1 : K + 2 - 1 = K + 1 := by omega
  have f2 : K + 2 + m - 1 = K + 1 + m := by omega
  have f3 : K + 2 - 2 = K := by omega
  have f4 : K + 2 + m - 2 = K + m := by omega
  rw [f1, f2, f3, f4]
  exact h
