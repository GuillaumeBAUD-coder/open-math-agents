import OMAStatements.S_oeis_a103141
import Mathlib

namespace A103141Proof

open Polynomial in
theorem poly_coeff (k i : ℕ) :
    (((1 : ℚ[X]) + X + X ^ 2 + X ^ 3) ^ k).coeff i =
      ∑ j ∈ Finset.range (i + 1),
        (Nat.choose k j : ℚ) * (Nat.choose (3 * k - 2 * j) (i - j) : ℚ) * (-2) ^ j := by
  have hP : ((1 : ℚ[X]) + X + X ^ 2 + X ^ 3) = C (-2) * X * (1 + X) + (1 + X) ^ 3 := by
    simp only [map_neg, C_ofNat]
    ring
  rw [hP, add_pow, finsetSum_coeff]
  have hterm : ∀ m ∈ Finset.range (k + 1),
      ((C (-2 : ℚ) * X * (1 + X)) ^ m * ((1 + X) ^ 3) ^ (k - m) * (Nat.choose k m : ℚ[X])).coeff i =
        if m ≤ i then (Nat.choose k m : ℚ) * (Nat.choose (3 * k - 2 * m) (i - m) : ℚ) * (-2) ^ m
        else 0 := by
    intro m hm
    have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have he : m + 3 * (k - m) = 3 * k - 2 * m := by omega
    have : (C (-2 : ℚ) * X * (1 + X)) ^ m * ((1 + X) ^ 3) ^ (k - m) * (Nat.choose k m : ℚ[X]) =
        C ((-2 : ℚ) ^ m * (Nat.choose k m : ℚ)) * (X ^ m * (1 + X) ^ (3 * k - 2 * m)) := by
      rw [← he, pow_add, pow_mul, C_mul, C_pow, ← C_eq_natCast, mul_pow, mul_pow]
      ring
    rw [this, coeff_C_mul, coeff_X_pow_mul']
    split_ifs
    · rw [coeff_one_add_X_pow]; ring
    · simp
  rw [Finset.sum_congr rfl hterm]
  have h1 : ∑ m ∈ Finset.range (k + 1),
      (if m ≤ i then (Nat.choose k m : ℚ) * (Nat.choose (3 * k - 2 * m) (i - m) : ℚ) * (-2) ^ m
        else 0) = ∑ m ∈ Finset.range (k + i + 1),
      (if m ≤ i then (Nat.choose k m : ℚ) * (Nat.choose (3 * k - 2 * m) (i - m) : ℚ) * (-2) ^ m
        else 0) := by
    apply Finset.sum_subset
    · intro a ha; simp only [Finset.mem_range] at *; omega
    · intro a _ ha
      simp only [Finset.mem_range, not_lt] at ha
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
  have h2 : ∑ j ∈ Finset.range (i + 1),
        (Nat.choose k j : ℚ) * (Nat.choose (3 * k - 2 * j) (i - j) : ℚ) * (-2) ^ j =
      ∑ m ∈ Finset.range (k + i + 1),
      (if m ≤ i then (Nat.choose k m : ℚ) * (Nat.choose (3 * k - 2 * m) (i - m) : ℚ) * (-2) ^ m
        else 0) := by
    refine Eq.trans (Finset.sum_congr rfl ?_) (Finset.sum_subset ?_ ?_)
    · intro a ha
      rw [if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))]
    · intro a ha; simp only [Finset.mem_range] at *; omega
    · intro a _ ha
      simp only [Finset.mem_range, not_lt] at ha
      rw [if_neg (by omega)]
  rw [h1, h2]

open PowerSeries in
theorem inv_eq : ((1 : ℚ⟦X⟧) - X)⁻¹ = mk 1 := by
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by simp)]
  exact mk_one_mul_one_sub_eq_one ℚ

open PowerSeries in
theorem ps_coeff (k i : ℕ) :
    coeff i (((1 : ℚ⟦X⟧) + X + X ^ 2 + X ^ 3) ^ k) =
      ∑ j ∈ Finset.range (i + 1),
        (Nat.choose k j : ℚ) * (Nat.choose (3 * k - 2 * j) (i - j) : ℚ) * (-2) ^ j := by
  have hP : ((1 : ℚ⟦X⟧) + X + X ^ 2 + X ^ 3) =
      (((1 : Polynomial ℚ) + Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3 : Polynomial ℚ) : ℚ⟦X⟧) := by
    simp
  rw [hP, ← Polynomial.coe_pow, Polynomial.coeff_coe, poly_coeff]

end A103141Proof

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a103141.main := by
  intro n k hk
  unfold OMA.S_oeis_a103141.T
  have halg : ((1 : ℚ⟦X⟧) - X)⁻¹ * (X * (1 + X + X ^ 2 + X ^ 3) * ((1 : ℚ⟦X⟧) - X)⁻¹) ^ k =
      X ^ k * ((1 + X + X ^ 2 + X ^ 3) ^ k * (((1 : ℚ⟦X⟧) - X)⁻¹) ^ (k + 1)) := by
    rw [mul_pow, mul_pow]
    ring
  rw [halg, coeff_X_pow_mul', if_pos hk, A103141Proof.inv_eq, mk_one_pow_eq_mk_choose_add,
    coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n - k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [A103141Proof.ps_coeff, coeff_mk]
  have : k + (n - k - i) = n - i := by omega
  rw [this, mul_comm]
