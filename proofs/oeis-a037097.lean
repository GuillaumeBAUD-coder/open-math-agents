import OMAStatements.S_oeis_a037097
import Mathlib

namespace OMA.Helpers

open Polynomial

theorem a037097_pow3 (j : ℕ) : ∃ u : ℕ, 3 ^ (2 ^ (j + 1)) = 1 + 2 ^ (j + 3) * (2 * u + 1) := by
  induction j with
  | zero => exact ⟨0, by norm_num⟩
  | succ j ih =>
    obtain ⟨u, hu⟩ := ih
    refine ⟨u + 2 ^ (j + 1) * (2 * u + 1) ^ 2, ?_⟩
    have h : 3 ^ (2 ^ (j + 1 + 1)) = (3 ^ (2 ^ (j + 1))) ^ 2 := by
      rw [← pow_mul, pow_succ]
    rw [h, hu]
    ring

theorem a037097_digit (j k : ℕ) :
    OMA.S_oeis_a037097.digit (j + 3) (2 ^ (j + 1) + k) =
      OMA.S_oeis_a037097.digit (j + 3) k + 1 := by
  obtain ⟨u, hu⟩ := a037097_pow3 j
  unfold OMA.S_oeis_a037097.digit
  rw [ZMod.natCast_mod, ZMod.natCast_mod]
  have h3 : 3 ^ (2 ^ (j + 1) + k) = 3 ^ k + 2 ^ (j + 3) * ((2 * u + 1) * 3 ^ k) := by
    rw [pow_add, hu]
    ring
  have hpos : 0 < 2 ^ (j + 3) := by positivity
  rw [h3, Nat.add_mul_div_left _ _ hpos, Nat.cast_add]
  congr 1
  apply Odd.natCast_zmod_two
  exact Odd.mul (by exact ⟨u, rfl⟩) (Odd.pow (by decide))

theorem a037097_geom (M : ℕ) (hM : 1 ≤ M) (hpow : (X + 1 : (ZMod 2)[X]) ^ M = X ^ M + 1) :
    (∑ k ∈ Finset.range M, (X : (ZMod 2)[X]) ^ k) = (X + 1) ^ (M - 1) := by
  have hX : (X + 1 : (ZMod 2)[X]) ≠ 0 := by
    simpa using Polynomial.X_add_C_ne_zero (1 : ZMod 2)
  apply mul_right_cancel₀ hX
  have h1 := geom_sum_mul (X : (ZMod 2)[X]) M
  rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add] at h1
  rw [h1, ← hpow, ← pow_succ, Nat.sub_add_cancel hM]

theorem a037097_main (j : ℕ) :
    OMA.S_oeis_a037097.column (j + 3) (2 ^ (j + 2)) =
      (X + 1) ^ (2 ^ (j + 1) - 1) *
        ((X + 1) * OMA.S_oeis_a037097.column (j + 3) (2 ^ (j + 1)) + X ^ (2 ^ (j + 1))) := by
  set M := 2 ^ (j + 1) with hMdef
  have hM2 : 2 ^ (j + 2) = M + M := by rw [hMdef, pow_succ]; ring
  have hM1 : 1 ≤ M := Nat.one_le_two_pow
  have hpow : (X + 1 : (ZMod 2)[X]) ^ M = X ^ M + 1 := by
    rw [hMdef, add_pow_char_pow, one_pow]
  have hB := a037097_geom M hM1 hpow
  unfold OMA.S_oeis_a037097.column
  rw [hM2, Finset.sum_range_add]
  have hsplit : (∑ x ∈ Finset.range M,
      C (OMA.S_oeis_a037097.digit (j + 3) (M + x)) * (X : (ZMod 2)[X]) ^ (M + x)) =
      X ^ M * ((∑ k ∈ Finset.range M, C (OMA.S_oeis_a037097.digit (j + 3) k) * X ^ k) +
        ∑ k ∈ Finset.range M, (X : (ZMod 2)[X]) ^ k) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [hMdef, a037097_digit, map_add, map_one, pow_add]
    ring
  rw [hsplit, hB]
  have hsucc : (X + 1 : (ZMod 2)[X]) ^ M = (X + 1) ^ (M - 1) * (X + 1) := by
    rw [← pow_succ, Nat.sub_add_cancel hM1]
  generalize (∑ k ∈ Finset.range M, C (OMA.S_oeis_a037097.digit (j + 3) k) * (X : (ZMod 2)[X]) ^ k) = A
  have hr : (X + 1 : (ZMod 2)[X]) ^ (M - 1) * ((X + 1) * A + X ^ M) =
      (X + 1) ^ M * A + (X + 1) ^ (M - 1) * X ^ M := by
    rw [hsucc]; ring
  rw [hr, hpow]
  ring

end OMA.Helpers

open Polynomial in
theorem OMA.solution : type_of% @OMA.S_oeis_a037097.main := by
  intro n hn
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have e1 : j + 3 - 1 = j + 2 := by omega
  have e2 : j + 3 - 2 = j + 1 := by omega
  have hdvd : (X + 1 : (ZMod 2)[X]) ^ (2 ^ (j + 3 - 2) - 1) ∣
      OMA.S_oeis_a037097.column (j + 3) (2 ^ (j + 3 - 1)) := by
    rw [e1, e2, OMA.Helpers.a037097_main j]
    exact Dvd.intro _ rfl
  refine ⟨hdvd, ?_⟩
  have hne : (X + 1 : (ZMod 2)[X]) ^ (2 ^ (j + 3 - 2) - 1) ≠ 0 := by
    apply pow_ne_zero
    simpa using Polynomial.X_add_C_ne_zero (1 : ZMod 2)
  unfold OMA.S_oeis_a037097.quotient
  exact (EuclideanDomain.mul_div_cancel' hne hdvd).symm
