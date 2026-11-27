import OMAStatements.S_oeis_a108476
import Mathlib

namespace A108476

open OMA.S_oeis_a108476 PowerSeries in
noncomputable def f : PowerSeries ℚ :=
  (1 - 4 * X : PowerSeries ℚ) * (1 - 6 * X - 12 * X ^ 2 + 8 * X ^ 3 : PowerSeries ℚ)⁻¹

open OMA.S_oeis_a108476 PowerSeries in
lemma a_def (n : ℕ) : a n = coeff n f := rfl

open OMA.S_oeis_a108476 PowerSeries in
lemma key : f * (1 - 6 * X - 12 * X ^ 2 + 8 * X ^ 3 : PowerSeries ℚ) = 1 - 4 * X := by
  unfold f
  rw [mul_assoc, PowerSeries.inv_mul_cancel, mul_one]
  simp

open OMA.S_oeis_a108476 PowerSeries in
lemma expand : f * (1 - 6 * X - 12 * X ^ 2 + 8 * X ^ 3 : PowerSeries ℚ)
    = f - (6 : ℚ) • (f * X ^ 1) - (12 : ℚ) • (f * X ^ 2) + (8 : ℚ) • (f * X ^ 3) := by
  rw [smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul,
    show (C (6 : ℚ) : PowerSeries ℚ) = 6 from map_ofNat C 6,
    show (C (12 : ℚ) : PowerSeries ℚ) = 12 from map_ofNat C 12,
    show (C (8 : ℚ) : PowerSeries ℚ) = 8 from map_ofNat C 8]
  ring

open OMA.S_oeis_a108476 PowerSeries in
lemma rhs (n : ℕ) : coeff n (1 - 4 * X : PowerSeries ℚ)
    = if n = 0 then 1 else if n = 1 then -4 else 0 := by
  rw [show (4 : PowerSeries ℚ) = C (4 : ℚ) from (map_ofNat C 4).symm, map_sub, coeff_one,
    coeff_C_mul, coeff_X]
  by_cases h0 : n = 0
  · simp [h0]
  · by_cases h1 : n = 1
    · simp [h1]
    · simp [h0, h1]

open OMA.S_oeis_a108476 PowerSeries in
lemma rel (n : ℕ) :
    a n - 6 * (if 1 ≤ n then a (n - 1) else 0) - 12 * (if 2 ≤ n then a (n - 2) else 0)
      + 8 * (if 3 ≤ n then a (n - 3) else 0) = coeff n (1 - 4 * X : PowerSeries ℚ) := by
  rw [← key, expand]
  simp only [map_add, map_sub, coeff_smul, coeff_mul_X_pow', a_def, smul_eq_mul]

open OMA.S_oeis_a108476 PowerSeries in
lemma a0 : a 0 = 1 := by
  have h := rel 0
  rw [rhs] at h
  simpa using h

open OMA.S_oeis_a108476 PowerSeries in
lemma a1 : a 1 = 2 := by
  have h := rel 1
  rw [rhs] at h
  simp [a0] at h
  linarith

open OMA.S_oeis_a108476 PowerSeries in
lemma a2 : a 2 = 24 := by
  have h := rel 2
  rw [rhs] at h
  simp [a0, a1] at h
  linarith

open OMA.S_oeis_a108476 PowerSeries in
lemma a_rec (n : ℕ) : a (n + 3) = 6 * a (n + 2) + 12 * a (n + 1) - 8 * a n := by
  have h := rel (n + 3)
  rw [rhs, if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega),
    if_neg (by omega), show n + 3 - 1 = n + 2 by omega, show n + 3 - 2 = n + 1 by omega,
    show n + 3 - 3 = n by omega] at h
  linarith

open OMA.S_oeis_a108476 in
lemma b_rec (n : ℕ) : A002605 (n + 2) = 2 * (A002605 (n + 1) + A002605 n) := by
  rw [A002605]

open OMA.S_oeis_a108476 in
lemma c_rec (n : ℕ) : A026150 (n + 2) = 2 * A026150 (n + 1) + 2 * A026150 n := by
  rw [A026150]

open OMA.S_oeis_a108476 in
lemma prod_rec (n : ℕ) :
    A002605 (n + 4) * A026150 (n + 3)
      = 6 * (A002605 (n + 3) * A026150 (n + 2)) + 12 * (A002605 (n + 2) * A026150 (n + 1))
        - 8 * (A002605 (n + 1) * A026150 n) := by
  have p3 : A002605 (n + 3) = 2 * (A002605 (n + 2) + A002605 (n + 1)) := b_rec (n + 1)
  have p4 : A002605 (n + 4) = 2 * (A002605 (n + 3) + A002605 (n + 2)) := b_rec (n + 2)
  have q2 : A026150 (n + 2) = 2 * A026150 (n + 1) + 2 * A026150 n := c_rec n
  have q3 : A026150 (n + 3) = 2 * A026150 (n + 2) + 2 * A026150 (n + 1) := c_rec (n + 1)
  rw [p4, p3, q3, q2]
  ring

open OMA.S_oeis_a108476 in
lemma triple (n : ℕ) :
    a n = (A002605 (n + 1) : ℚ) * (A026150 n : ℚ) ∧
    a (n + 1) = (A002605 (n + 2) : ℚ) * (A026150 (n + 1) : ℚ) ∧
    a (n + 2) = (A002605 (n + 3) : ℚ) * (A026150 (n + 2) : ℚ) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · rw [a0]; norm_num [A002605, A026150]
    · rw [a1]; norm_num [A002605, A026150]
    · rw [a2]; norm_num [A002605, A026150]
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    refine ⟨h1, h2, ?_⟩
    have hp : ((A002605 (n + 4) : ℤ) : ℚ) * ((A026150 (n + 3) : ℤ) : ℚ)
        = 6 * (((A002605 (n + 3) : ℤ) : ℚ) * ((A026150 (n + 2) : ℤ) : ℚ))
          + 12 * (((A002605 (n + 2) : ℤ) : ℚ) * ((A026150 (n + 1) : ℤ) : ℚ))
          - 8 * (((A002605 (n + 1) : ℤ) : ℚ) * ((A026150 n : ℤ) : ℚ)) := by
      exact_mod_cast prod_rec n
    show a (n + 3) = (A002605 (n + 4) : ℚ) * (A026150 (n + 3) : ℚ)
    rw [a_rec n, hp, h0, h1, h2]

end A108476

theorem OMA.solution : type_of% @OMA.S_oeis_a108476.main := by
  intro n
  exact (A108476.triple n).1
