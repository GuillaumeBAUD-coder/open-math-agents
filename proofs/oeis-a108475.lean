import OMAStatements.S_oeis_a108475
import Mathlib

namespace A108475

open OMA.S_oeis_a108475 PowerSeries in
noncomputable def f : PowerSeries ℚ :=
  (1 - 3 * X : PowerSeries ℚ) * (1 - 5 * X - 5 * X ^ 2 + X ^ 3 : PowerSeries ℚ)⁻¹

open OMA.S_oeis_a108475 PowerSeries in
lemma a_def (n : ℕ) : a n = coeff n f := rfl

open OMA.S_oeis_a108475 PowerSeries in
lemma key : f * (1 - 5 * X - 5 * X ^ 2 + X ^ 3 : PowerSeries ℚ) = 1 - 3 * X := by
  unfold f
  rw [mul_assoc, PowerSeries.inv_mul_cancel, mul_one]
  simp

open OMA.S_oeis_a108475 PowerSeries in
lemma expand : f * (1 - 5 * X - 5 * X ^ 2 + X ^ 3 : PowerSeries ℚ)
    = f - (5 : ℚ) • (f * X ^ 1) - (5 : ℚ) • (f * X ^ 2) + f * X ^ 3 := by
  rw [smul_eq_C_mul, smul_eq_C_mul, show (C (5 : ℚ) : PowerSeries ℚ) = 5 from map_ofNat C 5]
  ring

open OMA.S_oeis_a108475 PowerSeries in
lemma rhs (n : ℕ) : coeff n (1 - 3 * X : PowerSeries ℚ)
    = if n = 0 then 1 else if n = 1 then -3 else 0 := by
  rw [show (3 : PowerSeries ℚ) = C (3 : ℚ) from (map_ofNat C 3).symm, map_sub, coeff_one,
    coeff_C_mul, coeff_X]
  by_cases h0 : n = 0
  · simp [h0]
  · by_cases h1 : n = 1
    · simp [h1]
    · simp [h0, h1]

open OMA.S_oeis_a108475 PowerSeries in
lemma rel (n : ℕ) :
    a n - 5 * (if 1 ≤ n then a (n - 1) else 0) - 5 * (if 2 ≤ n then a (n - 2) else 0)
      + (if 3 ≤ n then a (n - 3) else 0) = coeff n (1 - 3 * X : PowerSeries ℚ) := by
  rw [← key, expand]
  simp only [map_add, map_sub, coeff_smul, coeff_mul_X_pow', a_def, smul_eq_mul]

open OMA.S_oeis_a108475 PowerSeries in
lemma a0 : a 0 = 1 := by
  have h := rel 0
  rw [rhs] at h
  simpa using h

open OMA.S_oeis_a108475 PowerSeries in
lemma a1 : a 1 = 2 := by
  have h := rel 1
  rw [rhs] at h
  simp [a0] at h
  linarith

open OMA.S_oeis_a108475 PowerSeries in
lemma a2 : a 2 = 15 := by
  have h := rel 2
  rw [rhs] at h
  simp [a0, a1] at h
  linarith

open OMA.S_oeis_a108475 PowerSeries in
lemma a_rec (n : ℕ) : a (n + 3) = 5 * a (n + 2) + 5 * a (n + 1) - a n := by
  have h := rel (n + 3)
  rw [rhs, if_pos (by omega), if_pos (by omega), if_pos (by omega), if_neg (by omega),
    if_neg (by omega), show n + 3 - 1 = n + 2 by omega, show n + 3 - 2 = n + 1 by omega,
    show n + 3 - 3 = n by omega] at h
  linarith

open OMA.S_oeis_a108475 PowerSeries in
lemma pell_rec (n : ℕ) : pell (n + 2) = 2 * pell (n + 1) + pell n := by
  rw [pell]

open OMA.S_oeis_a108475 PowerSeries in
lemma pl_rec (n : ℕ) : pellLucas (n + 2) = 2 * pellLucas (n + 1) + pellLucas n := by
  rw [pellLucas]

open OMA.S_oeis_a108475 PowerSeries in
lemma prod_rec (n : ℕ) :
    pell (n + 4) * pellLucas (n + 3)
      = 5 * (pell (n + 3) * pellLucas (n + 2)) + 5 * (pell (n + 2) * pellLucas (n + 1))
        - pell (n + 1) * pellLucas n := by
  have p2 : pell (n + 2) = 2 * pell (n + 1) + pell n := pell_rec n
  have p3 : pell (n + 3) = 2 * pell (n + 2) + pell (n + 1) := pell_rec (n + 1)
  have p4 : pell (n + 4) = 2 * pell (n + 3) + pell (n + 2) := pell_rec (n + 2)
  have q2 : pellLucas (n + 2) = 2 * pellLucas (n + 1) + pellLucas n := pl_rec n
  have q3 : pellLucas (n + 3) = 2 * pellLucas (n + 2) + pellLucas (n + 1) := pl_rec (n + 1)
  rw [p4, p3, p2, q3, q2]
  ring

open OMA.S_oeis_a108475 PowerSeries in
lemma triple (n : ℕ) :
    a n = (pell (n + 1) : ℚ) * (pellLucas n : ℚ) ∧
    a (n + 1) = (pell (n + 2) : ℚ) * (pellLucas (n + 1) : ℚ) ∧
    a (n + 2) = (pell (n + 3) : ℚ) * (pellLucas (n + 2) : ℚ) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · rw [a0]; norm_num [pell, pellLucas]
    · rw [a1]; norm_num [pell, pellLucas]
    · rw [a2]; norm_num [pell, pellLucas]
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    refine ⟨h1, h2, ?_⟩
    have hp : ((pell (n + 4) : ℤ) : ℚ) * ((pellLucas (n + 3) : ℤ) : ℚ)
        = 5 * (((pell (n + 3) : ℤ) : ℚ) * ((pellLucas (n + 2) : ℤ) : ℚ))
          + 5 * (((pell (n + 2) : ℤ) : ℚ) * ((pellLucas (n + 1) : ℤ) : ℚ))
          - ((pell (n + 1) : ℤ) : ℚ) * ((pellLucas n : ℤ) : ℚ) := by
      exact_mod_cast prod_rec n
    show a (n + 3) = (pell (n + 4) : ℚ) * (pellLucas (n + 3) : ℚ)
    rw [a_rec n, hp, h0, h1, h2]

end A108475

theorem OMA.solution : type_of% @OMA.S_oeis_a108475.main := by
  intro n
  exact (A108475.triple n).1
