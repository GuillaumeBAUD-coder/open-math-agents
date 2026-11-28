import OMAStatements.S_oeis_a192031
import Mathlib

-- Problem: A192031. Distances in helm graphs.
-- Upstream: formal-conjectures statements/oeis-a192031.lean:0 (declaration OMA.S_oeis_a192031.main)
-- Credit: @npnelson (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof. For n >= 6 write n = 6 + 4 q + r with r < 4; then a(n) is the explicit quadratic
-- row (4 + q) r. The denominator is 1 - X + X^2 - X^3 - 2X^4 + 2X^5 - 2X^6 + 2X^7 + X^8 - X^9
-- + X^10 - X^11, so the recurrence is the vanishing of the coefficients of the product from
-- degree 17 on; for each residue of n mod 4 it is a polynomial identity in q. The numerator
-- is read off from a(0), ..., a(16).

namespace Helm192031Proof

open OMA.S_oeis_a192031

theorem ag0 (q : ℕ) : a (6 + 4 * q + 0) = 3 * (4 + (q : ℚ)) := by
  unfold a
  rw [if_neg (by omega), if_neg (by omega)]
  have e1 : (6 + 4 * q + 0 - 6) / 4 = q := by omega
  have e2 : (6 + 4 * q + 0 - 6) % 4 = 0 := by omega
  rw [e1, e2]
  rfl

theorem ag1 (q : ℕ) : a (6 + 4 * q + 1) = (4 + (q : ℚ)) * ((4 + (q : ℚ)) + 3) / 2 := by
  unfold a
  rw [if_neg (by omega), if_neg (by omega)]
  have e1 : (6 + 4 * q + 1 - 6) / 4 = q := by omega
  have e2 : (6 + 4 * q + 1 - 6) % 4 = 1 := by omega
  rw [e1, e2]
  rfl

theorem ag2 (q : ℕ) : a (6 + 4 * q + 2) = (4 + (q : ℚ)) * ((4 + (q : ℚ)) - 2) := by
  unfold a
  rw [if_neg (by omega), if_neg (by omega)]
  have e1 : (6 + 4 * q + 2 - 6) / 4 = q := by omega
  have e2 : (6 + 4 * q + 2 - 6) % 4 = 2 := by omega
  rw [e1, e2]
  rfl

theorem ag3 (q : ℕ) : a (6 + 4 * q + 3) = (4 + (q : ℚ)) * ((4 + (q : ℚ)) - 3) / 2 := by
  unfold a
  rw [if_neg (by omega), if_neg (by omega)]
  have e1 : (6 + 4 * q + 3 - 6) / 4 = q := by omega
  have e2 : (6 + 4 * q + 3 - 6) % 4 = 3 := by omega
  rw [e1, e2]
  rfl

theorem rec0 (q : ℕ) :
    a (17 + 4 * q + 0) = a (17 + 4 * q + 0 - 1) - a (17 + 4 * q + 0 - 2) + a (17 + 4 * q + 0 - 3) + 2 * a (17 + 4 * q + 0 - 4) -
      2 * a (17 + 4 * q + 0 - 5) + 2 * a (17 + 4 * q + 0 - 6) - 2 * a (17 + 4 * q + 0 - 7) - a (17 + 4 * q + 0 - 8) + a (17 + 4 * q + 0 - 9) -
      a (17 + 4 * q + 0 - 10) + a (17 + 4 * q + 0 - 11) := by
  rw [show 17 + 4 * q + 0 - 11 = 6 + 4 * (q + 0) + 0 by omega,
    show 17 + 4 * q + 0 - 10 = 6 + 4 * (q + 0) + 1 by omega,
    show 17 + 4 * q + 0 - 9 = 6 + 4 * (q + 0) + 2 by omega,
    show 17 + 4 * q + 0 - 8 = 6 + 4 * (q + 0) + 3 by omega,
    show 17 + 4 * q + 0 - 7 = 6 + 4 * (q + 1) + 0 by omega,
    show 17 + 4 * q + 0 - 6 = 6 + 4 * (q + 1) + 1 by omega,
    show 17 + 4 * q + 0 - 5 = 6 + 4 * (q + 1) + 2 by omega,
    show 17 + 4 * q + 0 - 4 = 6 + 4 * (q + 1) + 3 by omega,
    show 17 + 4 * q + 0 - 3 = 6 + 4 * (q + 2) + 0 by omega,
    show 17 + 4 * q + 0 - 2 = 6 + 4 * (q + 2) + 1 by omega,
    show 17 + 4 * q + 0 - 1 = 6 + 4 * (q + 2) + 2 by omega,
    show 17 + 4 * q + 0 = 6 + 4 * (q + 2) + 3 by omega]
  simp only [ag0, ag1, ag2, ag3]
  push_cast
  ring

theorem rec1 (q : ℕ) :
    a (17 + 4 * q + 1) = a (17 + 4 * q + 1 - 1) - a (17 + 4 * q + 1 - 2) + a (17 + 4 * q + 1 - 3) + 2 * a (17 + 4 * q + 1 - 4) -
      2 * a (17 + 4 * q + 1 - 5) + 2 * a (17 + 4 * q + 1 - 6) - 2 * a (17 + 4 * q + 1 - 7) - a (17 + 4 * q + 1 - 8) + a (17 + 4 * q + 1 - 9) -
      a (17 + 4 * q + 1 - 10) + a (17 + 4 * q + 1 - 11) := by
  rw [show 17 + 4 * q + 1 - 11 = 6 + 4 * (q + 0) + 1 by omega,
    show 17 + 4 * q + 1 - 10 = 6 + 4 * (q + 0) + 2 by omega,
    show 17 + 4 * q + 1 - 9 = 6 + 4 * (q + 0) + 3 by omega,
    show 17 + 4 * q + 1 - 8 = 6 + 4 * (q + 1) + 0 by omega,
    show 17 + 4 * q + 1 - 7 = 6 + 4 * (q + 1) + 1 by omega,
    show 17 + 4 * q + 1 - 6 = 6 + 4 * (q + 1) + 2 by omega,
    show 17 + 4 * q + 1 - 5 = 6 + 4 * (q + 1) + 3 by omega,
    show 17 + 4 * q + 1 - 4 = 6 + 4 * (q + 2) + 0 by omega,
    show 17 + 4 * q + 1 - 3 = 6 + 4 * (q + 2) + 1 by omega,
    show 17 + 4 * q + 1 - 2 = 6 + 4 * (q + 2) + 2 by omega,
    show 17 + 4 * q + 1 - 1 = 6 + 4 * (q + 2) + 3 by omega,
    show 17 + 4 * q + 1 = 6 + 4 * (q + 3) + 0 by omega]
  simp only [ag0, ag1, ag2, ag3]
  push_cast
  ring

theorem rec2 (q : ℕ) :
    a (17 + 4 * q + 2) = a (17 + 4 * q + 2 - 1) - a (17 + 4 * q + 2 - 2) + a (17 + 4 * q + 2 - 3) + 2 * a (17 + 4 * q + 2 - 4) -
      2 * a (17 + 4 * q + 2 - 5) + 2 * a (17 + 4 * q + 2 - 6) - 2 * a (17 + 4 * q + 2 - 7) - a (17 + 4 * q + 2 - 8) + a (17 + 4 * q + 2 - 9) -
      a (17 + 4 * q + 2 - 10) + a (17 + 4 * q + 2 - 11) := by
  rw [show 17 + 4 * q + 2 - 11 = 6 + 4 * (q + 0) + 2 by omega,
    show 17 + 4 * q + 2 - 10 = 6 + 4 * (q + 0) + 3 by omega,
    show 17 + 4 * q + 2 - 9 = 6 + 4 * (q + 1) + 0 by omega,
    show 17 + 4 * q + 2 - 8 = 6 + 4 * (q + 1) + 1 by omega,
    show 17 + 4 * q + 2 - 7 = 6 + 4 * (q + 1) + 2 by omega,
    show 17 + 4 * q + 2 - 6 = 6 + 4 * (q + 1) + 3 by omega,
    show 17 + 4 * q + 2 - 5 = 6 + 4 * (q + 2) + 0 by omega,
    show 17 + 4 * q + 2 - 4 = 6 + 4 * (q + 2) + 1 by omega,
    show 17 + 4 * q + 2 - 3 = 6 + 4 * (q + 2) + 2 by omega,
    show 17 + 4 * q + 2 - 2 = 6 + 4 * (q + 2) + 3 by omega,
    show 17 + 4 * q + 2 - 1 = 6 + 4 * (q + 3) + 0 by omega,
    show 17 + 4 * q + 2 = 6 + 4 * (q + 3) + 1 by omega]
  simp only [ag0, ag1, ag2, ag3]
  push_cast
  ring

theorem rec3 (q : ℕ) :
    a (17 + 4 * q + 3) = a (17 + 4 * q + 3 - 1) - a (17 + 4 * q + 3 - 2) + a (17 + 4 * q + 3 - 3) + 2 * a (17 + 4 * q + 3 - 4) -
      2 * a (17 + 4 * q + 3 - 5) + 2 * a (17 + 4 * q + 3 - 6) - 2 * a (17 + 4 * q + 3 - 7) - a (17 + 4 * q + 3 - 8) + a (17 + 4 * q + 3 - 9) -
      a (17 + 4 * q + 3 - 10) + a (17 + 4 * q + 3 - 11) := by
  rw [show 17 + 4 * q + 3 - 11 = 6 + 4 * (q + 0) + 3 by omega,
    show 17 + 4 * q + 3 - 10 = 6 + 4 * (q + 1) + 0 by omega,
    show 17 + 4 * q + 3 - 9 = 6 + 4 * (q + 1) + 1 by omega,
    show 17 + 4 * q + 3 - 8 = 6 + 4 * (q + 1) + 2 by omega,
    show 17 + 4 * q + 3 - 7 = 6 + 4 * (q + 1) + 3 by omega,
    show 17 + 4 * q + 3 - 6 = 6 + 4 * (q + 2) + 0 by omega,
    show 17 + 4 * q + 3 - 5 = 6 + 4 * (q + 2) + 1 by omega,
    show 17 + 4 * q + 3 - 4 = 6 + 4 * (q + 2) + 2 by omega,
    show 17 + 4 * q + 3 - 3 = 6 + 4 * (q + 2) + 3 by omega,
    show 17 + 4 * q + 3 - 2 = 6 + 4 * (q + 3) + 0 by omega,
    show 17 + 4 * q + 3 - 1 = 6 + 4 * (q + 3) + 1 by omega,
    show 17 + 4 * q + 3 = 6 + 4 * (q + 3) + 2 by omega]
  simp only [ag0, ag1, ag2, ag3]
  push_cast
  ring

theorem recAll (n : ℕ) (hn : 16 < n) :
    a (n) = a (n - 1) - a (n - 2) + a (n - 3) + 2 * a (n - 4) -
      2 * a (n - 5) + 2 * a (n - 6) - 2 * a (n - 7) - a (n - 8) + a (n - 9) -
      a (n - 10) + a (n - 11) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 4 ∧ n = 17 + 4 * q + r :=
    ⟨(n - 17) / 4, (n - 17) % 4, Nat.mod_lt _ (by norm_num), by omega⟩
  have h4 : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases h4 with rfl | rfl | rfl | rfl
  · exact rec0 q
  · exact rec1 q
  · exact rec2 q
  · exact rec3 q

theorem a_0 : a 0 = 0 := by
  norm_num [a, row]

theorem a_1 : a 1 = 0 := by
  norm_num [a, row]

theorem a_2 : a 2 = 0 := by
  norm_num [a, row]

theorem a_3 : a 3 = 9 := by
  norm_num [a, row]

theorem a_4 : a 4 = 9 := by
  norm_num [a, row]

theorem a_5 : a 5 = 3 := by
  norm_num [a, row]

theorem a_6 : a 6 = 12 := by
  norm_num [a, row]

theorem a_7 : a 7 = 14 := by
  norm_num [a, row]

theorem a_8 : a 8 = 8 := by
  norm_num [a, row]

theorem a_9 : a 9 = 2 := by
  norm_num [a, row]

theorem a_10 : a 10 = 15 := by
  norm_num [a, row]

theorem a_11 : a 11 = 20 := by
  norm_num [a, row]

theorem a_12 : a 12 = 15 := by
  norm_num [a, row]

theorem a_13 : a 13 = 5 := by
  norm_num [a, row]

theorem a_14 : a 14 = 18 := by
  norm_num [a, row]

theorem a_15 : a 15 = 27 := by
  norm_num [a, row]

theorem a_16 : a 16 = 24 := by
  norm_num [a, row]

open PowerSeries

theorem series :
    mk a * ((1 - X) ^ 3 * (1 + X) ^ 2 * (1 + X ^ 2) ^ 3) =
      X ^ 3 * (9 + 3 * X ^ 2 + 9 * X ^ 3 - 22 * X ^ 4 + 3 * X ^ 5 - 10 * X ^ 6 - 11 * X ^ 7 +
        16 * X ^ 8 + 2 * X ^ 9 + 6 * X ^ 10 + 3 * X ^ 11 - 3 * X ^ 12 - 3 * X ^ 13) := by
  let F : ℚ⟦X⟧ := mk a
  change F * _ = _
  have poly : F * ((1 - X) ^ 3 * (1 + X) ^ 2 * (1 + X ^ 2) ^ 3)
      = F - F * X ^ 1 + F * X ^ 2 - F * X ^ 3 - (2 : ℕ) • (F * X ^ 4) + (2 : ℕ) • (F * X ^ 5)
        - (2 : ℕ) • (F * X ^ 6) + (2 : ℕ) • (F * X ^ 7) + F * X ^ 8 - F * X ^ 9 + F * X ^ 10
        - F * X ^ 11 := by
    simp only [nsmul_eq_mul]
    push_cast
    ring
  have rhs : (X : ℚ⟦X⟧) ^ 3 * (9 + 3 * X ^ 2 + 9 * X ^ 3 - 22 * X ^ 4 + 3 * X ^ 5 - 10 * X ^ 6
        - 11 * X ^ 7 + 16 * X ^ 8 + 2 * X ^ 9 + 6 * X ^ 10 + 3 * X ^ 11 - 3 * X ^ 12 - 3 * X ^ 13)
      = (9 : ℕ) • X ^ 3 + (3 : ℕ) • X ^ 5 + (9 : ℕ) • X ^ 6 - (22 : ℕ) • X ^ 7 + (3 : ℕ) • X ^ 8
        - (10 : ℕ) • X ^ 9 - (11 : ℕ) • X ^ 10 + (16 : ℕ) • X ^ 11 + (2 : ℕ) • X ^ 12
        + (6 : ℕ) • X ^ 13 + (3 : ℕ) • X ^ 14 - (3 : ℕ) • X ^ 15 - (3 : ℕ) • X ^ 16 := by
    simp only [nsmul_eq_mul]
    push_cast
    ring
  rw [poly, rhs]
  ext n
  simp only [map_add, map_sub, map_nsmul, coeff_X_pow, coeff_mul_X_pow', F, coeff_mk]
  simp only [nsmul_eq_mul]
  by_cases h : n < 17
  · interval_cases n <;> norm_num [a_0, a_1, a_2, a_3, a_4, a_5, a_6, a_7, a_8, a_9, a_10, a_11, a_12, a_13, a_14, a_15, a_16]
  · have hr := recAll n (by omega)
    simp only [if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega), if_pos (show 3 ≤ n by omega), if_pos (show 4 ≤ n by omega), if_pos (show 5 ≤ n by omega), if_pos (show 6 ≤ n by omega), if_pos (show 7 ≤ n by omega), if_pos (show 8 ≤ n by omega), if_pos (show 9 ≤ n by omega), if_pos (show 10 ≤ n by omega), if_pos (show 11 ≤ n by omega),
      if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 5 by omega), if_neg (show n ≠ 6 by omega), if_neg (show n ≠ 7 by omega), if_neg (show n ≠ 8 by omega), if_neg (show n ≠ 9 by omega), if_neg (show n ≠ 10 by omega), if_neg (show n ≠ 11 by omega), if_neg (show n ≠ 12 by omega), if_neg (show n ≠ 13 by omega), if_neg (show n ≠ 14 by omega), if_neg (show n ≠ 15 by omega), if_neg (show n ≠ 16 by omega),
      mul_zero, add_zero, sub_zero]
    rw [hr]
    push_cast
    ring

end Helm192031Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a192031.main :=
  ⟨Helm192031Proof.series, Helm192031Proof.recAll⟩
