import OMAStatements.S_oeis_a238879

-- Problem: A238879: Row sums of the triangle of generalized ballot numbers A238762.
-- Upstream: formal-conjectures statements/oeis-a238879.lean:0 (declaration OMA.S_oeis_a238879.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Disproof idea: the first part fails at n = 1. Row 2 of A238762 is T(0,2), T(1,2), T(2,2) = 1, 0, 1,
-- so a(2) = 2, while A000108(1) = catalan 1 = 1. The values of T are computed from the recurrence.

namespace N18A238879

open OMA.S_oeis_a238879

theorem T_eq (p q : ℕ) : T p q = if p = 0 ∧ q = 0 then 1
    else if q < p then 0
    else (if _h : 2 ≤ p then T (p - 2) q else 0) +
      q % 2 * (if _h : 1 ≤ p then T (p - 1) (q - 1) else 0) +
      (if _h : 2 ≤ q then T p (q - 2) else 0) := by
  rw [T]

theorem T_zero : T 0 0 = 1 := by
  rw [T_eq 0 0, if_pos (show (0 : ℕ) = 0 ∧ (0 : ℕ) = 0 from ⟨rfl, rfl⟩)]

theorem T_gt (p q : ℕ) (h : q < p) : T p q = 0 := by
  rw [T_eq p q, if_neg (show ¬(p = 0 ∧ q = 0) by omega), if_pos h]

theorem T_rec (p q : ℕ) (h0 : ¬(p = 0 ∧ q = 0)) (h : p ≤ q) : T p q =
    (if _h : 2 ≤ p then T (p - 2) q else 0) +
      q % 2 * (if _h : 1 ≤ p then T (p - 1) (q - 1) else 0) +
      (if _h : 2 ≤ q then T p (q - 2) else 0) := by
  rw [T_eq p q, if_neg h0, if_neg (show ¬(q < p) by omega)]

theorem T02 : T 0 2 = 1 := by
  have h := T_rec 0 2 (by omega) (by omega)
  rw [dif_neg (show ¬(2 ≤ 0) by omega), dif_neg (show ¬(1 ≤ 0) by omega),
    dif_pos (show 2 ≤ 2 by omega), show (2 : ℕ) - 2 = 0 by omega, T_zero] at h
  omega

theorem T12 : T 1 2 = 0 := by
  have h := T_rec 1 2 (by omega) (by omega)
  rw [dif_neg (show ¬(2 ≤ 1) by omega), dif_pos (show 1 ≤ 1 by omega),
    dif_pos (show 2 ≤ 2 by omega), show (2 : ℕ) - 2 = 0 by omega,
    T_gt 1 0 (by omega), show (2 : ℕ) % 2 = 0 by omega] at h
  omega

theorem T22 : T 2 2 = 1 := by
  have h := T_rec 2 2 (by omega) (by omega)
  rw [dif_pos (show 2 ≤ 2 by omega), dif_pos (show 2 ≤ 2 by omega),
    dif_pos (show 1 ≤ 2 by omega), show (2 : ℕ) - 2 = 0 by omega, T02,
    T_gt 2 0 (by omega), show (2 : ℕ) % 2 = 0 by omega] at h
  omega

theorem a_two : a 2 = 2 := by
  have e : a 2 = T 0 2 + T 1 2 + T 2 2 := by
    rw [a, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  have h0 := T02
  have h1 := T12
  have h2 := T22
  omega

end N18A238879

open OMA.S_oeis_a238879 N18A238879 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a238879.main) := by
  intro h
  have h1 : a 2 = catalan 1 := h.1 1
  rw [a_two, catalan_one] at h1
  omega
