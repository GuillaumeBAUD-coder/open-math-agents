import OMAStatements.S_oeis_a176605
import Mathlib

-- Problem: A176605, Mathar's P-recursive recurrence.
-- Credit: @mhismail3 (the owner of the agent is credited as the solver)
-- The g.f. A satisfies X(1-X)A^2 + (X-1)A + (1-X+X^2) = 0. Differentiating and cancelling the unit
-- 2X(1-X)A + (X-1) gives a first order linear ODE whose coefficients are the recurrence.

namespace OMA.A176605Proof

open PowerSeries OMA.S_oeis_a176605

lemma aList_succ (m : ℕ) : ∃ x : ℤ, aList (m + 1) = aList m ++ [x] := by
  cases m with
  | zero => exact ⟨1, rfl⟩
  | succ n => exact ⟨_, rfl⟩

lemma length_aList (m : ℕ) : (aList m).length = m + 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    obtain ⟨x, hx⟩ := aList_succ m
    rw [hx]
    simp [ih]

lemma getD_aList (k d : ℕ) : (aList (k + d)).getD k 0 = a k := by
  induction d with
  | zero => rfl
  | succ d ih =>
    obtain ⟨x, hx⟩ := aList_succ (k + d)
    rw [← add_assoc, hx, List.getD_append _ _ _ _ (by rw [length_aList]; omega), ih]

lemma getD_aList' {k m : ℕ} (h : k ≤ m) : (aList m).getD k 0 = a k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact getD_aList k d

lemma a_rec (n : ℕ) :
    a (n + 2) = (∑ p ∈ Finset.range (n + 2), a p * a (n + 1 - p)) + 1 := by
  have h : aList (n + 2) = aList (n + 1) ++
      [(∑ p ∈ Finset.range (n + 2),
        (aList (n + 1)).getD p 0 * (aList (n + 1)).getD (n + 1 - p) 0) + 1] := rfl
  rw [a, h, List.getD_append_right _ _ _ _ (by simp [length_aList])]
  simp only [length_aList, Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_range] at hp
  rw [getD_aList' (by omega), getD_aList' (by omega)]

noncomputable def A : ℤ⟦X⟧ := mk a

lemma coeff_sq (n : ℕ) :
    coeff (n + 1) (A ^ 2) = ∑ p ∈ Finset.range (n + 2), a p * a (n + 1 - p) := by
  rw [sq, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff i A * coeff j A)]
  simp [A]

lemma key : (1 - X) * (A - 1 - X * A ^ 2) = (X ^ 2 : ℤ⟦X⟧) := by
  have ha0 : a 0 = 1 := rfl
  have hS : A - 1 - X * A ^ 2 = X ^ 2 * mk 1 := by
    ext n
    rcases n with _ | _ | n
    · simp [A, ha0, coeff_X_pow_mul']
    · have ha1 : a 1 = 1 := rfl
      rw [map_sub, map_sub, coeff_succ_X_mul, coeff_X_pow_mul']
      simp [A, sq, coeff_mul, ha0, ha1]
    · rw [map_sub, map_sub, coeff_succ_X_mul, coeff_sq, coeff_X_pow_mul']
      simp [A, a_rec]
  rw [hS, mul_comm, mul_assoc, mk_one_mul_one_sub_eq_one, mul_one]

lemma quad : X * (1 - X) * A ^ 2 + (X - 1) * A + (1 - X + X ^ 2) = (0 : ℤ⟦X⟧) := by
  linear_combination (-1 : ℤ⟦X⟧) * key

lemma dquad : ((1 - 2 * X) * A ^ 2 + A + (2 * X - 1)) +
    (2 * X * (1 - X) * A + (X - 1)) * d⁄dX ℤ A = 0 := by
  have h := congrArg (d⁄dX ℤ) quad
  simp only [map_add, map_sub, map_zero, Derivation.leibniz, Derivation.leibniz_pow,
    derivative_X, Derivation.map_one_eq_zero, smul_eq_mul] at h
  linear_combination h

lemma ode : X * d⁄dX ℤ A - 6 * X ^ 2 * d⁄dX ℤ A + 9 * X ^ 3 * d⁄dX ℤ A
    - 8 * X ^ 4 * d⁄dX ℤ A + 4 * X ^ 5 * d⁄dX ℤ A + A - 4 * X * A + 5 * X ^ 2 * A
    + (-1 + 2 * X - 4 * X ^ 2 + 2 * X ^ 3) = 0 := by
  have hne : (2 * X * (1 - X) * A + (X - 1) : ℤ⟦X⟧) ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h0
    simp at this
  refine (mul_eq_zero.mp ?_).resolve_left hne
  linear_combination (X * ((1 - X) * (1 - 5 * X + 4 * X ^ 2 - 4 * X ^ 3))) * dquad
    + (1 - X - 4 * X ^ 2 + 12 * X ^ 3 - 8 * X ^ 4) * quad

lemma ode' : X * d⁄dX ℤ A - C 6 * (X ^ 2 * d⁄dX ℤ A) + C 9 * (X ^ 3 * d⁄dX ℤ A)
    - C 8 * (X ^ 4 * d⁄dX ℤ A) + C 4 * (X ^ 5 * d⁄dX ℤ A) + A - C 4 * (X * A)
    + C 5 * (X ^ 2 * A) + (-1 + C 2 * X - C 4 * X ^ 2 + C 2 * X ^ 3) = 0 := by
  simp only [map_ofNat]
  linear_combination ode

end OMA.A176605Proof

open OMA.A176605Proof OMA.S_oeis_a176605 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a176605.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have h := congrArg (coeff (m + 4)) ode'
  simp only [map_add, map_sub, map_neg, map_zero, coeff_C_mul, coeff_X_pow_mul',
    coeff_succ_X_mul, coeff_derivative, coeff_one, coeff_X_pow, coeff_X, A, coeff_mk] at h
  rcases m with _ | m
  · norm_num at h ⊢
    linear_combination h
  · have e : m + 1 + 4 - 5 = m := by omega
    simp only [e, show 5 ≤ m + 1 + 4 by omega, if_true, show m + 1 + 4 ≠ 0 by omega,
      show m + 1 + 4 ≠ 1 by omega, show m + 1 + 4 ≠ 2 by omega, show m + 1 + 4 ≠ 3 by omega,
      if_false, show m + 1 + 4 - 1 = m + 1 + 3 by omega, show m + 1 + 4 - 2 = m + 1 + 2 by omega,
      show m + 1 + 4 - 3 = m + 1 + 1 by omega, show m + 1 + 4 - 4 = m + 1 by omega] at h ⊢
    push_cast at h ⊢
    linear_combination h
