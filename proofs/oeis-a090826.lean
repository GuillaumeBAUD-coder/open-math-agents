import OMAStatements.S_oeis_a090826
import Mathlib

-- Problem: A090826, Mathar's conjectured recurrence for a(n) = Sum_{k=0..n} F(k) C(n-k).
-- Upstream: formal-conjectures statements/oeis-a090826.lean (declaration OMA.S_oeis_a090826.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds).
-- Proof idea: the g.f. is F = Fib * Cat with (1 - x - x^2) Fib = x and x Cat^2 - Cat + 1 = 0, so
-- T = 1 - 2x Cat satisfies T^2 = 1 - 4x and T(0) = 1, hence T = S = sqrt(1 - 4x) and
-- 2 (1 - x - x^2) F = 1 - S (rel1). With 2 R S' = R' S (rel2), the recurrence is an explicit
-- polynomial combination of shifted instances of rel1 and rel2.

namespace OMA.P_oeis_a090826

open OMA.S_oeis_a090826 PowerSeries

noncomputable def R : PowerSeries ℚ := 1 - 4 * X

noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

theorem hR1 : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])

theorem S_sq : S ^ 2 = R := by
  have h : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = 1 + X := by
    rw [sq, ← PowerSeries.binomialSeries_add]
    have h12 : (1 / 2 + 1 / 2 : ℚ) = ((1 : ℕ) : ℚ) := by norm_num
    rw [h12, PowerSeries.binomialSeries_nat, pow_one]
  unfold S
  rw [← coe_substAlgHom hR1, ← map_pow, h, map_add, map_one, substAlgHom_X]
  ring

theorem ode : 2 * R * d⁄dX ℚ S = d⁄dX ℚ R * S := by
  have h := congrArg (d⁄dX ℚ) S_sq
  rw [pow_two, Derivation.leibniz, smul_eq_mul] at h
  rw [← h, ← S_sq]
  ring

theorem hRC : R = C (1 : ℚ) + C (-4 : ℚ) * X ^ 1 := by
  simp only [R, map_one, map_neg, map_ofNat]
  ring

theorem hDR : d⁄dX ℚ R = C (-4 : ℚ) := by
  rw [hRC]
  simp only [map_add, Derivation.leibniz, derivative_C, derivative_pow, derivative_X, smul_eq_mul,
    mul_zero, add_zero, Nat.reduceSub, pow_one, mul_one]
  simp only [map_one, map_neg, map_ofNat]
  push_cast
  ring

theorem E2 : C (2 : ℚ) * d⁄dX ℚ S + C (-8 : ℚ) * X ^ 1 * d⁄dX ℚ S - (C (-4 : ℚ) * S) = 0 := by
  have h := ode
  rw [hDR, hRC] at h
  simp only [map_one, map_neg, map_ofNat] at h ⊢
  linear_combination h

theorem cx (c : ℚ) (j n : ℕ) (f : ℚ⟦X⟧) (h : j ≤ n) :
    coeff n (C c * X ^ j * f) = c * coeff (n - j) f := by
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_pos h]

theorem cx0 (c : ℚ) (n : ℕ) (f : ℚ⟦X⟧) : coeff n (C c * f) = c * coeff n f := coeff_C_mul _ _ _

theorem cc (c : ℚ) (j n : ℕ) (h : n ≠ j) : coeff n (C c * X ^ j) = 0 := by
  rw [coeff_C_mul_X_pow, if_neg h]

theorem cc0 (c : ℚ) (n : ℕ) (h : n ≠ 0) : coeff n (C c : ℚ⟦X⟧) = 0 := by
  rw [coeff_C, if_neg h]

theorem rel2 (m : ℕ) : (2 : ℚ) * (coeff (m + 2) S * ((m : ℚ) + 2)) + (-8 : ℚ) * (coeff (m + 1) S * ((m : ℚ) + 1)) - ((-4 : ℚ) * coeff (m + 1) S) = 0 := by
  have h := congrArg (coeff (m + 1)) E2
  simp (disch := omega) only [map_add, map_sub, map_zero, cx, cx0, coeff_derivative] at h
  rw [show m + 1 - 1 = m from by omega] at h
  try simp only [Nat.add_assoc, Nat.reduceAdd] at h
  try push_cast at h
  linear_combination h

noncomputable def F : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ))

noncomputable def Cat : ℚ⟦X⟧ := PowerSeries.mk (fun n => (catalan n : ℚ))

noncomputable def Fib : ℚ⟦X⟧ := PowerSeries.mk (fun n => (Nat.fib n : ℚ))

theorem a_eq (n : ℕ) : (a n : ℚ) = coeff n F := by simp [F]

theorem S_const : constantCoeff S = 1 := by
  have h0 : constantCoeff (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) - 1) = 0 := by simp
  have hc : constantCoeff (R - 1) = 0 := by simp [R]
  have h1 := constantCoeff_subst_eq_zero (a := (R - 1 : ℚ⟦X⟧)) hc _ h0
  have h2 : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) - 1).subst (R - 1) = S - 1 := by
    unfold S
    rw [← coe_substAlgHom hR1, map_sub, map_one]
  rw [h2] at h1
  have h3 : constantCoeff (S - 1) = 0 := h1
  rw [map_sub, map_one, sub_eq_zero] at h3
  exact h3

theorem hCat : X * Cat ^ 2 - Cat + 1 = 0 := by
  ext n
  rw [map_zero]
  rcases n with _ | n
  · simp [Cat]
  · have e1 : coeff (n + 1) (X * Cat ^ 2) = coeff n (Cat ^ 2) := coeff_succ_X_mul _ _
    have e2 : coeff n (Cat ^ 2) = (catalan (n + 1) : ℚ) := by
      rw [pow_two, coeff_mul, catalan_succ']
      push_cast
      simp [Cat]
    have e3 : coeff (n + 1) Cat = (catalan (n + 1) : ℚ) := by simp [Cat]
    have e4 : coeff (n + 1) (1 : ℚ⟦X⟧) = 0 := by simp [coeff_one]
    rw [map_add, map_sub, e1, e2, e3, e4]
    ring

theorem hFib : (1 - X - X ^ 2) * Fib = X := by
  ext n
  rcases n with _ | _ | n
  · simp [Fib]
  · simp [Fib, sub_mul, coeff_X_pow_mul', coeff_one, coeff_X]
  · have e1 : coeff (n + 2) (X * Fib) = (Nat.fib (n + 1) : ℚ) := by
      rw [show n + 2 = (n + 1) + 1 from rfl, coeff_succ_X_mul]; simp [Fib]
    have e2 : coeff (n + 2) (X ^ 2 * Fib) = (Nat.fib n : ℚ) := by simp [Fib, coeff_X_pow_mul']
    have e3 : coeff (n + 2) Fib = (Nat.fib (n + 2) : ℚ) := by simp [Fib]
    have e4 : coeff (n + 2) (1 * Fib) = (Nat.fib (n + 2) : ℚ) := by rw [one_mul]; exact e3
    have e5 : coeff (n + 2) (X : ℚ⟦X⟧) = 0 := by simp [coeff_X]
    rw [sub_mul, sub_mul, map_sub, map_sub, e4, e1, e2, e5, Nat.fib_add_two]
    push_cast
    ring

theorem hA : F = Fib * Cat := by
  ext n
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [F, Fib, Cat, a]

theorem T_eq : 1 - 2 * X * Cat = S := by
  have hT : (1 - 2 * X * Cat) ^ 2 = R := by
    unfold R
    linear_combination (4 * X) * hCat
  have h : (1 - 2 * X * Cat - S) * (1 - 2 * X * Cat + S) = 0 := by
    linear_combination hT - S_sq
  rcases mul_eq_zero.mp h with h1 | h1
  · exact sub_eq_zero.mp h1
  · exfalso
    have h2 := congrArg constantCoeff h1
    norm_num [S_const] at h2

theorem E1 : C (2 : ℚ) * F + C (-2 : ℚ) * X ^ 1 * F + C (-2 : ℚ) * X ^ 2 * F - (C (-1 : ℚ) * S) - (C (1 : ℚ)) = 0 := by
  simp only [map_one, map_neg, map_ofNat]
  linear_combination (2 * Cat) * hFib + (2 * (1 - X - X ^ 2)) * hA - T_eq

theorem rel1 (m : ℕ) : (2 : ℚ) * coeff (m + 2) F + (-2 : ℚ) * coeff (m + 1) F + (-2 : ℚ) * coeff (m) F - ((-1 : ℚ) * coeff (m + 2) S) = 0 := by
  have h := congrArg (coeff (m + 2)) E1
  simp only [map_add, map_sub, map_zero] at h
  simp (disch := omega) only [cx, cc, cc0] at h
  simp only [cx0, sub_zero, add_zero, zero_add] at h
  rw [show m + 2 - 1 = m + 1 from by omega, show m + 2 - 2 = m from by omega] at h
  linear_combination h

theorem mainQ : ∀ n : ℕ, 3 ≤ n → (n : ℚ) * a n + (-5 * (n : ℚ) + 6) * a (n - 1) + 3 * ((n : ℚ) - 2) * a (n - 2)
      + 2 * (2 * (n : ℚ) - 3) * a (n - 3) = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rw [show k + 3 - 1 = k + 2 from by omega, show k + 3 - 2 = k + 1 from by omega, show k + 3 - 3 = k from by omega]
  simp only [a_eq]
  have r1_49 := rel1 (k)
  have r1_50 := rel1 (k + 1)
  have r2_49 := rel2 (k + 1)
  try simp only [Nat.add_assoc, Nat.reduceAdd] at r1_49 r1_50 r2_49 ⊢
  push_cast at r1_49 r1_50 r2_49 ⊢
  linear_combination ((3 : ℚ) + (-2 : ℚ) * ((k : ℚ) + 3) ^ 1) * r1_49 + ((1 / 2 : ℚ) * ((k : ℚ) + 3) ^ 1) * r1_50 + ((-1 / 4 : ℚ)) * r2_49

theorem main' : ∀ n : ℕ, 3 ≤ n →
    (n : ℤ) * a n + (-5 * (n : ℤ) + 6) * a (n - 1) + 3 * ((n : ℤ) - 2) * a (n - 2)
      + 2 * (2 * (n : ℤ) - 3) * a (n - 3) = 0 := by
  intro n hn
  have h := mainQ n hn
  exact_mod_cast h

end OMA.P_oeis_a090826

theorem OMA.solution : type_of% @OMA.S_oeis_a090826.main := OMA.P_oeis_a090826.main'
