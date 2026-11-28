import OMAStatements.S_oeis_a176752
import Mathlib

namespace OMA.MatharQ
open PowerSeries

/-- Hypotheses: `s 0 = 1`, `s 1 = c`, `s (m+2) = ∑_{p ≤ m+1} s p * s (m+1-p) - 2`. -/
structure Hyp (c : ℚ) (s : ℕ → ℚ) : Prop where
  h0 : s 0 = 1
  h1 : s 1 = c
  hrec : ∀ m, s (m + 2) = (∑ p ∈ Finset.range (m + 2), s p * s (m + 1 - p)) - 2

variable {c : ℚ} {s : ℕ → ℚ}

lemma quad (H : Hyp c s) :
    X * (mk s) ^ 2 = mk s - 1 + C (1 - c) * X + 2 * X ^ 2 * mk 1 := by
  have hg : ∀ n, coeff n (2 * X ^ 2 * mk 1 : ℚ⟦X⟧) = if 2 ≤ n then 2 else 0 := by
    intro n
    rw [mul_assoc, show (2 : ℚ⟦X⟧) = C 2 by simp only [map_ofNat], coeff_C_mul,
      coeff_X_pow_mul']
    split_ifs <;> simp
  ext n
  rcases n with _ | _ | m
  · simp [H.h0]
  · show coeff (0 + 1) _ = _
    rw [coeff_succ_X_mul]
    rw [map_add, hg]
    simp [sq, H.h0, H.h1]
  · show coeff ((m + 1) + 1) _ = _
    rw [coeff_succ_X_mul, sq, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i (mk s) * coeff j (mk s))]
    rw [map_add, hg, if_pos (by omega)]
    simp only [coeff_mk, map_add, map_sub, coeff_one]
    rw [show m + 1 + 1 = m + 2 by ring, H.hrec m]
    simp

lemma sq_eq (H : Hyp c s) :
    (1 - X) * (1 - 2 * X * mk s) ^ 2
      = 1 - 5 * X + C (8 - 4 * c) * X ^ 2 + C (4 + 4 * c) * X ^ 3 := by
  have hA := quad H
  have hG := mk_one_mul_one_sub_eq_one ℚ
  simp only [map_sub, map_add, map_mul, map_ofNat, map_one] at hA ⊢
  linear_combination (4 * X * (1 - X)) * hA + 8 * X ^ 3 * hG

lemma ode (H : Hyp c s) :
    4 * X * (X - 1) * (1 - 5 * X + C (8 - 4 * c) * X ^ 2 + C (4 + 4 * c) * X ^ 3) * d⁄dX ℚ (mk s)
      + 4 * (3 * X - 1) * (2 * X ^ 2 - X + 1) * mk s
      + 4 * (1 + C (2 * c - 4) * X + C (-4 * c - 1) * X ^ 2 + C (2 * c + 2) * X ^ 3) = 0 := by
  have hF := sq_eq H
  have hF' := congrArg (d⁄dX ℚ) hF
  have h2 : d⁄dX ℚ (2 : ℚ⟦X⟧) = 0 := by
    rw [show (2 : ℚ⟦X⟧) = C 2 by simp only [map_ofNat], derivative_C]
  have h5 : d⁄dX ℚ (5 : ℚ⟦X⟧) = 0 := by
    rw [show (5 : ℚ⟦X⟧) = C 5 by simp only [map_ofNat], derivative_C]
  simp only [map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow, derivative_one,
    derivative_X, derivative_C, smul_eq_mul, h2, h5, nsmul_eq_mul, Nat.cast_ofNat,
    Nat.add_one_sub_one, pow_one, mul_one, mul_zero, add_zero, zero_sub, sub_zero] at hF'
  set A := mk s
  set A' := d⁄dX ℚ A
  simp only [map_sub, map_add, map_mul, map_ofNat, map_one, map_neg] at hF hF' ⊢
  linear_combination (1 - X) * (1 - 2 * X * A) * hF'
    + (-2 * (1 - X) * (-2 * A - 2 * X * A') + (1 - 2 * X * A)) * hF
lemma X_mul_deriv : X * d⁄dX ℚ (mk s) = mk (fun n => (n : ℚ) * s n) := by
  ext n
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]
    simp [mul_comm]

lemma ode' (H : Hyp c s) :
    (-4 : ℚ) • (X ^ 0 * mk (fun n => (n : ℚ) * s n))
      + (24 : ℚ) • (X ^ 1 * mk (fun n => (n : ℚ) * s n))
      + (16 * c - 52) • (X ^ 2 * mk (fun n => (n : ℚ) * s n))
      + (16 - 32 * c) • (X ^ 3 * mk (fun n => (n : ℚ) * s n))
      + (16 * c + 16) • (X ^ 4 * mk (fun n => (n : ℚ) * s n))
      + (-4 : ℚ) • (X ^ 0 * mk s) + (16 : ℚ) • (X ^ 1 * mk s) + (-20 : ℚ) • (X ^ 2 * mk s)
      + (24 : ℚ) • (X ^ 3 * mk s)
      + ((4 : ℚ) • X ^ 0 + (8 * c - 16) • X ^ 1 + (-16 * c - 4) • X ^ 2
        + (8 * c + 8) • X ^ 3) = 0 := by
  have h := ode H
  rw [← X_mul_deriv]
  simp only [smul_eq_C_mul, map_sub, map_add, map_mul, map_ofNat, map_neg, map_one, pow_zero,
    pow_one] at h ⊢
  linear_combination h

theorem recur (H : Hyp c s) (m : ℕ) :
    ((m : ℚ) + 5) * s (m + 4) + 2 * (1 - 3 * ((m : ℚ) + 4)) * s (m + 3)
      + ((13 - 4 * c) * ((m : ℚ) + 2) + 5) * s (m + 2)
      + ((8 * c - 4) * ((m : ℚ) + 1) - 6) * s (m + 1)
      - 4 * (c + 1) * (m : ℚ) * s m = 0 := by
  have h := congrArg (coeff (m + 4)) (ode' H)
  simp only [map_add, map_zero, coeff_smul, coeff_X_pow_mul', coeff_X_pow, coeff_mk,
    smul_eq_mul] at h
  have e1 : m + 4 - 1 = m + 3 := by omega
  have e2 : m + 4 - 2 = m + 2 := by omega
  have e3 : m + 4 - 3 = m + 1 := by omega
  have e4 : m + 4 - 4 = m := by omega
  simp only [e1, e2, e3, e4, show 0 ≤ m + 4 by omega, show 1 ≤ m + 4 by omega,
    show 2 ≤ m + 4 by omega, show 3 ≤ m + 4 by omega, show 4 ≤ m + 4 by omega, if_true,
    show m + 4 ≠ 0 by omega, show m + 4 ≠ 1 by omega, show m + 4 ≠ 2 by omega,
    show m + 4 ≠ 3 by omega, if_false, Nat.sub_zero] at h
  push_cast at h
  linear_combination (-1 / 4 : ℚ) * h

end OMA.MatharQ

namespace OMA.P_a176752
open OMA.S_oeis_a176752

lemma length_aList : ∀ n, (aList n).length = n + 1
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    simp only [aList, List.length_append, List.length_singleton, length_aList (n + 1)]

lemma getD_aList : ∀ n k, k ≤ n → (aList n).getD k 0 = a k
  | 0, k, hk => by
    obtain rfl : k = 0 := by omega
    rfl
  | 1, k, hk => by
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl <;> rfl
  | n + 2, k, hk => by
    rcases (show k = n + 2 ∨ k ≤ n + 1 by omega) with rfl | hk'
    · rfl
    · rw [← getD_aList (n + 1) k hk']
      simp only [aList]
      exact List.getD_append _ _ _ _ (by rw [length_aList]; omega)

lemma a_rec (m : ℕ) :
    a (m + 2) = (∑ p ∈ Finset.range (m + 2), a p * a (m + 1 - p)) - 2 := by
  show (aList (m + 2)).getD (m + 2) 0 = _
  simp only [aList]
  rw [List.getD_append_right _ _ _ _ (by rw [length_aList])]
  simp only [length_aList, Nat.sub_self, List.getD_cons_zero]
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_range] at hp
  rw [getD_aList _ _ (by omega), getD_aList _ _ (by omega)]

lemma hyp : OMA.MatharQ.Hyp 0 (fun n => (a n : ℚ)) where
  h0 := by simp [a, aList]
  h1 := by simp [a, aList]
  hrec m := by simp only [a_rec m]; push_cast; rfl

end OMA.P_a176752

open OMA.S_oeis_a176752 OMA.P_a176752 in
theorem OMA.solution : type_of% @OMA.S_oeis_a176752.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have h := OMA.MatharQ.recur hyp m
  have e1 : m + 4 - 1 = m + 3 := by omega
  have e2 : m + 4 - 2 = m + 2 := by omega
  have e3 : m + 4 - 3 = m + 1 := by omega
  have e4 : m + 4 - 4 = m := by omega
  rw [e1, e2, e3, e4]
  have : ((((m + 4 : ℕ) : ℤ) + 1) * a (m + 4)
      + 2 * (-3 * ((m + 4 : ℕ) : ℤ) + 1) * a (m + 3)
      + (13 * ((m + 4 : ℕ) : ℤ) - 21) * a (m + 2)
      + 2 * (-2 * ((m + 4 : ℕ) : ℤ) + 3) * a (m + 1)
      + 4 * (-((m + 4 : ℕ) : ℤ) + 4) * a m : ℤ) = ((0 : ℤ) : ℚ) := by
    push_cast
    linear_combination h
  exact_mod_cast this
