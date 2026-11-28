import OMAStatements.S_oeis_a176753
import Mathlib

/-!
# A176753: proof of Mathar's recurrence

Let `A = ∑ a(n) Xⁿ`. The defining convolution gives `X·A² − A + R = 0` with
`(1 − X)·R = 1 − X − 2X²`. Writing `B = 1 − 2XA`, this says `(1 − X)·B² = P` for a polynomial `P`,
so differentiating and eliminating `B²` yields a first-order linear differential equation for `A`
with polynomial coefficients. Comparing coefficients of `Xⁿ` gives the recurrence.
-/

open PowerSeries

namespace OMA.A176753Proof

open OMA.S_oeis_a176753

lemma aList_length (n : ℕ) : (aList n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases n with _ | n
    · rfl
    · simp [aList, ih]

lemma aList_getD (n : ℕ) : ∀ k ≤ n, (aList n).getD k 0 = a k := by
  induction n with
  | zero => intro k hk; interval_cases k; rfl
  | succ n ih =>
    intro k hk
    rcases Nat.lt_or_ge k (n + 1) with h | h
    · rw [← ih k (by omega)]
      rcases n with _ | n
      · interval_cases k; rfl
      · simp only [aList]
        rw [List.getD_append _ _ _ _ (by rw [aList_length]; omega)]
    · have : k = n + 1 := by omega
      subst this; rfl

lemma a_rec (k : ℕ) :
    a (k + 2) = (∑ p ∈ Finset.range (k + 2), a p * a (k + 1 - p)) - 2 := by
  have h : a (k + 2) = (aList (k + 2)).getD (k + 2) 0 := rfl
  rw [h]
  simp only [aList]
  rw [List.getD_append_right _ _ _ _ (by rw [aList_length])]
  simp only [aList_length, Nat.sub_self, List.getD_cons_zero]
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_range] at hp
  rw [aList_getD _ p (by omega), aList_getD _ (k + 1 - p) (by omega)]

/-- The generating function. -/
noncomputable def A : ℤ⟦X⟧ := PowerSeries.mk fun n => a n

/-- Coefficients of the rational correction term. -/
def r : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | _ + 2 => -2

lemma quad : X * (A * A) - A + PowerSeries.mk r = 0 := by
  ext n
  rcases n with _ | m
  · simp [A, r]; rfl
  · rw [map_add, map_sub, coeff_succ_X_mul, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [A, coeff_mk, map_zero]
    rcases m with _ | k
    · simp [r]; rfl
    · rw [a_rec k]; simp [r]

lemma R_eq : (1 - X) * PowerSeries.mk r = 1 - X - X * X - X * X := by
  ext n
  rcases n with _ | _ | _ | n <;>
    simp [sub_mul, coeff_succ_X_mul, coeff_X, coeff_one, r]

lemma hE : (1 - X) * (X * (A * A) - A) + (1 - X - X * X - X * X) = 0 := by
  rw [← R_eq]; linear_combination (1 - X) * quad

lemma d_one : d⁄dX ℤ (1 : ℤ⟦X⟧) = 0 := (d⁄dX ℤ).map_one_eq_zero

lemma ode :
    (X ^ 1 * d⁄dX ℤ A) - 6 * (X ^ 2 * d⁄dX ℤ A) + 9 * (X ^ 3 * d⁄dX ℤ A) + 4 * (X ^ 4 * d⁄dX ℤ A)
      - 8 * (X ^ 5 * d⁄dX ℤ A) + (X ^ 0 * A) - 4 * (X ^ 1 * A) + 5 * (X ^ 2 * A)
      - 6 * (X ^ 3 * A) = 4 * X ^ 3 - 5 * X ^ 2 - 2 * X + 1 := by
  have h := congrArg (d⁄dX ℤ) hE
  simp only [Derivation.leibniz, smul_eq_mul, map_add, map_sub, derivative_X, d_one,
    map_zero] at h
  linear_combination (4 * A * X ^ 2 - 2 * A * X + 4 * (d⁄dX ℤ A) * X ^ 3
    - 4 * (d⁄dX ℤ A) * X ^ 2 - 1) * hE + (-X * (X - 1) * (2 * A * X - 1)) * h

lemma coeff_ofNat_mul' (n c : ℕ) [c.AtLeastTwo] (f : ℤ⟦X⟧) :
    coeff n ((no_index (OfNat.ofNat c : ℤ⟦X⟧)) * f) = (OfNat.ofNat c : ℤ) * coeff n f := by
  rw [← map_ofNat (C (R := ℤ)) c, coeff_C_mul]

end OMA.A176753Proof

open OMA.A176753Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a176753.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have h := congrArg (coeff (m + 4)) ode
  simp only [map_add, map_sub, coeff_ofNat_mul', coeff_X_pow_mul', coeff_derivative,
    coeff_X_pow, coeff_X, coeff_one, A, coeff_mk] at h
  simp only [show 0 ≤ m + 4 by omega, show 1 ≤ m + 4 by omega, show 2 ≤ m + 4 by omega,
    show 3 ≤ m + 4 by omega, show 5 ≤ m + 4 ↔ 1 ≤ m by omega, if_true,
    show m + 4 - 0 = m + 4 by omega, show m + 4 - 1 = m + 3 by omega,
    show m + 4 - 2 = m + 2 by omega, show m + 4 - 3 = m + 1 by omega,
    show m + 4 ≠ 0 by omega, show m + 4 ≠ 1 by omega, show m + 4 ≠ 2 by omega,
    show m + 4 ≠ 3 by omega, if_false] at h
  simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega]
  rcases m with _ | m
  · simp at h
    push_cast at h ⊢
    linear_combination h
  · simp only [show 1 ≤ m + 1 by omega, if_true, show m + 1 + 4 - 5 = m by omega] at h
    push_cast at h ⊢
    linear_combination h
