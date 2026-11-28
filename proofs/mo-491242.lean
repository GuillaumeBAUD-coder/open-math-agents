import OMAStatements.S_mo_491242
import Mathlib

open OMA.S_mo_491242
open PowerSeries
open scoped BigOperators

namespace ProductRecurrence

noncomputable def product (i : ℕ) : PowerSeries ℤ :=
  ∏ j ∈ Finset.range i, factor j

noncomputable def term (i k : ℕ) : PowerSeries ℤ :=
  product i * (geometric + (i : PowerSeries ℤ)) ^ (k + 1)

noncomputable def truncated (n k : ℕ) : PowerSeries ℤ :=
  ∑ i ∈ Finset.range (n + 1), term i k

lemma geometric_mul_sub : geometric * (1 - X) = (1 : PowerSeries ℤ) := by
  unfold geometric
  have h := (PowerSeries.invOneSubPow ℤ 1).val_inv
  rwa [PowerSeries.invOneSubPow_inv_eq_one_sub_pow, pow_one] at h

lemma factor_eq (i : ℕ) : factor i = X * (geometric + (i : PowerSeries ℤ)) := by
  have h : X * geometric = geometric - 1 := by
    have hg : geometric - geometric * X = 1 := by simpa only [mul_sub, mul_one] using geometric_mul_sub
    linear_combination -hg
  have hz : (X : PowerSeries ℤ) ^ 2 * geometric = X * (geometric - 1) := by
    rw [← h]
    ring
  unfold factor
  rw [hz, map_natCast]
  push_cast
  ring

lemma product_succ (i : ℕ) : product (i + 1) = product i * factor i :=
  Finset.prod_range_succ _ _

lemma term_step (i k : ℕ) :
    term (i + 1) k = X * ∑ j ∈ Finset.range (k + 2),
      ((k + 1).choose j : PowerSeries ℤ) * term i j := by
  let y := geometric + (i : PowerSeries ℤ)
  have hbin : (y + 1) ^ (k + 1) =
      ∑ j ∈ Finset.range (k + 2), ((k + 1).choose j : PowerSeries ℤ) * y ^ j := by
    simpa [mul_comm] using (add_pow y (1 : PowerSeries ℤ) (k + 1))
  have hy : geometric + ((i + 1 : ℕ) : PowerSeries ℤ) = y + 1 := by
    simp [y, add_assoc]
  unfold term
  rw [product_succ, factor_eq, hy, hbin]
  change product i * (X * y) * _ = _
  rw [mul_assoc]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change product i * ((X * y) * (((k + 1).choose j : PowerSeries ℤ) * y ^ j)) =
    X * (((k + 1).choose j : PowerSeries ℤ) * (product i * y ^ (j + 1)))
  ring

lemma term_zero (k : ℕ) : term 0 k = geometric ^ (k + 1) := by
  simp [term, product]

lemma partial_succ (n k : ℕ) :
    truncated (n + 1) k = geometric ^ (k + 1) +
      X * ∑ j ∈ Finset.range (k + 2), ((k + 1).choose j : PowerSeries ℤ) * truncated n j := by
  simp only [truncated]
  rw [Finset.sum_range_succ', term_zero, add_comm]
  simp only [term_step, ← Finset.mul_sum]
  congr 2
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

lemma coeff_geometric_pow (n k : ℕ) :
    coeff n (geometric ^ (k + 1)) = ((n + k).choose k : ℤ) := by
  have hp : ∀ d : ℕ, invOneSubPow ℤ 1 ^ d = invOneSubPow ℤ d := by
    intro d
    induction d with
    | zero => simp [invOneSubPow_zero]
    | succ d ih => rw [pow_succ, ih, invOneSubPow_add]
  have hp' := congrArg (fun u : (PowerSeries ℤ)ˣ => u.val) (hp (k + 1))
  rw [Units.val_pow_eq_pow_val, ← geometric] at hp'
  rw [hp', invOneSubPow_val_succ_eq_mk_add_choose, coeff_mk, Nat.add_comm k n]

lemma coeff_X_mul (n : ℕ) (p : PowerSeries ℤ) : coeff (n + 1) (X * p) = coeff n p := by
  simpa only [pow_one, mul_comm X p] using coeff_mul_X_pow p 1 n

lemma coeff_partial (n : ℕ) : ∀ k, coeff n (truncated n k) = (R n k : ℤ) := by
  induction n with
  | zero =>
    intro k
    simp [truncated, term_zero, coeff_geometric_pow, R]
  | succ n ih =>
    intro k
    rw [partial_succ, map_add, coeff_geometric_pow, coeff_X_mul, R]
    push_cast
    congr 1
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hs : ((k + 1).choose j : PowerSeries ℤ) = C ((k + 1).choose j : ℤ) := by simp
    rw [hs, coeff_C_mul, ih]

lemma X_mul_term (i : ℕ) : X * term i 0 = product (i + 1) := by
  rw [product_succ, factor_eq]
  simp [term, mul_left_comm]

lemma finish (n : ℕ) : (R n 0 : ℤ) = a (n + 1) := by
  rw [← coeff_partial, ← coeff_X_mul]
  unfold truncated a
  rw [Finset.mul_sum]
  simp only [X_mul_term]
  conv_rhs => rw [Finset.sum_range_succ']
  change coeff (n + 1) (∑ i ∈ Finset.range (n + 1), product (i + 1)) =
    coeff (n + 1) ((∑ i ∈ Finset.range (n + 1), product (i + 1)) + product 0)
  simp [product]

end ProductRecurrence

theorem OMA.solution : ∀ n : ℕ, (R n 0 : ℤ) = a (n + 1) :=
  ProductRecurrence.finish