import OMAStatements.S_oeis_a133307
import Mathlib

/-!
Proof of Mathar's recurrence for A133307, a(n) = (1/n) Sum_i C(n,i) C(n,i+1) 6^i 7^(n-i).

Let N(n,i) = C(n,i) C(n,i+1) / n be the Narayana numbers and p_n = Sum_i N(n,i) X^i. The identity
(n+3) N(n+2,j) = (2n+3) (N(n+1,j) + N(n+1,j-1)) - n (N(n,j) - 2 N(n,j-1) + N(n,j-2))
(a rational identity once all binomials are written through C(n,j-2) with
(k+1) C(n,k+1) = (n-k) C(n,k)) gives (n+3) p_(n+2) = (2n+3)(1+X) p_(n+1) - n (1-X)^2 p_n.
Since a(n) = y^n p_n(x/y), evaluating at x/y = 6/7 gives the stated recurrence.
-/

namespace OMA.NAR


open Polynomial Finset

/-- Narayana numbers as rationals: C(n,i) C(n,i+1) / n. -/
def N (n i : ℕ) : ℚ := (n.choose i : ℚ) * (n.choose (i + 1) : ℚ) / n

lemma choose_rel (n k : ℕ) :
    ((k : ℚ) + 1) * (n.choose (k + 1) : ℚ) = ((n : ℚ) - k) * (n.choose k : ℚ) := by
  rcases le_or_gt k n with h | h
  · have h1 := Nat.choose_succ_right_eq n k
    have h2 : ((n.choose (k + 1) * (k + 1) : ℕ) : ℚ) = ((n.choose k * (n - k) : ℕ) : ℚ) := by
      rw [h1]
    push_cast [Nat.cast_sub h] at h2
    linear_combination h2
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega : n < k + 1)]
    simp

lemma pascal (n j : ℕ) :
    ((n + 1).choose (j + 1) : ℚ) = (n.choose j : ℚ) + (n.choose (j + 1) : ℚ) := by
  rw [Nat.choose_succ_succ']
  push_cast
  ring

lemma alg (m k a0 a1 a2 a3 : ℚ) (hm : m ≠ 0) (hm1 : m + 1 ≠ 0) (hm2 : m + 2 ≠ 0)
    (hk1 : k + 1 ≠ 0) (hk2 : k + 2 ≠ 0) (hk3 : k + 3 ≠ 0)
    (r1 : (k + 1) * a1 = (m - k) * a0) (r2 : (k + 2) * a2 = (m - k - 1) * a1)
    (r3 : (k + 3) * a3 = (m - k - 2) * a2) :
    (m + 3) * ((a0 + a1 + (a1 + a2)) * (a1 + a2 + (a2 + a3)) / (m + 2))
      = (2 * m + 3) * ((a1 + a2) * (a2 + a3) / (m + 1) + (a0 + a1) * (a1 + a2) / (m + 1))
        - m * (a2 * a3 / m - 2 * (a1 * a2 / m) + a0 * a1 / m) := by
  have e1 : a1 = (m - k) / (k + 1) * a0 := by
    field_simp
    linear_combination r1
  have e2 : a2 = (m - k - 1) / (k + 2) * a1 := by
    field_simp
    linear_combination r2
  have e3 : a3 = (m - k - 2) / (k + 3) * a2 := by
    field_simp
    linear_combination r3
  rw [e3, e2, e1]
  field_simp
  ring

lemma N_gen (m k : ℕ) (hm : m ≠ 0) :
    ((m : ℚ) + 3) * N (m + 2) (k + 2)
      = (2 * (m : ℚ) + 3) * (N (m + 1) (k + 2) + N (m + 1) (k + 1))
        - (m : ℚ) * (N m (k + 2) - 2 * N m (k + 1) + N m k) := by
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have hm1 : (m : ℚ) + 1 ≠ 0 := by positivity
  have hm2 : (m : ℚ) + 2 ≠ 0 := by positivity
  have hk1 : (k : ℚ) + 1 ≠ 0 := by positivity
  have hk2 : (k : ℚ) + 2 ≠ 0 := by positivity
  have hk3 : (k : ℚ) + 3 ≠ 0 := by positivity
  have r1 := choose_rel m k
  have r2 : ((k : ℚ) + 2) * (m.choose (k + 2) : ℚ) = ((m : ℚ) - k - 1) * (m.choose (k + 1) : ℚ) := by
    have h := choose_rel m (k + 1)
    push_cast at h
    linear_combination h
  have r3 : ((k : ℚ) + 3) * (m.choose (k + 3) : ℚ) = ((m : ℚ) - k - 2) * (m.choose (k + 2) : ℚ) := by
    have h := choose_rel m (k + 2)
    push_cast at h
    linear_combination h
  have h22 : (((m + 2).choose (k + 2) : ℕ) : ℚ)
      = ((m + 1).choose (k + 1) : ℚ) + ((m + 1).choose (k + 2) : ℚ) := pascal (m + 1) (k + 1)
  have h23 : (((m + 2).choose (k + 3) : ℕ) : ℚ)
      = ((m + 1).choose (k + 2) : ℚ) + ((m + 1).choose (k + 3) : ℚ) := pascal (m + 1) (k + 2)
  have h11 : (((m + 1).choose (k + 1) : ℕ) : ℚ)
      = (m.choose k : ℚ) + (m.choose (k + 1) : ℚ) := pascal m k
  have h12 : (((m + 1).choose (k + 2) : ℕ) : ℚ)
      = (m.choose (k + 1) : ℚ) + (m.choose (k + 2) : ℚ) := pascal m (k + 1)
  have h13 : (((m + 1).choose (k + 3) : ℕ) : ℚ)
      = (m.choose (k + 2) : ℚ) + (m.choose (k + 3) : ℚ) := pascal m (k + 2)
  have key := alg (m : ℚ) (k : ℚ) (m.choose k) (m.choose (k + 1)) (m.choose (k + 2))
    (m.choose (k + 3)) hm' hm1 hm2 hk1 hk2 hk3 r1 r2 r3
  have u2 : N (m + 2) (k + 2)
      = (((m + 2).choose (k + 2) : ℕ) : ℚ) * (((m + 2).choose (k + 3) : ℕ) : ℚ) / ((m : ℚ) + 2) := by
    unfold N
    push_cast
    rfl
  have u12 : N (m + 1) (k + 2)
      = (((m + 1).choose (k + 2) : ℕ) : ℚ) * (((m + 1).choose (k + 3) : ℕ) : ℚ) / ((m : ℚ) + 1) := by
    unfold N
    push_cast
    rfl
  have u11 : N (m + 1) (k + 1)
      = (((m + 1).choose (k + 1) : ℕ) : ℚ) * (((m + 1).choose (k + 2) : ℕ) : ℚ) / ((m : ℚ) + 1) := by
    unfold N
    push_cast
    rfl
  have u02 : N m (k + 2) = (m.choose (k + 2) : ℚ) * (m.choose (k + 3) : ℚ) / (m : ℚ) := rfl
  have u01 : N m (k + 1) = (m.choose (k + 1) : ℚ) * (m.choose (k + 2) : ℚ) / (m : ℚ) := rfl
  have u00 : N m k = (m.choose k : ℚ) * (m.choose (k + 1) : ℚ) / (m : ℚ) := rfl
  rw [u2, u12, u11, u02, u01, u00, h22, h23, h11, h12, h13]
  linear_combination key

lemma N_zero (n : ℕ) (hn : n ≠ 0) : N n 0 = 1 := by
  unfold N
  simp
  exact hn

lemma N_one (n : ℕ) (hn : n ≠ 0) : N n 1 = ((n : ℚ) - 1) * n / 2 := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have h := choose_rel n 1
  have e : (n.choose 2 : ℚ) = ((n : ℚ) - 1) * n / 2 := by
    simp only [Nat.choose_one_right] at h
    push_cast at h
    linear_combination (1 / 2 : ℚ) * h
  unfold N
  rw [show (1 : ℕ) + 1 = 2 from rfl, e, Nat.choose_one_right]
  field_simp

/-- The Narayana polynomial of index n. -/
noncomputable def p (n : ℕ) : ℚ[X] := ∑ i ∈ range n, C (N n i) * X ^ i

lemma coeff_p (n j : ℕ) : (p n).coeff j = N n j := by
  unfold p
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · have hj : n ≤ j := by simpa using h
    unfold N
    rw [Nat.choose_eq_zero_of_lt (by omega : n < j + 1)]
    simp

lemma p_rec (m : ℕ) (hm : m ≠ 0) :
    C ((m : ℚ) + 3) * p (m + 2)
      = C (2 * (m : ℚ) + 3) * (p (m + 1) + X * p (m + 1))
        - C (m : ℚ) * (p m - C 2 * (X * p m) + X * (X * p m)) := by
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  ext j
  simp only [coeff_sub, coeff_add, coeff_C_mul]
  rcases j with _ | _ | k
  · simp only [coeff_X_mul_zero, coeff_p]
    rw [N_zero (m + 2) (by omega), N_zero (m + 1) (by omega), N_zero m hm]
    ring
  · simp only [zero_add, coeff_X_mul, coeff_X_mul_zero, coeff_p]
    rw [N_one (m + 2) (by omega), N_one (m + 1) (by omega), N_one m hm,
      N_zero (m + 1) (by omega), N_zero m hm]
    push_cast
    ring
  · simp only [coeff_X_mul, coeff_p]
    have h := N_gen m k hm
    linear_combination h

/-- The sequences of the statements, with general parameters. -/
def A (x y : ℚ) (n : ℕ) : ℚ :=
  if n = 0 then 1
  else (∑ i ∈ Finset.range n, (n.choose i : ℚ) * (n.choose (i + 1) : ℚ) * x ^ i * y ^ (n - i)) / n

lemma A_eq (t y : ℚ) (n : ℕ) (hn : n ≠ 0) :
    A (t * y) y n = y ^ n * (p n).eval t := by
  unfold A p
  rw [if_neg hn, eval_finsetSum, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := (mem_range.mp hi).le
  rw [eval_mul, eval_C, eval_pow, eval_X]
  have e : y ^ n = y ^ (n - i) * y ^ i := (pow_sub_mul_pow y hi').symm
  rw [e]
  unfold N
  ring

lemma A_rec (x y : ℚ) (hy : y ≠ 0) (m : ℕ) (hm : m ≠ 0) :
    ((m : ℚ) + 3) * A x y (m + 2) - (2 * (m : ℚ) + 3) * (x + y) * A x y (m + 1)
      + (m : ℚ) * (x - y) ^ 2 * A x y m = 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, x = t * y := ⟨x / y, by field_simp⟩
  rw [A_eq t y (m + 2) (by omega), A_eq t y (m + 1) (by omega), A_eq t y m hm]
  have h := congrArg (Polynomial.eval t) (p_rec m hm)
  simp only [eval_mul, eval_sub, eval_add, eval_C, eval_X] at h
  linear_combination y ^ (m + 2) * h

lemma A_two (x y : ℚ) :
    3 * A x y 2 - 3 * (x + y) * A x y 1 = 0 := by
  unfold A
  simp [Finset.sum_range_succ]
  ring

end OMA.NAR

theorem OMA.solution : type_of% @OMA.S_oeis_a133307.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have ha : ∀ k, OMA.S_oeis_a133307.a k = OMA.NAR.A 6 7 k := fun k => rfl
  have e1 : m + 2 - 1 = m + 1 := by omega
  simp only [Nat.add_sub_cancel, e1, ha]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h := OMA.NAR.A_two 6 7
    norm_num at h ⊢
    linear_combination h
  · have h := OMA.NAR.A_rec 6 7 (by norm_num) m (by omega)
    push_cast
    linear_combination h
