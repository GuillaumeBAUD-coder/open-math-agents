import OMAStatements.S_oeis_a380281

namespace OMA.S_oeis_a380281

open Finset

/-!
## Proof of OEIS A380281

We prove the term-by-term identity
`entry n k = (oddProduct (n + 1) : ℝ) * (n.choose k : ℝ) / (2 * k + 1)`
for all `0 ≤ k ≤ n`. Summing over `k ∈ range (n + 1)` gives
`(oddProduct (n + 1) : ℝ) * ∑ k ∈ range (n + 1), (n.choose k : ℝ) / (2 * k + 1)`,
which equals `(oddProduct (n + 1) : ℝ) * ∫ x in (0 : ℝ)..1, (1 + x ^ 2) ^ n`
by expanding `(1 + x ^ 2) ^ n` via the binomial theorem and integrating term by term.
-/

private lemma oddProduct_succ (j : ℕ) : oddProduct (j + 1) = oddProduct j * (2 * j + 1) := by
  simp [oddProduct, prod_range_succ]

private lemma halfRising_eq (j : ℕ) :
    halfRising j = ((2 * j).factorial : ℝ) / ((4 : ℝ) ^ j * (j.factorial : ℝ)) := by
  induction j with
  | zero => simp [halfRising]
  | succ j ih =>
    rw [halfRising, prod_range_succ, ← halfRising, ih]
    have hfac : (2 * (j + 1)).factorial = (2 * j + 2) * (2 * j + 1) * (2 * j).factorial := by
      rw [show 2 * (j + 1) = 2 * j + 2 by omega, Nat.factorial_succ, Nat.factorial_succ]
      ring
    have h4 : (4 : ℝ) ^ (j + 1) ≠ 0 := by positivity
    have hfj : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    have hfj1 : ((j + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (j + 1))
    rw [hfac, Nat.factorial_succ]
    push_cast
    field_simp [h4, hfj, hfj1]
    ring

private lemma oddProduct_eq (n : ℕ) :
    (oddProduct (n + 1) : ℝ) = ((2 * n + 1).factorial : ℝ) / ((2 : ℝ) ^ n * (n.factorial : ℝ)) := by
  induction n with
  | zero => simp [oddProduct]
  | succ n ih =>
    rw [oddProduct_succ, Nat.cast_mul, ih]
    have hfac : (2 * (n + 1) + 1).factorial = (2 * n + 3) * (2 * n + 2) * (2 * n + 1).factorial := by
      rw [show 2 * (n + 1) + 1 = 2 * n + 3 by omega, Nat.factorial_succ, Nat.factorial_succ]
      ring
    have h2 : (2 : ℝ) ^ (n + 1) ≠ 0 := by positivity
    have hfn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hfn1 : ((n + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n + 1))
    have hfn_succ : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hfac, hfn_succ, pow_succ]
    push_cast
    field_simp [h2, hfn, hfn1]
    ring

private lemma entry_eq (n k : ℕ) (hk : k ≤ n) :
    entry n k = (oddProduct (n + 1) : ℝ) * (n.choose k : ℝ) / (2 * (k : ℝ) + 1) := by
  rw [entry, halfRising_eq (n - k), halfRising_eq k, oddProduct_eq n]
  have hc1 : ((2 * n + 1).choose (2 * k + 1) : ℝ) =
      ((2 * n + 1).factorial : ℝ) /
        (((2 * k + 1).factorial : ℝ) * ((2 * (n - k)).factorial : ℝ)) := by
    have hle : 2 * k + 1 ≤ 2 * n + 1 := by omega
    have hsub : 2 * n + 1 - (2 * k + 1) = 2 * (n - k) := by omega
    have hnat := Nat.choose_mul_factorial_mul_factorial hle
    rw [hsub] at hnat
    have hd1 : ((2 * k + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hd2 : ((2 * (n - k)).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [eq_div_iff (mul_ne_zero hd1 hd2), ← mul_assoc]
    exact_mod_cast hnat
  have hc2 : (n.choose k : ℝ) =
      (n.factorial : ℝ) / ((k.factorial : ℝ) * ((n - k).factorial : ℝ)) := by
    have hnat := Nat.choose_mul_factorial_mul_factorial hk
    have hd1 : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hd2 : ((n - k).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [eq_div_iff (mul_ne_zero hd1 hd2), ← mul_assoc]
    exact_mod_cast hnat
  rw [hc1, hc2]
  have hfac2k1 : ((2 * k + 1).factorial : ℝ) = (2 * (k : ℝ) + 1) * ((2 * k).factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [hfac2k1]
  have hpow4 : (4 : ℝ) ^ (n - k) * (4 : ℝ) ^ k = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hk, show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
  have h4nk : (4 : ℝ) ^ (n - k) ≠ 0 := by positivity
  have h4k : (4 : ℝ) ^ k ≠ 0 := by positivity
  have hf1 : ((2 * k).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf2 : ((2 * (n - k)).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf3 : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf4 : ((n - k).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf5 : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2k1 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
  field_simp [h2n, h4nk, h4k, hf1, hf2, hf3, hf4, hf5, h2k1]
  rw [show (4 : ℝ) ^ (n - k) * (4 : ℝ) ^ k = (2 : ℝ) ^ n * (2 : ℝ) ^ n from hpow4]
  ring

private lemma integral_one_add_sq_pow (n : ℕ) :
    ∫ x : ℝ in (0 : ℝ)..1, (1 + x ^ 2) ^ n =
      ∑ k ∈ range (n + 1), (n.choose k : ℝ) / (2 * (k : ℝ) + 1) := by
  have hexp : ∀ x : ℝ, (1 + x ^ 2) ^ n =
      ∑ k ∈ range (n + 1), (n.choose k : ℝ) * x ^ (2 * k) := by
    intro x
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_pow, mul_one, ← pow_mul, mul_comm]
  simp_rw [hexp]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp [div_eq_mul_inv]
  · intro k _
    exact (continuous_const.mul (continuous_pow (2 * k))).intervalIntegrable 0 1

private lemma main_proof : ∀ n : ℕ, ∑ k ∈ range (n + 1), entry n k =
    (oddProduct (n + 1) : ℝ) * ∫ x : ℝ in 0..1, (1 + x ^ 2) ^ n := by
  intro n
  rw [integral_one_add_sq_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [entry_eq n k (Nat.lt_succ_iff.mp (mem_range.mp hk))]
  ring

end OMA.S_oeis_a380281

theorem OMA.solution : type_of% @OMA.S_oeis_a380281.main :=
  OMA.S_oeis_a380281.main_proof
