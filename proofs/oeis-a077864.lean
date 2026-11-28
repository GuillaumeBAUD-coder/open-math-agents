import OMAStatements.S_oeis_a077864
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

-- Original Lean proof: @JeremyDevs.

namespace OMA.P077864

open OMA.S_oeis_a077864 Finset Polynomial

private noncomputable abbrev P : ℤ[X] := 1 + X + X ^ 2

/-- A row-i entry on the diagonal of weight m, extended by zero. -/
private noncomputable def W (m i : ℕ) : ℤ := if 2 * i ≤ m then T i (m - 2 * i) else 0

private noncomputable def D (m : ℕ) : ℤ := ∑ i ∈ range (m / 2 + 1), W m i

private lemma coeff_shift (m i d : ℕ) (hi : 2 * i ≤ m) (hd : d ≤ m) :
    (X ^ d * P ^ i).coeff (m - 2 * i) = W (m - d) i := by
  rw [coeff_X_pow_mul']
  by_cases h : 2 * i ≤ m - d
  · rw [if_pos (by omega), W, if_pos h, T]
    congr 1
    omega
  · rw [if_neg (by omega), W, if_neg h]

private lemma W_step (m i : ℕ) :
    W (m + 4) (i + 1) = W (m + 2) i + W (m + 1) i + W m i := by
  by_cases h : 2 * i ≤ m + 2
  · have hP : P ^ (i + 1) = P ^ i + X ^ 1 * P ^ i + X ^ 2 * P ^ i := by
      rw [pow_succ']
      simp only [P, pow_one, add_mul, one_mul]
    rw [W, if_pos (by omega), T, hP, coeff_add, coeff_add,
      show m + 4 - 2 * (i + 1) = m + 2 - 2 * i by omega,
      coeff_shift (m + 2) i 1 h (by omega), coeff_shift (m + 2) i 2 h (by omega),
      show m + 2 - 1 = m + 1 by omega, Nat.add_sub_cancel]
    rw [show W (m + 2) i = (P ^ i).coeff (m + 2 - 2 * i) from if_pos h]
  · simp (disch := omega) only [W, if_neg, add_zero]

private lemma extend (m N : ℕ) (h : m / 2 + 1 ≤ N) :
    (∑ i ∈ range N, W m i) = D m := by
  symm
  refine sum_subset (range_mono h) (fun i _ hi => ?_)
  simp only [mem_range, not_lt] at hi
  rw [W, if_neg (by omega)]

private lemma D_rec (m : ℕ) : D (m + 4) = D (m + 2) + D (m + 1) + D m := by
  have h : D (m + 4) = (∑ i ∈ range (m / 2 + 2), W (m + 4) (i + 1)) := by
    unfold D
    rw [show (m + 4) / 2 + 1 = m / 2 + 2 + 1 by omega, sum_range_succ']
    have hz : W (m + 4) 0 = 0 := by simp [W, T, coeff_one]
    rw [hz, add_zero]
  rw [h]
  simp (disch := omega) only [W_step, sum_add_distrib, extend]

private noncomputable def odd (n : ℕ) : ℤ := D (2 * n + 3)

private lemma odd_rec (n : ℕ) :
    odd (n + 4) = 2 * odd (n + 3) + odd (n + 2) - odd (n + 1) - odd n := by
  let m := 2 * n + 3
  have h₀ := D_rec m
  have h₁ := D_rec (m + 1)
  have h₂ := D_rec (m + 2)
  have h₄ := D_rec (m + 4)
  simp only [Nat.add_assoc, Nat.reduceAdd] at h₁ h₂ h₄
  unfold odd
  have h (k : ℕ) : 2 * (n + k) + 3 = m + 2 * k := by omega
  simp only [h 1, h 2, h 3, h 4, Nat.reduceMul]
  change D (m + 8) = 2 * D (m + 6) + D (m + 4) - D (m + 2) - D m
  omega

private lemma initial : odd 0 = 1 ∧ odd 1 = 2 ∧ odd 2 = 5 ∧ odd 3 = 11 := by
  have hbase : D 0 = 1 ∧ D 1 = 0 ∧ D 2 = 1 ∧ D 3 = 1 := by
    norm_num [D, W, sum_range_succ, T, coeff_add, coeff_one, coeff_X, coeff_X_pow]
  obtain ⟨h0, h1, h2, h3⟩ := hbase
  have r0 := D_rec 0
  have r1 := D_rec 1
  have r2 := D_rec 2
  have r3 := D_rec 3
  have r4 := D_rec 4
  have r5 := D_rec 5
  norm_num only [Nat.reduceAdd] at r0 r1 r2 r3 r4 r5
  norm_num only [odd, Nat.reduceMul, Nat.reduceAdd]
  omega

private lemma a_odd (n : ℕ) : a n = odd n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < 4
    · obtain ⟨h0, h1, h2, h3⟩ := initial
      interval_cases n <;> simp [a, h0, h1, h2, h3]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      rw [a, odd_rec, ih (k + 3) (by omega), ih (k + 2) (by omega),
        ih (k + 1) (by omega), ih k (by omega)]

private lemma T_zero {i k : ℕ} (h : 2 * i < k) : T i k = 0 := by
  have hp : P.natDegree ≤ 2 := by
    simpa [P] using
      (natDegree_add_le_of_le (natDegree_add_le_of_le (by simp) (by simp)) (by simp) :
        (1 + X + X ^ 2 : ℤ[X]).natDegree ≤ max (max 0 1) 2)
  exact coeff_eq_zero_of_natDegree_lt ((natDegree_pow_le_of_le i hp).trans_lt (by omega))

theorem diagonal : type_of% @OMA.S_oeis_a077864.main := by
  intro n
  rw [a_odd]
  unfold odd D
  rw [show (2 * n + 3) / 2 + 1 = n + 2 by omega]
  calc
    (∑ i ∈ range (n + 2), W (2 * n + 3) i) =
        ∑ j ∈ range (n + 2), T (n + 1 - j) (2 * j + 1) := by
      rw [← sum_range_reflect (W (2 * n + 3)) (n + 2)]
      refine sum_congr rfl fun j hj => ?_
      have hj' := mem_range.mp hj
      rw [show n + 2 - 1 = n + 1 by omega, W, if_pos (by omega)]
      congr 1
      omega
    _ = ∑ j ∈ range (n / 2 + 1), T (n + 1 - j) (2 * j + 1) := by
      symm
      refine sum_subset (range_mono (by omega)) fun j hj hj' => ?_
      simp only [mem_range, not_lt] at hj hj'
      exact T_zero (by omega)

end OMA.P077864

theorem OMA.solution : type_of% @OMA.S_oeis_a077864.main := OMA.P077864.diagonal
