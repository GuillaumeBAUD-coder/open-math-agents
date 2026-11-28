import OMAStatements.S_oeis_a125790
import Mathlib

namespace OMA.P_oeis_a125790

open Polynomial Finset OMA.S_oeis_a125790

/-- Antidifference of a rational polynomial, with a degree bound and a prescribed value at 0. -/
lemma antidiff (Q : ℚ[X]) (d : ℕ) (hQ : Q.natDegree ≤ d) (c : ℚ) :
    ∃ P : ℚ[X], P.natDegree ≤ d + 1 ∧ P.comp (1 + X) - P = Q ∧ P.eval 0 = c := by
  set P0 : ℚ[X] := ∑ m ∈ range (d + 1),
    C (Q.coeff m / ((m : ℚ) + 1)) * Polynomial.bernoulli (m + 1) with hP0
  have hdeg0 : P0.natDegree ≤ d + 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [Polynomial.bernoulli_def]
    refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    refine (natDegree_monomial_le _).trans ?_
    have := mem_range.1 hm
    have := mem_range.1 hi
    omega
  have hdiff : P0.comp (1 + X) - P0 = Q := by
    have h1 : P0.comp (1 + X) - P0 = ∑ m ∈ range (d + 1), monomial m (Q.coeff m) := by
      rw [hP0, Polynomial.sum_comp, ← sum_sub_distrib]
      refine sum_congr rfl fun m _ => ?_
      rw [mul_comp, C_comp, Polynomial.bernoulli_comp_one_add_X, mul_add, add_sub_cancel_left,
        Nat.add_sub_cancel, nsmul_eq_mul, ← C_mul_X_pow_eq_monomial, ← C_eq_natCast, ← mul_assoc,
        ← C_mul]
      congr 2
      have : ((m : ℚ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
    rw [h1]
    exact (Q.as_sum_range' (d + 1) (by omega)).symm
  refine ⟨P0 - C (P0.eval 0) + C c, ?_, ?_, ?_⟩
  · refine (natDegree_add_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le hdeg0 ?_)) ?_)
      <;> simp
  · rw [← hdiff]
    simp only [add_comp, sub_comp, C_comp]
    ring
  · simp

/-- Each row of the table is a polynomial function of degree at most n, vanishing at -1 for n > 0. -/
lemma row_poly (n : ℕ) : ∃ P : ℚ[X], P.natDegree ≤ n ∧ (∀ k : ℕ, P.eval (k : ℚ) = (T n k : ℚ)) ∧
    (0 < n → P.eval (-1) = 0) := by
  induction n with
  | zero => exact ⟨1, by simp, fun k => by simp [T], fun h => absurd h (lt_irrefl _)⟩
  | succ n ih =>
    obtain ⟨R, hRd, hR, -⟩ := ih
    obtain ⟨P, hPd, hP, hP0⟩ := antidiff (R.comp (C 2 * X + C 2)) n (by
      refine natDegree_comp_le.trans ?_
      have h1 : (C 2 * X + C 2 : ℚ[X]).natDegree ≤ 1 := by
        refine (natDegree_add_le _ _).trans (max_le ?_ (by simp))
        exact (natDegree_C_mul_le _ _).trans (by simp)
      calc R.natDegree * (C 2 * X + C 2 : ℚ[X]).natDegree ≤ n * 1 := Nat.mul_le_mul hRd h1
        _ = n := mul_one n) 1
    have hstep : ∀ x : ℚ, P.eval (1 + x) = P.eval x + R.eval (2 * x + 2) := by
      intro x
      have := congrArg (Polynomial.eval x) hP
      simp only [eval_sub, eval_comp, eval_add, eval_one, eval_X, eval_mul, eval_C] at this
      linarith
    refine ⟨P, hPd, ?_, fun _ => ?_⟩
    · intro k
      induction k with
      | zero => simp [T, hP0]
      | succ k ihk =>
        have h2 := hR (2 * (k + 1))
        have h3 := hstep (k : ℚ)
        rw [T]
        push_cast at h2 ⊢
        rw [show ((k : ℚ) + 1) = 1 + k by ring, h3, ihk]
        rw [show (2 : ℚ) * k + 2 = 2 * (k + 1) by ring, h2]
    · have h3 := hstep (-1)
      have hT : (T n 0 : ℚ) = 1 := by cases n <;> simp [T]
      have h4 : R.eval 0 = 1 := by
        have := hR 0
        rw [hT] at this
        simpa using this
      norm_num at h3
      rw [hP0, h4] at h3
      linarith

/-- Coefficients of (1 - X)^m. -/
lemma coeff_one_sub_pow (m j : ℕ) :
    PowerSeries.coeff j ((1 - PowerSeries.X : PowerSeries ℤ) ^ m) = (-1) ^ j * (m.choose j : ℤ) := by
  induction m generalizing j with
  | zero => cases j <;> simp [PowerSeries.coeff_one]
  | succ m ih =>
    rw [pow_succ, mul_sub, mul_one, map_sub]
    cases j with
    | zero => simp [ih]
    | succ j =>
      rw [PowerSeries.coeff_succ_mul_X, ih, ih, Nat.choose_succ_succ]
      push_cast
      ring

/-- Coefficients of a series times (1 - X)^m. -/
lemma coeff_mk_mul (f : ℕ → ℤ) (m i : ℕ) :
    PowerSeries.coeff i (PowerSeries.mk f * (1 - PowerSeries.X) ^ m) =
      ∑ j ∈ range (i + 1), (m.choose j : ℤ) * f (i - j) * (-1) ^ j := by
  rw [mul_comm, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine sum_congr rfl fun j _ => ?_
  rw [coeff_one_sub_pow, PowerSeries.coeff_mk]
  ring

/-- The alternating sums vanish from index n on. -/
lemma alt_sum_zero (n i : ℕ) (hn : 0 < n) (hi : n ≤ i) :
    ∑ j ∈ range (i + 1), ((n + 1).choose j : ℤ) * (T n (i - j) : ℤ) * (-1) ^ j = 0 := by
  obtain ⟨P, hPd, hP, hP1⟩ := row_poly n
  have hP1 := hP1 hn
  have hz := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (P := P) (n := n + 1)
    (by omega)) ((i : ℚ) - (n + 1))
  rw [fwdDiff_iter_eq_sum_shift, ← Finset.sum_range_reflect] at hz
  simp only [Pi.zero_apply] at hz
  have key : ∑ j ∈ range (n + 2), ((n + 1).choose j : ℚ) * P.eval ((i : ℚ) - j) * (-1) ^ j = 0 := by
    rw [← hz]
    refine sum_congr rfl fun j hj => ?_
    have hj' : j ≤ n + 1 := by have := mem_range.1 hj; omega
    have e1 : n + 1 + 1 - 1 - j = n + 1 - j := by omega
    rw [e1, Nat.sub_sub_self hj', Nat.choose_symm hj']
    have e2 : (i : ℚ) - (↑n + 1) + (n + 1 - j : ℕ) • (1 : ℚ) = (i : ℚ) - j := by
      rw [nsmul_eq_mul, Nat.cast_sub hj']; push_cast; ring
    rw [e2]
    simp only [zsmul_eq_mul]
    push_cast
    ring
  have goalQ : ∑ j ∈ range (i + 1), ((n + 1).choose j : ℚ) * (T n (i - j) : ℚ) * (-1) ^ j = 0 := by
    rw [← key]
    rcases hi.eq_or_lt with h | h
    · subst h
      rw [sum_range_succ _ (n + 1)]
      have : P.eval ((n : ℚ) - ((n + 1 : ℕ) : ℚ)) = 0 := by
        rw [show (n : ℚ) - ((n + 1 : ℕ) : ℚ) = -1 by push_cast; ring]; exact hP1
      rw [this]
      simp only [mul_zero, zero_mul, add_zero]
      refine sum_congr rfl fun j hj => ?_
      have hj' : j ≤ n := by have := mem_range.1 hj; omega
      rw [← hP, Nat.cast_sub hj']
    · symm
      refine (sum_subset (range_subset_range.2 (by omega)) fun j _ hj => ?_).trans
        (sum_congr rfl fun j hj => ?_)
      · have : n + 1 < j := by simp only [mem_range, not_lt] at hj; omega
        simp [Nat.choose_eq_zero_of_lt this]
      · have hj' : j ≤ i := by have := mem_range.1 hj; omega
        rw [← hP, Nat.cast_sub hj']
  exact_mod_cast goalQ

end OMA.P_oeis_a125790

theorem OMA.solution : type_of% @OMA.S_oeis_a125790.main := by
  intro n hn
  obtain ⟨s, hs⟩ : ∃ s : ℕ → ℤ, s = fun i' => ∑ j ∈ Finset.range (i' + 1),
      ((n + 1).choose j : ℤ) * (OMA.S_oeis_a125790.T n (i' - j) : ℤ) * (-1) ^ j := ⟨_, rfl⟩
  have hR : ∀ i' : ℕ, (PowerSeries.X : PowerSeries ℤ) ^ i' *
      ∑ j ∈ Finset.range (i' + 1),
        ((n + 1).choose j : PowerSeries ℤ) * (OMA.S_oeis_a125790.T n (i' - j) : PowerSeries ℤ)
          * (-1) ^ j =
      PowerSeries.C (s i') * PowerSeries.X ^ i' := by
    intro i'
    rw [mul_comm, hs]
    congr 1
    simp [map_sum]
  ext i
  rw [OMA.P_oeis_a125790.coeff_mk_mul]
  simp only [hR, map_sum, PowerSeries.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.range n) i]
  by_cases h : i < n
  · simp [h, hs]
  · simp only [Finset.mem_range, h, if_false]
    exact OMA.P_oeis_a125790.alt_sum_zero n i hn (by omega)
