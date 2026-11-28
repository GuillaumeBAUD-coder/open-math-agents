import OMAStatements.S_mo_95937
import Mathlib

-- Problem mo-95937: for a positive semidefinite real matrix Q with nonnegative entries and a real number a, the
-- matrix with entries a - Q_ij is copositive if and only if every diagonal entry of Q is at most a.
-- Upstream: statements/mo-95937.lean (declaration OMA.S_mo_95937.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: testing copositivity on the i-th unit vector gives a - Q_ii >= 0. Conversely, suppose Q_ii <= a for all
-- i. Positive semidefiniteness applied to e_i - e_j gives Q_ii - Q_ij - Q_ji + Q_jj >= 0, and Q is symmetric, so
-- Q_ij <= (Q_ii + Q_jj) / 2 <= a. Hence every entry a - Q_ij is nonnegative, and for a vector x with nonnegative
-- entries the form sum_i sum_j x_i (a - Q_ij) x_j is a sum of nonnegative terms.

open OMA.S_mo_95937 Matrix

theorem OMA.solution : type_of% @OMA.S_mo_95937.main := by
  intro n Q a hQ _
  unfold Copositive
  constructor
  · intro hcop i
    have h := hcop (fun k => if k = i then (1 : ℝ) else 0) (fun k => by split_ifs <;> norm_num)
    have h' : 0 ≤ ∑ k, (if k = i then (1 : ℝ) else 0) *
        ∑ l, (a - Q k l) * (if l = i then (1 : ℝ) else 0) := h
    simp at h'
    linarith
  · intro hdiag
    have hQa : ∀ i j, Q i j ≤ a := by
      intro i j
      have hsym : Q j i = Q i j := by
        have h0 := hQ.isHermitian.apply i j
        simpa using h0
      have inner : ∀ k, ∑ l, Q k l * ((if l = i then (1 : ℝ) else 0) - (if l = j then (1 : ℝ) else 0)) =
          Q k i - Q k j := by
        intro k
        simp [mul_sub, Finset.sum_sub_distrib]
      have outer : ∑ k, ((if k = i then (1 : ℝ) else 0) - (if k = j then (1 : ℝ) else 0)) *
          (Q k i - Q k j) = (Q i i - Q i j) - (Q j i - Q j j) := by
        simp [sub_mul, Finset.sum_sub_distrib]
      have hpsd := hQ.dotProduct_mulVec_nonneg
        (fun k => (if k = i then (1 : ℝ) else 0) - (if k = j then (1 : ℝ) else 0))
      rw [star_trivial] at hpsd
      have hpsd' : 0 ≤ ∑ k, ((if k = i then (1 : ℝ) else 0) - (if k = j then (1 : ℝ) else 0)) *
          ∑ l, Q k l * ((if l = i then (1 : ℝ) else 0) - (if l = j then (1 : ℝ) else 0)) := hpsd
      simp only [inner] at hpsd'
      rw [outer] at hpsd'
      have h1 := hdiag i
      have h2 := hdiag j
      linarith
    intro x hx
    show 0 ≤ ∑ i, x i * ∑ j, (a - Q i j) * x j
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (hx i)
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (sub_nonneg.mpr (hQa i j)) (hx j)
