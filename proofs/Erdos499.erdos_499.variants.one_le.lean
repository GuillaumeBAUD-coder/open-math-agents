import FormalConjectures.ErdosProblems.«499»
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Convex.Birkhoff

/-! The weighted diagonal sum of a Birkhoff decomposition is the sum of squared entries. -/

open Finset

theorem OMA.solution : type_of% @Erdos499.erdos_499.variants.one_le := by
  classical
  intro n hn M hM
  obtain ⟨w, hw, htot, hdec⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM
  have hent (i j : Fin n) : M i j = ∑ σ : Equiv.Perm (Fin n), if σ i = j then w σ else 0 := by
    rw [← hdec]; simp [Matrix.sum_apply, Matrix.smul_apply, PEquiv.toMatrix_apply,
      Equiv.toPEquiv_apply, smul_eq_mul, mul_ite]
  have hwt : ∑ σ : Equiv.Perm (Fin n), w σ * ∑ i, M i (σ i) = ∑ i, ∑ j, M i j ^ 2 := by
    simp_rw [mul_sum]; rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    trans ∑ σ : Equiv.Perm (Fin n), ∑ j : Fin n, M i j * if σ i = j then w σ else 0
    · exact sum_congr rfl fun σ _ => by simp [mul_ite, mul_comm]
    · rw [sum_comm]; exact sum_congr rfl fun j _ => by rw [← mul_sum, ← hent, pow_two]
  have hsq : 1 ≤ ∑ i, ∑ j, M i j ^ 2 := by
    have hrow (i : Fin n) : 1 ≤ (n : ℝ) * ∑ j, M i j ^ 2 := by
      simpa [sum_row_of_mem_doublyStochastic hM i] using
        sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin n))) (f := M i)
    have h := sum_le_sum fun i (_ : i ∈ univ) => hrow i
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, ← mul_sum] at h
    exact le_of_mul_le_mul_left (by simpa using h) (by exact_mod_cast hn : (0 : ℝ) < n)
  have ⟨σ, hσ, hdiag⟩ : ∃ σ : Equiv.Perm (Fin n), 0 < w σ ∧ 1 ≤ ∑ i, M i (σ i) := by
    by_contra hno
    have hlt (σ) (hp : 0 < w σ) : w σ * ∑ i, M i (σ i) < w σ := by
      simpa using mul_lt_mul_of_pos_left (lt_of_not_ge fun h => hno ⟨σ, hp, h⟩) hp
    obtain ⟨σ, hσ, hσp⟩ := exists_lt_of_sum_lt
      (show ∑ _ : Equiv.Perm (Fin n), (0 : ℝ) < ∑ σ, w σ by rw [htot]; simp)
    have hsum := sum_lt_sum (fun σ _ => (hw σ).eq_or_lt.elim (fun h => by simp [← h]) fun h => (hlt σ h).le)
      ⟨σ, hσ, hlt σ hσp⟩
    linarith
  refine ⟨σ, fun i => ne_of_gt (hσ.trans_le ?_), hdiag⟩
  rw [hent]
  simpa using single_le_sum (f := fun τ : Equiv.Perm (Fin n) => if τ i = σ i then w τ else 0)
    (fun τ _ => by split <;> simp [hw]) (mem_univ σ)
