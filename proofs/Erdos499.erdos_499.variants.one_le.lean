import FormalConjectures.ErdosProblems.«499»
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Convex.Birkhoff

/-! The weighted diagonal sum of a Birkhoff decomposition is the sum of squared entries. -/

open Finset

theorem OMA.solution : type_of% @Erdos499.erdos_499.variants.one_le := by
  classical
  intro n hn M hM
  obtain ⟨w, hw, htotal, hdecomp⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM
  let diagonal (σ : Equiv.Perm (Fin n)) := ∑ i, M i (σ i)
  have entry (i j : Fin n) :
      M i j = ∑ σ : Equiv.Perm (Fin n), if σ i = j then w σ else 0 := by
    calc
      M i j = (∑ σ : Equiv.Perm (Fin n), w σ • σ.permMatrix ℝ) i j := by rw [hdecomp]
      _ = _ := by
        simp [Matrix.sum_apply, Matrix.smul_apply, PEquiv.toMatrix_apply,
          Equiv.toPEquiv_apply, smul_eq_mul, mul_ite]
  have weighted :
      ∑ σ : Equiv.Perm (Fin n), w σ * diagonal σ = ∑ i, ∑ j, M i j ^ 2 := by
    calc
      _ = ∑ i, ∑ σ : Equiv.Perm (Fin n), w σ * M i (σ i) := by
        simp only [diagonal, Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        calc
          _ = ∑ σ : Equiv.Perm (Fin n), ∑ j : Fin n,
              M i j * (if σ i = j then w σ else 0) := by
            apply Finset.sum_congr rfl
            intro σ _
            simp [mul_ite, mul_comm]
          _ = ∑ j, M i j ^ 2 := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            rw [← Finset.mul_sum, ← entry, pow_two]
  have row (i : Fin n) : 1 ≤ (n : ℝ) * ∑ j, M i j ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
      (f := fun j => M i j)
    rw [sum_row_of_mem_doublyStochastic hM i] at h
    simpa using h
  have squares : 1 ≤ ∑ i, ∑ j, M i j ^ 2 := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun i _ => row i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      ← Finset.mul_sum] at h
    exact le_of_mul_le_mul_left (by simpa only [mul_one] using h) hn'
  have chosen : ∃ σ : Equiv.Perm (Fin n), 0 < w σ ∧ 1 ≤ diagonal σ := by
    by_contra hno
    have less (σ : Equiv.Perm (Fin n)) (hp : 0 < w σ) :
        w σ * diagonal σ < w σ := by
      have hd : diagonal σ < 1 := lt_of_not_ge (fun h => hno ⟨σ, hp, h⟩)
      simpa using mul_lt_mul_of_pos_left hd hp
    have weak (σ : Equiv.Perm (Fin n)) : w σ * diagonal σ ≤ w σ := by
      rcases (hw σ).eq_or_lt with hzero | hpos
      · simp [← hzero]
      · exact (less σ hpos).le
    have hpos : (∑ σ : Equiv.Perm (Fin n), (0 : ℝ)) < ∑ σ, w σ := by
      rw [htotal]
      simp
    obtain ⟨σ, hσ, hσpos⟩ := Finset.exists_lt_of_sum_lt hpos
    have hsum := Finset.sum_lt_sum (fun σ _ => weak σ) ⟨σ, hσ, less σ hσpos⟩
    rw [weighted, htotal] at hsum
    exact (not_lt_of_ge squares) hsum
  obtain ⟨σ, hσ, hdiag⟩ := chosen
  refine ⟨σ, ?_, hdiag⟩
  intro i
  apply ne_of_gt (hσ.trans_le ?_)
  rw [entry]
  calc
    w σ = (if σ i = σ i then w σ else 0) := by simp
    _ ≤ ∑ τ : Equiv.Perm (Fin n), if τ i = σ i then w τ else 0 :=
      Finset.single_le_sum (f := fun τ : Equiv.Perm (Fin n) => if τ i = σ i then w τ else 0)
        (fun τ _ => by split <;> simp [hw]) (Finset.mem_univ σ)