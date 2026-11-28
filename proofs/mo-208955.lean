import OMAStatements.S_mo_208955
import Mathlib

open Matrix Finset
open scoped BigOperators Matrix.Norms.L2Operator

open OMA.S_mo_208955

private theorem circulant_sum_shifts {n : ℕ} (a : Fin (n+1) → ℝ) :
    RowCirculant a = ∑ k : Fin (n+1), (a k : ℂ) • (Equiv.addRight k).permMatrix ℂ := by
  ext i j
  rw [Matrix.sum_apply]
  change (a (j-i) : ℂ) = ∑ k : Fin (n+1),
    (a k : ℂ) • (Equiv.addRight k).permMatrix ℂ i j
  simp only [Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,
    Equiv.addRight,smul_eq_mul]
  rw [Finset.sum_eq_single (j-i)]
  · have h : i+(j-i) = j := (add_comm i (j-i)).trans (sub_add_cancel j i)
    simp [h]
  · intro k _ hk
    have h : i+k ≠ j := by
      intro he
      apply hk
      calc
        k = i+k-i := by rw [add_comm i k,add_sub_cancel_right]
        _ = j-i := congrArg (fun l : Fin (n+1) => l-i) he
    simp [h]
  · simp

private theorem circulant_ones {n : ℕ} (a : Fin (n+1) → ℝ) :
    RowCirculant a *ᵥ (fun _ => 1) = (fun _ => ((∑ k, a k : ℝ) : ℂ)) := by
  ext i
  simp only [Matrix.mulVec,dotProduct,RowCirculant,mul_one]
  rw [Complex.ofReal_sum]
  simpa [sub_eq_add_neg] using
    (Equiv.sum_comp (Equiv.addRight (-i)) (fun j => (a j : ℂ)))

theorem OMA.solution : type_of% @OMA.S_mo_208955.main := by
  intro n hn
  cases n with
  | zero => omega
  | succ n =>
    intro a hNonneg
    apply le_antisymm
    · rw [circulant_sum_shifts]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hNonneg k)]
      exact (mul_le_mul_of_nonneg_left (Matrix.permMatrix_l2_opNorm_le _) (hNonneg k)).trans_eq (mul_one _)
    · let v : EuclideanSpace ℂ (Fin (n+1)) := WithLp.toLp 2 (fun _ => 1)
      have hNe : v ≠ 0 := by
        intro h
        have h0 := congrArg (fun w : EuclideanSpace ℂ (Fin (n+1)) => w.ofLp 0) h
        change (1 : ℂ) = 0 at h0
        exact one_ne_zero h0
      have hPos : 0 < ‖v‖ := norm_pos_iff.mpr hNe
      have hSum : 0 ≤ ∑ k, a k := Finset.sum_nonneg (fun k _ => hNonneg k)
      have hEigen :
          Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℂ) (RowCirculant a) v = ((∑ k, a k : ℝ) : ℂ) • v := by
        rw [Matrix.toEuclideanCLM_toLp, circulant_ones]
        apply (WithLp.equiv 2 (Fin (n+1) → ℂ)).injective
        funext i
        change ((∑ k, a k : ℝ) : ℂ) = ((∑ k, a k : ℝ) : ℂ) * 1
        rw [mul_one]
      have hOp := (Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℂ) (RowCirculant a)).le_opNorm v
      rw [hEigen,Matrix.l2_opNorm_toEuclideanCLM,norm_smul,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg hSum] at hOp
      exact le_of_mul_le_mul_right hOp hPos
