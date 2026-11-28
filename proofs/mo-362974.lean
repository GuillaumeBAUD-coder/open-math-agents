import OMAStatements.S_mo_362974
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-!
# Upper bound for smallest eigenvalue of infinite family of graphs

Question by Yahav Boneh on MathOverflow, 13 June 2020.
https://mathoverflow.net/questions/362974/upper-bound-for-smallest-eigenvalue-of-infinite-family-of-graphs

Formal statement credited to @etaubman. Proof credited to @grp06.
-/

open OMA.S_mo_362974 (adjacency)

theorem OMA.solution : type_of% @OMA.S_mo_362974.main := by
  classical
  intro n G _ _ edges _
  refine ⟨-(1 / 2 : ℝ), by norm_num, 0, ?_⟩
  intro i _
  obtain ⟨u, v, huv⟩ := edges i
  let A := adjacency (G i)
  let C : Matrix (Fin (n i)) (Fin (n i)) ℝ := A + (1 / 2 : ℝ) • 1
  have hdiag (w : Fin (n i)) : C w w = (1 / 2 : ℝ) := by
    simp [C, A, adjacency, Matrix.one_apply, (G i).irrefl]
  have hentry {x y : Fin (n i)} (hxy : (G i).Adj x y) : C x y = 1 := by
    simp [C, A, adjacency, Matrix.one_apply, hxy, hxy.ne]
  have hnot : ¬ C.PosSemidef := by
    intro h
    let e : Fin 2 → Fin (n i) := ![u, v]
    have h0 : e 0 = u := by simp [e]
    have h1 : e 1 = v := by simp [e]
    have hdet := (h.submatrix e).det_nonneg
    rw [Matrix.det_fin_two] at hdet
    simp only [Matrix.submatrix_apply, h0, h1, hdiag, hentry huv, hentry huv.symm] at hdet
    norm_num at hdet
  have hA : A.IsHermitian := (G i).isHermitian_adjMatrix ℝ
  have hId : (1 : Matrix (Fin (n i)) (Fin (n i)) ℝ).IsHermitian :=
    Matrix.isHermitian_one
  have hC : C.IsHermitian := hA.add (hId.smul (IsSelfAdjoint.all (1 / 2 : ℝ)))
  have hnegative : ¬ ∀ j, 0 ≤ hC.eigenvalues j := by
    intro h
    apply hnot
    exact hC.posSemidef_iff_eigenvalues_nonneg.mpr h
  obtain ⟨j, hj⟩ := not_forall.mp hnegative
  have hlt : hC.eigenvalues j < 0 := lt_of_not_ge hj
  have heigen : Module.End.HasEigenvalue C.toLin' (hC.eigenvalues j) := by
    apply Module.End.hasEigenvalue_iff_mem_spectrum.mpr
    rw [Matrix.spectrum_toLin']
    exact hC.eigenvalues_mem_spectrum_real j
  have hshift : C.toLin' = A.toLin' + (1 / 2 : ℝ) • LinearMap.id := by
    simp only [C, map_add, map_smul, Matrix.toLin'_one]
  rw [hshift, Module.End.hasEigenvalue_add_iff, Matrix.toLin'_apply'] at heigen
  exact ⟨hC.eigenvalues j - 1 / 2, by linarith, heigen⟩
