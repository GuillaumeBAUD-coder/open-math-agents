import OMAStatements.S_mo_266728
import Mathlib

namespace OMA.SimplexColumns

open Matrix

private theorem hull {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    convexHull ℝ (Set.range A.col) = A.mulVec '' stdSimplex ℝ (Fin n) := by
  classical
  rw [← convexHull_rangle_single_eq_stdSimplex ℝ (Fin n)]
  change _ = A.mulVecLin '' _
  rw [LinearMap.image_convexHull, ← Set.range_comp]
  congr 1
  ext j
  simp [Function.comp_def]

private theorem columns_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ((fun _ : Fin n => (1 : ℝ)) ᵥ* A) = (fun _ => 1) ↔
      ∀ j, ∑ i, A i j = 1 := by
  rw [funext_iff]
  simp [Matrix.vecMul, dotProduct]

private theorem sum_image {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ j, ∑ i, A i j = 1) (x : Fin n → ℝ) :
    (∑ i, (A *ᵥ x) i) = ∑ i, x i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_mul, h i, one_mul]

private theorem scaled_inverse {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hd : A.det ≠ 0) (i j : Fin n) :
    A.det^2 * A⁻¹ i j = A.det * A.adjugate i j := by
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  field_simp [hd]

theorem characterization : type_of% @OMA.S_mo_266728.main := by
  intro n A
  classical
  constructor
  · rintro ⟨diagonal, equality⟩
    have witness (j : Fin n) :
        ∃ w ∈ stdSimplex ℝ (Fin n), A *ᵥ w = Pi.single j 1 := by
      have basis : Pi.single j (1 : ℝ) ∈ stdSimplex ℝ (Fin n) := by
        refine ⟨?_, by simp⟩
        intro i
        by_cases h : i = j <;> simp [h]
      rw [← equality, hull A] at basis
      exact basis.1
    choose w hw he using witness
    let B : Matrix (Fin n) (Fin n) ℝ := fun i j => w j i
    have ab : A * B = 1 := by
      apply Matrix.ext
      intro i j
      change (A *ᵥ w j) i = (1 : Matrix (Fin n) (Fin n) ℝ) i j
      have entry : (A *ᵥ w j) i = (Pi.single j (1 : ℝ) : Fin n → ℝ) i :=
        congrFun (he j) i
      simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using entry
    have ba : B * A = 1 := mul_eq_one_comm.mp ab
    have hinv : A⁻¹ = B := Matrix.inv_eq_right_inv ab
    have hd : A.det ≠ 0 := by
      intro h
      have hdet := congrArg Matrix.det ab
      rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at hdet
      exact zero_ne_one hdet
    let u : Fin n → ℝ := fun _ => 1
    have ub : u ᵥ* B = u := (columns_iff B).mpr fun j => (hw j).2
    have ua : u ᵥ* A = u := by
      calc
        _ = (u ᵥ* B) ᵥ* A := by rw [ub]
        _ = u := by rw [Matrix.vecMul_vecMul, ba, Matrix.vecMul_one]
    refine ⟨diagonal, (columns_iff A).mp ua, hd, ?_⟩
    intro i j
    rw [← scaled_inverse A hd, hinv]
    exact mul_nonneg (sq_nonneg _) ((hw j).1 i)
  · rintro ⟨diagonal, columns, hd, hadj⟩
    let B := A⁻¹
    have ab : A * B = 1 := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hd)
    have nonneg (i j : Fin n) : 0 ≤ B i j := by
      apply (mul_le_mul_iff_right₀ (sq_pos_of_ne_zero hd)).mp
      rw [mul_zero]
      exact (scaled_inverse A hd i j).symm ▸ hadj i j
    let u : Fin n → ℝ := fun _ => 1
    have ua : u ᵥ* A = u := (columns_iff A).mpr columns
    have ub : u ᵥ* B = u := by
      calc
        _ = (u ᵥ* A) ᵥ* B := by rw [ua]
        _ = u := by rw [Matrix.vecMul_vecMul, ab, Matrix.vecMul_one]
    refine ⟨diagonal, ?_⟩
    rw [hull A]
    ext x
    constructor
    · rintro ⟨⟨w, hw, rfl⟩, hx⟩
      exact ⟨hx, (sum_image A columns w).trans hw.2⟩
    · intro hx
      refine ⟨⟨B *ᵥ x, ⟨?_, (sum_image B ((columns_iff B).mp ub) x).trans hx.2⟩, ?_⟩, hx.1⟩
      · intro i
        change 0 ≤ ∑ j : Fin n, B i j * x j
        exact Finset.sum_nonneg fun j _ => mul_nonneg (nonneg i j) (hx.1 j)
      · rw [Matrix.mulVec_mulVec, ab, Matrix.one_mulVec]

end OMA.SimplexColumns

theorem OMA.solution : type_of% @OMA.S_mo_266728.main :=
  OMA.SimplexColumns.characterization