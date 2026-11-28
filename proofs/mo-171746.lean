import OMAStatements.S_mo_171746

/-! The segment of diagonal matrices with second diagonal entry
2t − 1 + i/2 stays in the domain. The swapped coordinate selector
makes the midpoint objective larger than both endpoint values. -/

open Matrix Set OMA.S_mo_171746
open scoped ComplexOrder

private def selector {ι κ : Type} [DecidableEq κ] (e : ι → κ) : Matrix ι κ ℂ :=
  Matrix.of fun i j => if e i = j then 1 else 0

private lemma selector_row {ι κ : Type} [DecidableEq κ] (e : ι → κ) (i : ι) :
    ∃! j, selector e i j ≠ 0 := by
  refine ⟨e i, by simp [selector], ?_⟩
  intro j hj
  by_contra he
  exact hj (by simp [selector, Ne.symm he])

private lemma selector_compress {ι κ : Type} [Fintype κ] [DecidableEq κ]
    (e : ι → κ) (A : Matrix κ κ ℂ) :
    selector e * A * (selector e)ᴴ = A.submatrix e e := by
  ext i j
  simp [Matrix.mul_apply, selector, eq_comm, ite_mul, mul_ite]

private lemma selector_mulVec {ι κ : Type} [Fintype κ] [DecidableEq κ]
    (e : ι → κ) (v : κ → ℂ) : selector e *ᵥ v = fun i => v (e i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, selector, eq_comm, ite_mul]

private lemma diag_unit {ι : Type} [DecidableEq ι] [Fintype ι] (d : ι → ℂ)
    (hd : ∀ i, d i ≠ 0) : IsUnit (diagonal d) :=
  isUnit_diagonal.mpr (Pi.isUnit_iff.mpr fun i => isUnit_iff_ne_zero.mpr (hd i))

private lemma diag_inverse {ι : Type} [DecidableEq ι] [Fintype ι] (d : ι → ℂ)
    (hd : ∀ i, d i ≠ 0) : (diagonal d)⁻¹ = diagonal fun i => (d i)⁻¹ := by
  have h : diagonal d * diagonal (fun i => (d i)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    exact funext fun i => mul_inv_cancel₀ (hd i)
  exact left_inv_eq_right_inv (nonsing_inv_mul _ (isUnit_det_of_right_inverse h)) h

private lemma gram_diagonal {ι : Type} [DecidableEq ι] [Fintype ι] (d : ι → ℂ) :
    1 + (diagonal d)ᴴ * diagonal d = diagonal (fun i => 1 + (Complex.normSq (d i) : ℂ)) := by
  rw [diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one, ← diagonal_add]
  congr 1
  funext i
  simp only [Pi.star_apply, Complex.star_def, Complex.normSq_eq_conj_mul_self]

private lemma gram_entry_ne (z : ℂ) : 1 + (Complex.normSq z : ℂ) ≠ 0 := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.ofReal_ne_zero]
  linarith [Complex.normSq_nonneg z]

private noncomputable def diagonalCore (z : ℂ) : ℂ :=
  (Complex.normSq z : ℂ) / (1 + (Complex.normSq z : ℂ))

private lemma diagonalCore_ne (z : ℂ) (hz : z ≠ 0) : diagonalCore z ≠ 0 := by
  exact div_ne_zero (Complex.ofReal_ne_zero.mpr (mt Complex.normSq_eq_zero.mp hz)) (gram_entry_ne z)

private lemma core_diagonal {ι : Type} [DecidableEq ι] [Fintype ι] (d : ι → ℂ) :
    diagonal d * (1 + (diagonal d)ᴴ * diagonal d)⁻¹ * (diagonal d)ᴴ =
      diagonal (fun i => diagonalCore (d i)) := by
  rw [gram_diagonal, diag_inverse _ (fun i => gram_entry_ne (d i)),
    diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  simp only [diagonalCore, Complex.star_def, Pi.star_apply, div_eq_mul_inv]
  rw [mul_right_comm, Complex.mul_conj]

private def zIndex : Fin 4 → Fin 3 × Fin 2 := ![(0, 0), (0, 1), (1, 0), (1, 1)]

private def dIndex : Fin 4 → Fin 2 × Fin 2 := ![(1, 1), (0, 1), (1, 0), (0, 0)]

private lemma zIndex_inj : Function.Injective zIndex := by decide +kernel

private lemma dIndex_surj : Function.Surjective dIndex := by decide +kernel

private noncomputable def diagonalInput (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal ![1, z]

private lemma compressed_diagonal (z : ℂ) :
    compressed 1 (selector zIndex) (diagonalInput z) =
      diagonal (fun i => diagonalCore (![1, z] ((zIndex i).2))) := by
  unfold compressed diagonalInput
  rw [core_diagonal, ← diagonal_one, Matrix.kronecker, diagonal_kronecker_diagonal, selector_compress,
    submatrix_diagonal _ _ zIndex_inj]
  simp

private lemma compressed_entry_ne (z : ℂ) (hz : z ≠ 0) (i : Fin 4) :
    diagonalCore (![1, z] ((zIndex i).2)) ≠ 0 := by
  apply diagonalCore_ne
  generalize (zIndex i).2 = j
  fin_cases j <;> simp [hz]

private lemma d_vec (z : ℂ) :
    selector dIndex *ᵥ (fun p => diagonalInput z p.1 p.2) = ![z, 0, 0, 1] := by
  rw [selector_mulVec]
  funext i
  fin_cases i <;> simp [dIndex, diagonalInput]

private lemma objective_diagonal (z : ℂ) (hz : z ≠ 0) :
    objective 1 (selector zIndex) (selector dIndex) (diagonalInput z) =
      2 * Complex.normSq z + (1 + Complex.normSq z) / Complex.normSq z := by
  unfold objective
  rw [d_vec, compressed_diagonal, diag_inverse _ (compressed_entry_ne z hz)]
  simp only [dotProduct, Pi.star_apply, mulVec_diagonal, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero]
  simp [zIndex, diagonalCore]
  rw [Complex.normSq_apply]
  ring

private noncomputable def zAt (t : ℝ) : ℂ := ⟨2 * t - 1, 1 / 2⟩

private lemma zAt_ne (t : ℝ) : zAt t ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  norm_num [zAt] at hi

private lemma mix_diagonal (t : ℝ) :
    mix (diagonalInput (zAt 0)) (diagonalInput (zAt 1)) t = diagonalInput (zAt t) := by
  unfold mix diagonalInput
  rw [← diagonal_smul, ← diagonal_smul, diagonal_add]
  congr 1
  funext i
  fin_cases i <;> apply Complex.ext <;> simp [zAt, Complex.real_smul] <;> ring

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_171746.main) := by
  intro h
  have hSurj (j : Fin 2 × Fin 2) : ∃ i, selector dIndex i j ≠ 0 := by
    obtain ⟨i, rfl⟩ := dIndex_surj j
    exact ⟨i, by simp [selector]⟩
  have h2 := h 3 2 4 1 (selector zIndex) (selector dIndex) (by decide)
    Matrix.PosDef.one (by intro i j; by_cases hi : zIndex i = j <;> simp [selector, hi])
    (selector_row zIndex) (selector_row dIndex) hSurj
    (diagonalInput (zAt 0)) (diagonalInput (zAt 1))
    (by
      intro t _
      rw [mix_diagonal, compressed_diagonal]
      constructor
      · unfold diagonalInput
        rw [gram_diagonal]
        exact diag_unit _ (fun i => gram_entry_ne _)
      · exact diag_unit _ (compressed_entry_ne _ (zAt_ne t)))
    (1 / 2) (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1)
  rw [mix_diagonal] at h2
  simp_rw [objective_diagonal _ (zAt_ne _)] at h2
  norm_num [zAt, Complex.normSq_apply] at h2
