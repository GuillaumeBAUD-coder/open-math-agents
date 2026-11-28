import OMAStatements.S_mo_126666
import Mathlib

namespace MatrixMeanCounterexample

open Matrix OMA.S_mo_126666

private def pair (t : ℝ) : RealMatrix 2 := !![85, t; t, 5]

private theorem pair_positive (t : ℝ) (ht : t ^ 2 = 169) : (pair t).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [pair]
  · intro x hx
    simp [pair, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hidentity :
        5 * (x 0 * (85 * x 0 + t * x 1) + x 1 * (t * x 0 + 5 * x 1)) =
          (t * x 0 + 5 * x 1) ^ 2 + 256 * (x 0) ^ 2 := by
      linear_combination -(x 0)^2 * ht
    by_cases h0 : x 0 = 0
    · have h1 : x 1 ≠ 0 := by
        intro h1
        apply hx
        funext i
        fin_cases i <;> assumption
      rw [h0]
      nlinarith [sq_pos_of_ne_zero h1]
    · nlinarith [sq_pos_of_ne_zero h0, sq_nonneg (t * x 0 + 5 * x 1)]

private def family : Fin 2 → RealMatrix 2 := ![pair 13, pair (-13)]

private theorem family_positive (i : Fin 2) : (family i).PosDef := by
  fin_cases i <;> apply pair_positive <;> norm_num

private theorem arithmetic :
    (1 / (2 : ℝ)) • (∑ i : Fin 2, family i) = diagonal ![85, 5] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_two, family, pair, Matrix.diagonal, Matrix.smul_apply]

private theorem product :
    (1 / (2 : ℝ)) •
      (∑ order : Equiv.Perm (Fin 2), (List.ofFn fun i => family (order i)).prod) =
        diagonal ![7056, -144] := by
  have hperm : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
      {1, Equiv.swap 0 1} := by decide +kernel
  have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide +kernel
  rw [hperm, Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [List.ofFn_succ, family, pair, Matrix.diagonal, Matrix.mul_apply,
      Matrix.smul_apply, Equiv.swap_apply_def, Fin.sum_univ_two]

private theorem singular_diagonal (a b : ℝ) (hab : b ^ 2 < a ^ 2) :
    singularValue (diagonal ![a, b]) 0 = |a| ∧
      singularValue (diagonal ![a, b]) 1 = |b| := by
  let A : RealMatrix 2 := diagonal ![a, b]
  let hA := isHermitian_conjTranspose_mul_self A
  let e : Fin 2 → ℝ := fun i => hA.eigenvalues₀ (Fin.cast (Fintype.card_fin 2).symm i)
  let f : Fin 2 ≃ Fin 2 :=
    (finCongr (Fintype.card_fin 2).symm).trans (Fintype.equivOfCardEq (Fintype.card_fin 2))
  have he (i : Fin 2) : hA.eigenvalues (f i) = e i := by
    exact congrArg hA.eigenvalues₀
      ((Fintype.equivOfCardEq (Fintype.card_fin 2)).symm_apply_apply
        (Fin.cast (Fintype.card_fin 2).symm i))
  have hsort : e 1 ≤ e 0 := hA.eigenvalues₀_antitone (by decide)
  have hmat : A.conjTranspose * A = diagonal ![a ^ 2, b ^ 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [A, Matrix.diagonal, Matrix.mul_apply, pow_two]
  have hsum : e 0 + e 1 = a ^ 2 + b ^ 2 := by
    calc
      _ = ∑ i, hA.eigenvalues (f i) := by
        rw [Fin.sum_univ_two]
        exact congrArg₂ (· + ·) (he 0).symm (he 1).symm
      _ = ∑ i, hA.eigenvalues i := f.sum_comp _
      _ = (A.conjTranspose * A).trace := by
        simpa using hA.trace_eq_sum_eigenvalues.symm
      _ = _ := by rw [hmat]; simp [Matrix.trace, Fin.sum_univ_two]
  have hprod : e 0 * e 1 = a ^ 2 * b ^ 2 := by
    calc
      _ = ∏ i, hA.eigenvalues (f i) := by
        rw [Fin.prod_univ_two]
        exact congrArg₂ (· * ·) (he 0).symm (he 1).symm
      _ = ∏ i, hA.eigenvalues i := f.prod_comp _
      _ = (A.conjTranspose * A).det := by
        simpa using hA.det_eq_prod_eigenvalues.symm
      _ = _ := by rw [hmat]; simp [Matrix.det_diagonal, Fin.prod_univ_two]
  have hroots : (e 0 - a ^ 2) * (e 0 - b ^ 2) = 0 := by
    linear_combination e 0 * hsum - hprod
  have htop : e 0 = a ^ 2 := by
    rcases mul_eq_zero.mp hroots with h | h
    · linarith
    · linarith
  have hbot : e 1 = b ^ 2 := by linarith
  change Real.sqrt (e 0) = |a| ∧ Real.sqrt (e 1) = |b|
  simp only [htop, hbot, Real.sqrt_sq_eq_abs, and_self]

theorem witness : type_of% @OMA.S_mo_126666.main := by
  refine ⟨2, 2, family, by decide, family_positive, 1, ?_⟩
  norm_num only [Nat.cast_ofNat]
  rw [arithmetic, product]
  have hiic : Finset.Iic (1 : Fin 2) = Finset.univ := by decide +kernel
  rw [hiic, Fin.sum_univ_two, Fin.sum_univ_two]
  obtain ⟨ha, hb⟩ := singular_diagonal 85 5 (by norm_num)
  obtain ⟨hc, hd⟩ := singular_diagonal 7056 (-144) (by norm_num)
  rw [ha, hb, hc, hd]
  norm_num only [Nat.cast_ofNat, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 85),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 7056),
    abs_of_neg (by norm_num : (-144 : ℝ) < 0), neg_neg]

end MatrixMeanCounterexample

theorem OMA.solution : type_of% @OMA.S_mo_126666.main :=
  MatrixMeanCounterexample.witness