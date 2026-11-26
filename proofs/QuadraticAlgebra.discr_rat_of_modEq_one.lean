import FormalConjectures.Wikipedia.WallSunSun

/-! The integral pair consisting of one and the half-sum of one and the
square root of d has discriminant d. Squarefreeness forces its index to be one. -/

open NumberField
open scoped Matrix

namespace OMA

lemma quadraticTrace {d : ℚ} (z : QuadraticAlgebra ℚ d 0) :
    Algebra.trace ℚ (QuadraticAlgebra ℚ d 0) z = 2 * z.re := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis _ _), Matrix.trace_fin_two]
  simp [Algebra.leftMulMatrix_eq_repr_mul, QuadraticAlgebra.basis]
  ring

end OMA

theorem OMA.solution : type_of% @QuadraticAlgebra.discr_rat_of_modEq_one := by
  classical
  intro d hsf hd1 hd
  let K := QuadraticAlgebra ℚ (d : ℚ) 0
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hd
  let z : K := ⟨1 / 2, 1 / 2⟩
  have hz : IsIntegral ℤ z := by
    let f : Polynomial ℤ := Polynomial.X ^ 2 - (Polynomial.X - Polynomial.C k)
    have hf : f.Monic := Polynomial.monic_X_pow_sub (by
      rw [Polynomial.degree_X_sub_C]
      decide)
    refine ⟨f, hf, ?_⟩
    rw [← Polynomial.aeval_def]
    simp only [f, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    have hkQ : 1 - (d : ℚ) = 4 * (k : ℚ) := by exact_mod_cast hk
    change z ^ 2 - (z - (k : K)) = 0
    ext <;> simp [z, K, pow_two] <;> linarith
  let v : Fin 2 → 𝓞 K := ![1, ⟨z, hz⟩]
  let b₀ := Module.Free.chooseBasis ℤ (𝓞 K)
  have hc : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 := by
    rw [← Module.finrank_eq_card_basis b₀, RingOfIntegers.rank,
      Module.finrank_eq_card_basis (QuadraticAlgebra.basis (d : ℚ) 0)]
    simp
  let b := b₀.reindex (Fintype.equivFinOfCardEq hc)
  let bQ := b.localizationLocalization ℚ (nonZeroDivisors ℤ) K
  let P : Matrix (Fin 2) (Fin 2) ℤ := b.toMatrix v
  have hb : ((bQ : Fin 2 → K) ᵥ* (P.map (algebraMap ℤ ℚ)).map (algebraMap ℚ K)) =
      ![1, z] := by
    funext j
    have h := congrArg (algebraMap (𝓞 K) K) (b.sum_toMatrix_smul_self v j)
    have hzcoe : algebraMap (𝓞 K) K ⟨z, hz⟩ = z := rfl
    fin_cases j <;>
      simpa [P, v, bQ, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
        Module.Basis.localizationLocalization_apply, Algebra.smul_def, mul_comm, hzcoe] using h
  have hpair : Algebra.discr ℚ (![1, z] : Fin 2 → K) = (d : ℚ) := by
    rw [Algebra.discr_def, Matrix.det_fin_two]
    let T := Algebra.trace ℚ (QuadraticAlgebra ℚ (d : ℚ) 0)
    change T (1 * 1) * T (z * z) - T (1 * z) * T (z * 1) = (d : ℚ)
    have hT (w : K) : T w = 2 * w.re := OMA.quadraticTrace w
    simp only [one_mul, mul_one, hT]
    have hre : (1 : K).re = 1 := rfl
    rw [hre]
    simp [z, K]
    ring
  have hscale := Algebra.discr_of_matrix_vecMul (bQ : Fin 2 → K) (P.map (algebraMap ℤ ℚ))
  rw [hb, hpair] at hscale
  change (d : ℚ) = ((algebraMap ℤ ℚ).mapMatrix P).det ^ 2 * Algebra.discr ℚ bQ at hscale
  rw [← RingHom.map_det] at hscale
  dsimp only [bQ] at hscale
  rw [Algebra.discr_localizationLocalization, NumberField.discr_eq_discr] at hscale
  have hscaleZ : d = P.det ^ 2 * NumberField.discr K := by
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_mul, Int.cast_pow]
    exact hscale
  have hu : IsUnit P.det := hsf.out _ ⟨NumberField.discr K, by simpa [pow_two] using hscaleZ⟩
  rcases Int.isUnit_iff.mp hu with h | h <;> simpa [h] using hscaleZ.symm
