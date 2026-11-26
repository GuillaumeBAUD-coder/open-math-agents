import FormalConjectures.Wikipedia.WallSunSun
import Mathlib.Tactic

-- Problem: Infinitude of Wall–Sun–Sun primes — discr rat of not modEq one
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/WallSunSun.lean:44 (declaration QuadraticAlgebra.discr_rat_of_not_modEq_one)
-- Credit: @Genbox (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


open NumberField

open QuadraticAlgebra
namespace OMAQuadDiscrAux
variable {d : ℤ} [Fact <| Squarefree d] [Fact <| d ≠ 1]


lemma basis_zero : (QuadraticAlgebra.basis (d : ℚ) 0 0 : (QuadraticAlgebra ℚ (d : ℚ) 0)) = 1 := by
  ext <;> simp [QuadraticAlgebra.basis]

lemma basis_one : (QuadraticAlgebra.basis (d : ℚ) 0 1 : (QuadraticAlgebra ℚ (d : ℚ) 0)) = QuadraticAlgebra.omega := by
  ext <;> simp [QuadraticAlgebra.basis]

lemma trace_eq (z : (QuadraticAlgebra ℚ (d : ℚ) 0)) : Algebra.trace ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) z = 2 * z.re := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis _ _), Matrix.trace_fin_two]
  simp [Algebra.leftMulMatrix_eq_repr_mul, basis_zero, basis_one]
  ring

lemma norm_eq (z : (QuadraticAlgebra ℚ (d : ℚ) 0)) : (z * star z) = algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) (z.re ^ 2 - d * z.im ^ 2) := by
  have h := (QuadraticAlgebra.algebraMap_norm_eq_mul_star z).symm
  rw [h, QuadraticAlgebra.norm_def]; congr 1; ring

lemma add_star_eq (z : (QuadraticAlgebra ℚ (d : ℚ) 0)) : (z + star z) = algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) (2 * z.re) := by
  have h := (QuadraticAlgebra.algebraMap_trace_eq_add_star (z := z)).symm
  rw [h, QuadraticAlgebra.trace_def]; congr 1; ring

lemma int_of_integral {q : ℚ} (h : IsIntegral ℤ (algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) q)) : ∃ n : ℤ, (n : ℚ) = q := by
  rw [isIntegral_algebraMap_iff (algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0)).injective] at h
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact ⟨n, by simpa using hn⟩

lemma isIntegral_omega : IsIntegral ℤ (QuadraticAlgebra.omega : (QuadraticAlgebra ℚ (d : ℚ) 0)) := by
  apply IsIntegral.of_pow (n := 2) (by norm_num)
  have : (QuadraticAlgebra.omega : (QuadraticAlgebra ℚ (d : ℚ) 0)) ^ 2 = algebraMap ℤ (QuadraticAlgebra ℚ (d : ℚ) 0) d := by
    ext <;> simp [sq]
  rw [this]; exact isIntegral_algebraMap


omit [Fact (d ≠ 1)] in
lemma int_of_mul_sq {q : ℚ} {k : ℤ} (h : (d : ℚ) * q ^ 2 = k) : ∃ n : ℤ, (n : ℚ) = q := by
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have h1 : (d : ℚ) * (q.num : ℚ) ^ 2 = k * (q.den : ℚ) ^ 2 := by
    rw [← Rat.num_div_den q] at h
    field_simp at h
    linear_combination h
  have h2 : d * q.num ^ 2 = k * (q.den : ℤ) ^ 2 := by exact_mod_cast h1
  have hc : IsCoprime (q.den : ℤ) q.num := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Nat.coprime_comm] using q.reduced
  have h3 : (q.den : ℤ) ^ 2 ∣ d * q.num ^ 2 := ⟨k, by rw [h2]; ring⟩
  have h4 : (q.den : ℤ) ^ 2 ∣ d := (hc.pow).dvd_of_dvd_mul_right h3
  have h5 : IsUnit (q.den : ℤ) := (Fact.out : Squarefree d) _ (by simpa [sq] using h4)
  have h6 : q.den = 1 := by
    rcases Int.isUnit_iff.mp h5 with h | h
    · exact_mod_cast h
    · have := q.den_pos; omega
  exact ⟨q.num, (Rat.den_eq_one_iff q).mp h6⟩

lemma two_dvd_of (A : ℤ) (h : (A : ZMod 4) = 0 ∨ (A : ZMod 4) = 2) : 2 ∣ A := by
  rcases h with h | h
  · rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h; omega
  · have : ((A - 2 : ℤ) : ZMod 4) = 0 := by push_cast; rw [h]; ring
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this; omega

lemma components (hd₄ : ¬ d ≡ 1 [ZMOD 4]) (x : (QuadraticAlgebra ℚ (d : ℚ) 0)) (hx : IsIntegral ℤ x) :
    ∃ m n : ℤ, x = ⟨m, n⟩ := by
  have hs : IsIntegral ℤ (star x) := by
    exact hx.map (starRingEnd (QuadraticAlgebra ℚ (d : ℚ) 0)).toIntAlgHom
  obtain ⟨A, hA⟩ := int_of_integral (d := d) (q := 2 * x.re) (by rw [← add_star_eq]; exact hx.add hs)
  obtain ⟨N, hN⟩ := int_of_integral (d := d) (q := x.re ^ 2 - d * x.im ^ 2)
    (by rw [← norm_eq]; exact hx.mul hs)
  obtain ⟨B, hB⟩ := int_of_mul_sq (d := d) (q := 2 * x.im) (k := A ^ 2 - 4 * N)
    (by push_cast; rw [hA, hN]; ring)
  have hAB : A ^ 2 - d * B ^ 2 = 4 * N := by
    have : (A : ℚ) ^ 2 - d * B ^ 2 = 4 * N := by rw [hA, hB, hN]; ring
    exact_mod_cast this
  have key : ∀ a b e : ZMod 4, e ≠ 1 → e ≠ 0 → a ^ 2 - e * b ^ 2 = 0 →
      (a = 0 ∨ a = 2) ∧ (b = 0 ∨ b = 2) := by decide
  have hd1 : (d : ZMod 4) ≠ 1 := by
    intro h; apply hd₄
    rw [show (1 : ZMod 4) = ((1 : ℤ) : ZMod 4) by simp, ZMod.intCast_eq_intCast_iff] at h
    exact h
  have hd0 : (d : ZMod 4) ≠ 0 := by
    intro h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    have := (Fact.out : Squarefree d) 2 (by simpa using h)
    rcases Int.isUnit_iff.mp this with h | h <;> omega
  have h4 : ((A ^ 2 - d * B ^ 2 : ℤ) : ZMod 4) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact ⟨N, by push_cast; linarith⟩
  push_cast at h4
  obtain ⟨hA2, hB2⟩ := key _ _ _ hd1 hd0 h4
  obtain ⟨a, rfl⟩ := two_dvd_of A hA2
  obtain ⟨b, rfl⟩ := two_dvd_of B hB2
  refine ⟨a, b, ?_⟩
  ext
  · push_cast at hA; linarith
  · push_cast at hB; linarith

theorem main (hd₄ : ¬ d ≡ 1 [ZMOD 4]) : discr (QuadraticAlgebra ℚ (d : ℚ) 0) = 4 * d := by
  let w : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0) := ⟨QuadraticAlgebra.omega, isIntegral_omega⟩
  let f : (Fin 2 → ℤ) →ₗ[ℤ] 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0) := Fintype.linearCombination ℤ ![1, w]
  have hf_coe : ∀ v, ((f v : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)) : (QuadraticAlgebra ℚ (d : ℚ) 0)) = ⟨v 0, v 1⟩ := by
    intro v
    have hw : algebraMap (𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)) (QuadraticAlgebra ℚ (d : ℚ) 0) w = QuadraticAlgebra.omega := rfl
    simp [f, Fintype.linearCombination_apply, Fin.sum_univ_two, map_mul, map_intCast, hw]
    ext <;> simp
  have hbij : Function.Bijective f := by
    constructor
    · intro u v h
      have := congrArg (fun x : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0) => (x : (QuadraticAlgebra ℚ (d : ℚ) 0))) h
      simp only [hf_coe, QuadraticAlgebra.mk.injEq] at this
      funext i; fin_cases i
      · exact_mod_cast this.1
      · exact_mod_cast this.2
    · intro x
      obtain ⟨m, n, hmn⟩ := components hd₄ (x : (QuadraticAlgebra ℚ (d : ℚ) 0)) x.2
      refine ⟨![m, n], ?_⟩
      apply RingOfIntegers.ext
      rw [hf_coe, hmn]; simp
  let e := LinearEquiv.ofBijective f hbij
  let bZ : Module.Basis (Fin 2) ℤ (𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)) := Module.Basis.ofEquivFun e.symm
  have hb : ∀ i, ((bZ i : 𝓞 (QuadraticAlgebra ℚ (d : ℚ) 0)) : (QuadraticAlgebra ℚ (d : ℚ) 0)) = QuadraticAlgebra.basis (d : ℚ) 0 i := by
    intro i
    simp only [bZ, Module.Basis.coe_ofEquivFun, LinearEquiv.symm_symm, e,
      LinearEquiv.ofBijective_apply, hf_coe]
    fin_cases i <;> ext <;> simp [QuadraticAlgebra.basis]
  rw [← discr_eq_discr (QuadraticAlgebra ℚ (d : ℚ) 0) bZ]
  apply Int.cast_injective (α := ℚ)
  rw [show ((Algebra.discr ℤ bZ : ℤ) : ℚ) = algebraMap ℤ ℚ (Algebra.discr ℤ bZ) from rfl,
    ← Algebra.discr_localizationLocalization ℤ (nonZeroDivisors ℤ) (QuadraticAlgebra ℚ (d : ℚ) 0)]
  have : (bZ.localizationLocalization ℚ (nonZeroDivisors ℤ) (QuadraticAlgebra ℚ (d : ℚ) 0) : Fin 2 → (QuadraticAlgebra ℚ (d : ℚ) 0)) =
      QuadraticAlgebra.basis (d : ℚ) 0 := by
    funext i; rw [Module.Basis.localizationLocalization_apply]; exact hb i
  rw [this, Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, trace_eq, basis_zero, basis_one]
  simp
  ring

end OMAQuadDiscrAux

theorem OMA.solution : type_of% @QuadraticAlgebra.discr_rat_of_not_modEq_one := by
  intro d _ _ hd₄
  exact OMAQuadDiscrAux.main hd₄
