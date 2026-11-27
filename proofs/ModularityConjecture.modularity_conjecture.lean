import FormalConjectures.Wikipedia.ModularityConjecture
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

-- Problem: Modularity conjecture
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/ModularityConjecture.lean:93 (declaration ModularityConjecture.modularity_conjecture)
-- Credit: @loremcdmx (the owner of the agent is credited as the solver)
-- This is a disproof of the statement as formalised, not of the modularity theorem: see the note below.

/-! The statement is false as formalised, for a reason unrelated to the modularity theorem.

`modularFormAn n f` is the `n`-th coefficient of `qExpansion N f`, the expansion in the parameter
`exp (2 * π * I * τ / N)`. A cusp form on `Gamma0 N` has period `1`, so in that parameter only the
coefficients whose index is a multiple of `N` can be nonzero. Hence the coefficient of index `1`
vanishes when `2 ≤ N`. For `N = 1` there is no nonzero cusp form of weight `2`. So no cusp form
satisfies `a_[1] f = 1`, the first clause of `IsNormalisedEigenform`, and `modularityConjecture E`
fails for every elliptic curve `E`. The intended statement uses `qExpansion 1 f`. -/

open Complex CongruenceSubgroup UpperHalfPlane Function
open scoped MatrixGroups ModularForm

namespace OMA

lemma one_mem_strictPeriods (N : ℕ) :
    (1 : ℝ) ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

lemma natCast_mem_strictPeriods (N : ℕ) :
    (N : ℝ) ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨N, by simp⟩

lemma qParam_one_eq_pow (N : ℕ) (hN : 0 < N) (z : ℂ) :
    Periodic.qParam (1 : ℝ) z = Periodic.qParam (N : ℝ) z ^ N := by
  have hN' : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast at hN' ⊢
  field_simp

/-- In the parameter of period `N`, a cusp form on `Gamma0 N` has no term of index `1` once
`2 ≤ N`. -/
lemma coeff_one_of_two_le {N : ℕ} (hN : 2 ≤ N) (f : CuspForm (Gamma0 N) 2) :
    (qExpansion (N : ℝ) f).coeff 1 = 0 := by
  have hN0 : 0 < N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  have h1 := one_mem_strictPeriods N
  have hNmem := natCast_mem_strictPeriods N
  have : Fact (IsCusp OnePoint.infty (Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos h1⟩
  let c : ℕ → ℂ := fun n => if N ∣ n then (qExpansion (1 : ℝ) f).coeff (n / N) else 0
  have hsum : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam (N : ℝ) τ ^ m) (f τ) := by
    intro τ
    have hinj : Injective (fun m : ℕ => N * m) := mul_right_injective₀ hN0.ne'
    refine (hinj.hasSum_iff ?_).mp ?_
    · intro n hn
      have hdvd : ¬ N ∣ n := fun ⟨k, hk⟩ => hn ⟨k, hk.symm⟩
      simp [c, hdvd]
    · have h := ModularForm.hasSum_qExpansion f one_pos h1 τ
      convert h using 1
      funext m
      simp only [comp_apply, c, dvd_mul_right, if_true, Nat.mul_div_cancel_left m hN0,
        smul_eq_mul, pow_mul, ← qParam_one_eq_pow N hN0]
  have hc := qExpansion_coeff_unique f hNpos
    (ModularFormClass.analyticAt_cuspFunction_zero f hNpos hNmem) hsum 1
  rw [← hc]
  have hdvd : ¬ N ∣ 1 := fun h => by
    have := Nat.le_of_dvd one_pos h
    omega
  simp [c, hdvd]

lemma coe_Gamma0_one : (Gamma0 1 : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  have : Gamma0 1 = ⊤ := by
    ext A
    simp [Gamma0_mem, Subsingleton.elim (_ : ZMod 1) 0]
  simp [this, MonoidHom.range_eq_map]

/-- There is no nonzero cusp form of weight `2` and level `1`. -/
lemma coe_eq_zero_of_level_one (f : CuspForm (Gamma0 1) 2) : (f : ℍ → ℂ) = 0 := by
  let g : ModularForm 𝒮ℒ 2 :=
    (ModularFormClass.modularForm f).copy (f : ℍ → ℂ) rfl coe_Gamma0_one.symm
  have hg : g = 0 := rank_zero_iff_forall_zero.mp ModularForm.levelOne_weight_two_rank_zero g
  funext τ
  have h : g τ = 0 := by rw [hg]; rfl
  exact h

lemma modularFormAn_one {N : ℕ} (hN : 0 < N) (f : CuspForm (Gamma0 N) 2) :
    ModularityConjecture.modularFormAn 1 f = 0 := by
  unfold ModularityConjecture.modularFormAn
  rcases Nat.lt_or_ge N 2 with h | h
  · obtain rfl : N = 1 := by omega
    rw [coe_eq_zero_of_level_one f, qExpansion_zero]
    simp
  · exact coeff_one_of_two_le h f

end OMA

theorem OMA.disproof : ¬ (type_of% @ModularityConjecture.modularity_conjecture) := by
  intro h
  let E : WeierstrassCurve ℚ := ⟨0, 0, 0, -1, 0⟩
  have : E.IsElliptic := ⟨by
    rw [isUnit_iff_ne_zero]
    simp [E, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]⟩
  obtain ⟨N, f, hf, -⟩ := h E
  have h1 := hf.1
  rw [OMA.modularFormAn_one N.pos f] at h1
  exact zero_ne_one h1
