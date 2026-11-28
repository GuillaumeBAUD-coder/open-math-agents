import OMAStatements.S_mo_277756
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.FieldTheory.Separable
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.FinCases

/-!
The semisimple-part map is not even continuous. This formalizes the
August 2017 comments by Christian Remling and LSpice on the source page.
The two-by-two family [[t,1],[0,0]] is semisimple for nonzero t and
nilpotent at zero. Its semisimple part therefore has a discontinuous
upper-right entry. General existence and uniqueness below verify that
the statement characterizes the ordinary Jordan-Chevalley semisimple part.
-/

open scoped Matrix Matrix.Norms.Elementwise Polynomial

namespace OMA.S_mo_277756

theorem semisimplePart_unique {n : ℕ} {M S T : Matrix (Fin n) (Fin n) ℂ}
    (hS : IsSemisimplePart M S) (hT : IsSemisimplePart M T) : S = T := by
  apply Matrix.toLinAlgEquiv'.injective
  exact (Module.End.isNilpotent_isSemisimple_unique
    hS.2.1 hS.1 hT.2.1 hT.1 hS.2.2 hT.2.2 (by simp)).2

theorem semisimplePart_exists {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    ∃ S, IsSemisimplePart M S := by
  obtain ⟨N, hN, S, hS, hnil, hsemi, hsum⟩ :=
    Module.End.exists_isNilpotent_isSemisimple (f := Matrix.toLinAlgEquiv' M)
  refine ⟨Matrix.toLinAlgEquiv'.symm S, ?_⟩
  have hcomm : Commute N S :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hS
      (Algebra.commute_of_mem_adjoin_self hN).symm
  simpa only [IsSemisimplePart, AlgEquiv.apply_symm_apply, hsum,
    add_sub_cancel_right] using And.intro hsemi (And.intro hnil hcomm)

def family (t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![t, 1; 0, 0]

theorem family_sq (t : ℂ) : family t ^ 2 = t • family t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [family, pow_two, Matrix.mul_apply, Fin.sum_univ_two, smul_eq_mul]

theorem family_semisimple {t : ℂ} (ht : t ≠ 0) :
    Module.End.IsSemisimple (Matrix.toLinAlgEquiv' (family t)) := by
  have hcop : IsCoprime (Polynomial.X : ℂ[X])
      (Polynomial.X - Polynomial.C t) := by
    simpa using (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      (a := (0 : ℂ)) (b := t) (by simpa using (neg_ne_zero.mpr ht).isUnit))
  have hsf : Squarefree ((Polynomial.X : ℂ[X]) *
      (Polynomial.X - Polynomial.C t)) :=
    (Polynomial.separable_X.mul Polynomial.separable_X_sub_C hcop).squarefree
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsf
  have hsq : (Matrix.toLinAlgEquiv' (family t)) ^ 2 =
      t • Matrix.toLinAlgEquiv' (family t) := by
    simpa only [map_pow, map_smul] using congrArg Matrix.toLinAlgEquiv' (family_sq t)
  simp only [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
  rw [mul_sub, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one,
    ← pow_two, hsq, sub_self]

theorem family_zero_nilpotent : IsNilpotent (Matrix.toLinAlgEquiv' (family 0)) := by
  refine ⟨2, ?_⟩
  simpa only [map_pow, map_smul, zero_smul, map_zero] using
    congrArg Matrix.toLinAlgEquiv' (family_sq 0)

theorem semisimplePart_self {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : Module.End.IsSemisimple (Matrix.toLinAlgEquiv' M)) : IsSemisimplePart M M := by
  refine ⟨hM, ?_, ?_⟩
  · simp
  · simp [Commute]

theorem semisimplePart_zero {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : IsNilpotent (Matrix.toLinAlgEquiv' M)) : IsSemisimplePart M 0 := by
  simp only [IsSemisimplePart, map_zero, sub_zero]
  exact ⟨Module.End.isSemisimple_zero, hM, Commute.zero_right _⟩

theorem selector_family {σ : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ}
    (hσ : ∀ M, IsSemisimplePart M (σ M)) :
    σ (family 0) = 0 ∧ ∀ t : ℂ, t ≠ 0 → σ (family t) = family t := by
  constructor
  · exact semisimplePart_unique (hσ _) (semisimplePart_zero family_zero_nilpotent)
  · intro t ht
    exact semisimplePart_unique (hσ _) (semisimplePart_self (family_semisimple ht))

theorem selector_not_continuous
    {σ : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ}
    (hσ : ∀ M, IsSemisimplePart M (σ M)) : ¬ Continuous σ := by
  intro hc
  obtain ⟨h0, hne⟩ := selector_family hσ
  have hfamily : Continuous family := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fin_cases i <;> fin_cases j
    · exact continuous_id
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const
  have hcoord : Continuous (fun t : ℂ => σ (family t) (0 : Fin 2) (1 : Fin 2)) :=
    (continuous_apply 1).comp ((continuous_apply 0).comp (hc.comp hfamily))
  have heq : (fun t : ℂ => σ (family t) (0 : Fin 2) (1 : Fin 2)) =
      fun _ => (1 : ℂ) := by
    apply Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hcoord continuous_const
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
    exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) (hne t ht)
  have h01 := congrFun heq 0
  rw [h0] at h01
  exact zero_ne_one h01

end OMA.S_mo_277756

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_277756.main) := by
  intro h
  obtain ⟨σ, hσ, hhol⟩ := h 2
  exact OMA.S_mo_277756.selector_not_continuous hσ hhol.continuous
