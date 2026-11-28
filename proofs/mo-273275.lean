import OMAStatements.S_mo_273275
import Mathlib

/-!
MathOverflow 273275: Darij Grinberg's example: on Q[X] with F_k = X^k Q[X] (expansion E_k = Q X^k), the map p -> p(X + X^2) preserves the filtration and is the identity on gr, but X is not in its image.
-/

namespace OMA.P273275

open Polynomial

/-- The filtration `F_k = X^k ℚ[X]`. -/
noncomputable def F (k : ℕ) : Submodule ℚ ℚ[X] := (Ideal.span {(X : ℚ[X]) ^ k}).restrictScalars ℚ

theorem mem_F {k : ℕ} {p : ℚ[X]} : p ∈ F k ↔ X ^ k ∣ p := by
  simp [F, Submodule.restrictScalars_mem, Ideal.mem_span_singleton]

/-- The expansion `E_k = ℚ X^k`. -/
noncomputable def E (k : ℕ) : Submodule ℚ ℚ[X] := ℚ ∙ (basisMonomials ℚ k)

theorem basis_eq (k : ℕ) : basisMonomials ℚ k = X ^ k := by
  simp [coe_basisMonomials, X_pow_eq_monomial]

theorem F_zero : F 0 = ⊤ := by
  ext p; simp [mem_F]

theorem F_anti : Antitone F := by
  intro k l hkl p hp
  rw [mem_F] at hp ⊢
  exact (pow_dvd_pow X hkl).trans hp

theorem X_dvd_sub_C (q : ℚ[X]) : X ∣ q - C (q.coeff 0) := by
  rw [X_dvd_iff]; simp

theorem E_props (k : ℕ) : E k ≤ F k ∧ E k ⊔ F (k + 1) = F k ∧ Disjoint (E k) (F (k + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [E, Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_F, basis_eq]
  · apply le_antisymm
    · exact sup_le (by rw [E, Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
        mem_F, basis_eq]) (F_anti (Nat.le_succ k))
    · intro p hp
      rw [mem_F] at hp
      obtain ⟨q, rfl⟩ := hp
      rw [Submodule.mem_sup]
      refine ⟨q.coeff 0 • basisMonomials ℚ k, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _),
        X ^ k * (q - C (q.coeff 0)), ?_, ?_⟩
      · rw [mem_F, pow_succ]
        exact mul_dvd_mul_left _ (X_dvd_sub_C q)
      · rw [basis_eq, smul_eq_C_mul]; ring
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    rw [E, Submodule.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    rw [mem_F, basis_eq, smul_eq_C_mul, pow_succ, mul_comm (C c)] at hx'
    have h1 : X ∣ C c := (mul_dvd_mul_iff_left (pow_ne_zero k X_ne_zero)).1 hx'
    rw [X_dvd_iff, coeff_C_zero] at h1
    rw [basis_eq, h1, zero_smul]

theorem E_internal : DirectSum.IsInternal E := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨(basisMonomials ℚ).linearIndependent.iSupIndep_span_singleton, ?_⟩
  show (⨆ k, ℚ ∙ basisMonomials ℚ k) = ⊤
  rw [← Submodule.span_range_eq_iSup, (basisMonomials ℚ).span_eq]

/-- The algebra map `x ↦ x + x²` (Darij Grinberg's example), as a `ℚ`-linear map. -/
noncomputable def φ : ℚ[X] →ₗ[ℚ] ℚ[X] := (aeval (X + X ^ 2 : ℚ[X])).toLinearMap

theorem φ_apply (p : ℚ[X]) : φ p = p.comp (X + X ^ 2) := rfl

theorem r_pow (k : ℕ) : (X + X ^ 2 : ℚ[X]) ^ k = X ^ k * (1 + X) ^ k := by
  rw [← mul_pow]; ring

theorem comp_coeff_zero (q : ℚ[X]) : (q.comp (X + X ^ 2)).coeff 0 = q.coeff 0 := by
  simp [coeff_zero_eq_eval_zero, eval_comp]

theorem disproof :
    ¬ ∀ (K V W : Type) [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
      (FV : ℕ → Submodule K V) (FW : ℕ → Submodule K W),
      FV 0 = ⊤ → Antitone FV → FW 0 = ⊤ → Antitone FW →
      (∃ E : ℕ → Submodule K V, (∀ k, E k ≤ FV k ∧ E k ⊔ FV (k + 1) = FV k ∧
        Disjoint (E k) (FV (k + 1))) ∧ DirectSum.IsInternal E) →
      (∃ E : ℕ → Submodule K W, (∀ k, E k ≤ FW k ∧ E k ⊔ FW (k + 1) = FW k ∧
        Disjoint (E k) (FW (k + 1))) ∧ DirectSum.IsInternal E) →
      ∀ φ : V →ₗ[K] W, (∀ k, ∀ v ∈ FV k, φ v ∈ FW k) →
        (∀ k, ∀ v ∈ FV k, φ v ∈ FW (k + 1) → v ∈ FV (k + 1)) →
        (∀ k, ∀ w ∈ FW k, ∃ v ∈ FV k, w - φ v ∈ FW (k + 1)) →
        Function.Bijective φ := by
  intro h
  have hb := h ℚ ℚ[X] ℚ[X] F F F_zero F_anti F_zero F_anti ⟨E, E_props, E_internal⟩
    ⟨E, E_props, E_internal⟩ φ
    (by
      intro k v hv
      rw [mem_F] at hv ⊢
      obtain ⟨q, rfl⟩ := hv
      rw [φ_apply, mul_comp, X_pow_comp, r_pow, mul_assoc]
      exact dvd_mul_right _ _)
    (by
      intro k v hv hv'
      rw [mem_F] at hv hv' ⊢
      obtain ⟨q, rfl⟩ := hv
      rw [φ_apply, mul_comp, X_pow_comp, r_pow, mul_assoc, pow_succ] at hv'
      have h1 : X ∣ (1 + X) ^ k * q.comp (X + X ^ 2) :=
        (mul_dvd_mul_iff_left (pow_ne_zero k X_ne_zero)).1 hv'
      rw [X_dvd_iff, mul_coeff_zero, comp_coeff_zero] at h1
      have h2 : ((1 + X : ℚ[X]) ^ k).coeff 0 = 1 := by
        simp [coeff_zero_eq_eval_zero]
      rw [h2, one_mul] at h1
      rw [pow_succ]
      exact mul_dvd_mul_left _ (X_dvd_iff.2 h1))
    (by
      intro k w hw
      rw [mem_F] at hw
      obtain ⟨q, rfl⟩ := hw
      refine ⟨C (q.coeff 0) * X ^ k, by rw [mem_F]; exact dvd_mul_left _ _, ?_⟩
      rw [mem_F, φ_apply, mul_comp, C_comp, X_pow_comp, r_pow]
      have : X ^ k * q - C (q.coeff 0) * (X ^ k * (1 + X) ^ k) =
          X ^ k * (q - C (q.coeff 0) * (1 + X) ^ k) := by ring
      rw [this, pow_succ]
      refine mul_dvd_mul_left _ ?_
      rw [X_dvd_iff, coeff_sub, coeff_C_mul]
      simp [coeff_zero_eq_eval_zero])
  obtain ⟨p, hp⟩ := hb.2 X
  rw [φ_apply] at hp
  have hd := congrArg natDegree hp
  rw [natDegree_comp, natDegree_X] at hd
  have h2 : (X + X ^ 2 : ℚ[X]).natDegree = 2 := by compute_degree!
  rw [h2] at hd
  omega

end OMA.P273275

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_273275.main) := OMA.P273275.disproof
