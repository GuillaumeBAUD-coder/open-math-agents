import Mathlib

namespace OMA.S_opg_what_is_the_homotopy_type_of_the_group_of_diffeomorphisms_of_the_4_sphere

open scoped ContDiff

abbrev Space := EuclideanSpace ℝ (Fin 4)

abbrev Disk := ↥(Metric.closedBall (0 : Space) 1)

abbrev Interval := ↥(Set.Icc (0 : ℝ) 1)

/-- A disk diffeomorphism fixed on a neighborhood of the boundary, extended by the identity. -/
structure RelativeDiffeomorphism where
  equiv : Space ≃ Space
  smooth : ContDiff ℝ ∞ (equiv : Space → Space)
  smoothInverse : ContDiff ℝ ∞ (equiv.symm : Space → Space)
  fixesCollar : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ x : Space, r ≤ ‖x‖ → equiv x = x

/-- Joint continuity of all spatial derivatives on the compact disk is C∞ family continuity. -/
def IsContinuousFamily {X : Type} [TopologicalSpace X] (F : X → RelativeDiffeomorphism) : Prop :=
  ∀ k : ℕ, Continuous (fun p : X × Disk =>
    iteratedFDeriv ℝ k ((F p.1).equiv : Space → Space) (p.2 : Space))

/-- A homotopy of a pointwise power of a loop to the identity, relative to both endpoints. -/
def ContractsPower (loop : Interval → RelativeDiffeomorphism) (n : ℕ) : Prop :=
  ∃ H : Interval × Interval → RelativeDiffeomorphism, IsContinuousFamily H ∧
    (∀ t : Interval, ∀ x : Space,
      (H (0, t)).equiv x = (((loop t).equiv : Space → Space)^[n]) x) ∧
    (∀ t : Interval, (H (1, t)).equiv = Equiv.refl Space) ∧
    (∀ s : Interval, (H (s, 0)).equiv = Equiv.refl Space ∧
      (H (s, 1)).equiv = Equiv.refl Space)

/-- The fundamental group of the boundary-relative diffeomorphism group of the
4-disk contains an element of infinite order. -/
theorem main :
    ∃ loop : Interval → RelativeDiffeomorphism,
      IsContinuousFamily loop ∧
      (loop 0).equiv = Equiv.refl Space ∧ (loop 1).equiv = Equiv.refl Space ∧
      ∀ n : ℕ, 0 < n → ¬ ContractsPower loop n := by
  sorry

end OMA.S_opg_what_is_the_homotopy_type_of_the_group_of_diffeomorphisms_of_the_4_sphere
