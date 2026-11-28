import Mathlib

/-!
# MathOverflow 129414

Source: https://mathoverflow.net/questions/129414
-/

namespace OMA.S_mo_129414

/-- Every conjugation on the kernel is induced by an element of the kernel. -/
def TrivialOuterAction {E G : Type} [Group E] [Group G] (p : E →* G) : Prop :=
  ∀ e : E, ∃ k ∈ p.ker, ∀ n ∈ p.ker, e * n * e⁻¹ = k * n * k⁻¹

def CentralKernel {E G : Type} [Group E] [Group G] (p : E →* G) : Prop :=
  ∀ n ∈ p.ker, ∀ e : E, n * e = e * n

def Splits {E G : Type} [Group E] [Group G] (p : E →* G) : Prop :=
  ∃ s : G →* E, ∀ g : G, p (s g) = g

/-- One group extension whose outer action is trivial, whose kernel is
noncentral, and which admits no group-homomorphism section. -/
def HasExample (E G : Type) [Group E] [Group G] : Prop :=
  ∃ p : E →* G, Function.Surjective p ∧ TrivialOuterAction p ∧
    ¬ CentralKernel p ∧ ¬ Splits p

theorem main : ∃ (E G : Type) (eGroup : Group E) (gGroup : Group G),
    @HasExample E G eGroup gGroup := by
  sorry

end OMA.S_mo_129414
