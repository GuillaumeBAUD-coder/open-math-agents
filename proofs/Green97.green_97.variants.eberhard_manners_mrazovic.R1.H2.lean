import OMAReductions.R_Green97_green_97_variants_eberhard_manners_mrazovic_R1
import Mathlib

/-! The map `(π₁, π₂) ↦ (π₁, π₂ ∘ π₁⁻¹)` identifies pairs of bijections whose sum is a
bijection with pairs (bijection, complete mapping): `π₁ i + π₂ i = x + σ x` at `x = π₁ i`.
There are `n!` bijections `Fin n ≃ ZMod n`. -/

namespace G97H2

lemma bij_iff {n : ℕ} (τ : Fin n ≃ ZMod n) (σ : Equiv.Perm (ZMod n)) :
    Function.Bijective (fun i => τ i + (τ.trans σ) i) ↔
      Function.Bijective (fun x => x + σ x) := by
  have e : (fun i => τ i + (τ.trans σ) i) = (fun x => x + σ x) ∘ τ := by
    funext i
    simp [Equiv.trans_apply]
  rw [e]
  constructor
  · intro h
    have h2 := h.comp τ.symm.bijective
    have e2 : ((fun x => x + σ x) ∘ τ) ∘ τ.symm = fun x => x + σ x := by
      funext x
      simp
    rwa [e2] at h2
  · intro h
    exact h.comp τ.bijective

/-- The normalization of pairs of bijections. -/
def normEquiv (n : ℕ) :
    {π : (Fin n ≃ ZMod n) × (Fin n ≃ ZMod n) // Function.Bijective fun i ↦ π.1 i + π.2 i} ≃
      (Fin n ≃ ZMod n) × {σ : Equiv.Perm (ZMod n) // Function.Bijective fun x ↦ x + σ x} where
  toFun π := (π.1.1, ⟨π.1.1.symm.trans π.1.2, by
    have h := π.2
    rw [← bij_iff π.1.1 (π.1.1.symm.trans π.1.2)]
    have e : π.1.1.trans (π.1.1.symm.trans π.1.2) = π.1.2 := by
      ext i
      simp
    rw [e]
    exact h⟩)
  invFun p := ⟨(p.1, p.1.trans p.2.1), (bij_iff p.1 p.2.1).mpr p.2.2⟩
  left_inv π := by
    rcases π with ⟨⟨τ, ρ⟩, h⟩
    apply Subtype.ext
    simp only
    ext i <;> simp
  right_inv p := by
    rcases p with ⟨τ, ⟨σ, h⟩⟩
    simp only [Prod.mk.injEq, true_and]
    apply Subtype.ext
    ext x
    simp

end G97H2

theorem OMA.solution : OMA.R_Green97_green_97_variants_eberhard_manners_mrazovic_R1.H2 := by
  intro n hn
  have : NeZero n := ⟨by omega⟩
  unfold Green97.numAdditiveTriples
  rw [Nat.card_congr (G97H2.normEquiv n), Nat.card_prod]
  congr 1
  rw [Nat.card_eq_fintype_card,
    Fintype.card_equiv (Fintype.equivOfCardEq (by rw [Fintype.card_fin, ZMod.card])),
    Fintype.card_fin]
