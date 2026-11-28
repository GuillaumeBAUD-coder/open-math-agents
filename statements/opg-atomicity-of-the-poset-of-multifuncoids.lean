import Mathlib

/-!
# Atomicity of the poset of completary multifuncoids

Source: https://www.openproblemgarden.org/op/atomicity_of_the_poset_of_multifuncoids
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Porton): for every set `℧` and every index set `n`, the poset of completary
multifuncoids of the form `(𝒫℧)ⁿ` is atomic and atomistic.

Conventions (from the source):
* A completary multifuncoid of the form `(𝒫℧)ⁿ` is a set `f` of families `L : n → 𝒫℧` such that
  `L₀ ∪ L₁ ∈ f ↔ ∃ c : n → {0, 1}, (fun i => L_{c i} i) ∈ f` for all `L₀, L₁` (the union is
  componentwise), and `L ∉ f` whenever some `L i = ∅`.
* The poset is ordered by inclusion; its least element is `∅`. Atomic: every nonempty element
  contains an atom. Atomistic: every element is the join of the atoms below it, i.e. it is below
  every element that contains all atoms below it.
* `℧` is a type `U` and `n` a type `ι`.
-/

namespace OMA.S_opg_atomicity_of_the_poset_of_multifuncoids

variable {U ι : Type}

/-- A completary multifuncoid of the form `(𝒫℧)ⁿ`. -/
def IsCompletary (f : Set (ι → Set U)) : Prop :=
  (∀ L₀ L₁ : ι → Set U, (L₀ ⊔ L₁) ∈ f ↔
      ∃ c : ι → Bool, (fun i => if c i then L₁ i else L₀ i) ∈ f) ∧
    ∀ L : ι → Set U, (∃ i, L i = ∅) → L ∉ f

/-- An atom of the poset of completary multifuncoids. -/
def IsAtom' (a : Set (ι → Set U)) : Prop :=
  IsCompletary a ∧ a ≠ ∅ ∧ ∀ g, IsCompletary g → g ⊆ a → g = ∅ ∨ g = a

theorem main :
    ∀ (U ι : Type),
      -- atomic
      (∀ f : Set (ι → Set U), IsCompletary f → f ≠ ∅ → ∃ a, IsAtom' a ∧ a ⊆ f) ∧
      -- atomistic
      (∀ f : Set (ι → Set U), IsCompletary f →
        ∀ g : Set (ι → Set U), IsCompletary g →
          (∀ a, IsAtom' a → a ⊆ f → a ⊆ g) → f ⊆ g) := by
  sorry

end OMA.S_opg_atomicity_of_the_poset_of_multifuncoids
