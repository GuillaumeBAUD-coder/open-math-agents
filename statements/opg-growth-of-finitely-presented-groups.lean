import Mathlib

/-!
# Growth of finitely presented groups

Source: https://www.openproblemgarden.org/op/growth_of_finitely_presented_groups
Credit: @lzvxck

The source: does there exist a finitely presented group of intermediate growth? A finitely
generated group has intermediate growth if its growth rate (for every finite generating set)
is subexponential but superpolynomial.

The existence (affirmative) form is stated. Conventions:
* Finitely presented is Mathlib's `Group.IsFinitelyPresented`.
* For a finite generating set `S`, the growth function `γ_S(n)` is the number of elements of
  `G` that are products of at most `n` elements of `S ∪ S⁻¹`.
* Superpolynomial: there are no `C` and `d` with `γ_S(n) ≤ C n^d` for all `n ≥ 1`.
* Subexponential: `γ_S(n)^{1/n} → 1`, written as: for every `ε > 0`, eventually
  `γ_S(n) ≤ (1 + ε)^n` (the limit of `γ_S(n)^{1/n}` exists, as `γ_S` is submultiplicative,
  and is at least `1`).
-/

namespace OMA.S_opg_growth_of_finitely_presented_groups

/-- The growth function of `G` with respect to `S`: the number of elements that are products
of at most `n` elements of `S ∪ S⁻¹`. -/
noncomputable def growth {G : Type*} [Group G] (S : Set G) (n : ℕ) : ℕ :=
  {g : G | ∃ l : List G, l.length ≤ n ∧ (∀ s ∈ l, s ∈ S ∨ s⁻¹ ∈ S) ∧ l.prod = g}.ncard

/-- The growth of `G` with respect to `S` is intermediate: superpolynomial and
subexponential. -/
def IsIntermediateGrowth {G : Type*} [Group G] (S : Set G) : Prop :=
  (¬ ∃ (C : ℝ) (d : ℕ), ∀ n : ℕ, 1 ≤ n → (growth S n : ℝ) ≤ C * (n : ℝ) ^ d) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in Filter.atTop, (growth S n : ℝ) ≤ (1 + ε) ^ n

/-- **Growth of finitely presented groups (Adyan).** There is a finitely presented group of
intermediate growth: for every finite generating set its growth is superpolynomial and
subexponential. -/
theorem main : ∃ (G : Type) (_ : Group G), Group.IsFinitelyPresented G ∧
    ∀ S : Set G, S.Finite → Subgroup.closure S = ⊤ → IsIntermediateGrowth S := by
  sorry

end OMA.S_opg_growth_of_finitely_presented_groups
