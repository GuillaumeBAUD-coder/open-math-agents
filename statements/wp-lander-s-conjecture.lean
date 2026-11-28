import Mathlib

/-!
# Lander's conjecture (on abelian difference sets)

Source: https://en.wikipedia.org/wiki/Difference_set#Ryser_and_Lander_conjectures
Credit: @joshuadc11

If a finite abelian group `G` of order `v` contains a `(v, k, λ)`-difference set of order
`n = k - λ > 0`, and a prime `p` divides both `v` and `n`, then the Sylow `p`-subgroup of `G`
is not cyclic.

Formalization notes:
- A subset `D : Finset G` is a difference set with parameter `λ` if every non-identity element
  `g ≠ 1` of `G` has exactly `λ` representations `g = d₁ * d₂⁻¹` with `d₁, d₂ ∈ D`.
- Its order is `n = D.card - λ`. Requiring `0 < n` with `p ∣ n` and `p` prime automatically
  ensures `n ≥ 2` and rules out trivial difference sets (`∅`, `G`, singletons, complements of
  singletons).
- Since `G` is abelian, its Sylow `p`-subgroup `P : Sylow p G` is unique; non-cyclicity is
  stated as `∀ P : Sylow p G, ¬ IsCyclic P`.
-/

namespace OMA.S_wp_lander_s_conjecture

/-- `D` is a difference set with parameter `λ` in a finite group `G`. -/
def IsDifferenceSet {G : Type*} [Group G] [DecidableEq G] (D : Finset G) (lam : ℕ) : Prop :=
  ∀ g : G, g ≠ 1 → ((D ×ˢ D).filter (fun x => x.1 * x.2⁻¹ = g)).card = lam

theorem main :
    ∀ (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G]
      (D : Finset G) (lam p : ℕ) [Fact p.Prime],
      IsDifferenceSet D lam →
      let n := D.card - lam
      0 < n →
      p ∣ Fintype.card G →
      p ∣ n →
      ∀ P : Sylow p G, ¬ IsCyclic P := by
  sorry

end OMA.S_wp_lander_s_conjecture
