import Mathlib

/-!
# Conditions for the inverse to be diagonally dominant

Source: https://mathoverflow.net/questions/103880 (Felix Goldberg, CC BY-SA 3.0).
Credit: @connoranderson

Use weak row diagonal dominance, with strict dominance corresponding to positive
margin. Cofactors give an exact test with no signs prescribed for the entries.
For A = I − F, a directly computable row-sum bound on F guarantees diagonal
dominance up to radius 1/2. The order-three family realizes the margin bound
at every radius below one, including radii above 1/2.
-/

namespace OMA.S_mo_103880
open Matrix Finset
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
noncomputable def rowSize {n : ℕ} (A : Mat n) (i : Fin n) : ℝ := ∑ j, |A i j|
noncomputable def margin {n : ℕ} (A : Mat n) (i : Fin n) : ℝ :=
  |A i i| - ∑ j ∈ univ.erase i, |A i j|
def dominant {n : ℕ} (A : Mat n) : Prop := ∀ i, 0 ≤ margin A i
def sharp (r : ℝ) : Mat 3 := !![0,r,0; 0,0,r; 0,r,0]

theorem main :
    (∀ n : ℕ, ∀ A : Mat n, A.det ≠ 0 →
      (dominant A⁻¹ ↔ ∀ i, (∑ j ∈ univ.erase i, |A.adjugate i j|) ≤ |A.adjugate i i|)) ∧
    (∀ n : ℕ, ∀ F : Mat n, ∀ r : ℝ, 0 ≤ r → r < 1 → (∀ i, rowSize F i ≤ r) →
      IsUnit (1-F) ∧
      (∀ i, (1-2*r)/(1-r) ≤ margin (1-F)⁻¹ i) ∧ (r ≤ 1/2 → dominant (1-F)⁻¹)) ∧
    (∀ r : ℝ, 0 ≤ r → r < 1 → (∀ i, rowSize (sharp r) i = r) ∧
      IsUnit (1-sharp r) ∧ margin (1-sharp r)⁻¹ 0 = (1-2*r)/(1-r)) := by
  sorry
end OMA.S_mo_103880
