import Mathlib.Data.Real.Basic
import Mathlib.SetTheory.Cardinal.Finite

namespace BolDistance

/-- Both translations are bijective, there is a two-sided identity, and the
operation satisfies the left Bol identity. -/
def IsLeftBolLoop {Q : Type} (op : Q → Q → Q) : Prop :=
  (∃ e : Q, ∀ x, op e x = x ∧ op x e = x) ∧
  (∀ x, Function.Bijective (op x)) ∧
  (∀ y, Function.Bijective (fun x => op x y)) ∧
  ∀ x y z, op x (op y (op x z)) = op (op x (op y x)) z

/-- An isomorphism is a relabeling that preserves every product. -/
def Isomorphic {Q : Type} (f g : Q → Q → Q) : Prop :=
  ∃ e : Q ≃ Q, ∀ x y, e (f x y) = g (e x) (e y)

/-- Number of ordered pairs on which two multiplication tables differ. -/
noncomputable def tableDistance {Q : Type} (f g : Q → Q → Q) : ℕ :=
  Nat.card {p : Q × Q // f p.1 p.2 ≠ g p.1 p.2}

end BolDistance

namespace OMA.S_wp_problems_in_loop_theory_and_quasigroup_theory_consider_generalizations_of_groups

open BolDistance

/-- Aleš Drápal's question at Loops '99 (Bol part): are finite Bol loops
quadratic in multiplication-table distance? We use the left Bol convention. -/
theorem main :
    ∃ α : ℝ, 0 < α ∧ ∀ (Q : Type) [Fintype Q] (f g : Q → Q → Q),
      IsLeftBolLoop f → IsLeftBolLoop g →
      (tableDistance f g : ℝ) < α * (Fintype.card Q : ℝ) ^ 2 →
      Isomorphic f g := by
  sorry

end OMA.S_wp_problems_in_loop_theory_and_quasigroup_theory_consider_generalizations_of_groups
