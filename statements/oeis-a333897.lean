import Mathlib

/-!
# Four-vertex loopless multigraphs with a bound on every degree

Each graph records the two edge multiplicities in each of the opposite
pairs (01,23), (02,13), (03,12). Vertex permutations act simultaneously
on the two indices of its adjacency matrix. Isolated vertices and zero
edge multiplicities are allowed. A333897 counts isomorphism classes
under this action by their maximum permitted degree.

Sources: https://oeis.org/A333897 and the general array
https://oeis.org/A333893. The generating function and recurrence were
conjectured by Colin Barker, April 10, 2020.
-/

namespace OMA.S_oeis_a333897

abbrev Triple (α : Type) := α × α × α
abbrev Graph := Triple (ℕ × ℕ)

def edge (g : Graph) : Fin 4 → Fin 4 → ℕ :=
  ![![0,g.1.1,g.2.1.1,g.2.2.1], ![g.1.1,0,g.2.2.2,g.2.1.2],
    ![g.2.1.1,g.2.2.2,0,g.1.2], ![g.2.2.1,g.2.1.2,g.1.2,0]]

def maxDegree (g : Graph) : ℕ :=
  max (max (g.1.1+g.2.1.1+g.2.2.1) (g.1.1+g.2.1.2+g.2.2.2))
    (max (g.1.2+g.2.1.1+g.2.2.2) (g.1.2+g.2.1.2+g.2.2.1))

def Iso (g h : Graph) : Prop :=
  ∃ p : Equiv.Perm (Fin 4), ∀ i j, edge g i j = edge h (p i) (p j)

def isoSetoid (n : ℕ) : Setoid {g : Graph // maxDegree g ≤ n} where
  r g h := Iso g.val h.val
  iseqv := {
    refl := fun _ => ⟨Equiv.refl _,fun _ _ => rfl⟩
    symm := by
      rintro a b ⟨p,h⟩
      exact ⟨p.symm,fun i j => by simpa using (h (p.symm i) (p.symm j)).symm⟩
    trans := by
      rintro a b c ⟨p,h⟩ ⟨q,k⟩
      exact ⟨p.trans q,fun i j => (h i j).trans (k (p i) (p j))⟩ }

noncomputable def a (n : ℕ) : ℕ := Nat.card (Quotient (isoSetoid n))

open PowerSeries

theorem main :
    ((1-X)^7*(1+X)^3*(1+X+X^2)^2*PowerSeries.mk (fun n => (a n : ℤ)) =
      (1+X+X^2+X^3+X^4)*(1+X^2+2*X^3+X^4+X^6)) ∧
    (∀ n : ℕ, 13<n → (a n : ℤ)=
      2*(a (n-1):ℤ)+2*a (n-2)-4*a (n-3)-4*a (n-4)+2*a (n-5)+9*a (n-6)-
      9*a (n-8)-2*a (n-9)+4*a (n-10)+4*a (n-11)-2*a (n-12)-
      2*a (n-13)+a (n-14)) := by
  sorry

end OMA.S_oeis_a333897
