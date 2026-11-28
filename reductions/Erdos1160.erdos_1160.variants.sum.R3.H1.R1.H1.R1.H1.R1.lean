import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H1_R1
import Mathlib.GroupTheory.Commutator.Basic

-- Reduction Erdos1160.erdos_1160.variants.sum.R3.H1.R1.H1.R1.H1.R1 of step Erdos1160.erdos_1160.variants.sum.R3.H1.R1.H1.R1.H1
-- Credit: @wojcik-kacper

/-!
Partition the central Frattini-rank strip of 2-groups of order 2^m into three disjoint
populations by the binary class-two obstruction K = [F, G] F^2 (where F = G^2), following
Su and Xia (arXiv:2610.11092):

* H1 (roots on the strip): K = ⊥.
* H2 (bounded-width non-roots on the strip): K ≠ ⊥ and |F| ≤ 2^192000 * |K|.
* H3 (wide non-roots on the strip): K ≠ ⊥ and 2^192000 * |K| < |F|.

Closing these three sub-steps closes R3.H1.R1.H1.R1.H1, which is the final open step of R3.H1.R1.H1.
-/

open Filter CategoryTheory Erdos1160
open scoped commutatorElement

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H1_R1_H1_R1

/-- Central-strip roots: groups of order 2^m in the Frattini-rank strip with K = ⊥. -/
def H1 : Prop := ∀ᶠ m : ℕ in atTop,
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2 ^ m}
  let B : Set A := {c |
    let G := c.property.choose
    let d := Nat.log 2 (frattini G).index
    let F := Subgroup.closure (Set.range (fun x : G => x * x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val * x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val, z.2⁆))
    1000 * (2 * m - 3 * d) ≤ 2 * d ∧ 1000 * (3 * d - 2 * m) ≤ 2 * d ∧ K = ⊥}
  (3 * B.ncard) ^ 27 ≤ 2 ^ (2 * m ^ 3 + 216 * (m + 1) ^ 2)

/-- Central-strip bounded-width non-roots: K ≠ ⊥ and |F| ≤ 2^192000 * |K|. -/
def H2 : Prop := ∀ᶠ m : ℕ in atTop,
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2 ^ m}
  let B : Set A := {c |
    let G := c.property.choose
    let d := Nat.log 2 (frattini G).index
    let F := Subgroup.closure (Set.range (fun x : G => x * x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val * x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val, z.2⁆))
    1000 * (2 * m - 3 * d) ≤ 2 * d ∧ 1000 * (3 * d - 2 * m) ≤ 2 * d ∧
      K ≠ ⊥ ∧ Nat.card F ≤ 2 ^ 192000 * Nat.card K}
  (3 * B.ncard) ^ 27 ≤ 2 ^ (2 * m ^ 3 + 216 * (m + 1) ^ 2)

/-- Central-strip wide non-roots: K ≠ ⊥ and 2^192000 * |K| < |F|. -/
def H3 : Prop := ∀ᶠ m : ℕ in atTop,
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2 ^ m}
  let B : Set A := {c |
    let G := c.property.choose
    let d := Nat.log 2 (frattini G).index
    let F := Subgroup.closure (Set.range (fun x : G => x * x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val * x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val, z.2⁆))
    1000 * (2 * m - 3 * d) ≤ 2 * d ∧ 1000 * (3 * d - 2 * m) ≤ 2 * d ∧
      K ≠ ⊥ ∧ 2 ^ 192000 * Nat.card K < Nat.card F}
  (3 * B.ncard) ^ 27 ≤ 2 ^ (2 * m ^ 3 + 216 * (m + 1) ^ 2)

lemma union3_pow_bound {α : Type*} {C B1 B2 B3 : Set α} {u : ℕ}
    (hcov : C = B1 ∪ B2 ∪ B3)
    (h1 : (3 * B1.ncard) ^ 27 ≤ u)
    (h2 : (3 * B2.ncard) ^ 27 ≤ u)
    (h3 : (3 * B3.ncard) ^ 27 ≤ u) :
    C.ncard ^ 27 ≤ u := by
  have hsum : C.ncard ≤ B1.ncard + B2.ncard + B3.ncard := by
    rw [hcov]
    exact (Set.ncard_union_le (B1 ∪ B2) B3).trans
      (Nat.add_le_add_right (Set.ncard_union_le B1 B2) _)
  let M := max (max B1.ncard B2.ncard) B3.ncard
  have hle : C.ncard ≤ 3 * M := by
    have hM1 : B1.ncard ≤ M := (le_max_left _ _).trans (le_max_left _ _)
    have hM2 : B2.ncard ≤ M := (le_max_right _ _).trans (le_max_left _ _)
    have hM3 : B3.ncard ≤ M := le_max_right _ _
    omega
  have hM : (3 * M) ^ 27 ≤ u := by
    have hcases : M = B1.ncard ∨ M = B2.ncard ∨ M = B3.ncard := by
      dsimp only [M]
      omega
    rcases hcases with e | e | e <;> rw [e]
    · exact h1
    · exact h2
    · exact h3
  exact (Nat.pow_le_pow_left hle 27).trans hM

theorem main : H1 → H2 → H3 → OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H1_R1.H1 := by
  intro hroots hnarrow hwide
  filter_upwards [hroots, hnarrow, hwide] with m hr hn hw
  let A : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = 2 ^ m}
  let C : Set A := {c |
    let d := Nat.log 2 (frattini c.property.choose).index
    1000 * (2 * m - 3 * d) ≤ 2 * d ∧ 1000 * (3 * d - 2 * m) ≤ 2 * d}
  let B1 : Set A := {c |
    let G := c.property.choose
    let d := Nat.log 2 (frattini G).index
    let F := Subgroup.closure (Set.range (fun x : G => x * x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val * x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val, z.2⁆))
    1000 * (2 * m - 3 * d) ≤ 2 * d ∧ 1000 * (3 * d - 2 * m) ≤ 2 * d ∧ K = ⊥}
  let B2 : Set A := {c |
    let G := c.property.choose
    let d := Nat.log 2 (frattini G).index
    let F := Subgroup.closure (Set.range (fun x : G => x * x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val * x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val, z.2⁆))
    1000 * (2 * m - 3 * d) ≤ 2 * d ∧ 1000 * (3 * d - 2 * m) ≤ 2 * d ∧
      K ≠ ⊥ ∧ Nat.card F ≤ 2 ^ 192000 * Nat.card K}
  let B3 : Set A := {c |
    let G := c.property.choose
    let d := Nat.log 2 (frattini G).index
    let F := Subgroup.closure (Set.range (fun x : G => x * x))
    let K := Subgroup.closure (Set.range (fun x : F => x.val * x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val, z.2⁆))
    1000 * (2 * m - 3 * d) ≤ 2 * d ∧ 1000 * (3 * d - 2 * m) ≤ 2 * d ∧
      K ≠ ⊥ ∧ 2 ^ 192000 * Nat.card K < Nat.card F}
  have hcov : C = B1 ∪ B2 ∪ B3 := by
    ext c
    simp only [Set.mem_union, C, B1, B2, B3, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hs1, hs2⟩
      set G := c.property.choose
      set F := Subgroup.closure (Set.range (fun x : G => x * x))
      set K := Subgroup.closure (Set.range (fun x : F => x.val * x.val) ∪
        Set.range (fun z : F × G => ⁅z.1.val, z.2⁆))
      by_cases hK : K = ⊥
      · exact Or.inl (Or.inl ⟨hs1, hs2, hK⟩)
      · by_cases hF : Nat.card F ≤ 2 ^ 192000 * Nat.card K
        · exact Or.inl (Or.inr ⟨hs1, hs2, hK, hF⟩)
        · exact Or.inr ⟨hs1, hs2, hK, lt_of_not_ge hF⟩
    · rintro ((⟨hs1, hs2, _⟩ | ⟨hs1, hs2, _, _⟩) | ⟨hs1, hs2, _, _⟩) <;> exact ⟨hs1, hs2⟩
  exact union3_pow_bound hcov hr hn hw

end OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H1_R1_H1_R1
