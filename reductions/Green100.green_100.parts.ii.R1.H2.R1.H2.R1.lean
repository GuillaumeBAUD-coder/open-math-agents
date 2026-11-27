import OMAReductions.R_Green100_green_100_parts_ii_R1_H2_R1

/-! A group action detecting the central involution, and the finite presentation to which it applies. -/
-- Problem: Green100.green_100.parts.ii.R1.H2.R1.H2
-- Credit: @sobrien032
-- Source for the group and twisting relation: Gao–Yu–Zhi, arXiv:2610.10248v2, §§4–5.

namespace OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1

open Green100 Filter
open scoped Topology commutatorElement

/-- A point stabilizer and a moved translate give two copies agreeing on the stabilizer
and an involution detected by a representation of the twisting relation. -/
def H1 : Prop :=
  ∀ (Q : Type) [Group Q] (X : Type) [MulAction Q X] (x : X) (h t : Q),
    h • x = x → h • (t • x) ≠ t • x →
    ∃ (G : Type) (_ : Group G) (a b : Q →* G) (j z : G),
      (∀ q, q • x = x → a q = b q) ∧ j ≠ 1 ∧ j ^ 2 = 1 ∧
      (∀ q, Commute j (a q) ∧ Commute j (b q)) ∧ Commute j z ∧
      (let w := ⁅a h, b t * (a t)⁻¹⁆; z * w * z⁻¹ = w * j)

/-- A finite presentation realizing these relations whose marked word vanishes in matrix quotients. -/
def H2 : Prop :=
  ∃ (R : Finset (List (Fin 74 × Bool))) (Q : Type) (_ : Group Q)
    (X : Type) (_ : MulAction Q X) (x : X) (h t : Q),
    let S := FreeGroup.mk '' (↑R : Set (List (Fin 74 × Bool)))
    let J := PresentedGroup.mk S (FreeGroup.of (72 : Fin 74))
    h • x = x ∧ h • (t • x) ≠ t • x ∧
    (∀ (G : Type) [Group G] (a b : Q →* G) (j z : G),
      (∀ q, q • x = x → a q = b q) → j ^ 2 = 1 →
      (∀ q, Commute j (a q) ∧ Commute j (b q)) → Commute j z →
      (let w := ⁅a h, b t * (a t)⁻¹⁆; z * w * z⁻¹ = w * j) →
      ∃ f : PresentedGroup S →* G, f J = j) ∧
    ∀ (d : ℕ → ℕ), (∀ i, 0 < d i) →
      let U := (i : ℕ) → Matrix.unitaryGroup (Fin (d i)) ℂ
      let N := Subgroup.normalClosure {v : U |
        Tendsto (fun i => hsDist (v i) 1) (hyperfilter ℕ) (𝓝 0)}
      ∀ ρ : PresentedGroup S →* U ⧸ N, ρ J = 1

theorem main : H1 → H2 → OMA.R_Green100_green_100_parts_ii_R1_H2_R1.H2 := by
  intro action presentation
  obtain ⟨R, Q, groupQ, X, actionX, x, h, t, fixes, moves, lift, collapses⟩ := presentation
  obtain ⟨G, groupG, a, b, j, z, agree, survives, inv, central, centralZ, twist⟩ :=
    action Q X x h t fixes moves
  obtain ⟨f, detects⟩ := lift G a b j z agree inv central centralZ twist
  refine ⟨R, ?_, collapses⟩
  intro trivial
  exact survives (detects.symm.trans ((congrArg f trivial).trans f.map_one))

end OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1
