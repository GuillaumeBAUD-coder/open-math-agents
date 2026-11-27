import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1_H4_R1
import Mathlib

/-! The sign of the length of a word is unchanged by removing adjacent
inverse letters. Equivalently the homomorphism which sends every generator
to minus one annihilates every even-length relation. -/
theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1_H4_R1.H3 := by
  intro k w hk hw htriv
  let f : Fin k → ℤˣ := fun _ => -1
  have rel : ∀ r ∈ ({FreeGroup.mk w} : Set (FreeGroup (Fin k))), FreeGroup.lift f r = 1 := by
    rintro r (rfl : r = FreeGroup.mk w)
    rw [FreeGroup.lift_mk]
    have hs (x : Fin k × Bool) : (cond x.2 (f x.1) (f x.1)⁻¹) = -1 := by
      rcases x with ⟨i,b⟩
      cases b <;> simp [f]
    simp_rw [hs]
    simp [hw, pow_mul]
  let g := PresentedGroup.toGroup rel
  let j : Fin k := ⟨0,hk⟩
  have eq : (PresentedGroup.of j : PresentedGroup ({FreeGroup.mk w} : Set (FreeGroup (Fin k)))) = 1 :=
    htriv.elim _ _
  have e := congrArg g eq
  change PresentedGroup.toGroup rel (PresentedGroup.of j) = PresentedGroup.toGroup rel 1 at e
  rw [PresentedGroup.toGroup.of, map_one] at e
  exact (by decide : (-1 : ℤˣ) ≠ 1) e

