import OMAStatements.S_mo_217656
import Mathlib

namespace MO217656Aux
def A : OMA.S_mo_217656.Selection 3 2 := ⟨{0, 1}, by decide⟩
def B : OMA.S_mo_217656.Selection 3 2 := ⟨{0, 2}, by decide⟩
def C : OMA.S_mo_217656.Selection 3 2 := ⟨{1, 2}, by decide⟩
lemma hA0 : (0 : Fin 3) ∈ A.val := by decide
lemma hA1 : (1 : Fin 3) ∈ A.val := by decide
lemma hB0 : (0 : Fin 3) ∈ B.val := by decide
lemma hB2 : (2 : Fin 3) ∈ B.val := by decide
lemma hC1 : (1 : Fin 3) ∈ C.val := by decide
lemma hC2 : (2 : Fin 3) ∈ C.val := by decide
lemma memB : ∀ v : Fin 3, v ∈ B.val → v = 0 ∨ v = 2 := by decide
end MO217656Aux

open MO217656Aux in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_217656.main) := by
  intro h
  obtain ⟨maps, -, hfix, hcoc⟩ := h 3 2 (by norm_num)
  have e1 := hfix A B 0 hA0 hB0
  have e2 := hfix B C 2 hB2 hC2
  have e3 := hfix A C 1 hA1 hC1
  have e4 := hcoc B C A ⟨1, hA1⟩
  rw [e3] at e4
  obtain ⟨x, hx⟩ : ∃ x, maps A B ⟨1, hA1⟩ = x := ⟨_, rfl⟩
  rw [hx] at e4
  obtain ⟨v, hv⟩ := x
  rcases memB v hv with rfl | rfl
  · have h10 : maps A B ⟨1, hA1⟩ = maps A B ⟨0, hA0⟩ := by rw [hx, e1]
    have h10' := (maps A B).injective h10
    have h10'' : (1 : Fin 3) = 0 := congrArg Subtype.val h10'
    exact absurd h10'' (by decide)
  · have h21 := e2.symm.trans e4
    have h21' : (2 : Fin 3) = 1 := congrArg Subtype.val h21
    exact absurd h21' (by decide)
