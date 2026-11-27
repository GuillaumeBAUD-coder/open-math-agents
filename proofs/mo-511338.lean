import OMAStatements.S_mo_511338
import Mathlib

/- Counterexample in the case k = 1, where the bound 2^(k-1) - 1 is 0: n = 2,
   F = {empty set, {0, 1}} (1-union-closed, with union [2]) and x = (1/2, 1/2).
   For either i the left side is x_i * w(empty) = 1/2 and the right side is w({0,1}) = 1/4. -/

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_511338.main) := by
  intro h
  let F : Finset (Finset (Fin 2)) := {∅, Finset.univ}
  have hk : OMA.S_mo_511338.KUnionClosed 1 F := by
    unfold OMA.S_mo_511338.KUnionClosed; decide
  have hsup : F.sup id = Finset.univ := by decide
  obtain ⟨i, hi⟩ := h 2 1 F (by norm_num) le_rfl hk hsup (fun _ => (1 / 2 : ℝ))
    (fun _ => by norm_num)
  have h1 : F.filter (fun S => i ∉ S) = {∅} := by
    fin_cases i <;> decide
  have h2 : F.filter (fun S => i ∈ S) = {Finset.univ} := by
    fin_cases i <;> decide
  rw [h1, h2] at hi
  simp at hi
  norm_num at hi
