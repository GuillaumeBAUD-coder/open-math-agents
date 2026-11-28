import OMAStatements.S_oeis_a376355
import Mathlib.Tactic.NormNum

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a376355.main) := by
  intro h
  have hw : OMA.S_oeis_a376355.Consecutive 1 2598054 2598061 := by
    unfold OMA.S_oeis_a376355.Consecutive
    decide +kernel
  have hg : 7 ∈ {g : ℕ | ∃ a b : ℕ, OMA.S_oeis_a376355.Consecutive 1 a b ∧ g = b - a} :=
    ⟨2598054, 2598061, hw, by decide⟩
  rw [h] at hg
  norm_num at hg
