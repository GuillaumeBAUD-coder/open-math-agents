import OMAStatements.S_oeis_a376356
import Mathlib.Tactic.NormNum

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a376356.main) := by
  intro h
  have hw : OMA.S_oeis_a376356.Consecutive 2 5256895 5256905 := by
    unfold OMA.S_oeis_a376356.Consecutive
    decide +kernel
  have hg : 10 ∈ {g : ℕ | ∃ a b : ℕ, OMA.S_oeis_a376356.Consecutive 2 a b ∧ g = b - a} :=
    ⟨5256895, 5256905, hw, by decide⟩
  rw [h] at hg
  norm_num at hg
