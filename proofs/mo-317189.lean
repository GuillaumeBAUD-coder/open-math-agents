import OMAStatements.S_mo_317189

open Pointwise

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_317189.main) := by
  intro h
  let A : Finset ℤ := {-5, -4, -2, -1}
  have hbad := h A
    ⟨-5, by simp [A], by norm_num⟩
  have hn : ¬ 2 * (A + A).card ≤ (A + A + A).card + A.card := by decide
  exact hn hbad
