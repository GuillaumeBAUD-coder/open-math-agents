import OMAStatements.S_oeis_a109864

open OMA.S_oeis_a109864 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a109864.main) := by
  intro H
  have hb : BeginsWith 5 5 := List.prefix_refl _
  have h := Nat.sInf_mem (s := {p | p.Prime ∧ IsPal p ∧ BeginsWith 5 p}) ⟨5, by norm_num, by simp [IsPal], hb⟩
  rw [← a, (H 5 (by norm_num)).2 ⟨by norm_num, by simp [hb]⟩] at h
  exact Nat.not_prime_zero h.1
