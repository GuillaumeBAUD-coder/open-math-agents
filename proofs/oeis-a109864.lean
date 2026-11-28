import OMAStatements.S_oeis_a109864

-- Problem: A109864: Least palindromic prime beginning with n, or 0 if no such prime exists.
-- Upstream: formal-conjectures statements/oeis-a109864.lean:0 (declaration OMA.S_oeis_a109864.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: n = 5 is a counterexample. 5 is a palindromic prime beginning with 5, so the set whose
-- least element is a(5) is nonempty and a(5) = 5 is not 0; but 5 > 3 and 5 begins with 5.

open OMA.S_oeis_a109864 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a109864.main) := by
  intro H
  have hd5 : Nat.digits 10 5 = [5] := Nat.digits_of_lt 10 5 (by norm_num) (by norm_num)
  have hb : BeginsWith 5 5 := by
    unfold BeginsWith
    exact List.prefix_refl _
  have hmem : 5 ∈ {p : ℕ | p.Prime ∧ IsPal p ∧ BeginsWith 5 p} := by
    rw [Set.mem_ofPred_eq]
    refine ⟨by norm_num, ?_, hb⟩
    unfold IsPal
    rw [hd5, List.reverse_singleton]
  have hne : a 5 ≠ 0 := by
    intro h0
    have h := Nat.sInf_mem ⟨5, hmem⟩
    unfold a at h0
    rw [h0, Set.mem_ofPred_eq] at h
    exact Nat.not_prime_zero h.1
  exact hne ((H 5 (by norm_num)).mpr ⟨by norm_num, Or.inr (Or.inr (Or.inr (Or.inr hb)))⟩)
