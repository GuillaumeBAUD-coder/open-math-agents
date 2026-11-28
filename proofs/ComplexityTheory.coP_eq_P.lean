import FormalConjectures.Millennium.PvsNP

-- Problem: Conjectures in Complexity Theory — coP eq P
-- Upstream: formal-conjectures FormalConjectures/Millennium/PvsNP.lean:70 (declaration ComplexityTheory.coP_eq_P)
-- Credit: @ashnewmanjones (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


/-! Boolean encoding uses a single bit. Composing the output alphabet with bit negation
decides the complement in the same time. -/

open ComplexityTheory Turing

lemma OMA.compl_mem_P (L : DecisionProblem) (h : L ∈ P) : Lᶜ ∈ P := by
  obtain ⟨M⟩ := h
  refine ⟨{ M with
    outputAlphabet := M.outputAlphabet.trans Equiv.boolNot
    outputsFun := fun a => ?_ }⟩
  have output := M.outputsFun a
  change TM2OutputsInTime _ _ (some [M.outputAlphabet.symm (L a)]) _ at output
  change TM2OutputsInTime _ _
    (some [M.outputAlphabet.symm (Equiv.boolNot.symm (Lᶜ a))]) _
  simpa [Equiv.boolNot] using output

theorem OMA.solution : type_of% @ComplexityTheory.coP_eq_P := by
  ext L
  exact ⟨fun hL => by simpa only [compl_compl] using OMA.compl_mem_P _ hL,
    OMA.compl_mem_P L⟩
