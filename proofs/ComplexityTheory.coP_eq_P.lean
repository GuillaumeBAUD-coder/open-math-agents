import FormalConjectures.Millennium.PvsNP

-- Problem: Conjectures in Complexity Theory — coP eq P
-- Upstream: formal-conjectures FormalConjectures/Millennium/PvsNP.lean:70 (declaration ComplexityTheory.coP_eq_P)
-- Credit: @ashnewmanjones (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


open ComplexityTheory Turing

-- Bool is encoded as a single bit, so a machine deciding L, read through an output alphabet
-- composed with Boolean negation, decides the complement of L in the same time.
lemma OMA.compl_mem_P (L : DecisionProblem) (h : L ∈ P) : Lᶜ ∈ P := by
  obtain ⟨M⟩ := h
  refine ⟨{ M with
    outputAlphabet := M.outputAlphabet.trans Equiv.boolNot
    outputsFun := fun a => ?_ }⟩
  have hM := M.outputsFun a
  have key : List.map (M.outputAlphabet.trans Equiv.boolNot).invFun
      ((BitstringEncoding.toEncoding (α := Bool)).encode (Lᶜ a)) =
      List.map M.outputAlphabet.invFun ((BitstringEncoding.toEncoding (α := Bool)).encode (L a)) := by
    show [M.outputAlphabet.symm (Equiv.boolNot.symm ((Lᶜ) a))] = [M.outputAlphabet.symm (L a)]
    simp [Equiv.boolNot]
  rw [key]
  exact hM

theorem OMA.solution : type_of% @ComplexityTheory.coP_eq_P := by
  ext L
  constructor
  · intro hL
    have := OMA.compl_mem_P _ hL
    rwa [compl_compl] at this
  · intro hL
    exact OMA.compl_mem_P L hL
