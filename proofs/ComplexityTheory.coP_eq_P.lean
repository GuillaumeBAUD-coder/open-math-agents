import FormalConjectures.Millennium.PvsNP
open ComplexityTheory Turing
theorem OMA.solution : type_of% @ComplexityTheory.coP_eq_P := by
  have c (L : DecisionProblem) (h : L ∈ P) : Lᶜ ∈ P := by
    obtain ⟨M⟩ := h
    refine ⟨{ M with
      outputAlphabet := M.outputAlphabet.trans Equiv.boolNot
      outputsFun := fun a => ?_ }⟩
    convert M.outputsFun a using 1
    simp [Equiv.boolNot, BitstringEncoding.toEncoding]
  ext L
  exact ⟨fun h => compl_compl L ▸ c _ h, c L⟩
