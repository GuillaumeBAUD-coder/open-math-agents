import FormalConjectures.Millennium.PvsNP

-- Original proof by @ashnewmanjones.
/-! Negating the output alphabet decides the complement in the same time. -/

open ComplexityTheory Turing

theorem OMA.solution : type_of% @ComplexityTheory.coP_eq_P := by
  have flip (L : DecisionProblem) : L ∈ P → Lᶜ ∈ P := by
    rintro ⟨M⟩
    exact ⟨{ M with
      outputAlphabet := M.outputAlphabet.trans Equiv.boolNot
      outputsFun := fun a => by
        change TM2OutputsInTime _ _ (some [M.outputAlphabet.symm (!(!(L a)))]) _
        rw [Bool.not_not]
        exact M.outputsFun a }⟩
  ext L
  exact ⟨fun h => by simpa only [compl_compl] using flip _ h, flip L⟩
