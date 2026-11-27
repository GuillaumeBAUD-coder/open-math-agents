import OMAReductions.R_Arxiv_2507_17780_tx_graffiti_conjecture_1_R1_H1_R1

-- Step Arxiv.2507.17780.tx_graffiti_conjecture_1.R1.H1.R1.H2
-- Credit: @caa1982

theorem OMA.solution : OMA.R_Arxiv_2507_17780_tx_graffiti_conjecture_1_R1_H1_R1.H2 := by
  have aux : ∀ n : ℕ, ∀ s : List ℕ, s.length = n → SimpleGraph.residueAux s ≤ s.length := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hs
      cases s with
      | nil => simp [SimpleGraph.residueAux]
      | cons d rest =>
        cases d with
        | zero =>
          rw [SimpleGraph.residueAux]
          simp [add_comm]
        | succ d =>
          rw [SimpleGraph.residueAux.eq_3 _ _ (by omega)]
          have hlen := SimpleGraph.havelHakimiStep_length_cons (d + 1) rest
          have hle := ih rest.length (by simp at hs; omega) (SimpleGraph.havelHakimiStep ((d + 1) :: rest)) hlen
          rw [hlen] at hle
          simp
          omega
  intro s
  exact aux s.length s rfl
