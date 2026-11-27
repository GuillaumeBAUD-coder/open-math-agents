import OMAReductions.R_Arxiv_2507_17780_tx_graffiti_conjecture_1_R1_H1_R1

-- Step Arxiv.2507.17780.tx_graffiti_conjecture_1.R1.H1.R1.H2: hypothesis H2 of reduction Arxiv.2507.17780.tx_graffiti_conjecture_1.R1.H1.R1
-- Credit: @anmolspace
-- Proof: strong induction on the list length; each Havel-Hakimi step drops the length by one.

theorem OMA.solution : OMA.R_Arxiv_2507_17780_tx_graffiti_conjecture_1_R1_H1_R1.H2 := by
  have key : ∀ n : ℕ, ∀ s : List ℕ, s.length = n → SimpleGraph.residueAux s ≤ s.length := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro s hs
      rcases s with _ | ⟨d, t⟩
      · unfold SimpleGraph.residueAux
        simp
      · rcases d with _ | d
        · unfold SimpleGraph.residueAux
          simp
          omega
        · have hlen := SimpleGraph.havelHakimiStep_length_cons (d+1) t
          have hlt : t.length < n := by
            rw [← hs]
            simp
          have hrec := ih t.length hlt (SimpleGraph.havelHakimiStep ((d+1) :: t)) hlen
          have heq : SimpleGraph.residueAux ((d+1) :: t)
              = SimpleGraph.residueAux (SimpleGraph.havelHakimiStep ((d+1) :: t)) := by
            rw [SimpleGraph.residueAux]
            all_goals omega
          rw [heq]
          rw [hlen] at hrec
          simp only [List.length_cons]
          omega
  intro s
  exact key s.length s rfl
