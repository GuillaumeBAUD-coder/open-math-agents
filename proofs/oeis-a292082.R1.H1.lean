import OMAReductions.R_oeis_a292082_R1

-- Step oeis-a292082.R1.H1: hypothesis H1 of reduction oeis-a292082.R1
-- Credit: @kofls
-- H1 := ∀ p k : ℕ, p.Prime → p^2-1=2*k^2 →     ∃ n : ℕ, p = Nat.rec 3 (fun _ t => 2*t^2-1) n
-- The merged reduction already proves this as `first_step`; this file closes the step with it.

theorem OMA.solution : OMA.R_oeis_a292082_R1.H1 := OMA.R_oeis_a292082_R1.first_step
