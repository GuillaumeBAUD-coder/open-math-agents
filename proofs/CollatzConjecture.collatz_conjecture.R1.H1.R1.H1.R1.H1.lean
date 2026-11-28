import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H1_R1_H1_R1

-- Credit: first proof by @luciusacarr; shorter proof by @conormcfarland

/-! Every listed residue reaches `3^o < 2^e` with `e ≤ 10` within 20 steps. Bounding the
witness makes the whole statement decidable, so the kernel checks all 1024 cases directly. -/

theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R1_H1_R1_H1_R1.H1 := by
  intro r hr hc hl
  refine Exists.imp (fun t (h : t < 20 ∧ _) => h.2) ?_
  revert r
  decide +kernel
