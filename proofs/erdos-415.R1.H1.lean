import OMAReductions.R_erdos_415_R1

-- Step erdos-415.R1.H1: hypothesis H1 of reduction erdos-415.R1
-- Credit: @sntntHb

/-! If every ordering pattern of length `k` appears in some window `φ(m+1), …, φ(m+k)` with
`m + k ≤ n`, then so does the identity pattern, which is a strictly increasing run of length
`k`. So the set defining `F n` is contained in the set of run lengths, which is bounded by `n`;
and `0` lies in the first set (the empty window). Monotonicity of `sSup` (csSup_le_csSup)
gives `F n ≤ R n`. -/

theorem OMA.solution : OMA.R_erdos_415_R1.H1 := by
  intro n
  unfold OMA.S_erdos_415.F
  apply csSup_le_csSup
  · refine ⟨n, fun k hk => ?_⟩
    obtain ⟨m, hm, -⟩ := hk
    omega
  · refine ⟨0, fun σ => ⟨0, by omega, fun i => i.elim0⟩⟩
  · intro k hk
    obtain ⟨m, hm, h⟩ := hk (Equiv.refl _)
    exact ⟨m, hm, fun i j hij => (h i j).mpr hij⟩
