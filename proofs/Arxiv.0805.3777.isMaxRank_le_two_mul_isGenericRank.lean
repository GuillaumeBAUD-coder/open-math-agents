import FormalConjectures.Arxiv.«0805.3777».TensorRank

/-! The maximum complex tensor rank is at most twice the generic rank. -/

open scoped Arxiv.«0805.3777»

theorem OMA.solution : type_of% @Arxiv.«0805.3777».isMaxRank_le_two_mul_isGenericRank := by
  classical
  intro ds r R hr hR
  obtain ⟨U, hUopen, hUdense, hUrank⟩ := hr
  obtain ⟨T, hT⟩ := hR.1
  change T.cprank = R at hT
  have hcont : Continuous (fun X : Holor ℂ ds => T - X) := by
    change Continuous (fun X : HolorIndex ds → ℂ => fun i => T i - X i)
    exact continuous_pi (fun i => continuous_const.sub (continuous_apply i))
  obtain ⟨Y, hY⟩ := hUdense.nonempty
  obtain ⟨X, hX, hTX⟩ := hUdense.exists_mem_open (hUopen.preimage hcont)
    ⟨T - Y, by change T - (T - Y) ∈ U; rwa [sub_sub_cancel]⟩
  have rankBound (Y : Holor ℂ ds) (hY : Y ∈ U) : Holor.CPRankMax r Y := by
    rw [← hUrank Y hY]
    exact Nat.find_spec (p := fun n => Holor.CPRankMax n Y)
      ⟨ds.prod, Holor.cprankMax_upper_bound Y⟩
  rw [two_mul, ← hT]
  apply Nat.find_min'
  simpa only [sub_add_cancel] using
    Holor.cprankMax_add (rankBound (T - X) hTX) (rankBound X hX)
