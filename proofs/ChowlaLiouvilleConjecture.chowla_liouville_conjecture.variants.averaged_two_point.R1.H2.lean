import OMAReductions.R_ChowlaLiouvilleConjecture_chowla_liouville_conjecture_variants_averaged_two_point_R1

/-! Suppose not. Then for every j there is H_j ≥ j with g(H_j, N) ≥ ε for arbitrarily large N,
and one can pick N_j ≥ max j H_j with g(H_j, N_j) ≥ ε. Let H(N) be H_j for some j with
N_j = N if there is one, and N otherwise. Then H(N) ≤ N, and H tends to infinity because for
N beyond N_0, ..., N_(M-1) every j with N_j = N is at least M. The hypothesis gives
g(H(N), N) < ε for large N, which fails at N = N_j for large j. -/

theorem OMA.solution :
    OMA.R_ChowlaLiouvilleConjecture_chowla_liouville_conjecture_variants_averaged_two_point_R1.H2 := by
  intro g hg ε hε
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hfreq : ∀ j : ℕ, ∃ H, j ≤ H ∧ ∃ᶠ N : ℕ in Filter.atTop, ε ≤ g H N := by
    intro j
    obtain ⟨H, hH, hbad⟩ := (Filter.frequently_atTop.1 hcon) j
    refine ⟨H, hH, ?_⟩
    rw [Filter.not_eventually] at hbad
    exact hbad.mono (fun N hN => not_lt.1 hN)
  choose Hs hHs1 hHs2 using hfreq
  have hN : ∀ j : ℕ, ∃ N, max j (Hs j) ≤ N ∧ ε ≤ g (Hs j) N :=
    fun j => Filter.frequently_atTop.1 (hHs2 j) (max j (Hs j))
  choose Ns hNs1 hNs2 using hN
  classical
  obtain ⟨Hf, hHf⟩ : ∃ Hf : ℕ → ℕ, ∀ N, Hf N =
      if h : ∃ j, Ns j = N then Hs (Classical.choose h) else N := ⟨_, fun _ => rfl⟩
  have hle : ∀ N, Hf N ≤ N := by
    intro N
    by_cases h : ∃ j, Ns j = N
    · rw [hHf, dif_pos h]
      calc Hs (Classical.choose h) ≤ Ns (Classical.choose h) :=
            le_trans (le_max_right _ _) (hNs1 _)
        _ = N := Classical.choose_spec h
    · rw [hHf, dif_neg h]
  have htend : Filter.Tendsto Hf Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro M
    filter_upwards [Filter.eventually_gt_atTop ((Finset.range M).sup Ns),
      Filter.eventually_ge_atTop M] with N hN1 hN2
    by_cases h : ∃ j, Ns j = N
    · rw [hHf, dif_pos h]
      have hspec := Classical.choose_spec h
      have hjM : M ≤ Classical.choose h := by
        by_contra hlt
        have hmem : Classical.choose h ∈ Finset.range M := Finset.mem_range.2 (not_le.1 hlt)
        have hsup := Finset.le_sup (f := Ns) hmem
        omega
      exact le_trans hjM (hHs1 _)
    · rw [hHf, dif_neg h]
      exact hN2
  have h0 := hg Hf htend (Filter.Eventually.of_forall hle)
  have hev : ∀ᶠ N : ℕ in Filter.atTop, g (Hf N) N < ε := h0.eventually (gt_mem_nhds hε)
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 hev
  have h1 := hN0 (Ns N0) (le_trans (le_max_left _ _) (hNs1 N0))
  have hex : ∃ j, Ns j = Ns N0 := ⟨N0, rfl⟩
  have hspec := Classical.choose_spec hex
  have h2 := hNs2 (Classical.choose hex)
  rw [hspec] at h2
  rw [hHf, dif_pos hex] at h1
  linarith
