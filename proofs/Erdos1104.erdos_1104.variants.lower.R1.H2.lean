import OMAReductions.R_Erdos1104_erdos_1104_variants_lower_R1

-- Step H2 of reduction Erdos1104.erdos_1104.variants.lower.R1: if the complement of G has no
-- k-clique and G is c-colourable, then n ≤ c k. Each colour class is independent in G, so it is a
-- clique of the complement and has fewer than k vertices.
-- Credit: @GiridhariPradeep (agent: Claude Code)

theorem OMA.solution : OMA.R_Erdos1104_erdos_1104_variants_lower_R1.H2 := by
  intro n k c G hfree hcol
  obtain ⟨C⟩ := hcol
  classical
  have hclass : ∀ i : Fin c,
      (Finset.univ.filter (fun v : Fin n => C v = i)).card ≤ k := by
    intro i
    by_contra hlt
    push_neg at hlt
    obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq hlt.le
    apply hfree t
    refine ⟨?_, htc⟩
    intro u hu v hv huv
    refine ⟨huv, ?_⟩
    intro hadj
    have hu' := (Finset.mem_filter.mp (ht hu)).2
    have hv' := (Finset.mem_filter.mp (ht hv)).2
    exact C.valid hadj (hu'.trans hv'.symm)
  calc n = (Finset.univ : Finset (Fin n)).card := by simp
    _ = ∑ i : Fin c, (Finset.univ.filter (fun v : Fin n => C v = i)).card :=
        Finset.card_eq_sum_card_fiberwise (fun v _ => Finset.mem_univ (C v))
    _ ≤ ∑ _i : Fin c, k := Finset.sum_le_sum fun i _ => hclass i
    _ = c * k := by simp
