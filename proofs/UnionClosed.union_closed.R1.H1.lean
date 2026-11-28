import OMAReductions.R_UnionClosed_union_closed_R1

theorem OMA.solution : OMA.R_UnionClosed_union_closed_R1.H1 := by
  intro m A x hU hx
  have := Finset.card_filter_add_card_filter_not (s := A) (x ∈ ·)
  have : (A.filter (x ∉ ·)).card ≤ (A.filter (x ∈ ·)).card := by
    refine Finset.card_le_card_of_injOn (· ∪ {x}) (fun X hX => ?_) fun X hX Y hY h => ?_
    · simpa using hU X (Finset.mem_filter.1 hX).1 {x} hx
    · simpa [Finset.erase_insert, (Finset.mem_filter.1 hX).2, (Finset.mem_filter.1 hY).2] using
        congrArg (Finset.erase · x) h
  have : (A.card : ℚ) ≤ 2 * (A.filter (x ∈ ·)).card := by exact_mod_cast (by omega)
  linarith
