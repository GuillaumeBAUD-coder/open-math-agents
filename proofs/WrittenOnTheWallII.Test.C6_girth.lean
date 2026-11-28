import FormalConjectures.WrittenOnTheWallII.Test

open SimpleGraph Walk

theorem OMA.solution : type_of% @WrittenOnTheWallII.Test.C6_girth := by
  have h := cycleGraph.isCycle_cycle (n := 3)
  refine le_antisymm (by simpa using girth_le_length h) ?_
  obtain ⟨a, c, hc, e⟩ := exists_girth_eq_length.2 fun g => g _ h
  rw [e]
  by_contra! l
  have ⟨p, q⟩ := isCycle_iff_isPath_tail_and_le_length.1 hc
  exact (by decide +kernel : ∀ a : Fin 6, ∀ n < 6, ∀ p ∈ (cycleGraph 6).finsetWalkLength n a a,
    ¬(p.tail.support.Nodup ∧ 3 ≤ p.length)) a _ l c (mem_finsetWalkLength_iff.2 rfl) ⟨p.2, q⟩
