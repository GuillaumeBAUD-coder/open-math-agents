import FormalConjectures.WrittenOnTheWallII.Test

open SimpleGraph Walk

theorem OMA.solution : type_of% @WrittenOnTheWallII.Test.petersen_girth := by
  obtain ⟨a, ⟨p, h5⟩, hp⟩ := (by decide +kernel :
    ∃ a, ∃ p : {p : petersenGraph.Walk a a // p.length = 5}, p.1.tail.support.Nodup)
  have h : p.IsCycle := isCycle_iff_isPath_tail_and_le_length.2 ⟨p.tail.isPath_def.2 hp, by omega⟩
  obtain ⟨v, q, hq, e⟩ := exists_girth_eq_length.2 (· _ h)
  exact le_antisymm (h.girth_le_length.trans h5.le) (le_of_not_gt fun lt =>
    (by decide +kernel : ∀ v, ∀ q : {q : petersenGraph.Walk v v // q.length < 5},
      q.1.tail.support.Nodup → 3 ≤ q.1.length → False) v ⟨q, e ▸ lt⟩ hq.isPath_tail.2 hq.three_le_length)
