import FormalConjectures.ErdosProblems.«23»

/-! Pick a monochromatic side of each pentagon. Its layers and endpoint labels recover the pentagon. -/

open SimpleGraph Erdos23 Finset

theorem OMA.solution : type_of% @Erdos23.blowupC5_tight := by
  rintro n hn H _ ⟨color⟩
  let _ : NeZero n := ⟨hn.ne'⟩
  let vertex (p : Fin n × Fin n) (i : Fin 5) : Fin 5 × Fin n :=
    (i, ![p.1, p.2, p.1, p.2, p.1 + p.2] i)
  have odd : ∀ c : Fin 5 → Fin 2, ∃ i, c i = c (i + 1) := by decide
  classical
  rw [show n ^ 2 = (univ : Finset (Fin n × Fin n)).card by simp [sq]]
  apply card_le_card_of_forall_subsingleton (fun p e => ∃ i, e = s(vertex p i, vertex p (i + 1)))
  · intro p _
    obtain ⟨i, same⟩ := odd (color ∘ vertex p)
    refine ⟨_, mem_sdiff.mpr ⟨mem_edgeFinset.mpr ?_, fun h => color.valid (mem_edgeFinset.mp h) same⟩, i, rfl⟩
    exact ⟨by change vertex p i ≠ _; simp [vertex], .inl (.inl rfl)⟩
  · rintro e _ p ⟨_, i, rfl⟩ q ⟨_, j, h⟩
    simp only [Sym2.eq_iff, vertex, Prod.mk.injEq] at h
    rcases h with ⟨⟨rfl, x⟩, _, y⟩ | reversed
    · fin_cases i <;> apply Prod.ext <;> simp_all [Fin.isValue]
    · omega
