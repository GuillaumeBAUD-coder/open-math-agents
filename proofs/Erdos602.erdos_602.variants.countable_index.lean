import FormalConjectures.ErdosProblems.«602»

-- Problem: Countable index set case.
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/602.lean:156 (declaration Erdos602.erdos_602.variants.countable_index)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @Erdos602.erdos_602.variants.countable_index := by
  intro α A hA hfin _
  -- the part of `A i` outside all earlier sets is infinite
  have hinf : ∀ i, (A i \ ⋃ j ∈ Finset.range i, A j).Infinite := by
    intro i
    have hsub : A i \ ⋃ j ∈ Finset.range i, A j =
        A i \ ⋃ j ∈ Finset.range i, (A i ∩ A j) := by
      ext x
      simp only [Set.mem_diff, Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
      constructor
      · rintro ⟨hx, hn⟩
        exact ⟨hx, fun ⟨j, hj, _, hj'⟩ => hn ⟨j, hj, hj'⟩⟩
      · rintro ⟨hx, hn⟩
        exact ⟨hx, fun ⟨j, hj, hj'⟩ => hn ⟨j, hj, hx, hj'⟩⟩
    rw [hsub]
    refine (hA i).2.diff ?_
    refine Set.Finite.biUnion (Finset.finite_toSet _) ?_
    intro j hj
    have hji : j < i := Finset.mem_range.mp hj
    exact hfin i j (by omega)
  have hpick : ∀ i, ∃ a b : α, a ∈ A i \ ⋃ j ∈ Finset.range i, A j ∧
      b ∈ A i \ ⋃ j ∈ Finset.range i, A j ∧ a ≠ b := by
    intro i
    obtain ⟨a, ha⟩ := (hinf i).nonempty
    obtain ⟨b, hb, hba⟩ := ((hinf i).diff (Set.finite_singleton a)).nonempty
    exact ⟨a, b, ha, hb, fun h => hba (h ▸ rfl)⟩
  choose a b ha hb hab using hpick
  have key : ∀ i j, a i ≠ b j := by
    intro i j h
    rcases lt_trichotomy i j with hij | rfl | hij
    · apply (hb j).2
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨i, Finset.mem_range.mpr hij, h ▸ (ha i).1⟩
    · exact hab i h
    · apply (ha i).2
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨j, Finset.mem_range.mpr hij, h.symm ▸ (hb j).1⟩
  classical
  let f : α → Fin 2 := fun n => if ∃ i, n = b i then 1 else 0
  refine ⟨f, fun i hMono => ?_⟩
  have hfa : f (a i) = 0 := by
    simp only [f]
    rw [if_neg]
    rintro ⟨j, hj⟩
    exact key i j hj
  have hfb : f (b i) = 1 := by
    simp only [f]
    rw [if_pos ⟨i, rfl⟩]
  have hne := hMono (a i) (ha i).1 (b i) (hb i).1
  rw [hfa, hfb] at hne
  exact absurd hne (by decide)
