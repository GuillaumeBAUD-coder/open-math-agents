import FormalConjectures.ErdosProblems.«1171»

-- Problem: Erdős Problem 1171 — mono k
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1171.lean:62 (declaration Erdos1171.erdos_1171.variants.mono_k)
-- Credit: @Saturnorbiting (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof idea: a coloring with j + 1 colors is a coloring with k + 1 colors through Fin.castLE.
-- A color-0 set stays a color-0 set. A set of cardinality 3 has two distinct points, so its
-- common color comes from a nonzero color c of the small coloring, and the set has color c.

theorem OMA.solution : type_of% @Erdos1171.erdos_1171.variants.mono_k := by
  intro j k hjk hk col
  have hle : j + 1 ≤ k + 1 := Nat.succ_le_succ hjk
  have hz : Fin.castLE hle (0 : Fin (j + 1)) = 0 := Fin.ext (by simp)
  rcases hk (fun e => Fin.castLE hle (col e)) with ⟨A, hA, hP⟩ | ⟨i, A, hA, hcard⟩
  · refine Or.inl ⟨A, fun x hx y hy hxy => ?_, hP⟩
    have h : Fin.castLE hle (col s(x, y)) = 0 := hA x hx y hy hxy
    exact Fin.castLE_injective hle (h.trans hz.symm)
  · have h2 : (2 : Cardinal) ≤ Cardinal.mk A := by rw [hcard]; norm_num
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hne⟩ := Cardinal.two_le_iff.mp h2
    have hxy : x ≠ y := fun h => hne (Subtype.ext h)
    have hc : Fin.castLE hle (col s(x, y)) = i.succ := hA x hx y hy hxy
    have hc0 : col s(x, y) ≠ 0 := by
      intro h0
      rw [h0, hz] at hc
      exact Fin.succ_ne_zero i hc.symm
    refine Or.inr ⟨(col s(x, y)).pred hc0, A, fun x' hx' y' hy' hxy' => ?_, hcard⟩
    rw [Fin.succ_pred]
    have h' : Fin.castLE hle (col s(x', y')) = i.succ := hA x' hx' y' hy' hxy'
    exact Fin.castLE_injective hle (h'.trans hc.symm)

