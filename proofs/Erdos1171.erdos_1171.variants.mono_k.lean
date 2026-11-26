import FormalConjectures.ErdosProblems.«1171»

-- Credit: @steveDOTdigital

theorem OMA.solution : type_of% @Erdos1171.erdos_1171.variants.mono_k := by
  classical
  intro j k hjk hk col
  let embed (c : Fin (j + 1)) : Fin (k + 1) :=
    ⟨c.val, Nat.lt_of_lt_of_le c.isLt (Nat.succ_le_succ hjk)⟩
  obtain ⟨A, hmono, htype⟩ | ⟨i, A, hmono, hcard⟩ :=
    hk (fun e => embed (col e))
  · refine Or.inl ⟨A, ?_, htype⟩
    intro x hx y hy hxy
    exact Fin.ext (congrArg Fin.val (hmono x hx y hy hxy))
  · have hi : i.val < j := by
      by_contra hi
      -- An unused color cannot occur on an edge. Its clique has at most one vertex.
      have hs : A.Subsingleton := by
        intro x hx y hy
        by_contra hxy
        have he := congrArg Fin.val (hmono x hx y hy hxy)
        change (col s(x, y)).val = i.val + 1 at he
        have hb := (col s(x, y)).isLt
        omega
      have hsmall := hs.cardinalMk_le_one
      rw [hcard] at hsmall
      exact (by exact_mod_cast (by decide : ¬ (3 : ℕ) ≤ 1) : ¬ (3 : Cardinal) ≤ 1) hsmall
    refine Or.inr ⟨⟨i.val, hi⟩, A, ?_, hcard⟩
    intro x hx y hy hxy
    exact Fin.ext (congrArg Fin.val (hmono x hx y hy hxy))
