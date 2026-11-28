import OMAReductions.R_DisjointNPPairs_no_complete_disjoint_NP_pair_variants_exists_of_NP_eq_coNP_R1_H1_R1

-- Step DisjointNPPairs.no_complete_disjoint_NP_pair.variants.exists_of_NP_eq_coNP.R1.H1.R1.H2: hypothesis H2 of reduction DisjointNPPairs.no_complete_disjoint_NP_pair.variants.exists_of_NP_eq_coNP.R1.H1.R1

/-!
Let `L` be the length of the encoding of `F` and take `w = [a 0, …, a (L - 1)]`. A literal `t` of
a clause of `F` contributes `t.2 + 3` symbols to the encoding, so `t.2 < L` and the entry of `w`
at position `t.2` is `a t.2`.
-/

private theorem encoding_length {α β : Type} (f : α → List β) {l : List α} {x : α}
    (hx : x ∈ l) : (f x).length ≤ (l.flatMap f).length := by
  rw [List.length_flatMap]
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨x, hx, rfl⟩)

theorem OMA.solution :
    OMA.R_DisjointNPPairs_no_complete_disjoint_NP_pair_variants_exists_of_NP_eq_coNP_R1_H1_R1.H2 := by
  intro F a
  let lit (t : Bool × ℕ) := [true, t.1] ++ List.replicate t.2 true ++ [false]
  let clause (c : List (Bool × ℕ)) := c.flatMap lit ++ [false]
  let L := (F.flatMap clause).length
  refine ⟨(List.range L).map a, by simp [L, clause, lit], ?_⟩
  intro c hc t ht
  have h1 := encoding_length lit ht
  have h2 := encoding_length clause hc
  have length_lit : (lit t).length = t.2 + 3 := by simp [lit]
  rw [length_lit] at h1
  change (c.flatMap lit ++ [false]).length ≤ L at h2
  rw [List.length_append] at h2
  rw [List.getElem?_map, List.getElem?_range (by omega)]
  rfl
