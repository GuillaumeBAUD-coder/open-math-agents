import OMAStatements.S_mo_130120
import Mathlib

-- Problem: mo-130120, is there f(N) such that in every bipartite graph (V1, V2) in which each
-- vertex of V1 has between 2 and N neighbours, V2 can be coloured with f(N) colours so that
-- every vertex of V1 sees two colours?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No, already for N = 2. Let V2 have t = f(2) + 2 vertices and let V1 be the set of ordered
-- pairs of distinct vertices of V2, each joined to its two entries. Every vertex of V1 has
-- exactly 2 neighbours and every vertex of V2 has a neighbour. A colouring with f(2) < t
-- colours gives two distinct vertices a, b the same colour, and then the pair (a, b) sees only
-- one colour. (This is the statement that complete graphs have unbounded chromatic number.)

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_130120.main) := by
  rintro ⟨f, hf⟩
  have h1 : ∀ v : {p : Fin (f 2 + 2) × Fin (f 2 + 2) // p.1 ≠ p.2},
      2 ≤ {w : Fin (f 2 + 2) | w = v.1.1 ∨ w = v.1.2}.ncard ∧
        {w : Fin (f 2 + 2) | w = v.1.1 ∨ w = v.1.2}.ncard ≤ 2 := by
    intro v
    have hset : {w : Fin (f 2 + 2) | w = v.1.1 ∨ w = v.1.2} = {v.1.1, v.1.2} := by
      ext w
      simp
    rw [hset, Set.ncard_pair v.2]
    exact ⟨le_rfl, le_rfl⟩
  have h2 : ∀ w : Fin (f 2 + 2),
      ∃ v : {p : Fin (f 2 + 2) × Fin (f 2 + 2) // p.1 ≠ p.2}, w = v.1.1 ∨ w = v.1.2 := by
    intro w
    by_cases h : w = 0
    · exact ⟨⟨(w, 1), by rw [h]; exact Fin.zero_ne_one⟩, Or.inl rfl⟩
    · exact ⟨⟨(w, 0), h⟩, Or.inl rfl⟩
  obtain ⟨c, hc⟩ := hf 2 {p : Fin (f 2 + 2) × Fin (f 2 + 2) // p.1 ≠ p.2} (Fin (f 2 + 2))
    (fun v w => w = v.1.1 ∨ w = v.1.2) h1 h2
  obtain ⟨a, b, hab, hcab⟩ := Fintype.exists_ne_map_eq_of_card_lt c (by simp)
  obtain ⟨w, w', hw, hw', hne⟩ := hc ⟨(a, b), hab⟩
  have hw1 : w = a ∨ w = b := hw
  have hw2 : w' = a ∨ w' = b := hw'
  rcases hw1 with rfl | rfl <;> rcases hw2 with rfl | rfl
  · exact hne rfl
  · exact hne hcab
  · exact hne hcab.symm
  · exact hne rfl
