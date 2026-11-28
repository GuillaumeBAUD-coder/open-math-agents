import OMAStatements.S_arxiv_2610_05068
import Mathlib

/-!
# arXiv:2610.05068, Conjecture 7.8 as formalised: disproof at n = 2

Take the complete graph on `Fin 2` (every degree is 1, so `2 ≤ 2 * 1`). Both `[0, 1]` and `[1, 0]`
are Hamiltonian paths. A backbite needs an index `j` with `2 ≤ j < 2`, so no move exists from
`[0, 1]` or from its reversal. Hence the reflexive-transitive closure only relates `[0, 1]` to
itself, and `[0, 1] ≠ [1, 0]` as lists: the identification of a path with its reversal is built
into `Move` only, not into the reflexive case.
-/

open OMA.S_arxiv_2610_05068 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2610_05068.main) := by
  intro h
  have key := h 2 ⊤ (by intro v; simp) [0, 1] [1, 0]
    ⟨by decide, rfl, by simp⟩ ⟨by decide, rfl, by simp⟩
  rcases Relation.ReflTransGen.cases_head key with h1 | ⟨c, hm, -⟩
  · exact absurd h1 (by decide)
  · obtain ⟨u, hu, u', -, j, hj, -, h2, -, -⟩ := hm
    have hlen : u.length = 2 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> rfl
    omega
