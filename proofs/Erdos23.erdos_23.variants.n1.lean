import FormalConjectures.ErdosProblems.«23»

open SimpleGraph

namespace N1

def I : Fin 5 → Fin 5 → Fin 10 :=
  ![![0,0,1,2,3],![0,0,4,5,6],![1,4,0,7,8],![2,5,7,0,9],![3,6,8,9,0]]

def A (v : Fin 10 → Bool) (i j : Fin 5) : Bool := i != j && v (I i j)

def L : List (Fin 5 × Fin 5) :=
  [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

def M (v : Fin 10 → Bool) (s : Nat) :=
  L.filter fun p => A v p.1 p.2 && (s.testBit p.1 == s.testBit p.2)

def F (v : Fin 10 → Bool) : Bool :=
  L.any (fun p => (List.finRange 5).any fun z => A v p.1 p.2 && A v p.1 z && A v p.2 z) ||
    (List.range 32).any fun s => (M v s).length ≤ 1

set_option maxRecDepth 100000 in
theorem core : ∀ a b c d e f g h i j : Bool, F ![a,b,c,d,e,f,g,h,i,j] = true := by
  decide

theorem enc (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj] :
    ∃ v, ∀ i j, G.Adj i j ↔ A v i j = true :=
  ⟨fun k => decide (G.Adj (L.getD k (0,0)).1 (L.getD k (0,0)).2), by
    intro i j; fin_cases i <;> fin_cases j <;> simp [A, I, L] <;> exact G.adj_comm _ _⟩

theorem memL : ∀ x y : Fin 5, x < y → (x, y) ∈ L := by decide

end N1

open N1 in
theorem OMA.solution : type_of% @Erdos23.erdos_23.variants.n1 := by
  classical
  intro G hG
  obtain ⟨v, hA⟩ := enc G
  have hF := core (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) (v 8) (v 9)
  rw [show ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] = v from
    funext fun k => by fin_cases k <;> rfl] at hF
  simp only [F, Bool.or_eq_true, List.any_eq_true] at hF
  rcases hF with ⟨p, -, z, -, h⟩ | ⟨s, -, hs⟩
  · simp only [Bool.and_eq_true] at h
    exact (hG {p.1, p.2, z} (is3Clique_triple_iff.2
      ⟨(hA _ _).2 h.1.1, (hA _ _).2 h.1.2, (hA _ _).2 h.2⟩)).elim
  let c : Fin 5 → Bool := fun i => s.testBit i
  refine ⟨G ⊓ (⊤ : SimpleGraph Bool).comap c, inf_le_left,
    by simpa [IsBipartite] using ((Coloring.mk c fun h => h :
      ((⊤ : SimpleGraph Bool).comap c).Coloring Bool).colorable).mono_left inf_le_right, ?_⟩
  refine (Finset.card_le_card (s := _) (t := ((M v s).map fun p => s(p.1, p.2)).toFinset)
    ?_).trans ((List.toFinset_card_le _).trans (by simpa using hs))
  intro e he
  induction e using Sym2.ind with
  | h x y =>
    simp only [Finset.mem_sdiff, mem_edgeFinset, mem_edgeSet, inf_adj, comap_adj, top_adj,
      not_and, not_not] at he
    have hc : s.testBit x = s.testBit y := he.2 he.1
    simp only [List.mem_toFinset, List.mem_map, M, List.mem_filter]
    rcases lt_or_gt_of_ne (G.ne_of_adj he.1) with h | h
    · exact ⟨(x, y), ⟨memL x y h, by simp [(hA x y).1 he.1, hc]⟩, rfl⟩
    · exact ⟨(y, x), ⟨memL y x h, by simp [(hA y x).1 he.1.symm, hc]⟩, Sym2.eq_swap⟩
