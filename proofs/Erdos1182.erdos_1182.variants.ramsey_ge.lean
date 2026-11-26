import FormalConjectures.ErdosProblems.«1182»

/-!
# The elementary Ramsey lower bound for connected graphs

A complete bipartite graph with both parts smaller than the target graph has no triangle.
Its complement cannot contain a copy of a connected graph that is larger than either part.
-/

open SimpleGraph

namespace OMA

theorem adj_iff_edge_in_pair {m : ℕ} (C : SimpleGraph (Fin m)) (a b : Fin m) :
    (∃ u ∈ ({a, b} : Finset (Fin m)), ∃ v ∈ ({a, b} : Finset (Fin m)), C.Adj u v) ↔
      C.Adj a b := by
  constructor
  · rintro ⟨u, hu, v, hv, hadj⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (hadj.ne rfl).elim
    · exact hadj
    · exact hadj.symm
    · exact (hadj.ne rfl).elim
  · intro h
    exact ⟨a, by simp, b, by simp, h⟩

theorem finite_ramsey_witness {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ m : ℕ, ∀ C : SimpleGraph (Fin m),
      (⊤ : SimpleGraph (Fin 3)).IsContained C ∨ G.IsContained Cᶜ := by
  classical
  let m := (n + 3).choose n
  refine ⟨m, ?_⟩
  intro C
  let color (e : Finset (Fin m)) : Bool := decide (∃ a ∈ e, ∃ b ∈ e, C.Adj a b)
  rcases Combinatorics.Diagonal.hasRamseyProperty_choose n 3 color Finset.univ (by simp [m]) with
    ⟨s, _, hcard, hs⟩ | ⟨s, _, hcard, hs⟩
  · right
    have hs' : Cᶜ.IsNClique n s := by
      refine ⟨?_, hcard⟩
      intro a ha b hb hab
      apply (C.compl_adj a b).mpr
      refine ⟨hab, ?_⟩
      have hsub : ({a, b} : Finset (Fin m)) ⊆ s := by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · exact ha
        · exact hb
      have hc := hs {a, b} hsub (by simp [hab])
      simpa only [color, decide_eq_false_iff_not, adj_iff_edge_in_pair] using hc
    exact (SimpleGraph.IsContained.of_le le_top).trans
      ((SimpleGraph.not_cliqueFree_iff_top_isContained n).mp hs'.not_cliqueFree)
  · left
    have hs' : C.IsNClique 3 s := by
      refine ⟨?_, hcard⟩
      intro a ha b hb hab
      have hsub : ({a, b} : Finset (Fin m)) ⊆ s := by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · exact ha
        · exact hb
      have hc := hs {a, b} hsub (by simp [hab])
      simpa only [color, decide_eq_true_eq, adj_iff_edge_in_pair] using hc
    exact (SimpleGraph.not_cliqueFree_iff_top_isContained 3).mp hs'.not_cliqueFree

theorem no_ramsey_below_bound {n m : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.Connected) (hm : m < 2 * n - 1) :
    ∃ C : SimpleGraph (Fin m),
      ¬ (⊤ : SimpleGraph (Fin 3)).IsContained C ∧ ¬ G.IsContained Cᶜ := by
  let side (i : Fin m) : Bool := decide (i.val < n - 1)
  let C : SimpleGraph (Fin m) :=
    { Adj := fun i j => side i ≠ side j
      symm := ⟨fun _ _ h => h.symm⟩
      loopless := ⟨fun _ h => h rfl⟩ }
  refine ⟨C, ?_, ?_⟩
  · rintro ⟨f⟩
    have h01 : side (f 0) ≠ side (f 1) := f.toHom.map_rel (by decide)
    have h02 : side (f 0) ≠ side (f 2) := f.toHom.map_rel (by decide)
    have h12 : side (f 1) ≠ side (f 2) := f.toHom.map_rel (by decide)
    have two_colors (a b c : Bool) : a ≠ b → a ≠ c → b ≠ c → False := by
      cases a <;> cases b <;> cases c <;> simp
    exact two_colors _ _ _ h01 h02 h12
  · rintro ⟨f⟩
    have same_side {a b : Fin n} (h : G.Adj a b) : side (f a) = side (f b) := by
      exact not_not.mp ((C.compl_adj _ _).mp (f.toHom.map_rel h)).2
    obtain ⟨v⟩ := hG.nonempty
    have constant_side (u : Fin n) : side (f u) = side (f v) := by
      obtain ⟨w⟩ := hG.preconnected u v
      induction w with
      | nil => rfl
      | cons h _ ih => exact (same_side h).trans ih
    by_cases hv : side (f v) = true
    · have hv' (u : Fin n) : (f u).val < n - 1 := by
        simpa only [side, decide_eq_true_eq] using (constant_side u).trans hv
      let e (u : Fin n) : Fin (n - 1) := ⟨(f u).val, hv' u⟩
      have he : Function.Injective e := by
        intro a b hab
        exact f.injective' (Fin.ext (congrArg (fun i : Fin (n - 1) => i.val) hab))
      have hc := Fintype.card_le_of_injective e he
      simp only [Fintype.card_fin] at hc
      have := v.isLt
      omega
    · have hv' (u : Fin n) : n - 1 ≤ (f u).val := by
        have : side (f u) ≠ true := fun h => hv ((constant_side u).symm.trans h)
        simpa only [side, ne_eq, decide_eq_true_eq, not_lt] using this
      let e (u : Fin n) : Fin (n - 1) := ⟨(f u).val - (n - 1), by
        have := (f u).isLt
        omega⟩
      have he : Function.Injective e := by
        intro a b hab
        apply f.injective'
        apply Fin.ext
        have he' : (f.toHom a).val - (n - 1) = (f.toHom b).val - (n - 1) :=
          congrArg (fun i : Fin (n - 1) => i.val) hab
        have ha : n - 1 ≤ (f.toHom a).val := hv' a
        have hb : n - 1 ≤ (f.toHom b).val := hv' b
        omega
      have hc := Fintype.card_le_of_injective e he
      simp only [Fintype.card_fin] at hc
      have := v.isLt
      omega

end OMA

theorem OMA.solution : type_of% @Erdos1182.erdos_1182.variants.ramsey_ge := by
  intro n G hG
  unfold SimpleGraph.graphRamsey
  have hmem := Nat.sInf_mem (OMA.finite_ramsey_witness G)
  by_contra! hlt
  obtain ⟨C, h₁, h₂⟩ := OMA.no_ramsey_below_bound G hG hlt
  exact (hmem C).elim h₁ h₂
