import FormalConjectures.ErdosProblems.«150»
import Mathlib.Tactic

-- Problem: Erdős Problem 150 — erdos nesetril
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/150.lean:85 (declaration Erdos150.erdos_150.variants.erdos_nesetril)
-- Credit: @malikfassi (the owner of the agent is credited as the solver)
-- With the definition used upstream (a minimal cut is a minimal set of vertices whose removal
-- disconnects the graph), the 5-cycle has five minimal cuts, the pairs of vertices at distance
-- two. So the case m = 1 of the claimed identity, c(5) = 3, fails.

namespace OMA.E150

/-- The 5-cycle on `Fin 5`: `a` and `a + 1` are joined. -/
def G : SimpleGraph (Fin 5) := SimpleGraph.fromRel (fun a b : Fin 5 => b = a + 1)

lemma adj_iff (a b : Fin 5) : G.Adj a b ↔ (b = a + 1 ∨ a = b + 1) := by
  rw [G, SimpleGraph.fromRel_adj]
  revert a b
  decide

lemma a10 : ∀ c : Fin 5, G.Adj (c + 1) c := by
  intro c
  rw [adj_iff]
  revert c
  decide

lemma a12 : ∀ c : Fin 5, G.Adj (c + 1) (c + 2) := by
  intro c
  rw [adj_iff]
  revert c
  decide

lemma a23 : ∀ c : Fin 5, G.Adj (c + 2) (c + 3) := by
  intro c
  rw [adj_iff]
  revert c
  decide

lemma a34 : ∀ c : Fin 5, G.Adj (c + 3) (c + 4) := by
  intro c
  rw [adj_iff]
  revert c
  decide

lemma ne1 : ∀ c : Fin 5, c + 1 ≠ c := by decide
lemma ne2 : ∀ c : Fin 5, c + 2 ≠ c := by decide
lemma ne3 : ∀ c : Fin 5, c + 3 ≠ c := by decide
lemma ne12 : ∀ c : Fin 5, c + 1 ≠ c + 2 := by decide
lemma ne32 : ∀ c : Fin 5, c + 3 ≠ c + 2 := by decide
lemma ne13 : ∀ c : Fin 5, c + 1 ≠ c + 3 := by decide

lemma cover : ∀ c w : Fin 5, w = c ∨ w = c + 1 ∨ w = c + 2 ∨ w = c + 3 ∨ w = c + 4 := by
  decide

lemma nbr : ∀ i x : Fin 5, (x = i + 1 + 1 ∨ i + 1 = x + 1) → (x = i ∨ x = i + 2) := by
  decide

lemma inj : ∀ i j : Fin 5, (i = j ∨ i = j + 2) → (j = i ∨ j = i + 2) → i = j := by
  decide

/-- One edge of `G` between two kept vertices is a path in the induced graph. -/
lemma step {S : Set (Fin 5)} {u v : Fin 5} (hu : u ∈ Sᶜ) (hv : v ∈ Sᶜ) (h : G.Adj u v) :
    (G.induce Sᶜ).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  apply SimpleGraph.Adj.reachable
  simpa using h

/-- Removing at most one vertex `c` from the 5-cycle leaves it connected. -/
lemma conn (c : Fin 5) (S : Set (Fin 5)) (hS : ∀ x ∈ S, x = c) :
    (G.induce Sᶜ).Preconnected := by
  have nm : ∀ x : Fin 5, x ≠ c → x ∈ Sᶜ := fun x hx h => hx (hS x h)
  have h1 : c + 1 ∈ Sᶜ := nm _ (ne1 c)
  have h2 : c + 2 ∈ Sᶜ := nm _ (ne2 c)
  have h3 : c + 3 ∈ Sᶜ := nm _ (ne3 c)
  have key : ∀ (w : Fin 5) (hw : w ∈ Sᶜ),
      (G.induce Sᶜ).Reachable ⟨c + 1, h1⟩ ⟨w, hw⟩ := by
    intro w hw
    rcases cover c w with hc | hc | hc | hc | hc
    · subst hc
      exact step h1 hw (a10 w)
    · subst hc
      exact SimpleGraph.Reachable.refl _
    · subst hc
      exact step h1 hw (a12 c)
    · subst hc
      exact (step h1 h2 (a12 c)).trans (step h2 hw (a23 c))
    · subst hc
      exact ((step h1 h2 (a12 c)).trans (step h2 h3 (a23 c))).trans (step h3 hw (a34 c))
  intro u v
  exact (key u.1 u.2).symm.trans (key v.1 v.2)

/-- The five candidate cuts: two vertices at distance two. -/
def cut (i : Fin 5) : Set (Fin 5) := {i, i + 2}

lemma mem_cut (i x : Fin 5) : x ∈ cut i ↔ (x = i ∨ x = i + 2) := by
  simp [cut]

/-- Removing `i` and `i + 2` isolates `i + 1`. -/
lemma notconn (i : Fin 5) : ¬ (G.induce (cut i)ᶜ).Preconnected := by
  intro h
  have hu : i + 1 ∈ (cut i)ᶜ := by
    intro hx
    rcases (mem_cut i _).1 hx with hx | hx
    · exact ne1 i hx
    · exact ne12 i hx
  have hv : i + 3 ∈ (cut i)ᶜ := by
    intro hx
    rcases (mem_cut i _).1 hx with hx | hx
    · exact ne3 i hx
    · exact ne32 i hx
  have hne : (⟨i + 1, hu⟩ : ↥(cut i)ᶜ) ≠ ⟨i + 3, hv⟩ := by
    intro hEq
    exact ne13 i (congrArg Subtype.val hEq)
  obtain ⟨p⟩ := h ⟨i + 1, hu⟩ ⟨i + 3, hv⟩
  obtain ⟨w, hadj, -, -⟩ := p.exists_eq_cons_of_ne hne
  have hadj' : G.Adj (i + 1) w.1 := by simpa using hadj
  rw [adj_iff] at hadj'
  exact w.2 ((mem_cut i _).2 (nbr i w.1 hadj'))

lemma isCut (i : Fin 5) : Erdos150.IsMinimalCut G (cut i) := by
  refine ⟨notconn i, ?_⟩
  intro S hS
  by_cases hi : i ∈ S
  · apply conn i S
    intro x hx
    rcases (mem_cut i x).1 (hS.1 hx) with hxi | hxi
    · exact hxi
    · exfalso
      apply hS.2
      intro y hy
      rcases (mem_cut i y).1 hy with hy | hy
      · rw [hy]
        exact hi
      · rw [hy, ← hxi]
        exact hx
  · apply conn (i + 2) S
    intro x hx
    rcases (mem_cut i x).1 (hS.1 hx) with hxi | hxi
    · exfalso
      apply hi
      rw [← hxi]
      exact hx
    · exact hxi

lemma cut_injective : Function.Injective cut := by
  intro i j hij
  have h1 : i ∈ cut j := by
    rw [← hij]
    exact (mem_cut i i).2 (Or.inl rfl)
  have h2 : j ∈ cut i := by
    rw [hij]
    exact (mem_cut j j).2 (Or.inl rfl)
  exact inj i j ((mem_cut j i).1 h1) ((mem_cut i j).1 h2)

lemma range_card : (Set.range cut).ncard = 5 := by
  rw [← Set.image_univ, Set.ncard_image_of_injective _ cut_injective, Set.ncard_univ]
  simp

end OMA.E150

theorem OMA.solution : type_of% @Erdos150.erdos_150.variants.erdos_nesetril := by
  intro h
  have h5 : Erdos150.maxMinimalCuts 5 = 3 := by simpa using h 1
  have hbdd : BddAbove {k | ∃ G : SimpleGraph (Fin 5),
      {T : Set (Fin 5) | Erdos150.IsMinimalCut G T}.ncard = k} := by
    refine ⟨(Set.univ : Set (Set (Fin 5))).ncard, ?_⟩
    rintro k ⟨G, rfl⟩
    exact Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
  have hle : {T : Set (Fin 5) | Erdos150.IsMinimalCut OMA.E150.G T}.ncard
      ≤ Erdos150.maxMinimalCuts 5 :=
    le_csSup hbdd ⟨OMA.E150.G, rfl⟩
  have hsub : Set.range OMA.E150.cut ⊆
      {T : Set (Fin 5) | Erdos150.IsMinimalCut OMA.E150.G T} := by
    rintro _ ⟨i, rfl⟩
    exact OMA.E150.isCut i
  have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [OMA.E150.range_card] at hcard
  omega
