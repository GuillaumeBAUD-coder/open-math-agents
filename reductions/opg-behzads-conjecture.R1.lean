import OMAStatements.S_opg_behzads_conjecture

-- Reduction opg-behzads-conjecture.R1 of Total Colouring Conjecture
-- Credit: @yuka30240

/-!
Doubling at vertices of deficient degree reduces the upper bound to regular graphs.
On a bipartite graph, use two fresh vertex colours. On a nonbipartite regular graph,
a proper edge colouring with two spare colours at each vertex gives a 2-SAT instance.
A clash between adjacent vertices forces the opposite choice at the second vertex.
The remaining problem is to find an edge colouring with no contradictory pair of paths.
The choice of edge colouring matters even on the complete graph on four vertices.
Colouring its three perfect matchings uniformly leaves the same two choices everywhere.
In the other direction, a total colouring supplies a consistent choice at every vertex.
Regularity guarantees exactly two colours are missing from the incident edges.
-/

namespace OMA.R_opg_behzads_conjecture_R1

open OMA.S_opg_behzads_conjecture

/-- The regular bipartite case of König's edge colouring theorem. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ), G.IsRegularOfDegree d → G.IsBipartite →
    ∃ ce : G.edgeSet → Fin d, ∀ (e f : G.edgeSet), e ≠ f →
      (∃ v : V, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V)) → ce e ≠ ce f

/-- Find an edge colouring whose two missing colours at each vertex give a
conflict implication graph with the two choices in different strong components. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ), G.IsRegularOfDegree d → ¬ G.IsBipartite →
    ∃ (ce : G.edgeSet → Fin (d + 2)) (a : V → Bool → Fin (d + 2)),
      (∀ (e f : G.edgeSet), e ≠ f → (∃ v : V, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V)) → ce e ≠ ce f) ∧
      (∀ v, a v false ≠ a v true) ∧
      (∀ (e : G.edgeSet) (v : V), v ∈ (e : Sym2 V) → ∀ b, ce e ≠ a v b) ∧
      (let forces := fun (x y : V × Bool) ↦ G.Adj x.1 y.1 ∧ a x.1 x.2 = a y.1 (!y.2)
       ∀ v : V, ¬ (Relation.ReflTransGen forces (v, false) (v, true) ∧
         Relation.ReflTransGen forces (v, true) (v, false)))

lemma selectMissing {V α : Type} (G : SimpleGraph V) (a : V → Bool → α)
    (h : let forces := fun (x y : V × Bool) ↦ G.Adj x.1 y.1 ∧ a x.1 x.2 = a y.1 (!y.2)
         ∀ v : V, ¬ (Relation.ReflTransGen forces (v, false) (v, true) ∧
           Relation.ReflTransGen forces (v, true) (v, false))) :
    ∃ pick : V → Bool, ∀ u v, G.Adj u v → a u (pick u) ≠ a v (pick v) := by
  classical
  let forces (x y : V × Bool) := G.Adj x.1 y.1 ∧ a x.1 x.2 = a y.1 (!y.2)
  let pred (x : V × Bool) : Set (V × Bool) := {z | Relation.ReflTransGen forces z x}
  let rank (x : V × Bool) := toLinearExtension (pred x)
  have along {x y} (hxy : forces x y) : rank x ≤ rank y :=
    toLinearExtension.monotone (show pred x ⊆ pred y from fun _ hz ↦ hz.tail hxy)
  have distinct (v : V) : rank (v, false) ≠ rank (v, true) := by
    intro eq
    change pred (v, false) = pred (v, true) at eq
    apply h v
    constructor
    · change (v, false) ∈ pred (v, true)
      rw [← eq]
      exact Relation.ReflTransGen.refl
    · change (v, true) ∈ pred (v, false)
      rw [eq]
      exact Relation.ReflTransGen.refl
  let pick (v : V) : Bool := decide (rank (v, false) < rank (v, true))
  have higher (v : V) : rank (v, !(pick v)) < rank (v, pick v) := by
    by_cases hv : rank (v, false) < rank (v, true)
    · simp [pick, hv]
    · simpa [pick, hv] using lt_of_le_of_ne (le_of_not_gt hv) (distinct v).symm
  refine ⟨pick, ?_⟩
  intro u v huv clash
  have uv : forces (u, pick u) (v, !(pick v)) := ⟨huv, by simpa using clash⟩
  have vu : forces (v, pick v) (u, !(pick u)) := ⟨huv.symm, by simpa using clash.symm⟩
  exact (not_lt_of_ge (along vu)) (((higher u).trans_le (along uv)).trans (higher v))

private lemma colorRegular (h₁ : H1) (h₂ : H2) {V : Type} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (hr : G.IsRegularOfDegree d) :
    ∃ (cv : V → Fin (d + 2)) (ce : G.edgeSet → Fin (d + 2)), IsTotalColoring G cv ce := by
  classical
  by_cases hb : G.IsBipartite
  · obtain ⟨vert⟩ := hb
    obtain ⟨edge, proper⟩ := h₁ V G d hr ⟨vert⟩
    refine ⟨fun v ↦ Fin.natAdd d (vert v), fun e ↦ Fin.castAdd 2 (edge e), ?_, ?_, ?_⟩
    · intro u v huv eq
      exact vert.valid huv (Fin.ext (by simpa using congrArg Fin.val eq))
    · intro e f hef common eq
      exact proper e f hef common (Fin.ext (congrArg (fun a : Fin (d + 2) ↦ a.val) eq))
    · intro e v _ eq
      have he := (edge e).isLt
      have bad := congrArg Fin.val eq
      simp at bad
      omega
  · obtain ⟨edge, a, proper, _, missing, consistent⟩ := h₂ V G d hr hb
    obtain ⟨pick, good⟩ := selectMissing G a consistent
    exact ⟨fun v ↦ a v (pick v), edge, good, proper, fun e v hv ↦ missing e v hv _⟩

private lemma pullback {V W : Type} {G : SimpleGraph V} {K : SimpleGraph W}
    (i : G ↪g K) {α : Type} {cv : W → α} {ce : K.edgeSet → α}
    (hc : IsTotalColoring K cv ce) :
    IsTotalColoring G (fun v ↦ cv (i v)) (fun e ↦ ce (i.mapEdgeSet e)) := by
  have mem {v : V} {e : G.edgeSet} (hv : v ∈ (e : Sym2 V)) :
      i v ∈ (i.mapEdgeSet e : Sym2 W) :=
    Sym2.mem_map.mpr ⟨v, hv, rfl⟩
  refine ⟨fun _ _ h ↦ hc.1 _ _ (i.map_rel_iff.mpr h), ?_, ?_⟩
  · rintro e f hef ⟨v, hv, hw⟩
    exact hc.2.1 _ _ (fun eq ↦ hef (i.mapEdgeSet.injective eq)) ⟨i v, mem hv, mem hw⟩
  · exact fun e v hv ↦ hc.2.2 _ _ (mem hv)

/-- At a vertex of maximum degree, its colour and those of its incident edges are distinct. -/
private lemma lower {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ} {cv : V → Fin k} {ce : G.edgeSet → Fin k}
    (hc : IsTotalColoring G cv ce) : G.maxDegree + 1 ≤ k := by
  classical
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  let edge (e : G.incidenceSet v) : G.edgeSet := ⟨e.val, e.property.1⟩
  let f : Option (G.incidenceSet v) → Fin k := fun t ↦ t.elim (cv v) (fun e ↦ ce (edge e))
  have inj : Function.Injective f := by
    intro x y eq
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some b => exact (hc.2.2 (edge b) v b.property.2 eq.symm).elim
    | some a =>
      cases y with
      | none => exact (hc.2.2 (edge a) v a.property.2 eq).elim
      | some b =>
        by_contra ne
        exact hc.2.1 (edge a) (edge b)
          (fun he ↦ ne (congrArg some (Subtype.ext (congrArg (fun e : G.edgeSet ↦ e.val) he))))
          ⟨v, a.property.2, b.property.2⟩ eq
  simpa [hv, G.card_incidenceSet_eq_degree] using Fintype.card_le_of_injective f inj

/-- Take two copies and join corresponding vertices precisely where the degree is below d. -/
private lemma doubleAtDeficits {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (d : ℕ) :
    ∃ (K : SimpleGraph (V × Bool)) (_ : DecidableRel K.Adj), Nonempty (G ↪g K) ∧
      ∀ p : V × Bool, K.degree p = G.degree p.1 + (if G.degree p.1 < d then 1 else 0) := by
  classical
  let K : SimpleGraph (V × Bool) := {
    Adj := fun x y ↦ (x.2 = y.2 ∧ G.Adj x.1 y.1) ∨
      (x.1 = y.1 ∧ x.2 ≠ y.2 ∧ G.degree x.1 < d)
    symm := ⟨by
      rintro x y (⟨hb, ha⟩ | ⟨hv, hb, hd⟩)
      · exact Or.inl ⟨hb.symm, ha.symm⟩
      · exact Or.inr ⟨hv.symm, hb.symm, hv ▸ hd⟩⟩
    loopless := ⟨fun x h ↦ h.elim (fun a ↦ G.loopless.irrefl x.1 a.2) (fun a ↦ a.2.1 rfl)⟩ }
  let _ : DecidableRel K.Adj := Classical.decRel _
  let embed : G ↪g K := {
    toEmbedding := Function.Embedding.sectL V false
    map_rel_iff' := by
      intro u v
      change ((false = false ∧ G.Adj u v) ∨ (u = v ∧ false ≠ false ∧ G.degree u < d)) ↔ _
      simp }
  refine ⟨K, inferInstance, ⟨embed⟩, ?_⟩
  rintro ⟨v, b⟩
  let row := (G.neighborFinset v).map (Function.Embedding.sectL V b)
  have inRow (w : V) (c : Bool) : (w, c) ∈ row ↔ G.Adj v w ∧ c = b := by
    constructor
    · intro hw
      obtain ⟨z, hz, eq⟩ := Finset.mem_map.mp hw
      change (z, b) = (w, c) at eq
      cases eq
      exact ⟨(G.mem_neighborFinset _ _).mp hz, rfl⟩
    · rintro ⟨hw, rfl⟩
      exact Finset.mem_map.mpr ⟨w, (G.mem_neighborFinset _ _).mpr hw, rfl⟩
  have hcard : row.card = G.degree v := by simp [row]
  rw [← K.card_neighborFinset_eq_degree]
  by_cases hd : G.degree v < d
  · have neighbors : K.neighborFinset (v, b) = insert (v, !b) row := by
      ext ⟨w, c⟩
      rw [K.mem_neighborFinset, Finset.mem_insert, inRow]
      change ((b = c ∧ G.Adj v w) ∨ (v = w ∧ b ≠ c ∧ G.degree v < d)) ↔ _
      cases b <;> cases c <;> simp [hd, eq_comm]
    have outside : (v, !b) ∉ row := fun h ↦ G.loopless.irrefl v (inRow _ _ |>.mp h).1
    rw [neighbors, Finset.card_insert_of_notMem outside, hcard]
    simp [hd]
  · have neighbors : K.neighborFinset (v, b) = row := by
      ext ⟨w, c⟩
      rw [K.mem_neighborFinset, inRow]
      change ((b = c ∧ G.Adj v w) ∨ (v = w ∧ b ≠ c ∧ G.degree v < d)) ↔ _
      simp [hd, eq_comm, and_comm]
    rw [neighbors, hcard]
    simp [hd]

private lemma colorWithDeficit (h₁ : H1) (h₂ : H2) (d n : ℕ)
    {V : Type} [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (upper : ∀ v, G.degree v ≤ d) (gap : ∀ v, d ≤ G.degree v + n) :
    ∃ (cv : V → Fin (d + 2)) (ce : G.edgeSet → Fin (d + 2)), IsTotalColoring G cv ce := by
  induction n generalizing V with
  | zero =>
    exact colorRegular h₁ h₂ G d (fun v ↦ le_antisymm (upper v) (by simpa using gap v))
  | succ n ih =>
    obtain ⟨K, inst, ⟨i⟩, degree⟩ := doubleAtDeficits G d
    have up (p : V × Bool) : K.degree p ≤ d := by
      rw [degree]
      have := upper p.1
      split <;> omega
    have small (p : V × Bool) : d ≤ K.degree p + n := by
      rw [degree]
      have := gap p.1
      split <;> omega
    obtain ⟨cv, ce, hc⟩ := ih K up small
    exact ⟨_, _, pullback i hc⟩

theorem main : H1 → H2 → type_of% @OMA.S_opg_behzads_conjecture.main := by
  intro h₁ h₂ V _ _ G _
  obtain ⟨cv, ce, hc⟩ := colorWithDeficit h₁ h₂ G.maxDegree G.maxDegree G
    G.degree_le_maxDegree (fun v ↦ Nat.le_add_left _ _)
  let feasible : Set ℕ := {k | ∃ (c : V → Fin k) (e : G.edgeSet → Fin k), IsTotalColoring G c e}
  have witness : G.maxDegree + 2 ∈ feasible := ⟨cv, ce, hc⟩
  have hi := Nat.sInf_le witness
  obtain ⟨c, e, good⟩ := Nat.sInf_mem (show feasible.Nonempty from ⟨_, witness⟩)
  have lo := lower G good
  change sInf feasible = G.maxDegree + 1 ∨ sInf feasible = G.maxDegree + 2
  omega

end OMA.R_opg_behzads_conjecture_R1
