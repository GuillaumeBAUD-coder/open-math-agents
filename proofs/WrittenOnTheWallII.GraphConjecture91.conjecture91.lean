import FormalConjectures.WrittenOnTheWallII.GraphConjecture91

/-! Two squares and a four-clique joined in a chain give a counterexample. -/

open SimpleGraph

universe u

namespace OMA.Squares

abbrev V := ULift.{u} (Fin 12)

def edges : List (Fin 12 × Fin 12) :=
  [(0,1),(1,2),(2,3),(3,0),(3,4),(4,5),(5,6),(6,7),(7,4),(7,8),
   (8,9),(8,10),(8,11),(9,10),(9,11),(10,11)]

def graph : SimpleGraph V.{u} where
  Adj x y := (x.down,y.down) ∈ edges ∨ (y.down,x.down) ∈ edges
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel graph.{u}.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

lemma connected : graph.{u}.Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨ULift.up 0, fun v => ?_⟩
  induction v using WellFounded.induction (measure (fun v : V => v.down.val)).wf with
  | h v ih =>
    by_cases hz : v = ULift.up 0
    · subst v
      exact Reachable.refl _
    have lower : ∀ v : V.{u}, v ≠ ULift.up 0 → ∃ w : V, w.down.val < v.down.val ∧ graph.Adj w v := by decide
    obtain ⟨w, hw, ha⟩ := lower v hz
    exact (ih w hw).trans ha.reachable

def ten : Finset V.{u} := Finset.univ.filter fun v => v.down.val < 10

lemma bip_lower : 10 ≤ b graph.{u} := by
  have hb : (graph.induce (ten.{u} : Set V)).IsBipartite := by
    apply (induce_isBipartite_iff_exists_coloring graph ten).mpr
    refine ⟨fun v => (Fin.ofNat 2 v.down.val), ?_⟩
    decide
  have h : 10 ≤ graph.{u}.largestInducedBipartiteSubgraphSize := by
    unfold largestInducedBipartiteSubgraphSize
    apply le_csSup
    · exact ⟨12, fun _ ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
    · exact ⟨ten, hb, by decide⟩
  unfold b
  exact_mod_cast h

def square : Fin 2 → Fin 4 → Fin 12 := ![![0,1,2,3], ![4,5,6,7]]
def triple : Fin 4 → Fin 3 → Fin 12 := ![![8,9,10],![8,9,11],![8,10,11],![9,10,11]]

lemma no_cycle {n : ℕ} {s : Finset V.{u}} (ha : (graph.induce (s : Set V)).IsAcyclic)
    (hn : 3 ≤ n) (f : Fin n → Fin 12) (hf : Function.Injective f)
    (he : ∀ i j, (cycleGraph n).Adj i j → graph.{0}.Adj (ULift.up (f i)) (ULift.up (f j))) :
    ¬ ∀ i, ULift.up (f i) ∈ s := by
  intro allIn
  apply isAcyclic_iff_free_cycleGraph.mp ha n hn
  let g : Fin n → ↥(s : Set V) := fun i => ⟨ULift.up (f i), allIn i⟩
  exact ⟨⟨⟨g, fun {i j} h => he i j h⟩,
    fun i j h => hf (congrArg (fun x : ↥(s : Set V) => x.val.down) h)⟩⟩

def block : Fin 3 → Finset (Fin 12) := ![{0,1,2,3},{4,5,6,7},{8,9,10,11}]
def capacity : Fin 3 → ℕ := ![3,3,2]

def oversized (j : Fin 3) : Finset (Finset (Fin 12)) :=
  (block j).powerset.filter fun t => capacity j < t.card ∧
    (∀ k, ¬ ∀ i, square k i ∈ t) ∧ (∀ k, ¬ ∀ i, triple k i ∈ t)

lemma local_capacity (j) (t) (ht : t ∈ (block j).powerset)
    (hs : ∀ k, ¬ ∀ i, square k i ∈ t) (hc : ∀ k, ¬ ∀ i, triple k i ∈ t) :
    t.card ≤ capacity j := by
  have checked : ∀ k : Fin 3, oversized k = ∅ := by decide
  by_contra! h
  have mem : t ∈ oversized j := Finset.mem_filter.mpr ⟨ht, h, hs, hc⟩
  simpa [checked] using mem

lemma forest_upper : graph.{u}.largestInducedForestSize ≤ 8 := by
  unfold largestInducedForestSize
  apply csSup_le
  · refine ⟨0, ∅, ?_, rfl⟩
    apply isAcyclic_iff_free_cycleGraph.mpr
    rintro n hn ⟨f⟩
    exact Finset.notMem_empty _ (f ⟨0, by omega⟩).property
  · rintro k ⟨s, ha, rfl⟩
    let e : V ↪ Fin 12 := Equiv.ulift.toEmbedding
    let t := s.map e
    let piece (j : Fin 3) := t ∩ block j
    have hin {j x} (hx : x ∈ piece j) : ULift.up x ∈ s := by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp (Finset.mem_inter.mp hx).1
      exact hv
    have hcap (j) : (piece j).card ≤ capacity j := by
      apply local_capacity j _ (Finset.mem_powerset.mpr Finset.inter_subset_right)
      · intro k hk
        exact no_cycle ha (by decide : 3 ≤ 4) (square k)
          ((by decide : ∀ a, Function.Injective (square a)) k)
          ((by decide : ∀ a i j, (cycleGraph 4).Adj i j →
            graph.{0}.Adj (ULift.up (square a i)) (ULift.up (square a j))) k)
          (fun i => hin (hk i))
      · intro k hk
        exact no_cycle ha (by decide : 3 ≤ 3) (triple k)
          ((by decide : ∀ a, Function.Injective (triple a)) k)
          ((by decide : ∀ a i j, (cycleGraph 3).Adj i j →
            graph.{0}.Adj (ULift.up (triple a i)) (ULift.up (triple a j))) k)
          (fun i => hin (hk i))
    have hcov : t ⊆ piece 0 ∪ piece 1 ∪ piece 2 := by
      intro x hx
      have hx' := (by decide : ∀ x : Fin 12, x ∈ block 0 ∨ x ∈ block 1 ∨ x ∈ block 2) x
      simpa [piece, hx] using hx'
    have hc := Finset.card_le_card hcov
    have h1 := Finset.card_union_le (piece 0) (piece 1)
    have h2 := Finset.card_union_le (piece 0 ∪ piece 1) (piece 2)
    have h0 : (piece 0).card ≤ 3 := hcap 0
    have h1' : (piece 1).card ≤ 3 := hcap 1
    have h2' : (piece 2).card ≤ 2 := hcap 2
    have ht : t.card = s.card := Finset.card_map _
    omega

def weight (v : V.{u}) : ℕ := ![2,2,2,3,3,2,2,3,2,1,1,1] v.down

lemma avg_upper : l graph.{u} ≤ 2 := by
  have bound (v : V.{u}) : indepNeighborsCard graph v ≤ weight v := by
    unfold indepNeighborsCard
    rw [indep_num_eq_computable]
    exact (by decide : ∀ w : V, (graph.induce (graph.neighborSet w)).computable_indep_num ≤ weight w) v
  have hs : ∑ v : V.{u}, indepNeighborsCard graph v ≤ 24 :=
    (Finset.sum_le_sum (fun v _ => bound v)).trans (by decide)
  unfold l averageIndepNeighbors indepNeighbors
  rw [← Nat.cast_sum]
  have hs' : (↑(∑ v : V.{u}, indepNeighborsCard graph v) : ℝ) ≤ 24 := by exact_mod_cast hs
  change (↑(∑ v : V.{u}, indepNeighborsCard graph v) : ℝ) / 12 ≤ 2
  linarith

end OMA.Squares

open OMA.Squares

theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture91.conjecture91 := by
  intro allGraphs
  have claim := allGraphs graph connected
  have hc : ⌈l graph⌉ ≤ 2 := Int.ceil_le.mpr (by simpa using avg_upper)
  have hf : (graph.largestInducedForestSize : ℝ) ≤ 8 := by exact_mod_cast forest_upper
  have hm := mul_le_mul_of_nonneg_left (show (⌈l graph⌉ : ℝ) ≤ 2 by exact_mod_cast hc)
    (Nat.cast_nonneg graph.largestInducedForestSize : (0 : ℝ) ≤ _)
  linarith [bip_lower]
