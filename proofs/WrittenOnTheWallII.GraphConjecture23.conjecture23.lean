import FormalConjectures.WrittenOnTheWallII.GraphConjecture23

/-! Four disjoint triangles along a path give a counterexample on nineteen vertices. -/

open SimpleGraph

namespace OMA.Wall

abbrev V := Fin 19

def edges : List (V × V) :=
  [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(9,10),
   (0,11),(1,11),(3,12),(4,12),(6,13),(7,13),(9,14),(10,14),
   (0,15),(0,16),(10,17),(10,18)]

def graph : SimpleGraph V where
  Adj x y := (x,y) ∈ edges ∨ (y,x) ∈ edges
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

lemma connected : graph.Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨0, fun v => ?_⟩
  induction v using WellFounded.induction (measure (fun v : V => v.val)).wf with
  | h v ih =>
    by_cases hv : v = 0
    · subst v
      exact Reachable.refl _
    have lower : ∀ v : V, v ≠ 0 → ∃ u : V, u.val < v.val ∧ graph.Adj u v := by decide
    obtain ⟨u, hu, ha⟩ := lower v hv
    exact (ih u hu).trans ha.reachable

def layer : V → ℕ := ![0,1,2,3,4,5,6,7,8,9,10,0,3,6,9,0,0,10,10]

lemma walk_bound {u v : V} (p : graph.Walk u v) : layer v ≤ layer u + p.length := by
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
    have step : ∀ x y : V, graph.Adj x y → layer y ≤ layer x + 1 := by decide
    have := step a b hab
    rw [Walk.length_cons]
    omega

lemma dist_bound : 10 ≤ graph.dist 0 10 := by
  obtain ⟨p, hp⟩ := connected.exists_walk_length_eq_dist 0 10
  have h := walk_bound p
  rw [hp] at h
  simpa [layer] using h

lemma max_set : {v : V | graph.degree v = graph.maxDegree} = ({0,10} : Set V) := by
  ext v
  change graph.degree v = graph.maxDegree ↔ v = 0 ∨ v = 10
  exact (by decide : ∀ x : V, graph.degree x = graph.maxDegree ↔ x = 0 ∨ x = 10) v

lemma average_bound : 10 ≤ distAvgSet graph ({0,10} : Set V) := by
  classical
  let pairs : Finset (V × V) := {((0 : V),10), (10,0)}
  have hn : ((0 : V), (10 : V)) ≠ (10,0) := by decide
  unfold distAvgSet
  extract_lets q
  have he : q = pairs := by
    ext ⟨x,y⟩
    simp [q, pairs, Finset.mem_product, Prod.mk.injEq]
    grind
  rw [he]
  simp [pairs, hn, graph.dist_comm (u := 10) (v := 0)]
  <;> exact dist_bound


def independent : Finset V := {2,5,8,11,12,13,14,15,16,17,18}

lemma indep_bound : 11 ≤ graph.indepNum := by
  have hi : graph.IsIndepSet independent := by
    intro x hx y hy hxy
    exact (by decide : ∀ x ∈ independent, ∀ y ∈ independent, x ≠ y → ¬ graph.Adj x y)
      x hx y hy hxy
  exact hi.card_le_indepNum

def leftVertex : Fin 4 → V := ![0,3,6,9]
def rightVertex : Fin 4 → V := ![1,4,7,10]
def thirdVertex : Fin 4 → V := ![11,12,13,14]
def triangle (i : Fin 4) : Finset V := {leftVertex i, rightVertex i, thirdVertex i}

lemma omitted (s : Finset V) (hb : (graph.induce s).IsBipartite) (i : Fin 4) :
    ∃ v ∈ triangle i, v ∉ s := by
  obtain ⟨c, hc⟩ := (induce_isBipartite_iff_exists_coloring graph s).mp hb
  by_contra! h
  have ha := h (leftVertex i) (by simp [triangle])
  have hb' := h (rightVertex i) (by simp [triangle])
  have hd := h (thirdVertex i) (by simp [triangle])
  have he : ∀ j, graph.Adj (leftVertex j) (rightVertex j) ∧
      graph.Adj (leftVertex j) (thirdVertex j) ∧ graph.Adj (rightVertex j) (thirdVertex j) := by decide
  have h₁ := hc _ ha _ hb' (he i).1
  have h₂ := hc _ ha _ hd (he i).2.1
  have h₃ := hc _ hb' _ hd (he i).2.2
  exact (by decide : ∀ a b d : Fin 2, a ≠ b → a ≠ d → b ≠ d → False) _ _ _ h₁ h₂ h₃

lemma card_bound (s : Finset V) (hb : (graph.induce s).IsBipartite) : s.card ≤ 15 := by
  choose f hf hn using omitted s hb
  have disj : ∀ i j : Fin 4, ∀ v : V, v ∈ triangle i → v ∈ triangle j → i = j := by decide
  have inj : Function.Injective f := by
    intro i j h
    exact disj i j (f j) (h ▸ hf i) (hf j)
  let e : Fin 4 ↪ ↥(sᶜ : Finset V) :=
    ⟨fun i => ⟨f i, Finset.mem_compl.mpr (hn i)⟩, fun i j h => inj (congrArg Subtype.val h)⟩
  have h := Fintype.card_le_of_embedding e
  simp at h
  have hs := s.card_le_univ
  simp at hs
  omega

lemma bip_bound : b graph ≤ 15 := by
  unfold b
  have h : graph.largestInducedBipartiteSubgraphSize ≤ 15 := by
    unfold largestInducedBipartiteSubgraphSize
    apply csSup_le
    · refine ⟨0, ∅, ?_, rfl⟩
      rw [induce_isBipartite_iff_exists_coloring]
      exact ⟨fun _ => 0, by simp⟩
    · rintro n ⟨s, hs, rfl⟩
      exact card_bound s hs
  exact_mod_cast h

end OMA.Wall

open OMA.Wall

theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture23.conjecture23 := by
  intro h
  have claim := h V graph connected
  dsimp only at claim
  rw [max_set] at claim
  have hi : (11 : ℝ) ≤ graph.indepNum := by exact_mod_cast indep_bound
  have hf : (16 : ℤ) ≤ ⌊(graph.indepNum : ℝ) + distAvgSet graph ({0,10} : Set V) / 2⌋ := by
    apply Int.le_floor.mpr
    push_cast
    linarith [average_bound]
  have hf' : (16 : ℝ) ≤ (⌊(graph.indepNum : ℝ) + distAvgSet graph ({0,10} : Set V) / 2⌋ : ℤ) := by
    exact_mod_cast hf
  linarith [bip_bound]
