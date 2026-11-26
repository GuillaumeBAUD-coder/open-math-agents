import FormalConjectures.WrittenOnTheWallII.GraphConjecture33

/-! A rooted tree with three short branches and a binary tree at the end of a fourth. -/

open SimpleGraph

namespace OMA.Branches

abbrev V := Fin 20

def parent : V → V := ![0,0,0,0,0,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11]

def graph : SimpleGraph V where
  Adj x y := (x < y ∧ parent y = x) ∨ (y < x ∧ parent x = y)
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨fun x => by simp⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

lemma connected : graph.Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨0, fun v => ?_⟩
  induction v using WellFounded.induction (measure (fun v : V => v.val)).wf with
  | h v ih =>
    by_cases hz : v = 0
    · subst v
      exact Reachable.refl _
    have lower := (by decide : ∀ v : V, v ≠ 0 → parent v < v) v hz
    exact (ih (parent v) lower).trans (show graph.Adj (parent v) v from Or.inl ⟨lower,rfl⟩).reachable

def level : V → ℕ := ![0,1,1,1,1,2,3,3,4,4,4,4,5,5,5,5,5,5,5,5]

lemma walk_bound {v w : V} (p : graph.Walk v w) : level w ≤ level v + p.length := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    have := (by decide : ∀ a b, graph.Adj a b → level b ≤ level a + 1) a b h
    rw [Walk.length_cons]
    omega

lemma dist_lower (v : V) : level v ≤ graph.dist 0 v := by
  obtain ⟨p, hp⟩ := connected.exists_walk_length_eq_dist 0 v
  have h := walk_bound p
  simpa [hp, show level 0 = 0 by decide] using h

lemma max_set : {v : V | graph.degree v = graph.maxDegree} = ({0} : Set V) := by
  ext v
  exact (by decide : ∀ v : V, graph.degree v = graph.maxDegree ↔ v = 0) v

/- The maximum number of further edges after a directed edge on a non-backtracking path. -/
def remaining (a b : V) : ℕ :=
  if a < b then ![0,0,0,0,4,3,2,2,1,1,1,1,0,0,0,0,0,0,0,0] b
  else ![0,5,5,5,1,2,3,3,4,4,4,4,5,5,5,5,5,5,5,5] a

lemma upper : path graph ≤ 7 := by
  apply path_le_of_not_exists_inducedPath_succ
  rintro ⟨f, hf, hadj⟩
  have edge : ∀ i : Fin 7, graph.Adj (f i.castSucc) (f i.succ) := by
    intro i
    apply (hadj _ _).mpr
    exact Or.inl rfl
  let r (i : Fin 7) := remaining (f i.castSucc) (f i.succ)
  have step (i : Fin 6) : r i.succ < r i.castSucc := by
    have decrease : ∀ a b c : V, graph.Adj a b → graph.Adj b c → a ≠ c →
        remaining b c < remaining a b := by decide
    apply decrease _ _ _ (edge i.castSucc) (edge i.succ)
    exact fun h => (by decide : ∀ k : Fin 6, k.castSucc.castSucc ≠ k.succ.succ) i (hf h)
  have start : r 0 ≤ 5 :=
    (by decide : ∀ a b : V, remaining a b ≤ 5) _ _
  have h0 : r 1 < r 0 := step 0
  have h1 : r 2 < r 1 := step 1
  have h2 : r 3 < r 2 := step 2
  have h3 : r 4 < r 3 := step 3
  have h4 : r 5 < r 4 := step 4
  have h5 : r 6 < r 5 := step 5
  omega

def others : Finset V := Finset.univ.erase 0

lemma sum_lower : (68 : ℝ) ≤ ∑ v ∈ others, (graph.dist 0 v : ℝ) := by
  have h : (68 : ℕ) ≤ ∑ v ∈ others, graph.dist 0 v := by
    calc
      68 = ∑ v ∈ others, level v := by decide
      _ ≤ _ := Finset.sum_le_sum fun v _ => dist_lower v
  exact_mod_cast h

end OMA.Branches

open OMA.Branches

theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture33.conjecture33 := by
  intro allGraphs
  have h := allGraphs V graph connected
  dsimp only at h
  generalize hq : @Finset.filter (V × V) (fun p => graph.dist p.1 p.2 ≠ 0) _ _ = q at h
  let pairs : Finset (V × V) := ({0} : Finset V) ×ˢ others
  have he : q = pairs := by
    rw [← hq]
    ext ⟨a,b⟩
    have hm : graph.degree a = graph.maxDegree ↔ a = 0 := by
      change a ∈ {v : V | graph.degree v = graph.maxDegree} ↔ _
      rw [max_set]
      rfl
    simp [pairs, others, Finset.mem_product, connected.dist_eq_zero_iff, hm]
    grind
  rw [he] at h
  have hcard : pairs.card = 19 := by decide
  have hsum : ∑ p ∈ pairs, (graph.dist p.1 p.2 : ℝ) = ∑ v ∈ others, (graph.dist 0 v : ℝ) := by
    simp [pairs, Finset.sum_product]
  rw [hsum, hcard] at h
  have hp : (path graph : ℤ) ≤ 7 := by exact_mod_cast upper
  have hh := Int.ceil_le.mp (h.trans hp)
  norm_num at hh
  linarith [sum_lower]

