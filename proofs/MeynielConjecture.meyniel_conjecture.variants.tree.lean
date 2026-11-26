import FormalConjectures.Wikipedia.MeynielConjecture

-- Problem: Trees are cop-win (Nowakowski–Winkler 1983).
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/MeynielConjecture.lean:158 (declaration MeynielConjecture.meyniel_conjecture.variants.tree)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA

open SimpleGraph

variable {V : Type} {G : SimpleGraph V}

/-- In a tree every path is a geodesic. -/
theorem path_len (ha : G.IsAcyclic) (hc : G.Connected) {u v : V} (p : G.Walk u v)
    (hp : p.IsPath) : p.length = G.dist u v := by
  obtain ⟨q, hq, hql⟩ := hc.exists_path_of_dist u v
  have h := (ha.subsingleton_path u v).elim ⟨p, hp⟩ ⟨q, hq⟩
  have h' : p = q := congrArg Subtype.val h
  rw [h', hql]

/-- In a tree, distances to the two ends of an edge differ by exactly one. -/
theorem dist_adj (ha : G.IsAcyclic) (hc : G.Connected) (x : V) {y z : V} (h : G.Adj y z) :
    G.dist x z = G.dist x y + 1 ∨ G.dist x y = G.dist x z + 1 := by
  classical
  obtain ⟨p, hp, hpl⟩ := hc.exists_path_of_dist x y
  by_cases hz : z ∈ p.support
  · right
    have h1 := path_len ha hc _ (hp.takeUntil hz)
    have h2 := path_len ha hc _ (hp.dropUntil hz)
    have h3 := congrArg Walk.length (p.take_spec hz)
    rw [Walk.length_append] at h3
    have h4 : G.dist z y = 1 := dist_eq_one_iff_adj.mpr h.symm
    omega
  · left
    have h1 := path_len ha hc _ (hp.concat hz h)
    rw [Walk.length_concat] at h1
    omega

/-- From `c ≠ r` one can step to a neighbour of `c` that is closer to `r`. -/
theorem step_toward (hc : G.Connected) {c r : V} (hne : c ≠ r) :
    ∃ c', G.Adj c c' ∧ G.dist c' r + 1 = G.dist c r := by
  obtain ⟨p, hpl⟩ := hc.exists_walk_length_eq_dist c r
  cases p with
  | nil => exact absurd rfl hne
  | @cons _ c' _ h q =>
    refine ⟨c', h, ?_⟩
    rw [Walk.length_cons] at hpl
    have h1 := dist_le q
    have h2 := hc.dist_triangle (u := c) (v := c') (w := r)
    have h3 : G.dist c c' = 1 := dist_eq_one_iff_adj.mpr h
    omega

/-- In a tree a vertex has at most one neighbour closer to a given base point. -/
theorem parent_unique (ha : G.IsAcyclic) (hc : G.Connected) (x : V) {y1 y2 z : V}
    (h1 : G.Adj y1 z) (h2 : G.Adj y2 z)
    (d1 : G.dist x y1 + 1 = G.dist x z) (d2 : G.dist x y2 + 1 = G.dist x z) : y1 = y2 := by
  obtain ⟨p1, hp1⟩ := hc.exists_walk_length_eq_dist x y1
  obtain ⟨p2, hp2⟩ := hc.exists_walk_length_eq_dist x y2
  have e1 : (p1.concat h1).IsPath :=
    Walk.isPath_of_length_eq_dist _ (by rw [Walk.length_concat]; omega)
  have e2 : (p2.concat h2).IsPath :=
    Walk.isPath_of_length_eq_dist _ (by rw [Walk.length_concat]; omega)
  have h := (ha.subsingleton_path x z).elim ⟨_, e1⟩ ⟨_, e2⟩
  have h' : p1.concat h1 = p2.concat h2 := congrArg Subtype.val h
  obtain ⟨hv, -⟩ := Walk.concat_inj h'
  exact hv

/-- If the cop at `c` lies between the base point and the robber, a robber move keeps it so. -/
theorem robber_step (ha : G.IsAcyclic) (hc : G.Connected) (c0 c r r' : V)
    (hI : G.dist c0 r = G.dist c0 c + G.dist c r) (hne : c ≠ r) (hadj : G.Adj r r') :
    G.dist c0 r' = G.dist c0 c + G.dist c r' := by
  have t := hc.dist_triangle (u := c0) (v := c) (w := r')
  rcases dist_adj ha hc c0 hadj with a | a <;> rcases dist_adj ha hc c hadj with b | b
  · omega
  · omega
  · exfalso
    obtain ⟨s, hs, hsd⟩ := step_toward hc (Ne.symm hne)
    have k1 := dist_comm (G := G) (u := s) (v := c)
    have k2 := dist_comm (G := G) (u := r) (v := c)
    have ts := hc.dist_triangle (u := c0) (v := c) (w := s)
    rcases dist_adj ha hc c0 hs with e | e
    · omega
    · have hsr := parent_unique ha hc c0 hs.symm hadj.symm (by omega) (by omega)
      subst hsr
      omega
  · omega

/-- The cop, always stepping towards the robber, wins within `n` rounds once it is deep enough. -/
theorem cop_wins (ha : G.IsAcyclic) (hc : G.Connected) (c0 : V) (B : ℕ)
    (hB : ∀ x, G.dist c0 x ≤ B) :
    ∀ n c r, G.dist c0 r = G.dist c0 c + G.dist c r → B ≤ n + G.dist c0 c →
      MeynielConjecture.CopsCatchWithin G 1 n (fun _ => c) r := by
  intro n
  induction n with
  | zero =>
    intro c r hI hn
    have hr := hB r
    have h0 : G.dist c r = 0 := by omega
    exact ⟨0, hc.dist_eq_zero_iff.mp h0⟩
  | succ n ih =>
    intro c r hI hn
    by_cases hcr : c = r
    · exact Or.inl ⟨0, hcr⟩
    · obtain ⟨c', hadj, hd⟩ := step_toward hc hcr
      have t := hc.dist_triangle (u := c0) (v := c') (w := r)
      have t2 := hc.dist_triangle (u := c0) (v := c) (w := c')
      have h1 : G.dist c c' = 1 := dist_eq_one_iff_adj.mpr hadj
      have hI' : G.dist c0 r = G.dist c0 c' + G.dist c' r := by omega
      refine Or.inr ⟨fun _ => c', fun _ => Or.inr hadj, ?_⟩
      by_cases hc'r : c' = r
      · exact Or.inl ⟨0, hc'r⟩
      · refine Or.inr fun r' hstep => ?_
        apply ih
        · rcases hstep with rfl | hrr
          · exact hI'
          · exact robber_step ha hc c0 c' r r' hI' hc'r hrr
        · omega

end OMA

theorem OMA.solution : type_of% @MeynielConjecture.meyniel_conjecture.variants.tree := by
  intro V instF instN G hc ha
  refine le_antisymm (Nat.sInf_le ?_) (MeynielConjecture.one_le_copNumber G)
  obtain ⟨c0⟩ := instN
  refine ⟨fun _ => c0, fun r => ⟨Finset.univ.sup (fun x => G.dist c0 x), ?_⟩⟩
  apply OMA.cop_wins ha hc c0 _
    (fun x => Finset.le_sup (f := fun x => G.dist c0 x) (Finset.mem_univ x))
  · simp
  · exact Nat.le_add_right _ _
