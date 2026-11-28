import OMAStatements.S_wp_degree_diameter_problem

-- Problem: Degree diameter problem (the maximum in the definition of n_{d,k} is attained)
-- Upstream: formal-conjectures statements/wp-degree-diameter-problem.lean:0
-- Credit: @LordDavidDev (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OMA.S_wp_degree_diameter_problem

theorem OMA.solution : type_of% @OMA.S_wp_degree_diameter_problem.main := by
  classical
  intro d k _ _
  -- A graph of maximum degree at most d and extended diameter at most k has at most
  -- (d + 1) ^ k vertices: the ball of radius r around a fixed vertex has at most
  -- (d + 1) ^ r elements, and the ball of radius k is everything.
  have key : ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      (∀ v, Set.ncard (G.neighborSet v) ≤ d) → G.ediam ≤ (k : ℕ∞) →
      Fintype.card V ≤ (d + 1) ^ k := by
    intro V _ G hdeg hdia
    by_cases hne : Nonempty V
    · obtain ⟨root⟩ := hne
      haveI : Nonempty V := ⟨root⟩
      have hconn : G.Connected :=
        SimpleGraph.connected_of_ediam_ne_top (ne_top_of_le_ne_top (by simp) hdia)
      -- the degree bound, phrased for a Finset of neighbours
      have hneighbor : ∀ u : V, (Finset.univ.filter (fun w => G.Adj u w)).card ≤ d := by
        intro u
        have hcard : (G.neighborSet u).ncard = (Finset.univ.filter (fun w => G.Adj u w)).card := by
          rw [Set.ncard_eq_toFinset_card]
          congr 1
          ext w
          simp
        rw [← hcard]
        exact hdeg u
      -- the ball of radius 0 is a single vertex
      have hzero : Finset.univ.filter (fun v => G.dist v root ≤ 0) = {root} := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro h
          exact (hconn.preconnected v root).dist_eq_zero_iff.mp (Nat.le_zero.mp h)
        · rintro rfl
          simp
      -- one more layer costs at most a factor (d + 1)
      have hstep : ∀ r : ℕ,
          (Finset.univ.filter (fun v => G.dist v root ≤ r + 1)).card ≤
            (Finset.univ.filter (fun v => G.dist v root ≤ r)).card * (d + 1) := by
        intro r
        have hsub : Finset.univ.filter (fun v => G.dist v root ≤ r + 1) ⊆
            Finset.univ.filter (fun v => G.dist v root ≤ r) ∪
              (Finset.univ.filter (fun v => G.dist v root ≤ r)).biUnion
                (fun u => Finset.univ.filter (fun w => G.Adj u w)) := by
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
          by_cases hvr : G.dist v root ≤ r
          · exact Finset.mem_union_left _ (by simp [hvr])
          · simp only [not_le] at hvr
            have hdr : G.dist v root = r + 1 := le_antisymm hv hvr
            obtain ⟨p, hp⟩ := (hconn.preconnected v root).exists_walk_length_eq_dist
            rw [hdr] at hp
            have hnil : ¬ p.Nil := by
              rw [SimpleGraph.Walk.not_nil_iff_lt_length]
              omega
            have hdist : G.dist p.snd root ≤ r := by
              calc G.dist p.snd root ≤ p.tail.length := SimpleGraph.dist_le p.tail
                _ = p.length - 1 := SimpleGraph.Walk.length_tail p
                _ = r := by omega
            refine Finset.mem_union_right _ ?_
            simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨p.snd, hdist, (p.adj_snd hnil).symm⟩
        calc (Finset.univ.filter (fun v => G.dist v root ≤ r + 1)).card
            ≤ (Finset.univ.filter (fun v => G.dist v root ≤ r) ∪
                (Finset.univ.filter (fun v => G.dist v root ≤ r)).biUnion
                  (fun u => Finset.univ.filter (fun w => G.Adj u w))).card :=
              Finset.card_le_card hsub
          _ ≤ (Finset.univ.filter (fun v => G.dist v root ≤ r)).card +
                ((Finset.univ.filter (fun v => G.dist v root ≤ r)).biUnion
                  (fun u => Finset.univ.filter (fun w => G.Adj u w))).card :=
              Finset.card_union_le _ _
          _ ≤ (Finset.univ.filter (fun v => G.dist v root ≤ r)).card +
                ∑ u ∈ Finset.univ.filter (fun v => G.dist v root ≤ r),
                  (Finset.univ.filter (fun w => G.Adj u w)).card :=
              Nat.add_le_add_left Finset.card_biUnion_le _
          _ ≤ (Finset.univ.filter (fun v => G.dist v root ≤ r)).card +
                ∑ _u ∈ Finset.univ.filter (fun v => G.dist v root ≤ r), d :=
              Nat.add_le_add_left (Finset.sum_le_sum (fun u _ => hneighbor u)) _
          _ = (Finset.univ.filter (fun v => G.dist v root ≤ r)).card * (d + 1) := by
              rw [Finset.sum_const, smul_eq_mul]
              ring
      have hbounded : ∀ r : ℕ,
          (Finset.univ.filter (fun v => G.dist v root ≤ r)).card ≤ (d + 1) ^ r := by
        intro r
        induction r with
        | zero => rw [hzero]; simp
        | succ r ih =>
            calc (Finset.univ.filter (fun v => G.dist v root ≤ r + 1)).card
                ≤ (Finset.univ.filter (fun v => G.dist v root ≤ r)).card * (d + 1) := hstep r
              _ ≤ (d + 1) ^ r * (d + 1) := Nat.mul_le_mul_right _ ih
              _ = (d + 1) ^ (r + 1) := by rw [pow_succ]
      -- the ball of radius k is everything
      have htop : Finset.univ.filter (fun v => G.dist v root ≤ k) = Finset.univ := by
        apply Finset.filter_true_of_mem
        intro v _
        have h1 : G.edist v root ≤ (k : ℕ∞) := le_trans SimpleGraph.edist_le_ediam hdia
        have h2 : ((G.dist v root : ℕ) : ℕ∞) = G.edist v root :=
          (hconn.preconnected v root).coe_dist_eq_edist
        rw [← h2] at h1
        exact WithTop.coe_le_coe.mp h1
      have hcard : Fintype.card V = (Finset.univ.filter (fun v => G.dist v root ≤ k)).card := by
        rw [htop, Finset.card_univ]
      rw [hcard]
      exact hbounded k
    · haveI : IsEmpty V := not_nonempty_iff.mp hne
      rw [Fintype.card_eq_zero]
      exact Nat.zero_le _
  have hnonempty : (vertexCounts d k).Nonempty := by
    refine ⟨0, PEmpty, inferInstance, ⊥, rfl, ?_, ?_⟩
    · intro v
      exact isEmptyElim v
    · rw [SimpleGraph.ediam_le_iff]
      intro u
      exact isEmptyElim u
  have hbdd : BddAbove (vertexCounts d k) := by
    refine ⟨(d + 1) ^ k, ?_⟩
    rintro c ⟨V, instV, G, hcard, hdeg, hdia⟩
    letI := instV
    rw [← hcard]
    exact key V G hdeg hdia
  obtain ⟨V, instV, G, hcard, hdeg, hdia⟩ := Nat.sSup_mem hnonempty hbdd
  exact ⟨V, instV, G, hcard, hdeg, hdia⟩
