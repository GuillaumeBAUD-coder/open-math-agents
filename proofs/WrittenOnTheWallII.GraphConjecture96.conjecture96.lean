import FormalConjectures.WrittenOnTheWallII.GraphConjecture96

-- Problem: Written on the Wall II - Conjecture 96
-- Upstream: formal-conjectures FormalConjectures/WrittenOnTheWallII/GraphConjecture96.lean:56 (declaration WrittenOnTheWallII.GraphConjecture96.conjecture96)
-- Credit: @JamesSlash (the owner of the agent is credited as the solver)
--
-- Prior work (found after this proof was written, stated here for honesty): the same breadth-first
-- parent argument was announced before this file by others, in particular
--   * umaia1234/agentic-conjectures pull request 67 (2026-10-25), a Lean proof for n >= 2,
--   * J. J. Gebendorfer, Local independence along breadth-first layers: a proof of Written on the
--     Wall II Conjecture 96 (google-deepmind/formal-conjectures issue 7664, 2026-10-28),
--   * v3ai/openmath (2026-10-30).
-- This file is therefore an independent rediscovery and formalization against the pinned
-- formal-conjectures statement, not a first proof of the conjecture.
--
-- Idea of the proof. Fix any vertex v and let L be the maximum local independence number.
-- Take a maximum independent set I and the breadth-first layers around v. Send every x in I that
-- lies at even distance from v to itself, and every x in I at odd distance to a neighbour one layer
-- closer to v (a BFS parent). Every vertex of I is thus charged to a vertex u at even distance.
-- The vertices charged to u form an independent set inside the neighbourhood of u (or are just u).
-- If u is not v, then u has its own BFS parent q; q is not adjacent to anything two layers further
-- out, so q can be added to the charged set, which therefore has at most L - 1 elements.
-- The vertex v itself receives at most L charges. Summing over the even vertices gives
--   alpha(G) <= L + (distEven v - 1) (L - 1) = 1 + distEven v * (L - 1)
-- for every v, in particular for the vertex minimising distEven.

open SimpleGraph

namespace OMA96

/-- An independent set of neighbours of `u` has at most `indepNeighborsCard G u` elements. -/
lemma card_le_indepNeighborsCard {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (u : α) (S : Finset α)
    (hadj : ∀ x ∈ S, G.Adj u x) (hind : G.IsIndepSet (S : Set α)) :
    S.card ≤ indepNeighborsCard G u := by
  classical
  unfold indepNeighborsCard
  have ht : (S.subtype (fun x => x ∈ G.neighborSet u)).card = S.card := by
    rw [Finset.card_subtype]
    congr 1
    exact Finset.filter_true_of_mem (fun x hx => hadj x hx)
  rw [← ht]
  apply SimpleGraph.IsIndepSet.card_le_indepNum
  intro a ha b hb hab hadj'
  have ha' : (a : α) ∈ S := by simpa using ha
  have hb' : (b : α) ∈ S := by simpa using hb
  exact hind ha' hb' (fun h => hab (Subtype.ext h)) (by simpa using hadj')

/-- In a connected graph every vertex other than `v` has a neighbour one step closer to `v`. -/
lemma exists_parent {α : Type*} (G : SimpleGraph α) (hG : G.Connected) (v x : α) (hx : x ≠ v) :
    ∃ p, G.Adj p x ∧ G.dist v p + 1 = G.dist v x := by
  obtain ⟨w, hw⟩ := hG.exists_walk_length_eq_dist x v
  obtain ⟨p, hadj, w', rfl⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hx w
  refine ⟨p, hadj.symm, ?_⟩
  have h1 : G.dist p v ≤ w'.length := SimpleGraph.dist_le w'
  have h2 : G.dist v x ≤ G.dist v p + G.dist p x := hG.dist_triangle
  have h3 : G.dist p x = 1 := by
    rw [SimpleGraph.dist_eq_one_iff_adj]
    exact hadj.symm
  have h4 : (SimpleGraph.Walk.cons hadj w').length = w'.length + 1 :=
    SimpleGraph.Walk.length_cons _ _
  have h5 : G.dist p v = G.dist v p := SimpleGraph.dist_comm
  have h6 : G.dist x v = G.dist v x := SimpleGraph.dist_comm
  omega

/-- Adjacent vertices lie in the same or in consecutive distance layers. -/
lemma dist_le_of_adj {α : Type*} (G : SimpleGraph α) (hG : G.Connected) (v a b : α)
    (h : G.Adj a b) : G.dist v a ≤ G.dist v b + 1 := by
  have h2 : G.dist v a ≤ G.dist v b + G.dist b a := hG.dist_triangle
  have h3 : G.dist b a = 1 := by
    rw [SimpleGraph.dist_eq_one_iff_adj]
    exact h.symm
  omega

/-- The charging argument, for an arbitrary base vertex `v` and any bound `L` on the local
independence numbers. Stated without subtraction. -/
lemma core {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]
    (G : SimpleGraph α) (hG : G.Connected) (v : α) (L : ℕ)
    (hL : ∀ u, indepNeighborsCard G u ≤ L) :
    G.indepNum + distEven G v ≤ 1 + distEven G v * L := by
  classical
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  have hIind : G.IsIndepSet (I : Set α) := hI.isIndepSet
  have hIcard : I.card = G.indepNum := hI.card_eq
  have hpar : ∀ x, x ≠ v → ∃ p, G.Adj p x ∧ G.dist v p + 1 = G.dist v x :=
    fun x hx => exists_parent G hG v x hx
  choose! par hpar using hpar
  let f : α → α := fun x => if Even (G.dist v x) then x else par x
  let E : Finset α := Finset.univ.filter (fun w => Even (G.dist v w))
  have hEcard : distEven G v = E.card := rfl
  have hodd_ne : ∀ x, ¬ Even (G.dist v x) → x ≠ v := by
    intro x hx hxv
    apply hx
    rw [hxv, SimpleGraph.dist_self]
    exact Even.zero
  have hf_even : ∀ x, Even (G.dist v x) → f x = x := fun x hx => if_pos hx
  have hf_odd : ∀ x, ¬ Even (G.dist v x) →
      G.Adj (f x) x ∧ G.dist v (f x) + 1 = G.dist v x := by
    intro x hx
    have hfx : f x = par x := if_neg hx
    rw [hfx]
    exact hpar x (hodd_ne x hx)
  have hfE : ∀ x ∈ I, f x ∈ E := by
    intro x _
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hx : Even (G.dist v x)
    · rw [hf_even x hx]
      exact hx
    · obtain ⟨_, h2⟩ := hf_odd x hx
      by_contra hne
      exact hx (h2 ▸ Nat.even_add_one.mpr hne)
  have hvE : v ∈ E := by
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [SimpleGraph.dist_self]
    exact Even.zero
  have hfib : ∀ u ∈ E,
      (I.filter (fun x => f x = u)).card + (if u = v then 0 else 1) ≤ L := by
    intro u hu
    have hue : Even (G.dist v u) := by
      simpa only [E, Finset.mem_filter, Finset.mem_univ, true_and] using hu
    by_cases huI : u ∈ I
    · have hsub : I.filter (fun x => f x = u) ⊆ {u} := by
        intro x hx
        rw [Finset.mem_filter] at hx
        obtain ⟨hxI, hfx⟩ := hx
        rw [Finset.mem_singleton]
        by_cases hxe : Even (G.dist v x)
        · rw [hf_even x hxe] at hfx
          exact hfx
        · obtain ⟨hadj, _⟩ := hf_odd x hxe
          rw [hfx] at hadj
          exact absurd hadj (hIind huI hxI hadj.ne)
      have hc : (I.filter (fun x => f x = u)).card ≤ 1 := by
        calc (I.filter (fun x => f x = u)).card ≤ ({u} : Finset α).card :=
              Finset.card_le_card hsub
          _ = 1 := Finset.card_singleton u
      by_cases huv : u = v
      · rw [if_pos huv]
        obtain ⟨z, hz⟩ := exists_ne u
        obtain ⟨p, hp, _⟩ := exists_parent G hG z u hz.symm
        have h0 := card_le_indepNeighborsCard G u {p}
          (by
            intro y hy
            rw [Finset.mem_singleton] at hy
            rw [hy]
            exact hp.symm)
          (by simp)
        rw [Finset.card_singleton] at h0
        have h1 := hL u
        omega
      · rw [if_neg huv]
        obtain ⟨hq, hqd⟩ := hpar u huv
        have hq_ne : par u ≠ v := by
          intro h
          rw [h, SimpleGraph.dist_self] at hqd
          rw [← hqd] at hue
          exact absurd hue (by decide)
        obtain ⟨hq', hqd'⟩ := hpar (par u) hq_ne
        have hnadj : ¬ G.Adj u (par (par u)) := by
          intro h
          have h3 := dist_le_of_adj G hG v u (par (par u)) h
          omega
        have hne : u ≠ par (par u) := by
          intro h
          rw [← h] at hqd'
          omega
        have h0 := card_le_indepNeighborsCard G (par u) {u, par (par u)}
          (by
            intro y hy
            rw [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with hy | hy
            · rw [hy]
              exact hq
            · rw [hy]
              exact hq'.symm)
          (by
            intro a ha b hb hab
            simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
              Set.mem_singleton_iff] at ha hb
            rcases ha with ha | ha <;> rcases hb with hb | hb
            · exact absurd (ha.trans hb.symm) hab
            · rw [ha, hb]
              exact hnadj
            · rw [ha, hb]
              exact fun h => hnadj h.symm
            · exact absurd (ha.trans hb.symm) hab)
        rw [Finset.card_pair hne] at h0
        have h1 := hL (par u)
        omega
    · have hch : ∀ x ∈ I.filter (fun x => f x = u),
          G.Adj u x ∧ G.dist v u + 1 = G.dist v x := by
        intro x hx
        rw [Finset.mem_filter] at hx
        obtain ⟨hxI, hfx⟩ := hx
        by_cases hxe : Even (G.dist v x)
        · rw [hf_even x hxe] at hfx
          rw [hfx] at hxI
          exact absurd hxI huI
        · have h3 := hf_odd x hxe
          rw [hfx] at h3
          exact h3
      have hFind : G.IsIndepSet ((I.filter (fun x => f x = u) : Finset α) : Set α) := by
        intro a ha b hb hab
        exact hIind (Finset.mem_of_mem_filter a ha) (Finset.mem_of_mem_filter b hb) hab
      by_cases huv : u = v
      · rw [if_pos huv]
        have h0 := card_le_indepNeighborsCard G u (I.filter (fun x => f x = u))
          (fun x hx => (hch x hx).1) hFind
        have h1 := hL u
        omega
      · rw [if_neg huv]
        obtain ⟨hq, hqd⟩ := hpar u huv
        have hqF : par u ∉ I.filter (fun x => f x = u) := by
          intro h
          have h3 := (hch _ h).2
          omega
        have h0 := card_le_indepNeighborsCard G u (insert (par u) (I.filter (fun x => f x = u)))
          (by
            intro y hy
            rw [Finset.mem_insert] at hy
            rcases hy with hy | hy
            · rw [hy]
              exact hq.symm
            · exact (hch y hy).1)
          (by
            intro a ha b hb hab
            rw [Finset.coe_insert, Set.mem_insert_iff] at ha hb
            rcases ha with ha | ha <;> rcases hb with hb | hb
            · exact absurd (ha.trans hb.symm) hab
            · rw [ha]
              intro h
              have h3 := dist_le_of_adj G hG v b (par u) h.symm
              have h4 := (hch b hb).2
              omega
            · rw [hb]
              intro h
              have h3 := dist_le_of_adj G hG v a (par u) h
              have h4 := (hch a ha).2
              omega
            · exact hFind ha hb hab)
        rw [Finset.card_insert_of_notMem hqF] at h0
        have h1 := hL u
        omega
  have hsum : I.card = ∑ u ∈ E, (I.filter (fun x => f x = u)).card :=
    Finset.card_eq_sum_card_fiberwise hfE
  have hite : (∑ u ∈ E, (if u = v then 0 else 1)) + 1 = E.card := by
    have h1 : ∑ u ∈ E, ((if u = v then 0 else 1) + (if u = v then 1 else 0)) = ∑ u ∈ E, 1 := by
      apply Finset.sum_congr rfl
      intro u _
      split_ifs <;> rfl
    rw [Finset.sum_add_distrib] at h1
    have h2 : ∑ u ∈ E, (if u = v then 1 else 0) = 1 := by
      rw [Finset.sum_ite_eq' E v (fun _ => 1), if_pos hvE]
    rw [h2] at h1
    rw [h1]
    simp
  have hbound : ∑ u ∈ E, ((I.filter (fun x => f x = u)).card + (if u = v then 0 else 1))
      ≤ ∑ _u ∈ E, L := Finset.sum_le_sum hfib
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← hsum] at hbound
  rw [hEcard, ← hIcard]
  omega

end OMA96

theorem OMA.solution : type_of% @WrittenOnTheWallII.GraphConjecture96.conjecture96 := by
  intro α _ _ _ G h
  intro minDistEven maxL
  have hmem : minDistEven ∈ Finset.univ.image (distEven G) :=
    Finset.min'_mem (Finset.univ.image (distEven G)) _
  obtain ⟨v, -, hv⟩ := Finset.mem_image.mp hmem
  have hL : ∀ u, indepNeighborsCard G u ≤ maxL := by
    intro u
    exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ u))
  have hcore := OMA96.core G h v maxL hL
  rw [hv] at hcore
  have hcore' : (G.indepNum : ℝ) + (minDistEven : ℝ) ≤ 1 + (minDistEven : ℝ) * (maxL : ℝ) := by
    exact_mod_cast hcore
  have hring : 1 + (minDistEven : ℝ) * ((maxL : ℝ) - 1)
      = 1 + (minDistEven : ℝ) * (maxL : ℝ) - (minDistEven : ℝ) := by ring
  rw [hring]
  linarith
