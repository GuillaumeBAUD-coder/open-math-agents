import FormalConjectures.WrittenOnTheWallII.GraphConjecture72

-- Problem: Written on the Wall II - Conjecture 72
-- Upstream: formal-conjectures FormalConjectures/WrittenOnTheWallII/GraphConjecture72.lean:53 (declaration WrittenOnTheWallII.GraphConjecture72.conjecture72)
-- Credit: @rpinho (the owner of the agent is credited as the solver)
-- Prior art: Falsity of the ceil(A + Lambda/3) <= tree reading first reported 2026-07-23 (@4thRT / VibeMathed 2026-08-17);
-- subsequent refutations include a 28-vertex Lean counterexample (umaia1234/agentic-conjectures#68) and a 31-vertex counterexample
-- with unbounded-deficit family by Jonas J. Gebendorfer (google-deepmind/formal-conjectures#7662, 2026-10-28).
-- Formalizes the minimum-order 17-vertex, 63-edge counterexample (layers 9, 2, 1, 3, 1, 1; A = 74/17, Lambda = 5, tree = 6 < 7).
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! A layered witness for the formal inequality in WOWII Conjecture 72. -/

namespace WOW72Witness

open SimpleGraph

universe u

-- Lifting the vertex type supplies the same witness in every universe of the target.
private abbrev V := ULift.{u} (Fin 17)

private instance (n : ℕ) : OfNat V n := ⟨⟨OfNat.ofNat n⟩⟩

private def layer (v : V) : ℕ :=
  if v.down.val < 9 then 0 else if v.down.val < 11 then 1 else if v.down.val < 12 then 2
  else if v.down.val < 15 then 3 else if v.down.val < 16 then 4 else 5

private def G17 : SimpleGraph V where
  Adj u v := u ≠ v ∧ ((layer u = 0 ∧ layer v = 0) ∨
    layer u + 1 = layer v ∨ layer v + 1 = layer u)
  symm := by constructor; rintro u v ⟨hne, h⟩; exact ⟨hne.symm, by tauto⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private instance : DecidableRel G17.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

-- Count the oriented adjacent pairs on the seventeen vertices.
private theorem edge_count : G17.{u}.edgeFinset.card = 63 := by
  have h := G17.{u}.two_mul_card_edgeFinset
  change 2 * G17.{u}.edgeFinset.card = 126 at h
  omega

private theorem connected : G17.{u}.Connected := by
  apply (connected_iff_exists_forall_reachable G17).2
  refine ⟨11, fun v => ?_⟩
  have r9 := (show G17.{u}.Adj 11 9 by decide).reachable
  have r12 := (show G17.{u}.Adj 11 12 by decide).reachable
  have r15 := r12.trans (show G17.{u}.Adj 12 15 by decide).reachable
  fin_cases v <;> first
    | exact Reachable.refl _
    | exact (show G17.Adj _ _ by decide).reachable
    | apply r9.trans; exact (show G17.Adj _ _ by decide).reachable
    | exact r15
    | apply r15.trans; exact (show G17.Adj _ _ by decide).reachable

private theorem edge_step {u v : V} (h : G17.Adj u v) : layer v ≤ layer u + 1 := by
  rcases h.2 with h | h | h <;> omega

private theorem walk_bound {u v : V} (p : G17.Walk u v) :
    layer v ≤ layer u + p.length := by
  induction p with
  | nil => simp
  | cons h _ ih => have := edge_step h; simp only [Walk.length_cons]; omega

private theorem dist_bound (u v : V) : layer v ≤ layer u + G17.dist u v := by
  obtain ⟨p, hp⟩ := connected.exists_walk_length_eq_dist u v
  simpa [← hp] using walk_bound p

private theorem dist_le_ecc (u v : V) : G17.dist u v ≤ (G17.eccent u).toNat := by
  obtain ⟨w, hw⟩ := G17.exists_edist_eq_eccent_of_finite u
  exact ENat.toNat_le_toNat edist_le_eccent
    (hw ▸ edist_ne_top_iff_reachable.mpr (connected u w))

private theorem average_lower : (74 : ℝ) / 17 ≤ averageEccentricity G17.{u} := by
  have pointwise (v : V.{u}) : max (layer v) (5 - layer v) ≤ (G17.eccent v).toNat := by
    have h₀ := dist_bound 0 v
    have h₅ := dist_bound v 16
    rw [show layer 0 = 0 by rfl, zero_add, G17.dist_comm] at h₀
    rw [show layer 16 = 5 by rfl] at h₅
    have := dist_le_ecc v 0
    have := dist_le_ecc v 16
    omega
  have total : (∑ v : V.{u}, max (layer v) (5 - layer v)) = 74 := by decide
  have bound := Finset.sum_le_sum (s := Finset.univ) (fun (v : V.{u}) _ => pointwise v)
  rw [total] at bound
  unfold averageEccentricity
  rw [Fintype.card_ulift, Fintype.card_fin]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast bound

private theorem independent_lower : 5 ≤ indepNeighborsCard G17.{u} 11 := by
  let I : Finset (G17.{u}.neighborSet 11) :=
    {⟨9, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩}
  have hc : I.card = 5 := by decide
  have layers (v : G17.{u}.neighborSet 11) : layer v.val = 1 ∨ layer v.val = 3 := by
    have h := v.property
    change G17.Adj 11 v.val at h
    have h' := h.2
    rw [show layer 11 = 2 by rfl] at h'
    omega
  have hi : (G17.induce (G17.{u}.neighborSet 11)).IsIndepSet (I : Set _) := by
    intro u _ v _ _ h
    change G17.Adj u.val v.val at h
    have := h.2
    rcases layers u with hu | hu <;> rcases layers v with hv | hv <;> omega
  exact hc ▸ hi.card_le_indepNum

-- In a tree an edge and a two-edge path cannot have the same endpoints.
-- Likewise two paths of length two between distinct endpoints have the same middle.
private def via {α : Type*} {G : SimpleGraph α} {a b c : α}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac : a ≠ c) : G.Path a c :=
  ⟨.cons hab (.cons hbc .nil), by simp [Walk.isPath_def, hab.ne, hbc.ne, hac]⟩

private theorem noTriangle {s : Finset V} (ht : (G17.induce (s : Set V)).IsTree)
    {a b c : V} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (ab : G17.Adj a b) (bc : G17.Adj b c) (ac : G17.Adj a c) : False := by
  let H := G17.induce (s : Set V)
  let x : (s : Set V) := ⟨a, ha⟩
  let y : (s : Set V) := ⟨b, hb⟩
  let z : (s : Set V) := ⟨c, hc⟩
  have e : H.Adj x z := ac
  let p := via (show H.Adj x y from ab) (show H.Adj y z from bc) e.ne
  have he := (ht.isAcyclic.subsingleton_path x z).elim p ⟨e.toWalk, e.isPath_toWalk⟩
  have bad := congrArg (fun q : H.Path x z => q.val.length) he
  exact (by decide : (2 : ℕ) ≠ 1) bad

private theorem commonUnique {s : Finset V} (ht : (G17.induce (s : Set V)).IsTree)
    {a b c d : V} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s)
    (hac : a ≠ c) (ab : G17.Adj a b) (bc : G17.Adj b c)
    (ad : G17.Adj a d) (dc : G17.Adj d c) : b = d := by
  let H := G17.induce (s : Set V)
  let x : (s : Set V) := ⟨a, ha⟩
  let z : (s : Set V) := ⟨c, hc⟩
  have xz : x ≠ z := fun h => hac (congrArg Subtype.val h)
  let p := via (show H.Adj x ⟨b, hb⟩ from ab) (show H.Adj ⟨b, hb⟩ z from bc) xz
  let q := via (show H.Adj x ⟨d, hd⟩ from ad) (show H.Adj ⟨d, hd⟩ z from dc) xz
  have he := (ht.isAcyclic.subsingleton_path x z).elim p q
  exact congrArg (fun r : H.Path x z => (r.val.getVert 1).val) he

private def part (s : Finset V) (k : ℕ) := s.filter fun v => layer v = k

private theorem mem_part {s : Finset V} {k : ℕ} {v : V} :
    v ∈ part s k ↔ v ∈ s ∧ layer v = k := Finset.mem_filter

private theorem cliqueEdge {u v : V} (hu : layer u = 0) (hv : layer v = 0) (hne : u ≠ v) :
    G17.Adj u v := ⟨hne, Or.inl ⟨hu, hv⟩⟩

private theorem nextEdge {u v : V} (h : layer u + 1 = layer v) : G17.Adj u v := by
  refine ⟨?_, Or.inr (Or.inl h)⟩
  rintro rfl
  omega

-- A connected induced graph meeting layers i and j must meet every layer between them.
private theorem noGap {s : Finset V} (ht : (G17.induce (s : Set V)).IsTree)
    {i k j : ℕ} (hik : i < k) (hkj : k < j)
    (hi : 0 < (part s i).card) (hj : 0 < (part s j).card) : 0 < (part s k).card := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hi
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hj
  obtain ⟨has, hai⟩ := mem_part.mp ha
  obtain ⟨hbs, hbj⟩ := mem_part.mp hb
  obtain ⟨p⟩ := ht.connected (⟨a, has⟩ : (s : Set V)) ⟨b, hbs⟩
  obtain ⟨d, _, hl, hr⟩ := p.exists_boundary_dart {v | layer v.val < k}
    (show layer a < k by omega) (show ¬ layer b < k by omega)
  change layer d.fst.val < k at hl
  change ¬ layer d.snd.val < k at hr
  have step := edge_step (show G17.Adj d.fst.val d.snd.val from d.adj)
  exact Finset.card_pos.mpr ⟨d.snd.val, mem_part.mpr ⟨d.snd.property, by omega⟩⟩

private theorem tree_card {s : Finset V} (ht : (G17.induce (s : Set V)).IsTree) :
    s.card ≤ 6 := by
  let n (k : ℕ) := (part s k).card
  have splitCard : s.card = n 0 + n 1 + n 2 + n 3 + n 4 + n 5 := by
    have h := Finset.card_eq_sum_card_fiberwise (s := s) (t := Finset.range 6)
      (f := layer) (fun v _ => Finset.mem_range.mpr ((by decide : ∀ v : V, layer v < 6) v))
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, n, part] using h
  have cap (k : ℕ) : n k ≤ (part Finset.univ k).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ s))
  have h1 := cap 1
  have h2 := cap 2
  have h3 := cap 3
  have h4 := cap 4
  have h5 := cap 5
  change n 1 ≤ 2 at h1
  change n 2 ≤ 1 at h2
  change n 3 ≤ 3 at h3
  change n 4 ≤ 1 at h4
  change n 5 ≤ 1 at h5
  have clique : n 0 ≤ 2 := by
    by_contra! h
    obtain ⟨a, ha, b, hb, c, hc, ab, ac, bc⟩ := Finset.two_lt_card.mp h
    simp only [mem_part] at ha hb hc
    exact noTriangle ht ha.1 hb.1 hc.1 (cliqueEdge ha.2 hb.2 ab)
      (cliqueEdge hb.2 hc.2 bc) (cliqueEdge ha.2 hc.2 ac)
  have triangle : 0 < n 1 → n 0 ≤ 1 := by
    intro h
    obtain ⟨c, hc⟩ := Finset.card_pos.mp h
    by_contra! hn
    obtain ⟨a, ha, b, hb, ab⟩ := Finset.one_lt_card.mp hn
    simp only [mem_part] at ha hb hc
    exact noTriangle ht ha.1 hb.1 hc.1 (cliqueEdge ha.2 hb.2 ab)
      (nextEdge (by omega)) (nextEdge (by omega))
  -- Distinct vertices two layers apart have at most one common middle vertex in the tree.
  have middle (i : ℕ) (lo : 0 < n i) (hi : 0 < n (i+2)) : n (i+1) ≤ 1 := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp lo
    obtain ⟨c, hc⟩ := Finset.card_pos.mp hi
    apply Finset.card_le_one_iff.mpr
    intro b d hb hd
    simp only [mem_part] at ha hb hc hd
    apply commonUnique ht ha.1 hb.1 hc.1 hd.1
    · rintro rfl; omega
    all_goals exact nextEdge (by omega)
  have leftSquare : 0 < n 0 → 0 < n 2 → n 1 ≤ 1 := middle 0
  have rightSquare : 0 < n 2 → 0 < n 4 → n 3 ≤ 1 := middle 2
  have prefixBound : n 0 + n 1 + n 2 ≤ 3 := by omega
  -- If layer 2 or 4 is missing, connectivity confines the tree to one side.
  by_cases span₂ : 0 < n 2
  · by_cases span₄ : 0 < n 4
    · have := rightSquare span₂ span₄
      omega
    · have gap := noGap ht (i := 2) (k := 4) (j := 5) (by decide) (by decide)
      change (0 < n 2 → 0 < n 5 → 0 < n 4) at gap
      omega
  · have separated (i j : ℕ) (hi : i < 2) (hj : 2 < j) : n i = 0 ∨ n j = 0 := by
      have gap := noGap ht hi hj
      change (0 < n i → 0 < n j → 0 < n 2) at gap
      omega
    have := separated 0 3 (by decide) (by decide)
    have := separated 0 4 (by decide) (by decide)
    have := separated 0 5 (by decide) (by decide)
    have := separated 1 3 (by decide) (by decide)
    have := separated 1 4 (by decide) (by decide)
    have := separated 1 5 (by decide) (by decide)
    omega

private theorem tree_upper : largestInducedTreeSize G17 ≤ 6 := by
  apply csSup_le'
  rintro _ ⟨s, rfl, ht⟩
  exact tree_card ht

private theorem violates :
    let maxL := (Finset.univ.image (indepNeighborsCard G17.{u})).max' (by simp)
    ¬ ((↑⌈averageEccentricity G17.{u} + (maxL : ℝ) / 3⌉ : ℝ) ≤
      (largestInducedTreeSize G17.{u} : ℝ)) := by
  let maxL := (Finset.univ.image (indepNeighborsCard G17.{u})).max' (by simp)
  change ¬ ((↑⌈averageEccentricity G17.{u} + (maxL : ℝ) / 3⌉ : ℝ) ≤
    (largestInducedTreeSize G17.{u} : ℝ))
  intro h
  have hm : 5 ≤ maxL := independent_lower.trans
    (Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ 11)))
  have ceilBound := Int.le_ceil (averageEccentricity G17.{u} + (maxL : ℝ) / 3)
  have maxBound : (5 : ℝ) ≤ maxL := by exact_mod_cast hm
  have treeBound : (largestInducedTreeSize G17.{u} : ℝ) ≤ 6 := by exact_mod_cast tree_upper
  linarith [average_lower.{u}]

end WOW72Witness

open WOW72Witness

theorem OMA.disproof : ¬ (type_of% @WrittenOnTheWallII.GraphConjecture72.conjecture72) := by
  intro claim
  exact violates (claim G17 connected)
