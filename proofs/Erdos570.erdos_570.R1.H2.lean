import OMAReductions.R_Erdos570_erdos_570_R1

-- Step Erdos570.erdos_570.R1.H2: hypothesis H2 of reduction Erdos570.erdos_570.R1
-- Credit: @OrangeHeadz

/-!
Informal plan. H2 says R(C_k, k K_2) ≤ 2k + ⌊(k-1)/2⌋ (Faudree, Schelp and Sheehan, Ramsey
numbers for matchings, 1978; restated as Proposition 9 of arXiv:2601.10238).

Let G have N ≥ 2k + ⌊(k-1)/2⌋ vertices and no k pairwise disjoint edges.

1. Encode a matching as an involution μ of V with μ v = v or v ~ μ v. Take μ with the largest
   support P. Then |P| ≤ 2k - 2, since a support of size ≥ 2k - 1 contains k disjoint edges
   and H embeds. Let U be the fixed points, s = |U| = N - |P| ≥ ⌊(k-1)/2⌋ + 2.
2. Maximality (two augmentations): U is independent in G, and for v in P one of v, μ v has at
   most one G-neighbour in U. Call such vertices good; at least |P| / 2 vertices are good.
3. Put q = k - s (zero if s ≥ k). Then q ≤ #good and q + 2 ≤ s. Pick distinct good vertices
   z_0, ..., z_{q-1} and, greedily, distinct u_0, ..., u_{k-q-1} in U such that u_j and
   u_{j+1} avoid the single U-neighbour of z_j. The count works because position j has at
   most two forbidden vertices for j < q, at most one for j = q, and none after that.
4. u_0 z_0 u_1 z_1 ... u_{q-1} z_{q-1} u_q u_{q+1} ... u_{k-q-1} is a k-cycle in the complement.

Mathlib supplies cycleGraph_adj', Finset.exists_max_image, Fintype.equivFin and
Function.Embedding.nonempty_of_card_le. The reduction file supplies edge_count_from_degrees.
-/

open Finset SimpleGraph

open scoped Classical

namespace OMA.E570

/-- Choose `n` distinct elements of `U` one at a time, the `j`-th avoiding `F j`. -/
lemma greedy {V : Type} (v0 : V) (U : Finset V) (F : ℕ → Finset V) (n : ℕ)
    (h : ∀ j < n, (F j).card + j + 1 ≤ U.card) :
    ∃ g : ℕ → V, (∀ j < n, g j ∈ U ∧ g j ∉ F j) ∧ ∀ i < n, ∀ j < n, g i = g j → i = j := by
  induction n with
  | zero =>
    exact ⟨fun _ => v0, fun j hj => absurd hj (Nat.not_lt_zero j),
      fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    obtain ⟨g, hg1, hg2⟩ := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
    have hcard : ((F n) ∪ (range n).image g).card < U.card := by
      have h1 := Finset.card_union_le (F n) ((range n).image g)
      have h2 : ((range n).image g).card ≤ n := by
        refine (Finset.card_image_le).trans ?_
        rw [Finset.card_range]
      have h3 := h n (Nat.lt_succ_self n)
      omega
    obtain ⟨x, hxU, hx⟩ : ∃ x ∈ U, x ∉ (F n) ∪ (range n).image g := by
      by_contra hcon
      have hsub : U ⊆ F n ∪ (range n).image g := by
        intro x hx
        by_contra hx'
        exact hcon ⟨x, hx, hx'⟩
      exact absurd (Finset.card_le_card hsub) (not_le.mpr hcard)
    rw [mem_union, not_or] at hx
    refine ⟨Function.update g n x, ?_, ?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | heq
      · rw [Function.update_of_ne (ne_of_lt hlt)]
        exact hg1 j hlt
      · subst heq
        rw [Function.update_self]
        exact ⟨hxU, hx.1⟩
    · intro i hi j hj hij
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | hi'
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
        · rw [Function.update_of_ne (ne_of_lt hi'), Function.update_of_ne (ne_of_lt hj')] at hij
          exact hg2 i hi' j hj' hij
        · subst hj'
          rw [Function.update_of_ne (ne_of_lt hi'), Function.update_self] at hij
          exact absurd (mem_image.mpr ⟨i, mem_range.mpr hi', hij⟩) hx.2
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
        · subst hi'
          rw [Function.update_self, Function.update_of_ne (ne_of_lt hj')] at hij
          exact absurd (mem_image.mpr ⟨j, mem_range.mpr hj', hij.symm⟩) hx.2
        · rw [hi', hj']

lemma fin_sub_one {k : ℕ} (u v : Fin k) (h : (u - v).val = 1) :
    u.val = v.val + 1 ∨ (u.val = 0 ∧ v.val + 1 = k) := by
  rw [Fin.val_sub] at h
  have hu := u.isLt
  have hv := v.isLt
  rcases Nat.lt_or_ge u.val v.val with hlt | hge
  · rw [Nat.mod_eq_of_lt (by omega)] at h
    right
    omega
  · have h1 : k - v.val + u.val = (u.val - v.val) + k := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h
    left
    omega

/-- A cyclic sequence of distinct vertices with consecutive ones adjacent is a copy of `C_k`. -/
lemma cycle_of_seq {V : Type} (Gc : SimpleGraph V) (k : ℕ) (c : ℕ → V)
    (hinj : ∀ i < k, ∀ j < k, c i = c j → i = j)
    (hadj : ∀ i, i + 1 < k → Gc.Adj (c i) (c (i + 1)))
    (hwrap : Gc.Adj (c (k - 1)) (c 0)) : cycleGraph k ⊑ Gc := by
  refine ⟨⟨⟨fun i => c i.val, ?_⟩, ?_⟩⟩
  · intro u v huv
    show Gc.Adj (c u.val) (c v.val)
    rw [cycleGraph_adj'] at huv
    have hu := u.isLt
    have hv := v.isLt
    rcases huv with h | h
    · rcases fin_sub_one u v h with h1 | ⟨h1, h2⟩
      · rw [h1]
        exact (hadj v.val (by omega)).symm
      · rw [h1, show v.val = k - 1 by omega]
        exact hwrap.symm
    · rcases fin_sub_one v u h with h1 | ⟨h1, h2⟩
      · rw [h1]
        exact hadj u.val (by omega)
      · rw [h1, show u.val = k - 1 by omega]
        exact hwrap
  · intro u v huv
    exact Fin.ext (hinj _ u.isLt _ v.isLt huv)

/-- A matching, encoded as an involution moving each vertex to itself or to a neighbour. -/
def IsInv {V : Type} (G : SimpleGraph V) (μ : V → V) : Prop :=
  (∀ v, μ (μ v) = v) ∧ ∀ v, μ v = v ∨ G.Adj v (μ v)

/-- Two adjacent unmatched vertices enlarge the matching. -/
lemma aug_one {V : Type} [Fintype V] (G : SimpleGraph V) (μ : V → V)
    (hμ : IsInv G μ) {u u' : V} (hu : μ u = u) (hu' : μ u' = u') (hadj : G.Adj u u') :
    ∃ μ' : V → V, IsInv G μ' ∧
      (univ.filter (fun v => μ v ≠ v)).card < (univ.filter (fun v => μ' v ≠ v)).card := by
  have hne : u ≠ u' := hadj.ne
  let μ' : V → V := fun v => if v = u then u' else if v = u' then u else μ v
  have e1 : μ' u = u' := by simp [μ']
  have e2 : μ' u' = u := by simp [μ', hne.symm]
  have e3 : ∀ v, v ≠ u → v ≠ u' → μ' v = μ v := by
    intro v h1 h2
    simp [μ', h1, h2]
  have hfix : ∀ v, v ≠ u → v ≠ u' → μ v ≠ u ∧ μ v ≠ u' := by
    intro v h1 h2
    constructor
    · intro h
      apply h1
      rw [← hμ.1 v, h, hu]
    · intro h
      apply h2
      rw [← hμ.1 v, h, hu']
  refine ⟨μ', ⟨?_, ?_⟩, ?_⟩
  · intro v
    by_cases h1 : v = u
    · rw [h1, e1, e2]
    · by_cases h2 : v = u'
      · rw [h2, e2, e1]
      · rw [e3 v h1 h2, e3 _ (hfix v h1 h2).1 (hfix v h1 h2).2]
        exact hμ.1 v
  · intro v
    by_cases h1 : v = u
    · right
      rw [h1, e1]
      exact hadj
    · by_cases h2 : v = u'
      · right
        rw [h2, e2]
        exact hadj.symm
      · rw [e3 v h1 h2]
        exact hμ.2 v
  · apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨u, ?_, ?_⟩
      · rw [mem_filter]
        refine ⟨mem_univ _, ?_⟩
        rw [e1]
        exact hne.symm
      · rw [mem_filter]
        exact fun h => h.2 hu
    · intro v hv
      rw [mem_filter] at hv ⊢
      refine ⟨mem_univ _, ?_⟩
      have h1 : v ≠ u := fun h => hv.2 (by rw [h]; exact hu)
      have h2 : v ≠ u' := fun h => hv.2 (by rw [h]; exact hu')
      rw [e3 v h1 h2]
      exact hv.2

/-- A matched pair `x y` with `x ~ u`, `y ~ u'` for distinct unmatched `u u'` enlarges it. -/
lemma aug_two {V : Type} [Fintype V] (G : SimpleGraph V) (μ : V → V)
    (hμ : IsInv G μ) {x y u u' : V} (hxy : μ x = y) (hyx : μ y = x) (hne' : x ≠ y)
    (hu : μ u = u) (hu' : μ u' = u') (hne : u ≠ u') (h1 : G.Adj x u) (h2 : G.Adj y u') :
    ∃ μ' : V → V, IsInv G μ' ∧
      (univ.filter (fun v => μ v ≠ v)).card < (univ.filter (fun v => μ' v ≠ v)).card := by
  have hxu : x ≠ u := fun h => hne' (by rw [← hxy, h, hu])
  have hxu' : x ≠ u' := fun h => hne' (by rw [← hxy, h, hu'])
  have hyu : y ≠ u := fun h => hne' (by rw [← hyx, h, hu])
  have hyu' : y ≠ u' := fun h => hne' (by rw [← hyx, h, hu'])
  let μ' : V → V := fun v =>
    if v = x then u else if v = u then x else if v = y then u' else if v = u' then y else μ v
  have e1 : μ' x = u := by simp [μ']
  have e2 : μ' u = x := by simp [μ', hxu.symm]
  have e3 : μ' y = u' := by simp [μ', hne'.symm, hyu]
  have e4 : μ' u' = y := by simp [μ', hxu'.symm, hne.symm, hyu'.symm]
  have e5 : ∀ v, v ≠ x → v ≠ u → v ≠ y → v ≠ u' → μ' v = μ v := by
    intro v a b c d
    simp [μ', a, b, c, d]
  have hfix : ∀ v, v ≠ x → v ≠ u → v ≠ y → v ≠ u' →
      μ v ≠ x ∧ μ v ≠ u ∧ μ v ≠ y ∧ μ v ≠ u' := by
    intro v a b c d
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      apply c
      rw [← hμ.1 v, h, hxy]
    · intro h
      apply b
      rw [← hμ.1 v, h, hu]
    · intro h
      apply a
      rw [← hμ.1 v, h, hyx]
    · intro h
      apply d
      rw [← hμ.1 v, h, hu']
  refine ⟨μ', ⟨?_, ?_⟩, ?_⟩
  · intro v
    by_cases a : v = x
    · rw [a, e1, e2]
    · by_cases b : v = u
      · rw [b, e2, e1]
      · by_cases c : v = y
        · rw [c, e3, e4]
        · by_cases d : v = u'
          · rw [d, e4, e3]
          · obtain ⟨f1, f2, f3, f4⟩ := hfix v a b c d
            rw [e5 v a b c d, e5 _ f1 f2 f3 f4]
            exact hμ.1 v
  · intro v
    by_cases a : v = x
    · right
      rw [a, e1]
      exact h1
    · by_cases b : v = u
      · right
        rw [b, e2]
        exact h1.symm
      · by_cases c : v = y
        · right
          rw [c, e3]
          exact h2
        · by_cases d : v = u'
          · right
            rw [d, e4]
            exact h2.symm
          · rw [e5 v a b c d]
            exact hμ.2 v
  · apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨u, ?_, ?_⟩
      · rw [mem_filter]
        refine ⟨mem_univ _, ?_⟩
        rw [e2]
        exact hxu
      · rw [mem_filter]
        exact fun h => h.2 hu
    · intro v hv
      rw [mem_filter] at hv ⊢
      refine ⟨mem_univ _, ?_⟩
      have b : v ≠ u := fun h => hv.2 (by rw [h]; exact hu)
      have d : v ≠ u' := fun h => hv.2 (by rw [h]; exact hu')
      by_cases a : v = x
      · rw [a, e1]
        exact hxu.symm
      · by_cases c : v = y
        · rw [c, e3]
          exact hyu'.symm
        · rw [e5 v a b c d]
          exact hv.2

/-- An orientation of the two-element orbits of an involution. -/
lemma sides {α : Type} [Fintype α] (τ : α → α) (hτ : ∀ a, τ (τ a) = a) :
    ∃ σ : α → Prop, ∀ a, τ a ≠ a → (σ (τ a) ↔ ¬ σ a) := by
  refine ⟨fun a => Fintype.equivFin α a < Fintype.equivFin α (τ a), ?_⟩
  intro a ha
  show Fintype.equivFin α (τ a) < Fintype.equivFin α (τ (τ a)) ↔
    ¬ (Fintype.equivFin α a < Fintype.equivFin α (τ a))
  rw [hτ a]
  have hne : Fintype.equivFin α (τ a) ≠ Fintype.equivFin α a :=
    fun h => ha ((Fintype.equivFin α).injective h)
  constructor
  · intro h h'
    exact lt_asymm h h'
  · intro h
    exact lt_of_le_of_ne (not_lt.mp h) hne

/-- A perfect matching `H` embeds in `G` once the matching `μ` of `G` is large enough. -/
lemma embed_matching {W V : Type} [Fintype W] [Fintype V] (H : SimpleGraph W)
    (G : SimpleGraph V) (μ : V → V) (hμ : IsInv G μ) (π : W → W) (hπ : ∀ w, π (π w) = w)
    (hπne : ∀ w, π w ≠ w) (hH : ∀ w w', H.Adj w w' → w' = π w)
    (hcard : Fintype.card W ≤ (univ.filter (fun v => μ v ≠ v)).card + 1) : H ⊑ G := by
  obtain ⟨σH, hσH⟩ := sides π hπ
  obtain ⟨σG, hσG⟩ := sides μ hμ.1
  have hπinj : ∀ a b, π a = π b → a = b := by
    intro a b h
    rw [← hπ a, ← hπ b, h]
  have hμinj : ∀ a b, μ a = μ b → a = b := by
    intro a b h
    rw [← hμ.1 a, ← hμ.1 b, h]
  -- the two halves of W
  have hAH : 2 * (univ.filter σH).card ≤ Fintype.card W := by
    have h1 : (univ.filter σH).card ≤ (univ.filter (fun w => ¬ σH w)).card := by
      apply Finset.card_le_card_of_injOn π
      · intro w hw
        have hw' : σH w := (mem_filter.mp hw).2
        show π w ∈ univ.filter (fun w => ¬ σH w)
        exact mem_filter.mpr ⟨mem_univ _, fun h => (hσH w (hπne w)).mp h hw'⟩
      · intro a _ b _ hab
        exact hπinj a b hab
    have h2 := Finset.card_filter_add_card_filter_not (s := (univ : Finset W)) σH
    rw [Finset.card_univ] at h2
    omega
  -- the two halves of the support of μ
  have hAG : (univ.filter (fun v => μ v ≠ v)).card ≤
      2 * ((univ.filter (fun v => μ v ≠ v)).filter σG).card := by
    have h1 : ((univ.filter (fun v => μ v ≠ v)).filter (fun v => ¬ σG v)).card ≤
        ((univ.filter (fun v => μ v ≠ v)).filter σG).card := by
      apply Finset.card_le_card_of_injOn μ
      · intro v hv
        have hv' := mem_filter.mp hv
        have hvP : μ v ≠ v := (mem_filter.mp hv'.1).2
        show μ v ∈ (univ.filter (fun v => μ v ≠ v)).filter σG
        refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, ?_⟩, (hσG v hvP).mpr hv'.2⟩
        rw [hμ.1 v]
        exact hvP.symm
      · intro a _ b _ hab
        exact hμinj a b hab
    have h2 := Finset.card_filter_add_card_filter_not
      (s := univ.filter (fun v => μ v ≠ v)) σG
    omega
  obtain ⟨ι⟩ : Nonempty ({w // w ∈ univ.filter σH} ↪
      {v // v ∈ (univ.filter (fun v => μ v ≠ v)).filter σG}) :=
    Function.Embedding.nonempty_of_card_le (by
      rw [Fintype.card_coe, Fintype.card_coe]
      omega)
  have hmem : ∀ w, w ∉ univ.filter σH → π w ∈ univ.filter σH := by
    intro w hw
    refine mem_filter.mpr ⟨mem_univ _, (hσH w (hπne w)).mpr ?_⟩
    exact fun h => hw (mem_filter.mpr ⟨mem_univ _, h⟩)
  have hιP : ∀ a : {w // w ∈ univ.filter σH}, μ (ι a : V) ≠ (ι a : V) :=
    fun a => (mem_filter.mp (mem_filter.mp (ι a).2).1).2
  have hισ : ∀ a : {w // w ∈ univ.filter σH}, σG (ι a : V) :=
    fun a => (mem_filter.mp (ι a).2).2
  have hιadj : ∀ a : {w // w ∈ univ.filter σH}, G.Adj (ι a : V) (μ (ι a : V)) := by
    intro a
    rcases hμ.2 (ι a : V) with h | h
    · exact absurd h (hιP a)
    · exact h
  let f : W → V := fun w =>
    if hw : w ∈ univ.filter σH then (ι ⟨w, hw⟩ : V) else μ (ι ⟨π w, hmem w hw⟩ : V)
  have fpos : ∀ w (hw : w ∈ univ.filter σH), f w = (ι ⟨w, hw⟩ : V) := fun w hw => dif_pos hw
  have fneg : ∀ w (hw : w ∉ univ.filter σH), f w = μ (ι ⟨π w, hmem w hw⟩ : V) :=
    fun w hw => dif_neg hw
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro w w' hadj
    have hw' := hH w w' hadj
    subst hw'
    by_cases hw : w ∈ univ.filter σH
    · have hπw : π w ∉ univ.filter σH := by
        intro h
        exact (hσH w (hπne w)).mp (mem_filter.mp h).2 (mem_filter.mp hw).2
      have heq : (⟨π (π w), hmem (π w) hπw⟩ : {w // w ∈ univ.filter σH}) = ⟨w, hw⟩ :=
        Subtype.ext (hπ w)
      show G.Adj (f w) (f (π w))
      rw [fpos w hw, fneg (π w) hπw, heq]
      exact hιadj _
    · show G.Adj (f w) (f (π w))
      rw [fneg w hw, fpos (π w) (hmem w hw)]
      exact (hιadj _).symm
  · intro w w' h0
    have h : f w = f w' := h0
    by_cases hw : w ∈ univ.filter σH
    · by_cases hw' : w' ∈ univ.filter σH
      · rw [fpos w hw, fpos w' hw'] at h
        exact congrArg Subtype.val (ι.injective (Subtype.ext h))
      · rw [fpos w hw, fneg w' hw'] at h
        have h1 := hισ ⟨w, hw⟩
        rw [h] at h1
        exact absurd h1 (fun hc => (hσG _ (hιP _)).mp hc (hισ _))
    · by_cases hw' : w' ∈ univ.filter σH
      · rw [fneg w hw, fpos w' hw'] at h
        have h1 := hισ ⟨w', hw'⟩
        rw [← h] at h1
        exact absurd h1 (fun hc => (hσG _ (hιP _)).mp hc (hισ _))
      · rw [fneg w hw, fneg w' hw'] at h
        have h1 := ι.injective (Subtype.ext (hμinj _ _ h))
        exact hπinj w w' (congrArg Subtype.val h1)

/-- The matching case: `R(C_k, k K_2) ≤ 2k + ⌊(k - 1) / 2⌋`. -/
lemma main_aux (k : ℕ) (hk : 3 ≤ k) {W V : Type} [Fintype W] [Fintype V]
    (H : SimpleGraph W) (G : SimpleGraph V)
    (hdeg : ∀ v, (H.neighborSet v).ncard = 1) (hedges : H.edgeSet.ncard = k)
    (hN : 2 * k + (k - 1) / 2 ≤ Fintype.card V)
    (hC : ¬ (cycleGraph k ⊑ Gᶜ)) : H ⊑ G := by
  by_contra hH
  -- the partner function of the perfect matching H
  have hπex : ∀ w, ∃ w', H.neighborSet w = {w'} := fun w => Set.ncard_eq_one.mp (hdeg w)
  choose π hπs using hπex
  have hπadj : ∀ w w', H.Adj w w' ↔ w' = π w := by
    intro w w'
    have h : w' ∈ H.neighborSet w ↔ w' ∈ ({π w} : Set W) := by rw [hπs w]
    simpa using h
  have hπne : ∀ w, π w ≠ w := fun w => ((hπadj w (π w)).mpr rfl).ne'
  have hππ : ∀ w, π (π w) = w := fun w =>
    ((hπadj (π w) w).mp ((hπadj w (π w)).mpr rfl).symm).symm
  have hW : Fintype.card W = 2 * k := by
    have h := OMA.R_Erdos570_erdos_570_R1.edge_count_from_degrees H
    simp only [hdeg, hedges] at h
    simpa using h
  -- a largest matching of G
  have hne : (univ.filter (fun μ : V → V => IsInv G μ)).Nonempty :=
    ⟨id, mem_filter.mpr ⟨mem_univ _, fun v => rfl, fun v => Or.inl rfl⟩⟩
  obtain ⟨μ, hμmem, hμmax⟩ := Finset.exists_max_image _
    (fun μ : V → V => (univ.filter (fun v => μ v ≠ v)).card) hne
  have hμ : IsInv G μ := (mem_filter.mp hμmem).2
  have hmax : ∀ μ' : V → V, IsInv G μ' →
      (univ.filter (fun v => μ' v ≠ v)).card ≤ (univ.filter (fun v => μ v ≠ v)).card :=
    fun μ' h' => hμmax μ' (mem_filter.mpr ⟨mem_univ _, h'⟩)
  obtain ⟨P, hP⟩ : ∃ P : Finset V, P = univ.filter (fun v => μ v ≠ v) := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : Finset V, U = univ.filter (fun v => μ v = v) := ⟨_, rfl⟩
  have hUmem : ∀ v, v ∈ U ↔ μ v = v := by
    intro v
    rw [hU, mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩
  have hPmem : ∀ v, v ∈ P ↔ μ v ≠ v := by
    intro v
    rw [hP, mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩
  have hPU : P.card + U.card = Fintype.card V := by
    have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset V))
      (fun v => μ v = v)
    rw [Finset.card_univ] at h
    rw [hP, hU, add_comm]
    exact h
  have hPlt : P.card + 1 < 2 * k := by
    by_contra hcon
    apply hH
    refine embed_matching H G μ hμ π hππ hπne (fun w w' h => (hπadj w w').mp h) ?_
    rw [hW, ← hP]
    omega
  have hUindep : ∀ u ∈ U, ∀ u' ∈ U, ¬ G.Adj u u' := by
    intro u hu u' hu' hadj
    obtain ⟨μ', h1, h2⟩ := aug_one G μ hμ ((hUmem u).mp hu) ((hUmem u').mp hu') hadj
    exact absurd (hmax μ' h1) (not_le.mpr h2)
  -- good vertices: matched, with at most one neighbour in U
  obtain ⟨Good, hGooddef⟩ : ∃ Good : Finset V,
      Good = P.filter (fun v => ∃ b, ∀ u ∈ U, G.Adj v u → u = b) := ⟨_, rfl⟩
  have hGoodmem : ∀ v, v ∈ Good ↔ v ∈ P ∧ ∃ b, ∀ u ∈ U, G.Adj v u → u = b := by
    intro v
    rw [hGooddef, mem_filter]
  have hGood : P.card ≤ 2 * Good.card := by
    have h1 : (P.filter (fun v => ¬ ∃ b, ∀ u ∈ U, G.Adj v u → u = b)).card ≤ Good.card := by
      apply Finset.card_le_card_of_injOn μ
      · intro v hv
        have hv' := mem_filter.mp hv
        have hvP : μ v ≠ v := (hPmem v).mp hv'.1
        have hμvP : μ (μ v) ≠ μ v := by
          rw [hμ.1 v]
          exact hvP.symm
        show μ v ∈ Good
        refine (hGoodmem _).mpr ⟨(hPmem _).mpr hμvP, v, ?_⟩
        intro u' hu' hadj'
        exfalso
        apply hv'.2
        refine ⟨u', ?_⟩
        intro u hu hadj
        by_contra hneq
        obtain ⟨μ', h1, h2⟩ := aug_two G μ hμ (x := v) (y := μ v) rfl (hμ.1 v) hvP.symm
          ((hUmem u).mp hu) ((hUmem u').mp hu') hneq hadj hadj'
        exact absurd (hmax μ' h1) (not_le.mpr h2)
      · intro a _ b _ hab
        rw [← hμ.1 a, ← hμ.1 b, hab]
    have h2 := Finset.card_filter_add_card_filter_not (s := P)
      (fun v => ∃ b, ∀ u ∈ U, G.Adj v u → u = b)
    rw [← hGooddef] at h2
    omega
  -- the parameters
  obtain ⟨v0⟩ : Nonempty V := by
    rw [← Fintype.card_pos_iff]
    omega
  obtain ⟨q, hq⟩ : ∃ q, q = k - U.card := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, n = k - q := ⟨_, rfl⟩
  have hq1 : q ≤ Good.card := by omega
  have hq2 : q + 2 ≤ U.card := by omega
  have hn1 : n ≤ U.card := by omega
  have hn2 : q + 2 ≤ n := by omega
  have hkn : k = n + q := by omega
  -- the good vertices z and their forbidden neighbours
  obtain ⟨z, hz1, hz2⟩ := greedy v0 Good (fun _ => ∅) q (fun j hj => by
    rw [Finset.card_empty]
    omega)
  have hβex : ∀ v, ∃ b, ∀ u ∈ U, v ∈ Good → G.Adj v u → u = b := by
    intro v
    by_cases hv : v ∈ Good
    · obtain ⟨b, hb⟩ := ((hGoodmem v).mp hv).2
      exact ⟨b, fun u hu _ => hb u hu⟩
    · exact ⟨v, fun _ _ h => absurd h hv⟩
  choose β hβ using hβex
  obtain ⟨F, hF⟩ : ∃ F : ℕ → Finset V, F = fun j =>
      (if j < q then {β (z j)} else ∅) ∪ (if 1 ≤ j ∧ j ≤ q then {β (z (j - 1))} else ∅) :=
    ⟨_, rfl⟩
  have hFcard : ∀ j, (F j).card ≤
      (if j < q then 1 else 0) + (if 1 ≤ j ∧ j ≤ q then 1 else 0) := by
    intro j
    rw [hF]
    refine (Finset.card_union_le _ _).trans ?_
    apply Nat.add_le_add
    · split_ifs <;> simp
    · split_ifs <;> simp
  obtain ⟨g, hg1, hg2⟩ := greedy v0 U F n (by
    intro j hj
    have h := hFcard j
    split_ifs at h <;> omega)
  have hgU : ∀ j < n, μ (g j) = g j := fun j hj => (hUmem _).mp (hg1 j hj).1
  have hzP : ∀ j < q, μ (z j) ≠ z j :=
    fun j hj => (hPmem _).mp ((hGoodmem _).mp (hz1 j hj).1).1
  have hgz : ∀ i < n, ∀ j < q, g i ≠ z j := by
    intro i hi j hj h
    apply hzP j hj
    rw [← h]
    exact hgU i hi
  have hgg : ∀ i < n, ∀ j < n, i ≠ j → Gᶜ.Adj (g i) (g j) := by
    intro i hi j hj hij
    rw [SimpleGraph.compl_adj]
    exact ⟨fun h => hij (hg2 i hi j hj h), hUindep _ (hg1 i hi).1 _ (hg1 j hj).1⟩
  have hgz1 : ∀ j < q, Gᶜ.Adj (g j) (z j) := by
    intro j hj
    have hjn : j < n := by omega
    rw [SimpleGraph.compl_adj]
    refine ⟨hgz j hjn j hj, fun hadj => ?_⟩
    have hb := hβ (z j) (g j) (hg1 j hjn).1 (hz1 j hj).1 hadj.symm
    apply (hg1 j hjn).2
    rw [hF]
    show g j ∈ (if j < q then {β (z j)} else ∅) ∪
      (if 1 ≤ j ∧ j ≤ q then {β (z (j - 1))} else ∅)
    rw [if_pos hj]
    exact mem_union_left _ (mem_singleton.mpr hb)
  have hgz2 : ∀ j < q, Gᶜ.Adj (z j) (g (j + 1)) := by
    intro j hj
    have hjn : j + 1 < n := by omega
    rw [SimpleGraph.compl_adj]
    refine ⟨(hgz (j + 1) hjn j hj).symm, fun hadj => ?_⟩
    have hb := hβ (z j) (g (j + 1)) (hg1 (j + 1) hjn).1 (hz1 j hj).1 hadj
    apply (hg1 (j + 1) hjn).2
    rw [hF]
    show g (j + 1) ∈ (if j + 1 < q then {β (z (j + 1))} else ∅) ∪
      (if 1 ≤ j + 1 ∧ j + 1 ≤ q then {β (z (j + 1 - 1))} else ∅)
    rw [if_pos (show 1 ≤ j + 1 ∧ j + 1 ≤ q by omega), Nat.add_sub_cancel]
    exact mem_union_right _ (mem_singleton.mpr hb)
  -- the cyclic sequence u_0 z_0 u_1 z_1 ... u_q u_{q+1} ...
  obtain ⟨c, hc⟩ : ∃ c : ℕ → V, c = fun i =>
      if i < 2 * q then (if i % 2 = 0 then g (i / 2) else z (i / 2)) else g (i - q) :=
    ⟨_, rfl⟩
  have hc_even : ∀ a < q, c (2 * a) = g a := by
    intro a ha
    rw [hc]
    show (if 2 * a < 2 * q then (if 2 * a % 2 = 0 then g (2 * a / 2) else z (2 * a / 2))
      else g (2 * a - q)) = g a
    rw [if_pos (by omega), if_pos (by omega), show 2 * a / 2 = a by omega]
  have hc_odd : ∀ a < q, c (2 * a + 1) = z a := by
    intro a ha
    rw [hc]
    show (if 2 * a + 1 < 2 * q then
      (if (2 * a + 1) % 2 = 0 then g ((2 * a + 1) / 2) else z ((2 * a + 1) / 2))
      else g (2 * a + 1 - q)) = z a
    rw [if_pos (by omega), if_neg (by omega), show (2 * a + 1) / 2 = a by omega]
  have hc_tail : ∀ i, 2 * q ≤ i → c i = g (i - q) := by
    intro i hi
    rw [hc]
    show (if i < 2 * q then (if i % 2 = 0 then g (i / 2) else z (i / 2)) else g (i - q))
      = g (i - q)
    rw [if_neg (by omega)]
  have hcls : ∀ i, i < k → (∃ a, a < q ∧ i = 2 * a ∧ c i = g a) ∨
      (∃ a, a < q ∧ i = 2 * a + 1 ∧ c i = z a) ∨ (2 * q ≤ i ∧ c i = g (i - q)) := by
    intro i hi
    by_cases h1 : i < 2 * q
    · rcases Nat.even_or_odd' i with ⟨a, ha | ha⟩
      · left
        refine ⟨a, by omega, ha, ?_⟩
        rw [ha]
        exact hc_even a (by omega)
      · right
        left
        refine ⟨a, by omega, ha, ?_⟩
        rw [ha]
        exact hc_odd a (by omega)
    · right
      right
      exact ⟨by omega, hc_tail i (by omega)⟩
  have hinj : ∀ i < k, ∀ j < k, c i = c j → i = j := by
    intro i hi j hj hij
    rcases hcls i hi with ⟨a, ha, hia, hca⟩ | ⟨a, ha, hia, hca⟩ | ⟨hia, hca⟩
    · rcases hcls j hj with ⟨b, hb, hjb, hcb⟩ | ⟨b, hb, hjb, hcb⟩ | ⟨hjb, hcb⟩
      · rw [hca, hcb] at hij
        have h := hg2 a (by omega) b (by omega) hij
        omega
      · rw [hca, hcb] at hij
        exact absurd hij (hgz a (by omega) b hb)
      · rw [hca, hcb] at hij
        have h := hg2 a (by omega) (j - q) (by omega) hij
        omega
    · rcases hcls j hj with ⟨b, hb, hjb, hcb⟩ | ⟨b, hb, hjb, hcb⟩ | ⟨hjb, hcb⟩
      · rw [hca, hcb] at hij
        exact absurd hij.symm (hgz b (by omega) a ha)
      · rw [hca, hcb] at hij
        have h := hz2 a ha b hb hij
        omega
      · rw [hca, hcb] at hij
        exact absurd hij.symm (hgz (j - q) (by omega) a ha)
    · rcases hcls j hj with ⟨b, hb, hjb, hcb⟩ | ⟨b, hb, hjb, hcb⟩ | ⟨hjb, hcb⟩
      · rw [hca, hcb] at hij
        have h := hg2 (i - q) (by omega) b (by omega) hij
        omega
      · rw [hca, hcb] at hij
        exact absurd hij (hgz (i - q) (by omega) b hb)
      · rw [hca, hcb] at hij
        have h := hg2 (i - q) (by omega) (j - q) (by omega) hij
        omega
  have hadj : ∀ i, i + 1 < k → Gᶜ.Adj (c i) (c (i + 1)) := by
    intro i hi
    rcases hcls i (by omega) with ⟨a, ha, hia, hca⟩ | ⟨a, ha, hia, hca⟩ | ⟨hia, hca⟩
    · have hnext : c (i + 1) = z a := by
        rw [hia]
        exact hc_odd a ha
      rw [hca, hnext]
      exact hgz1 a ha
    · have hnext : c (i + 1) = g (a + 1) := by
        by_cases h : a + 1 < q
        · rw [hia, show 2 * a + 1 + 1 = 2 * (a + 1) by ring]
          exact hc_even (a + 1) h
        · rw [hc_tail (i + 1) (by omega), show i + 1 - q = a + 1 by omega]
      rw [hca, hnext]
      exact hgz2 a ha
    · rw [hca, hc_tail (i + 1) (by omega)]
      exact hgg (i - q) (by omega) (i + 1 - q) (by omega) (by omega)
  have hwrap : Gᶜ.Adj (c (k - 1)) (c 0) := by
    have h0 : c 0 = g 0 := by
      by_cases h : 0 < q
      · exact hc_even 0 h
      · rw [hc_tail 0 (by omega), Nat.zero_sub]
    rw [hc_tail (k - 1) (by omega), h0]
    exact hgg (k - 1 - q) (by omega) 0 (by omega) (by omega)
  exact hC (cycle_of_seq Gᶜ k c hinj hadj hwrap)

end OMA.E570

theorem OMA.solution : OMA.R_Erdos570_erdos_570_R1.H2 := by
  unfold OMA.R_Erdos570_erdos_570_R1.H2
  intro k hk W V _ _ H G hdeg hedges hN hC
  exact OMA.E570.main_aux k hk H G hdeg hedges hN hC
