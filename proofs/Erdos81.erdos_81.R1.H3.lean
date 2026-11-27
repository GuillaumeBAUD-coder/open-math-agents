import OMAReductions.R_Erdos81_erdos_81_R1

-- Step Erdos81.erdos_81.R1.H3: hypothesis H3 of reduction Erdos81.erdos_81.R1 (core-edge triangle saturation).
-- Credit: @JamesSlash. Proof: split C into halves A, B and R into P (2a-3+2t colours) and Q;
-- colour inside edges greedily from P and A-B edges from Q by Galvin's kernel method with a
-- Latin-square base colouring. Galvin library adapted from LeanPool/lean-pool
-- (LeanPool/ClassicalGraphColouring/Galvin: GaleShapley, Kernel, Orientation; Apache 2.0).

/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/


/-!

An inductive proof of the Gale–Shapley theorem. If no two men share the same favourite woman,
matching every man to his favourite is stable. Otherwise two men `m₁ ≠ m₂` share the favourite
`w`; if `w` prefers `m₁`, the pair `(m₂, w)` may be deleted: in a stable matching of the smaller
instance, `w` is matched to someone at least as good as `m₁` (because `m₁` cannot prefer anybody
to `w`), so the deleted pair is blocked.
-/


namespace Galvin

/-- `IsTop E r m w`: `w` is an acceptable partner of `m` of minimal rank. -/
def IsTop {M W : Type*} (E : M → W → Prop) (rm : M → W → ℕ) (m : M) (w : W) : Prop :=
  E m w ∧ ∀ w', E m w' → rm m w ≤ rm m w'

/-- The stable matching property. -/
def IsStable {M W : Type*} (E : M → W → Prop) (rm : M → W → ℕ) (rw : W → M → ℕ)
    (μ : M → W → Prop) : Prop :=
  (∀ m w, μ m w → E m w) ∧
      (∀ m w w', μ m w → μ m w' → w = w') ∧ (∀ m m' w, μ m w → μ m' w → m = m') ∧
      ∀ m w, E m w → ¬ μ m w →
        (∃ w', μ m w' ∧ rm m w' < rm m w) ∨ (∃ m', μ m' w ∧ rw w m' < rw w m)

theorem exists_isTop {M W : Type*} (E : M → W → Prop) (rm : M → W → ℕ) (m : M) (w : W)
    (h : E m w) : ∃ w', IsTop E rm m w' := by
  classical
  have hex : ∃ k, ∃ w, E m w ∧ rm m w = k := ⟨_, w, h, rfl⟩
  obtain ⟨w', hw', hk⟩ := Nat.find_spec hex
  refine ⟨w', hw', fun v hv => ?_⟩
  rw [hk]
  exact Nat.find_min' hex ⟨v, hv, rfl⟩

theorem isStable_of_removal {M W : Type*} (E : M → W → Prop)
    (rm : M → W → ℕ) (rw : W → M → ℕ)
    {m₁ m₂ : M} {w : W} (h₁ : IsTop E rm m₁ w) (hlt : rw w m₁ < rw w m₂)
    (μ : M → W → Prop)
    (hμ : IsStable (fun m v => E m v ∧ ¬ (m = m₂ ∧ v = w)) rm rw μ) (hne : m₁ ≠ m₂) :
    IsStable E rm rw μ := by
  obtain ⟨hsub, hm, hw, hst⟩ := hμ
  refine ⟨fun m v h => (hsub m v h).1, hm, hw, fun m v hE hnot => ?_⟩
  by_cases hrem : m = m₂ ∧ v = w
  · obtain ⟨rfl, rfl⟩ := hrem
    right
    by_cases hμ₁ : μ m₁ v
    · exact ⟨m₁, hμ₁, hlt⟩
    · rcases hst m₁ v ⟨h₁.1, fun h => hne h.1⟩ hμ₁ with ⟨w', hw', hr⟩ | ⟨m', hm', hr⟩
      · exact absurd (h₁.2 w' (hsub _ _ hw').1) (not_le.mpr hr)
      · exact ⟨m', hm', hr.trans hlt⟩
  · exact hst m v ⟨hE, hrem⟩ hnot

theorem exists_isStable {M W : Type*} [Finite M] [Finite W]
    (rm : M → W → ℕ) (rw : W → M → ℕ) (hrm : ∀ m, Function.Injective (rm m))
    (hrw : ∀ w, Function.Injective (rw w)) :
    ∀ (n : ℕ) (E : M → W → Prop), {p : M × W | E p.1 p.2}.ncard = n →
      ∃ μ, IsStable E rm rw μ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro E hn
  by_cases hsh : ∃ m₁ m₂ w, m₁ ≠ m₂ ∧ IsTop E rm m₁ w ∧ IsTop E rm m₂ w
  · obtain ⟨m₁, m₂, w, hne, h₁, h₂⟩ := hsh
    have key : ∀ a b : M, a ≠ b → IsTop E rm a w → IsTop E rm b w → rw w a < rw w b →
        ∃ μ, IsStable E rm rw μ := by
      intro a b hab ha hb hlt
      let E' : M → W → Prop := fun m v => E m v ∧ ¬ (m = b ∧ v = w)
      have hlt' : {p : M × W | E' p.1 p.2}.ncard < n := by
        rw [← hn]
        apply Set.ncard_lt_ncard _ (Set.toFinite _)
        refine ⟨fun p hp => hp.1, fun h => ?_⟩
        have := h (show (b, w) ∈ {p : M × W | E p.1 p.2} from hb.1)
        exact this.2 ⟨rfl, rfl⟩
      obtain ⟨μ, hμ⟩ := ih _ hlt' E' rfl
      exact ⟨μ, isStable_of_removal E rm rw ha hlt μ hμ hab⟩
    rcases lt_or_gt_of_ne (fun h => hne (hrw w h)) with h | h
    · exact key m₁ m₂ hne h₁ h₂ h
    · exact key m₂ m₁ (Ne.symm hne) h₂ h₁ h
  · push Not at hsh
    refine ⟨IsTop E rm, fun m w h => h.1, fun m w w' h h' => ?_, fun m m' w h h' => ?_,
      fun m w hE hnot => ?_⟩
    · exact hrm m (le_antisymm (h.2 _ h'.1) (h'.2 _ h.1))
    · by_contra hc
      exact hsh m m' w hc h h'
    · obtain ⟨w', hw'⟩ := exists_isTop E rm m w hE
      left
      refine ⟨w', hw', lt_of_le_of_ne (hw'.2 w hE) fun heq => ?_⟩
      rw [hrm m heq] at hw'
      exact hnot hw'

end Galvin
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/


/-!

Let `D` be a relation (the arcs of an orientation) on the vertices of a finite graph `G`. Suppose
every finite set `S` of vertices has a *kernel*: a `G`-independent `K ⊆ S` such that every
`x ∈ S \ K` has an arc `D x y` into `K`. If the list of every vertex is longer than its
out-degree, then there is a proper colouring choosing every colour from the corresponding list.
-/


namespace Galvin

open Finset

/-- Every finite set of vertices has a kernel with respect to the arcs `D`. -/
def HasKernels {α : Type*} (G : SimpleGraph α) (D : α → α → Prop) : Prop :=
  ∀ S : Finset α, ∃ K ⊆ S, (∀ x ∈ K, ∀ y ∈ K, ¬ G.Adj x y) ∧
    ∀ x ∈ S, x ∉ K → ∃ y ∈ K, D x y

theorem exists_listColoring_on {α Color : Type*} [Nonempty Color]
    (G : SimpleGraph α) (D : α → α → Prop) [DecidableRel D] (hK : HasKernels G D) :
    ∀ (n : ℕ) (U : Finset α), U.card = n → ∀ L : α → Finset Color,
      (∀ x ∈ U, (U.filter (D x ·)).card < (L x).card) →
      ∃ c : α → Color, (∀ x ∈ U, c x ∈ L x) ∧
        ∀ x ∈ U, ∀ y ∈ U, G.Adj x y → c x ≠ c y := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U hn L hL
  rcases U.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨fun _ => Classical.arbitrary _, by simp, by simp⟩
  obtain ⟨κ, hκ⟩ : (L x₀).Nonempty :=
    Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) (hL x₀ hx₀))
  set S := U.filter (κ ∈ L ·) with hS
  obtain ⟨K, hKS, hKind, hKabs⟩ := hK S
  have hx₀S : x₀ ∈ S := by simp [hS, hx₀, hκ]
  have hKU : K ⊆ U := hKS.trans (filter_subset _ _)
  have hKne : K.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    by_cases hx : x₀ ∈ K
    · simp [h] at hx
    · obtain ⟨y, hy, -⟩ := hKabs x₀ hx₀S hx
      simp [h] at hy
  have hlt : (U \ K).card < n := by
    rw [← hn]
    exact Finset.card_lt_card (Finset.sdiff_ssubset hKU hKne)
  obtain ⟨c', hc'L, hc'p⟩ := ih _ hlt (U \ K) rfl (fun x => (L x).erase κ) (by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    by_cases hκx : κ ∈ L x
    · rw [Finset.card_erase_of_mem hκx]
      obtain ⟨y, hy, hD⟩ := hKabs x (by simp [hS, hx.1, hκx]) hx.2
      have hsub : insert y ((U \ K).filter (D x ·)) ⊆ U.filter (D x ·) := by
        intro z hz
        rw [Finset.mem_insert] at hz
        rcases hz with rfl | hz
        · simp [hKU hy, hD]
        · simp only [Finset.mem_filter, Finset.mem_sdiff] at hz ⊢
          exact ⟨hz.1.1, hz.2⟩
      have hyn : y ∉ (U \ K).filter (D x ·) := by simp [hy]
      have := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hyn] at this
      have := hL x hx.1
      omega
    · rw [Finset.erase_eq_of_notMem hκx]
      refine lt_of_le_of_lt (Finset.card_le_card ?_) (hL x hx.1)
      exact Finset.filter_subset_filter _ Finset.sdiff_subset)
  refine ⟨fun x => if x ∈ K then κ else c' x, fun x hx => ?_, fun x hx y hy hxy => ?_⟩
  · by_cases hxK : x ∈ K
    · simp only [hxK, ite_true]
      have := hKS hxK
      simp only [hS, Finset.mem_filter] at this
      exact this.2
    · simp only [hxK, ite_false]
      exact Finset.mem_of_mem_erase (hc'L x (by simp [hx, hxK]))
  · by_cases hxK : x ∈ K <;> by_cases hyK : y ∈ K <;> simp only [hxK, hyK, ite_true, ite_false]
    · exact (hKind x hxK y hyK hxy).elim
    · intro h
      have := hc'L y (by simp [hy, hyK])
      rw [← h] at this
      simp at this
    · intro h
      have := hc'L x (by simp [hx, hxK])
      rw [h] at this
      simp at this
    · exact hc'p x (by simp [hx, hxK]) y (by simp [hy, hyK]) hxy

/-- **Kernel lemma.** If every finite set of vertices has a kernel and every list is longer than
the out-degree of its vertex, there is a proper list colouring. -/
theorem exists_listColoring {α Color : Type*} [Fintype α]
    (G : SimpleGraph α) (D : α → α → Prop) [DecidableRel D] (hK : HasKernels G D)
    (L : α → Finset Color)
    (hL : ∀ x, (Finset.univ.filter (D x ·)).card < (L x).card) :
    ∃ c : G.Coloring Color, ∀ x, c x ∈ L x := by
  classical
  cases isEmpty_or_nonempty α with
  | inl _ => exact ⟨SimpleGraph.Coloring.mk (fun x => isEmptyElim x) fun {x} => isEmptyElim x,
      fun x => isEmptyElim x⟩
  | inr hα => ?_
  have : Nonempty Color := by
    obtain ⟨x⟩ := hα
    obtain ⟨k, -⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) (hL x))
    exact ⟨k⟩
  obtain ⟨c, hcL, hcp⟩ := exists_listColoring_on G D hK _ Finset.univ rfl L
    (fun x _ => hL x)
  exact ⟨SimpleGraph.Coloring.mk c fun {x y} h => hcp x (mem_univ _) y (mem_univ _) h,
    fun x => hcL x (mem_univ _)⟩

end Galvin
/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/


/-!

Fix a `2`-colouring `c` of `G` (sides `0` and `1`) and a proper edge colouring `φ` with colours
in `Fin Δ`. Every edge `e` has an endpoint `endA c e` on side `0` and `endB c e` on side `1`. For
edges sharing their side-`0` endpoint, the arc goes from the larger to the smaller colour; for
edges sharing their side-`1` endpoint, from the smaller to the larger colour. Every out-degree is
less than `Δ`, and every set of edges has a kernel (a stable matching).
-/


namespace Galvin

open Finset SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

theorem exists_ends (c : G.Coloring (Fin 2)) (e : G.edgeSet) :
    ∃ a b : V, (e : Sym2 V) = s(a, b) ∧ c a = 0 := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ x y =>
  have hne : c x ≠ c y := c.valid he
  by_cases hx : c x = 0
  · exact ⟨x, y, rfl, hx⟩
  · refine ⟨y, x, Sym2.eq_swap, ?_⟩
    revert hne hx
    generalize c x = i
    generalize c y = j
    revert i j
    decide

/-- The endpoint of an edge on side `0`. -/
noncomputable def endA (c : G.Coloring (Fin 2)) (e : G.edgeSet) : V :=
  (exists_ends c e).choose

/-- The endpoint of an edge on side `1`. -/
noncomputable def endB (c : G.Coloring (Fin 2)) (e : G.edgeSet) : V :=
  (exists_ends c e).choose_spec.choose

theorem edge_eq_ends (c : G.Coloring (Fin 2)) (e : G.edgeSet) :
    (e : Sym2 V) = s(endA c e, endB c e) :=
  (exists_ends c e).choose_spec.choose_spec.1

theorem colour_endA (c : G.Coloring (Fin 2)) (e : G.edgeSet) : c (endA c e) = 0 :=
  (exists_ends c e).choose_spec.choose_spec.2

theorem adj_ends (c : G.Coloring (Fin 2)) (e : G.edgeSet) : G.Adj (endA c e) (endB c e) := by
  have := e.2
  rw [edge_eq_ends c e] at this
  exact this

theorem colour_endB (c : G.Coloring (Fin 2)) (e : G.edgeSet) : c (endB c e) = 1 := by
  have h1 := c.valid (adj_ends c e)
  rw [colour_endA] at h1
  revert h1
  generalize c (endB c e) = i
  revert i
  decide

theorem eq_of_ends (c : G.Coloring (Fin 2)) {e f : G.edgeSet} (hA : endA c e = endA c f)
    (hB : endB c e = endB c f) : e = f := by
  apply Subtype.ext
  rw [edge_eq_ends c e, edge_eq_ends c f, hA, hB]

theorem mem_edge_iff (c : G.Coloring (Fin 2)) (e : G.edgeSet) (v : V) :
    v ∈ (e : Sym2 V) ↔ v = endA c e ∨ v = endB c e := by
  rw [edge_eq_ends c e, Sym2.mem_iff]

theorem lineGraph_adj_iff_ends (c : G.Coloring (Fin 2)) {e f : G.edgeSet} :
    G.lineGraph.Adj e f ↔ e ≠ f ∧ (endA c e = endA c f ∨ endB c e = endB c f) := by
  rw [lineGraph_adj_iff_exists]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨v, hve, hvf⟩
    rw [mem_edge_iff c] at hve hvf
    have hA := colour_endA c e
    have hA' := colour_endA c f
    have hB := colour_endB c e
    have hB' := colour_endB c f
    rcases hve with rfl | rfl <;> rcases hvf with h | h
    · exact Or.inl h
    · rw [h, hB'] at hA; exact absurd hA (by decide)
    · rw [h, hA'] at hB; exact absurd hB (by decide)
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨endA c e, (mem_edge_iff c e _).2 (Or.inl rfl), (mem_edge_iff c f _).2 (Or.inl h)⟩
    · exact ⟨endB c e, (mem_edge_iff c e _).2 (Or.inr rfl), (mem_edge_iff c f _).2 (Or.inr h)⟩

theorem eq_of_colour_eq (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    {e f : G.edgeSet} (hφ : φ e = φ f) (h : endA c e = endA c f ∨ endB c e = endB c f) :
    e = f := by
  by_contra hne
  exact φ.valid ((lineGraph_adj_iff_ends c).2 ⟨hne, h⟩) hφ

/-- Galvin's orientation of the line graph. -/
def arc (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    (e f : G.edgeSet) : Prop :=
  (endA c e = endA c f ∧ φ f < φ e) ∨ (endB c e = endB c f ∧ φ e < φ f)

/-- Every out-degree of Galvin's orientation is less than `Δ`. -/
theorem card_arc_lt [Fintype G.edgeSet] (c : G.Coloring (Fin 2)) {Δ : ℕ}
    (φ : G.lineGraph.Coloring (Fin Δ)) (e : G.edgeSet) [DecidablePred (arc c φ e)] :
    (univ.filter (arc c φ e)).card < Δ := by
  classical
  have hsub : univ.filter (arc c φ e) ⊆
      univ.filter (fun f => endA c e = endA c f ∧ φ f < φ e) ∪
        univ.filter (fun f => endB c e = endB c f ∧ φ e < φ f) := by
    intro f hf
    simp only [arc, mem_filter, mem_univ, true_and, mem_union] at hf ⊢
    exact hf
  have h1 : (univ.filter (fun f => endA c e = endA c f ∧ φ f < φ e)).card ≤
      (Iio (φ e)).card := by
    refine card_le_card_of_injOn (fun f => φ f) (fun f hf => ?_) (fun f hf f' hf' h => ?_)
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hf
      simpa using hf.2
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hf hf'
      exact eq_of_colour_eq c φ h (Or.inl (hf.1.symm.trans hf'.1))
  have h2 : (univ.filter (fun f => endB c e = endB c f ∧ φ e < φ f)).card ≤
      (Ioi (φ e)).card := by
    refine card_le_card_of_injOn (fun f => φ f) (fun f hf => ?_) (fun f hf f' hf' h => ?_)
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hf
      simpa using hf.2
    · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hf hf'
      exact eq_of_colour_eq c φ h (Or.inr (hf.1.symm.trans hf'.1))
  rw [Fin.card_Iio] at h1
  rw [Fin.card_Ioi] at h2
  have h3 := (card_le_card hsub).trans (card_union_le _ _)
  have h4 := (φ e).isLt
  omega

/-- Rank of `w` for the man `m`: the colour of the edge `mw` (smaller colours preferred). -/
noncomputable def rankA (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    (idx : V → ℕ) (m w : V) : ℕ :=
  open Classical in
  if h : ∃ e : G.edgeSet, endA c e = m ∧ endB c e = w then (φ h.choose : ℕ) else Δ + idx w

/-- Rank of `m` for the woman `w`: `Δ` minus the colour of the edge `mw` (larger colours
preferred). -/
noncomputable def rankB (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    (idx : V → ℕ) (w m : V) : ℕ :=
  open Classical in
  if h : ∃ e : G.edgeSet, endA c e = m ∧ endB c e = w then Δ - (φ h.choose : ℕ)
  else Δ + 1 + idx m

theorem choose_ends_eq (c : G.Coloring (Fin 2)) (e : G.edgeSet)
    (h : ∃ f : G.edgeSet, endA c f = endA c e ∧ endB c f = endB c e) : h.choose = e :=
  eq_of_ends c h.choose_spec.1 h.choose_spec.2

theorem rankA_ends (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    (idx : V → ℕ) (e : G.edgeSet) : rankA c φ idx (endA c e) (endB c e) = φ e := by
  have h : ∃ f : G.edgeSet, endA c f = endA c e ∧ endB c f = endB c e := ⟨e, rfl, rfl⟩
  rw [rankA]
  split_ifs
  rw [choose_ends_eq c e h]

theorem rankB_ends (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    (idx : V → ℕ) (e : G.edgeSet) : rankB c φ idx (endB c e) (endA c e) = Δ - φ e := by
  have h : ∃ f : G.edgeSet, endA c f = endA c e ∧ endB c f = endB c e := ⟨e, rfl, rfl⟩
  rw [rankB]
  split_ifs
  rw [choose_ends_eq c e h]

theorem rankA_injective (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    {idx : V → ℕ} (hidx : Function.Injective idx) (m : V) :
    Function.Injective (rankA c φ idx m) := by
  intro w w' hww
  unfold rankA at hww
  split_ifs at hww with h h'
  · have := eq_of_colour_eq c φ (Fin.ext hww)
      (Or.inl (h.choose_spec.1.trans h'.choose_spec.1.symm))
    rw [← h.choose_spec.2, ← h'.choose_spec.2, this]
  · have := (φ h.choose).isLt; omega
  · rename_i h₂; have := (φ h₂.choose).isLt; omega
  · exact hidx (by omega)

theorem rankB_injective (c : G.Coloring (Fin 2)) {Δ : ℕ} (φ : G.lineGraph.Coloring (Fin Δ))
    {idx : V → ℕ} (hidx : Function.Injective idx) (w : V) :
    Function.Injective (rankB c φ idx w) := by
  intro m m' hmm
  unfold rankB at hmm
  split_ifs at hmm with h h'
  · have h1 := (φ h.choose).isLt
    have h2 := (φ h'.choose).isLt
    have := eq_of_colour_eq c φ (Fin.ext (by omega))
      (Or.inr (h.choose_spec.2.trans h'.choose_spec.2.symm))
    rw [← h.choose_spec.1, ← h'.choose_spec.1, this]
  · omega
  · omega
  · exact hidx (by omega)

/-- Every set of edges has a kernel for Galvin's orientation: a stable matching. -/
theorem hasKernels_arc [Finite V] (c : G.Coloring (Fin 2)) {Δ : ℕ}
    (φ : G.lineGraph.Coloring (Fin Δ)) : HasKernels G.lineGraph (arc c φ) := by
  classical
  intro S
  obtain ⟨N, ⟨eqv⟩⟩ := Finite.exists_equiv_fin V
  let idx : V → ℕ := fun v => (eqv v : ℕ)
  have hidx : Function.Injective idx := fun a b h => eqv.injective (Fin.ext h)
  let E : V → V → Prop := fun m w => ∃ e ∈ S, endA c e = m ∧ endB c e = w
  obtain ⟨μ, hsub, hm, hw, hst⟩ := exists_isStable (rankA c φ idx) (rankB c φ idx)
    (rankA_injective c φ hidx) (rankB_injective c φ hidx) _ E rfl
  refine ⟨S.filter (fun e => μ (endA c e) (endB c e)), filter_subset _ _, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [mem_filter] at hx hy
    obtain ⟨hne, h | h⟩ := (lineGraph_adj_iff_ends c).1 hxy
    · rw [h] at hx
      exact hne (eq_of_ends c h (hm _ _ _ hx.2 hy.2))
    · rw [h] at hx
      exact hne (eq_of_ends c (hw _ _ _ hx.2 hy.2) h)
  · intro x hxS hxK
    simp only [mem_filter, hxS, true_and] at hxK
    rcases hst _ _ ⟨x, hxS, rfl, rfl⟩ hxK with ⟨w', hμ, hlt⟩ | ⟨m', hμ, hlt⟩
    · obtain ⟨f, hfS, hfA, hfB⟩ := hsub _ _ hμ
      subst hfB
      rw [← hfA] at hμ hlt
      refine ⟨f, mem_filter.2 ⟨hfS, hμ⟩, Or.inl ⟨hfA.symm, ?_⟩⟩
      rw [rankA_ends, hfA, rankA_ends] at hlt
      exact hlt
    · obtain ⟨f, hfS, hfA, hfB⟩ := hsub _ _ hμ
      subst hfA
      rw [← hfB] at hμ hlt
      refine ⟨f, mem_filter.2 ⟨hfS, hμ⟩, Or.inr ⟨hfB.symm, ?_⟩⟩
      rw [rankB_ends, hfB, rankB_ends] at hlt
      have := (φ f).isLt
      have := (φ x).isLt
      change (φ x : ℕ) < φ f
      omega

end Galvin

namespace OMA81H3

open Finset SimpleGraph

/-- Greedy list colouring for a symmetric irreflexive conflict relation. -/
theorem greedy_list {α Color : Type*} [DecidableEq α] [DecidableEq Color]
    (K : α → α → Prop) [DecidableRel K] (hsymm : ∀ x y, K x y → K y x)
    (hirr : ∀ x, ¬ K x x) (L : α → Finset Color) (c0 : Color) :
    ∀ E : Finset α, (∀ x ∈ E, (E.filter (K x)).card < (L x).card) →
      ∃ col : α → Color, ∀ x ∈ E, col x ∈ L x ∧ ∀ y ∈ E, K x y → col x ≠ col y := by
  intro E
  induction E using Finset.induction_on with
  | empty => intro _; exact ⟨fun _ => c0, by simp⟩
  | @insert x E hx ih =>
    intro hcard
    have hcard' : ∀ y ∈ E, (E.filter (K y)).card < (L y).card := by
      intro y hy
      refine lt_of_le_of_lt (card_le_card ?_) (hcard y (mem_insert_of_mem hy))
      exact filter_subset_filter _ (subset_insert _ _)
    obtain ⟨col, hcol⟩ := ih hcard'
    set forb := (E.filter (K x)).image col with hforb
    have hfx : (insert x E).filter (K x) = E.filter (K x) := by
      rw [filter_insert, if_neg (hirr x)]
    have hlt : forb.card < (L x).card := by
      calc forb.card ≤ (E.filter (K x)).card := card_image_le
        _ = ((insert x E).filter (K x)).card := by rw [hfx]
        _ < (L x).card := hcard x (mem_insert_self _ _)
    obtain ⟨c, hcL, hcf⟩ : ∃ c ∈ L x, c ∉ forb := by
      by_contra h
      push Not at h
      exact absurd (card_le_card h) (not_le.mpr hlt)
    refine ⟨Function.update col x c, ?_⟩
    intro z hz
    rcases mem_insert.mp hz with rfl | hzE
    · refine ⟨by simpa using hcL, ?_⟩
      intro y hy hK
      have hyx : y ≠ z := fun h => hirr z (h ▸ hK)
      have hyE : y ∈ E := by
        rcases mem_insert.mp hy with h | h
        · exact absurd h hyx
        · exact h
      rw [Function.update_self, Function.update_of_ne hyx]
      intro hc
      apply hcf
      rw [hforb, hc]
      exact mem_image_of_mem _ (mem_filter.mpr ⟨hyE, hK⟩)
    · have hzx : z ≠ x := fun h => hx (h ▸ hzE)
      refine ⟨by rw [Function.update_of_ne hzx]; exact (hcol z hzE).1, ?_⟩
      intro y hy hK
      rw [Function.update_of_ne hzx]
      rcases mem_insert.mp hy with rfl | hyE
      · rw [Function.update_self]
        intro hc
        apply hcf
        rw [hforb, ← hc]
        exact mem_image_of_mem _ (mem_filter.mpr ⟨hzE, hsymm _ _ hK⟩)
      · have hyx : y ≠ x := fun h => hx (h ▸ hyE)
        rw [Function.update_of_ne hyx]
        exact (hcol z hzE).2 y hyE hK

theorem mod_cancel {a j x y : ℕ} (hx : x < a) (hy : y < a) (h : (j + x) % a = (j + y) % a) :
    x = y := by
  have h1 : (j + x) ≡ (j + y) [MOD a] := h
  have h2 : x ≡ y [MOD a] := Nat.ModEq.add_left_cancel' j h1
  unfold Nat.ModEq at h2
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h2

end OMA81H3

namespace OMA81H3

open Finset SimpleGraph

/-- Common neighbours inside `X` of the ends of an edge. -/
theorem common_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (R X : Finset (Fin n))
    (τ : ℕ) (hXR : X ⊆ R) (hτ : ∀ u, (R.filter (fun r ↦ ¬ G.Adj u r)).card ≤ τ → True)
    (u v : Fin n) (hu : (R.filter (fun r ↦ ¬ G.Adj u r)).card ≤ τ)
    (hv : (R.filter (fun r ↦ ¬ G.Adj v r)).card ≤ τ) :
    X.card ≤ (X.filter (fun r => ∀ x ∈ s(u, v), G.Adj x r)).card + 2 * τ := by
  have hsub : X ⊆ X.filter (fun r => ∀ x ∈ s(u, v), G.Adj x r) ∪
      (R.filter (fun r ↦ ¬ G.Adj u r) ∪ R.filter (fun r ↦ ¬ G.Adj v r)) := by
    intro r hr
    by_cases h : ∀ x ∈ s(u, v), G.Adj x r
    · exact mem_union_left _ (mem_filter.mpr ⟨hr, h⟩)
    · push Not at h
      obtain ⟨x, hx, hnx⟩ := h
      rcases Sym2.mem_iff.mp hx with rfl | rfl
      · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hXR hr, hnx⟩))
      · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hXR hr, hnx⟩))
  calc X.card ≤ _ := card_le_card hsub
    _ ≤ _ := card_union_le _ _
    _ ≤ _ := by
      have := card_union_le (R.filter (fun r ↦ ¬ G.Adj u r)) (R.filter (fun r ↦ ¬ G.Adj v r))
      omega

/-- Inside edges of two disjoint parts. -/
def inside {n : ℕ} (G : SimpleGraph (Fin n)) (X Y : Finset (Fin n)) : Set (Sym2 (Fin n)) :=
  {e | ∃ p q, e = s(p, q) ∧ G.Adj p q ∧ ((p ∈ X ∧ q ∈ X) ∨ (p ∈ Y ∧ q ∈ Y))}

/-- Conflict relation: distinct edges sharing a vertex. -/
def conf {n : ℕ} (e f : Sym2 (Fin n)) : Prop := e ≠ f ∧ ∃ x, x ∈ e ∧ x ∈ f

theorem conflict_sub {n : ℕ} (G : SimpleGraph (Fin n)) (X Y : Finset (Fin n))
    (hXY : Disjoint X Y) (E1 : Finset (Sym2 (Fin n))) (hE1 : ∀ e ∈ E1, e ∈ inside G X Y)
    (u v : Fin n) (hu : u ∈ X) (hv : v ∈ X) [DecidablePred (conf s(u, v))] :
    E1.filter (conf s(u, v)) ⊆
      ((X.erase u).erase v).image (fun w => s(u, w)) ∪
        ((X.erase u).erase v).image (fun w => s(v, w)) := by
  classical
  intro f hf
  obtain ⟨hfE, hne, x, hxe, hxf⟩ := mem_filter.mp hf
  obtain ⟨p, q, rfl, hpq, hpart⟩ := hE1 f hfE
  have hxX : x ∈ X := by rcases Sym2.mem_iff.mp hxe with rfl | rfl <;> assumption
  have hpqX : p ∈ X ∧ q ∈ X := by
    rcases hpart with h | ⟨hp, hq⟩
    · exact h
    · exfalso
      rcases Sym2.mem_iff.mp hxf with rfl | rfl
      · exact disjoint_left.mp hXY hxX hp
      · exact disjoint_left.mp hXY hxX hq
  -- write f as s(x, y)
  obtain ⟨y, hy, hfxy⟩ : ∃ y, y ∈ X ∧ s(p, q) = s(x, y) ∧ x ≠ y := by
    rcases Sym2.mem_iff.mp hxf with rfl | rfl
    · exact ⟨q, hpqX.2, rfl, hpq.ne⟩
    · exact ⟨p, hpqX.1, Sym2.eq_swap, hpq.ne.symm⟩
  rw [hfxy.1] at hne ⊢
  rcases Sym2.mem_iff.mp hxe with rfl | rfl
  · have hyv : y ≠ v := fun h => hne (by rw [h])
    exact mem_union_left _ (mem_image.mpr ⟨y, mem_erase.mpr ⟨hyv, mem_erase.mpr ⟨hfxy.2.symm, hy⟩⟩, rfl⟩)
  · have hyu : y ≠ u := fun h => hne (by rw [h, Sym2.eq_swap])
    exact mem_union_right _ (mem_image.mpr ⟨y, mem_erase.mpr ⟨hfxy.2.symm, mem_erase.mpr ⟨hyu, hy⟩⟩, rfl⟩)

end OMA81H3

namespace OMA81H3

open Finset SimpleGraph

theorem h3_main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C R : Finset (Fin n)) (τ : ℕ) (hC : 3 ≤ C.card)
    (hτ : ∀ u ∈ C, (R.filter (fun r ↦ ¬ G.Adj u r)).card ≤ τ)
    (hR : 3 * ((C.card + 1) / 2) + 4 * τ ≤ R.card + 3) :
    ∃ φ : Sym2 (Fin n) → Fin n,
      (∀ u ∈ C, ∀ v ∈ C, G.Adj u v →
        φ s(u, v) ∈ R ∧ G.Adj u (φ s(u, v)) ∧ G.Adj v (φ s(u, v))) ∧
      (∀ u ∈ C, ∀ v ∈ C, ∀ w ∈ C, v ≠ w → G.Adj u v → G.Adj u w →
        φ s(u, v) ≠ φ s(u, w)) := by
  classical
  set c := C.card with hc
  set a := (c + 1) / 2 with ha
  have ha2 : 2 ≤ a := by omega
  have hca : c - a ≤ a := by omega
  have hapos : 0 < a := by omega
  obtain ⟨u0, hu0⟩ : C.Nonempty := card_pos.mp (by omega)
  let eC := C.equivFin
  let ix : Fin n → ℕ := fun x => if h : x ∈ C then ((eC ⟨x, h⟩ : Fin c) : ℕ) else 0
  have ix_lt : ∀ x ∈ C, ix x < c := by
    intro x hx
    simp only [ix, dif_pos hx]
    exact (eC ⟨x, hx⟩).isLt
  have ix_inj : ∀ x ∈ C, ∀ y ∈ C, ix x = ix y → x = y := by
    intro x hx y hy h
    simp only [ix, dif_pos hx, dif_pos hy] at h
    have := eC.injective (Fin.ext h)
    exact congrArg Subtype.val this
  set A := C.filter (fun x => ix x < a) with hAdef
  set B := C.filter (fun x => a ≤ ix x) with hBdef
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have h1 := (mem_filter.mp hxA).2
    have h2 := (mem_filter.mp hxB).2
    omega
  have hnAB : ∀ x, x ∈ A → x ∈ B → False := fun x h1 h2 => Finset.disjoint_left.mp hAB h1 h2
  have hCAB : ∀ x ∈ C, x ∈ A ∨ x ∈ B := by
    intro x hx
    by_cases h : ix x < a
    · exact Or.inl (mem_filter.mpr ⟨hx, h⟩)
    · exact Or.inr (mem_filter.mpr ⟨hx, by omega⟩)
  have hAC : A ⊆ C := filter_subset _ _
  have hBC : B ⊆ C := filter_subset _ _
  have hAcard : A.card ≤ a := by
    have : A.card ≤ (range a).card := by
      apply card_le_card_of_injOn ix
      · intro x hx
        simp only [Finset.mem_coe, Finset.mem_range]
        exact (mem_filter.mp hx).2
      · intro x hx y hy h
        exact ix_inj x (hAC hx) y (hAC hy) h
    simpa using this
  have hBcard : B.card ≤ a := by
    have : B.card ≤ (range (c - a)).card := by
      apply card_le_card_of_injOn (fun x => ix x - a)
      · intro x hx
        have h1 := (mem_filter.mp hx).2
        have h2 := ix_lt x (hBC hx)
        simp only [Finset.mem_coe, Finset.mem_range]
        omega
      · intro x hx y hy h
        have h1 := (mem_filter.mp hx).2
        have h2 := (mem_filter.mp hy).2
        have h3 : ix x - a = ix y - a := h
        exact ix_inj x (hBC hx) y (hBC hy) (by omega)
    simp only [card_range] at this
    omega
  -- split R into P and Q
  have hPle : 2 * a - 3 + 2 * τ ≤ R.card := by omega
  obtain ⟨P, hPR, hPcard⟩ := exists_subset_card_eq hPle
  set Q := R \ P with hQ
  have hQR : Q ⊆ R := sdiff_subset
  have hQcard : a + 2 * τ ≤ Q.card := by
    have h1 : Q.card + P.card = R.card := card_sdiff_add_card_eq_card hPR
    omega
  have hPQ : Disjoint P Q := disjoint_sdiff
  let comm : Finset (Fin n) → Sym2 (Fin n) → Finset (Fin n) :=
    fun X e => X.filter (fun r => ∀ x ∈ e, G.Adj x r)
  have comm_card : ∀ X ⊆ R, ∀ u ∈ C, ∀ v ∈ C, X.card ≤ (comm X s(u, v)).card + 2 * τ :=
    fun X hX u hu v hv => common_card G R X τ hX (fun _ _ => trivial) u v (hτ u hu) (hτ v hv)
  -- inside edges: greedy colouring from P
  let E1 : Finset (Sym2 (Fin n)) := univ.filter (fun e => e ∈ inside G A B)
  have hE1 : ∀ e ∈ E1, e ∈ inside G A B := fun e he => (mem_filter.mp he).2
  have hE1' : ∀ e ∈ E1, e ∈ inside G B A := by
    intro e he
    obtain ⟨p, q, h1, h2, h3⟩ := hE1 e he
    exact ⟨p, q, h1, h2, h3.symm⟩
  have hconf_symm : ∀ e f : Sym2 (Fin n), conf e f → conf f e := by
    rintro e f ⟨hne, x, hx1, hx2⟩
    exact ⟨hne.symm, x, hx2, hx1⟩
  have hconf_irr : ∀ e : Sym2 (Fin n), ¬ conf e e := fun e h => h.1 rfl
  have hE1card : ∀ e ∈ E1, (E1.filter (conf e)).card < (comm P e).card := by
    intro e he
    obtain ⟨p, q, rfl, hpq, hpart⟩ := hE1 e he
    have hpC : p ∈ C := by
      rcases hpart with h | h
      · exact hAC h.1
      · exact hBC h.1
    have hqC : q ∈ C := by
      rcases hpart with h | h
      · exact hAC h.2
      · exact hBC h.2
    have hP := comm_card P hPR p hpC q hqC
    rcases hpart with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · have h1 := card_le_card (conflict_sub G A B hAB E1 hE1 p q hp hq)
      have h2 := card_union_le (((A.erase p).erase q).image (fun w => s(p, w)))
        (((A.erase p).erase q).image (fun w => s(q, w)))
      have h3 := card_image_le (s := (A.erase p).erase q) (f := fun w => s(p, w))
      have h4 := card_image_le (s := (A.erase p).erase q) (f := fun w => s(q, w))
      have h5 : ((A.erase p).erase q).card + 2 = A.card := by
        rw [card_erase_of_mem (mem_erase.mpr ⟨hpq.ne.symm, hq⟩), card_erase_of_mem hp]
        have : 2 ≤ A.card := by
          have : ({p, q} : Finset (Fin n)) ⊆ A := by
            intro x hx
            rcases mem_insert.mp hx with rfl | hx
            · exact hp
            · rw [mem_singleton.mp hx]; exact hq
          have h6 := card_le_card this
          rw [card_pair hpq.ne] at h6
          exact h6
        omega
      omega
    · have h1 := card_le_card (conflict_sub G B A hAB.symm E1 hE1' p q hp hq)
      have h2 := card_union_le (((B.erase p).erase q).image (fun w => s(p, w)))
        (((B.erase p).erase q).image (fun w => s(q, w)))
      have h3 := card_image_le (s := (B.erase p).erase q) (f := fun w => s(p, w))
      have h4 := card_image_le (s := (B.erase p).erase q) (f := fun w => s(q, w))
      have h5 : ((B.erase p).erase q).card + 2 = B.card := by
        rw [card_erase_of_mem (mem_erase.mpr ⟨hpq.ne.symm, hq⟩), card_erase_of_mem hp]
        have : 2 ≤ B.card := by
          have : ({p, q} : Finset (Fin n)) ⊆ B := by
            intro x hx
            rcases mem_insert.mp hx with rfl | hx
            · exact hp
            · rw [mem_singleton.mp hx]; exact hq
          have h6 := card_le_card this
          rw [card_pair hpq.ne] at h6
          exact h6
        omega
      omega
  obtain ⟨col1, hcol1⟩ := greedy_list conf hconf_symm hconf_irr (comm P) u0 E1 hE1card
  -- cross edges: Galvin from Q
  let H : SimpleGraph (Fin n) :=
    { Adj := fun x y => G.Adj x y ∧ ((x ∈ A ∧ y ∈ B) ∨ (x ∈ B ∧ y ∈ A))
      symm := ⟨fun x y h =>
        ⟨h.1.symm, h.2.elim (fun h' => Or.inr ⟨h'.2, h'.1⟩) (fun h' => Or.inl ⟨h'.2, h'.1⟩)⟩⟩
      loopless := ⟨fun x h => h.1.ne rfl⟩ }
  have hHadj : ∀ x y, H.Adj x y ↔ G.Adj x y ∧ ((x ∈ A ∧ y ∈ B) ∨ (x ∈ B ∧ y ∈ A)) :=
    fun x y => Iff.rfl
  let cH : H.Coloring (Fin 2) := Coloring.mk (fun x => if x ∈ A then 0 else 1) (by
    intro x y h
    rcases ((hHadj x y).mp h).2 with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · have : y ∉ A := fun h' => hnAB y h' hy
      simp [hx, this]
    · have : x ∉ A := fun h' => hnAB x h' hx
      simp [hy, this])
  have endA_mem : ∀ e : H.edgeSet, Galvin.endA cH e ∈ A := by
    intro e
    have h := Galvin.colour_endA cH e
    by_contra hn
    have h' : cH (Galvin.endA cH e) = 1 := by
      show (if Galvin.endA cH e ∈ A then (0 : Fin 2) else 1) = 1
      rw [if_neg hn]
    rw [h'] at h
    exact absurd h (by decide)
  have endB_mem : ∀ e : H.edgeSet, Galvin.endB cH e ∈ B := by
    intro e
    have hadj := (hHadj _ _).mp (Galvin.adj_ends cH e)
    have hA := endA_mem e
    rcases hadj.2 with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · exact absurd hA (fun h' => hnAB _ h' h)
  let jx : Fin n → ℕ := fun x => if ix x < a then ix x else ix x - a
  have jxB : ∀ x ∈ B, jx x < a ∧ jx x + a = ix x := by
    intro x hx
    have h1 := (mem_filter.mp hx).2
    have h2 := ix_lt x (hBC hx)
    have h3 : ¬ ix x < a := by omega
    simp only [jx, if_neg h3]
    omega
  have jxA : ∀ x ∈ A, jx x < a ∧ jx x = ix x := by
    intro x hx
    have h1 := (mem_filter.mp hx).2
    refine ⟨?_, ?_⟩ <;> simp [jx, h1]
  let lc : H.lineGraph.Coloring (Fin a) := Coloring.mk
    (fun e => ⟨(jx (Galvin.endA cH e) + jx (Galvin.endB cH e)) % a, Nat.mod_lt _ hapos⟩) (by
      intro e f hef heq
      rw [Galvin.lineGraph_adj_iff_ends cH] at hef
      obtain ⟨hne, hends⟩ := hef
      have heq' : (jx (Galvin.endA cH e) + jx (Galvin.endB cH e)) % a =
          (jx (Galvin.endA cH f) + jx (Galvin.endB cH f)) % a := congrArg Fin.val heq
      apply hne
      rcases hends with hA | hB
      · rw [hA] at heq'
        have hj := mod_cancel (jxB _ (endB_mem e)).1 (jxB _ (endB_mem f)).1 heq'
        have hB : Galvin.endB cH e = Galvin.endB cH f := by
          have h1 := (jxB _ (endB_mem e)).2
          have h2 := (jxB _ (endB_mem f)).2
          exact ix_inj _ (hBC (endB_mem e)) _ (hBC (endB_mem f)) (by omega)
        exact Galvin.eq_of_ends cH hA hB
      · rw [hB, add_comm (jx (Galvin.endA cH e)), add_comm (jx (Galvin.endA cH f))] at heq'
        have hj := mod_cancel (jxA _ (endA_mem e)).1 (jxA _ (endA_mem f)).1 heq'
        have hA : Galvin.endA cH e = Galvin.endA cH f := by
          have h1 := (jxA _ (endA_mem e)).2
          have h2 := (jxA _ (endA_mem f)).2
          exact ix_inj _ (hAC (endA_mem e)) _ (hAC (endA_mem f)) (by omega)
        exact Galvin.eq_of_ends cH hA hB)
  have hL2 : ∀ e : H.edgeSet, a ≤ (comm Q e.1).card := by
    intro e
    have h := comm_card Q hQR _ (hAC (endA_mem e)) _ (hBC (endB_mem e))
    rw [← Galvin.edge_eq_ends cH e] at h
    omega
  obtain ⟨col2, hcol2⟩ := Galvin.exists_listColoring H.lineGraph (Galvin.arc cH lc)
    (Galvin.hasKernels_arc cH lc) (fun e => comm Q e.1)
    (fun e => lt_of_lt_of_le (Galvin.card_arc_lt cH lc e) (hL2 e))
  -- the combined colouring
  let φ : Sym2 (Fin n) → Fin n := fun e =>
    if e ∈ E1 then col1 e else if h : e ∈ H.edgeSet then col2 ⟨e, h⟩ else u0
  have inE1 : ∀ u v, G.Adj u v → ((u ∈ A ∧ v ∈ A) ∨ (u ∈ B ∧ v ∈ B)) → s(u, v) ∈ E1 :=
    fun u v huv h => mem_filter.mpr ⟨mem_univ _, ⟨u, v, rfl, huv, h⟩⟩
  have notE1 : ∀ u v, ((u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)) → s(u, v) ∉ E1 := by
    intro u v h hE
    obtain ⟨p, q, hpq, _, hpart⟩ := hE1 _ hE
    rcases Sym2.eq_iff.mp hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hpart with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      first
        | exact hnAB _ h1 h3 | exact hnAB _ h3 h1 | exact hnAB _ h1 h4 | exact hnAB _ h4 h1
        | exact hnAB _ h2 h3 | exact hnAB _ h3 h2 | exact hnAB _ h2 h4 | exact hnAB _ h4 h2
  -- classification of an edge at u
  have key : ∀ u ∈ C, ∀ x ∈ C, G.Adj u x →
      (s(u, x) ∈ E1 ∧ φ s(u, x) = col1 s(u, x) ∧ col1 s(u, x) ∈ comm P s(u, x)) ∨
      (∃ h : s(u, x) ∈ H.edgeSet, φ s(u, x) = col2 ⟨_, h⟩ ∧ col2 ⟨_, h⟩ ∈ comm Q s(u, x)) := by
    intro u hu x hx hux
    rcases hCAB u hu with huA | huB <;> rcases hCAB x hx with hxA | hxB
    · have hE := inE1 u x hux (Or.inl ⟨huA, hxA⟩)
      exact Or.inl ⟨hE, by simp only [φ, if_pos hE], (hcol1 _ hE).1⟩
    · have hnE := notE1 u x (Or.inl ⟨huA, hxB⟩)
      have hH : s(u, x) ∈ H.edgeSet := (mem_edgeSet H).mpr ⟨hux, Or.inl ⟨huA, hxB⟩⟩
      exact Or.inr ⟨hH, by simp only [φ, if_neg hnE, dif_pos hH], hcol2 ⟨_, hH⟩⟩
    · have hnE := notE1 u x (Or.inr ⟨huB, hxA⟩)
      have hH : s(u, x) ∈ H.edgeSet := (mem_edgeSet H).mpr ⟨hux, Or.inr ⟨huB, hxA⟩⟩
      exact Or.inr ⟨hH, by simp only [φ, if_neg hnE, dif_pos hH], hcol2 ⟨_, hH⟩⟩
    · have hE := inE1 u x hux (Or.inr ⟨huB, hxB⟩)
      exact Or.inl ⟨hE, by simp only [φ, if_pos hE], (hcol1 _ hE).1⟩
  refine ⟨φ, ?_, ?_⟩
  · intro u hu v hv huv
    rcases key u hu v hv huv with ⟨_, hφ, hm⟩ | ⟨_, hφ, hm⟩
    · obtain ⟨hrP, hradj⟩ := mem_filter.mp hm
      rw [hφ]
      exact ⟨hPR hrP, hradj u (Sym2.mem_mk_left u v), hradj v (Sym2.mem_mk_right u v)⟩
    · obtain ⟨hrQ, hradj⟩ := mem_filter.mp hm
      rw [hφ]
      exact ⟨hQR hrQ, hradj u (Sym2.mem_mk_left u v), hradj v (Sym2.mem_mk_right u v)⟩
  · intro u hu v hv w hw hvw huv huw
    have hne : s(u, v) ≠ s(u, w) := fun h => hvw (Sym2.congr_right.mp h)
    rcases key u hu v hv huv with ⟨hEv, hφv, hmv⟩ | ⟨hHv, hφv, hmv⟩ <;>
      rcases key u hu w hw huw with ⟨hEw, hφw, hmw⟩ | ⟨hHw, hφw, hmw⟩
    · rw [hφv, hφw]
      exact (hcol1 _ hEv).2 _ hEw ⟨hne, u, Sym2.mem_mk_left u v, Sym2.mem_mk_left u w⟩
    · rw [hφv, hφw]
      intro h
      have h1 := (mem_filter.mp hmv).1
      have h2 := (mem_filter.mp hmw).1
      rw [h] at h1
      exact Finset.disjoint_left.mp hPQ h1 h2
    · rw [hφv, hφw]
      intro h
      have h1 := (mem_filter.mp hmv).1
      have h2 := (mem_filter.mp hmw).1
      rw [h] at h1
      exact Finset.disjoint_left.mp hPQ h2 h1
    · rw [hφv, hφw]
      apply col2.valid
      rw [lineGraph_adj_iff_exists]
      exact ⟨fun h => hne (congrArg Subtype.val h), u, Sym2.mem_mk_left u v, Sym2.mem_mk_left u w⟩

end OMA81H3

theorem OMA.solution : OMA.R_Erdos81_erdos_81_R1.H3 := by
  intro n G _ C R τ _ hC hτ hR
  exact OMA81H3.h3_main n G C R τ hC hτ hR
