import FormalConjectures.ErdosProblems.«742»

/-!
# Proof of the Murty--Simon conjecture (`Erdos742.erdos_742`)

Formalizes the proof of the `⌊n^2 / 4⌋` edge bound for every diameter-2-critical graph
from Sanjana Das and Jacob Fox, *A proof of the Murty--Simon conjecture on diameter-2-critical
graphs* (arXiv:2610.39032, 2026), Section 2.

Credit: @skhakim.
-/

namespace OMA.MurtySimon

open SimpleGraph Finset
open scoped Classical

section Basic

variable {V : Type*}

private lemma eq_ediam (G : SimpleGraph V) : G.diam = 2 ↔ G.ediam = 2 := by
  rw [SimpleGraph.diam, ENat.toNat_eq_iff (by decide : (2 : ℕ) ≠ 0)]
  rfl

/-- A non-edge `f` is critical if it has a unique common neighbor. -/
private def IsCritNonEdge (G : SimpleGraph V) (f : Sym2 V) : Prop :=
  ¬ f.IsDiag ∧ f ∉ G.edgeSet ∧ ∃! u : V, ∀ w ∈ f, G.Adj u w

private lemma isCritNonEdge_mk_iff (G : SimpleGraph V) (x y : V) :
    IsCritNonEdge G s(x, y) ↔ x ≠ y ∧ ¬ G.Adj x y ∧ ∃! u : V, G.Adj u x ∧ G.Adj u y := by
  simp only [IsCritNonEdge, Sym2.mk_isDiag_iff, mem_edgeSet, Sym2.mem_iff, forall_eq_or_imp,
    forall_eq]

/-- Edge `e` lies on the critical 2-path of critical non-edge `f`. -/
private def OnCrit2Path (G : SimpleGraph V) (e f : Sym2 V) : Prop :=
  e ∈ G.edgeSet ∧ IsCritNonEdge G f ∧
    ∃ x y u : V, f = s(x, y) ∧ G.Adj u x ∧ G.Adj u y ∧ (e = s(u, x) ∨ e = s(u, y))

private lemma onCrit2Path_unique_two (G : SimpleGraph V) {f : Sym2 V} (hf : IsCritNonEdge G f) :
    ∃ x y u : V, f = s(x, y) ∧ x ≠ y ∧ ¬ G.Adj x y ∧ G.Adj u x ∧ G.Adj u y ∧
      (∀ w : V, G.Adj w x → G.Adj w y → w = u) ∧
      ∀ e : Sym2 V, OnCrit2Path G e f ↔ e = s(u, x) ∨ e = s(u, y) := by
  induction f using Sym2.ind with
  | _ x y =>
    obtain ⟨hxy, hna, u, ⟨hux, huy⟩, huniq⟩ := (isCritNonEdge_mk_iff G x y).mp hf
    refine ⟨x, y, u, rfl, hxy, hna, hux, huy, fun w hwx hwy => huniq w ⟨hwx, hwy⟩, fun e => ?_⟩
    constructor
    · rintro ⟨_, _, x', y', u', hfeq, hu'x, hu'y, hor⟩
      rw [Sym2.eq_iff] at hfeq
      rcases hfeq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have : u' = u := huniq u' ⟨hu'x, hu'y⟩
        subst this; exact hor
      · have : u' = u := huniq u' ⟨hu'y, hu'x⟩
        subst this; exact hor.symm
    · rintro (rfl | rfl)
      · exact ⟨hux, hf, x, y, u, rfl, hux, huy, Or.inl rfl⟩
      · exact ⟨huy, hf, x, y, u, rfl, hux, huy, Or.inr rfl⟩

end Basic

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Lemma 2.1 (Das--Fox): every edge in a triangle lies on a critical 2-path. -/
private lemma triangle_on_crit_2path (G : SimpleGraph V) (hG : Erdos742.IsDiameter2Critical G)
    {v x y : V} (vx : G.Adj v x) (vy : G.Adj v y) (xy : G.Adj x y) :
    (∃ z : V, IsCritNonEdge G s(x, z) ∧ G.Adj y x ∧ G.Adj y z) ∨
    (∃ z : V, IsCritNonEdge G s(y, z) ∧ G.Adj x y ∧ G.Adj x z) := by
  let D := G.deleteEdges {s(x, y)}
  have less := SimpleGraph.ediam_anti (G.deleteEdges_le {s(x, y)})
  have base := (eq_ediam G).mp hG.1
  change G.ediam ≤ D.ediam at less
  rw [base] at less
  have large : ¬ D.ediam ≤ 2 := by
    intro h
    exact hG.2 _ xy ((eq_ediam D).mpr (le_antisymm h less))
  rw [SimpleGraph.ediam_le_iff] at large
  push Not at large
  obtain ⟨a, b, far⟩ := large
  obtain ⟨ne, non, empty⟩ := D.two_lt_edist_iff.mp far
  have good (p q : V) : D.Adj p q ↔ G.Adj p q ∧ ¬ ((p = x ∧ q = y) ∨ (p = y ∧ q = x)) := by
    change (G.deleteEdges {s(x, y)}).Adj p q ↔ _
    simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
  have bad (t : V) (ha : D.Adj a t) (hb : D.Adj b t) : False := by
    have h := D.mem_commonNeighbors.mpr ⟨ha, hb⟩
    rw [empty] at h
    exact h
  have d1 : D.Adj x v := (good x v).mpr ⟨vx.symm, by
    rintro (⟨_, h2⟩ | ⟨h1, _⟩)
    · exact vy.ne h2
    · exact xy.ne h1⟩
  have d2 : D.Adj y v := (good y v).mpr ⟨vy.symm, by
    rintro (⟨h1, _⟩ | ⟨_, h2⟩)
    · exact xy.ne h1.symm
    · exact vx.ne h2⟩
  have uncut (p q : V) (h : G.Adj p q) (no : ¬ D.Adj p q) :
      (p = x ∧ q = y) ∨ (p = y ∧ q = x) := by
    by_contra miss
    exact no ((good _ _).mpr ⟨h, miss⟩)
  have ab : ¬ G.Adj a b := by
    intro e
    rcases uncut a b e non with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact bad v d1 d2
    · exact bad v d2 d1
  have common : (G.commonNeighbors a b).Nonempty := by
    by_contra! e
    have gt := G.two_lt_edist_iff.mpr ⟨ne, ab, e⟩
    have le : G.edist a b ≤ 2 := G.edist_le_ediam.trans_eq base
    exact (not_lt_of_ge le) gt
  obtain ⟨t, ht⟩ := common
  obtain ⟨at', bt'⟩ := G.mem_commonNeighbors.mp ht
  have broken (q : V) (qa : G.Adj a q) (qb : G.Adj b q) :
      ((a = x ∧ q = y) ∨ (a = y ∧ q = x)) ∨ ((b = x ∧ q = y) ∨ (b = y ∧ q = x)) := by
    by_cases left : (a = x ∧ q = y) ∨ (a = y ∧ q = x)
    · exact Or.inl left
    · right
      by_contra right
      exact bad q ((good _ _).mpr ⟨qa, left⟩) ((good _ _).mpr ⟨qb, right⟩)
  have na : ¬ G.Adj b a := fun h => ab h.symm
  rcases broken t at' bt' with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · left
    refine ⟨b, (isCritNonEdge_mk_iff G a b).mpr ⟨ne, ab, t, ⟨xy.symm, bt'.symm⟩, ?_⟩, xy.symm, bt'.symm⟩
    intro w ⟨hwx, hwb⟩
    rcases broken w hwx.symm hwb.symm with (⟨_, rfl⟩ | ⟨hxy, _⟩) | (⟨rfl, _⟩ | ⟨rfl, _⟩)
    · rfl
    · exact (xy.ne hxy).elim
    · exact (ne rfl).elim
    · exact (ab xy).elim
  · right
    refine ⟨b, (isCritNonEdge_mk_iff G a b).mpr ⟨ne, ab, t, ⟨xy, bt'.symm⟩, ?_⟩, xy, bt'.symm⟩
    intro w ⟨hwy, hwb⟩
    rcases broken w hwy.symm hwb.symm with (⟨hxy, _⟩ | ⟨_, rfl⟩) | (⟨rfl, _⟩ | ⟨rfl, _⟩)
    · exact (xy.ne hxy.symm).elim
    · rfl
    · exact (ab xy.symm).elim
    · exact (ne rfl).elim
  · left
    refine ⟨a, (isCritNonEdge_mk_iff G b a).mpr ⟨ne.symm, na, t, ⟨xy.symm, at'.symm⟩, ?_⟩, xy.symm, at'.symm⟩
    intro w ⟨hwx, hwa⟩
    rcases broken w hwa.symm hwx.symm with (⟨rfl, _⟩ | ⟨rfl, _⟩) | (⟨_, rfl⟩ | ⟨hxy, _⟩)
    · exact (ne rfl).elim
    · exact (na xy).elim
    · rfl
    · exact (xy.ne hxy).elim
  · right
    refine ⟨a, (isCritNonEdge_mk_iff G b a).mpr ⟨ne.symm, na, t, ⟨xy, at'.symm⟩, ?_⟩, xy, at'.symm⟩
    intro w ⟨hwy, hwa⟩
    rcases broken w hwa.symm hwy.symm with (⟨rfl, _⟩ | ⟨rfl, _⟩) | (⟨hxy, _⟩ | ⟨_, rfl⟩)
    · exact (na xy.symm).elim
    · exact (ne rfl).elim
    · exact (xy.ne hxy.symm).elim
    · rfl

/-- A matching is a finset of pairwise vertex-disjoint edges of `G`. -/
private def IsMatching (G : SimpleGraph V) (M : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧
    ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂

private lemma exists_maximal_matching (G : SimpleGraph V) :
    ∃ M : Finset (Sym2 V), IsMatching G M ∧
      ∀ e ∈ G.edgeSet, e ∉ M → ∃ e' ∈ M, ∃ v : V, v ∈ e ∧ v ∈ e' := by
  let S : Finset (Finset (Sym2 V)) := Finset.univ.filter (IsMatching G)
  have hS : S.Nonempty := ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [IsMatching]⟩⟩
  obtain ⟨M, hMS, hMmax⟩ := Finset.exists_max_image S Finset.card hS
  have hM : IsMatching G M := (Finset.mem_filter.mp hMS).2
  refine ⟨M, hM, fun e he heM => ?_⟩
  by_contra hdisj
  push Not at hdisj
  have hins : IsMatching G (insert e M) := by
    refine ⟨?_, ?_⟩
    · intro e' he'
      rcases Finset.mem_insert.mp he' with rfl | he'M
      · exact he
      · exact hM.1 e' he'M
    · intro e₁ he₁ e₂ he₂ hne v hv₁ hv₂
      rcases Finset.mem_insert.mp he₁ with rfl | he₁M <;>
      rcases Finset.mem_insert.mp he₂ with rfl | he₂M
      · exact hne rfl
      · exact hdisj e₂ he₂M v hv₁ hv₂
      · exact hdisj e₁ he₁M v hv₂ hv₁
      · exact hM.2 e₁ he₁M e₂ he₂M hne v hv₁ hv₂
  have hmem : insert e M ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hins⟩
  have hle := hMmax (insert e M) hmem
  rw [Finset.card_insert_of_notMem heM] at hle
  omega

private lemma matching_card_bound (G : SimpleGraph V) (M : Finset (Sym2 V)) (hM : IsMatching G M) :
    2 * M.card ≤ Fintype.card V := by
  let VM : Finset V := M.biUnion Sym2.toFinset
  have hdisj : (M : Set (Sym2 V)).PairwiseDisjoint Sym2.toFinset := by
    intro e₁ he₁ e₂ he₂ hne
    change Disjoint e₁.toFinset e₂.toFinset
    rw [Finset.disjoint_left]
    intro v hv₁ hv₂
    exact hM.2 e₁ he₁ e₂ he₂ hne v (Sym2.mem_toFinset.mp hv₁) (Sym2.mem_toFinset.mp hv₂)
  have hcard : VM.card = ∑ e ∈ M, e.toFinset.card := Finset.card_biUnion hdisj
  have h2 : ∀ e ∈ M, e.toFinset.card = 2 := by
    intro e he
    have hedge := hM.1 e he
    induction e using Sym2.ind with
    | _ a b =>
      have hab : a ≠ b := G.ne_of_adj hedge
      have : (s(a, b) : Sym2 V).toFinset = {a, b} := by ext x; simp
      rw [this, Finset.card_pair hab]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm] at hcard
  have hle : VM.card ≤ Fintype.card V := Finset.card_le_univ VM
  omega

/-- Vertices covered by a matching `M`. -/
private def coveredVerts (M : Finset (Sym2 V)) : Finset V :=
  Finset.univ.filter (fun v => ∃ e ∈ M, v ∈ e)

/-- The mate of `v` in a matching `M` (or `v` if uncovered). -/
private noncomputable def mate (M : Finset (Sym2 V)) (v : V) : V :=
  if h : ∃ w : V, s(v, w) ∈ M then h.choose else v

private lemma mem_coveredVerts_iff (M : Finset (Sym2 V)) (v : V) :
    v ∈ coveredVerts M ↔ ∃ w : V, s(v, w) ∈ M := by
  simp only [coveredVerts, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨e, heM, hve⟩
    induction e using Sym2.ind with
    | _ a b =>
      rcases Sym2.mem_iff.mp hve with rfl | rfl
      · exact ⟨b, heM⟩
      · exact ⟨a, by rwa [Sym2.eq_swap]⟩
  · rintro ⟨w, hw⟩
    exact ⟨s(v, w), hw, Sym2.mem_mk_left v w⟩

private lemma mate_mem_matching {M : Finset (Sym2 V)}
    {v : V} (hv : v ∈ coveredVerts M) : s(v, mate M v) ∈ M := by
  have hex : ∃ w : V, s(v, w) ∈ M := (mem_coveredVerts_iff M v).mp hv
  dsimp only [mate]
  rw [dif_pos hex]
  exact hex.choose_spec

private lemma mate_adj {G : SimpleGraph V} {M : Finset (Sym2 V)} (hM : IsMatching G M)
    {v : V} (hv : v ∈ coveredVerts M) : G.Adj v (mate M v) :=
  hM.1 _ (mate_mem_matching hv)

private lemma mate_ne {G : SimpleGraph V} {M : Finset (Sym2 V)} (hM : IsMatching G M)
    {v : V} (hv : v ∈ coveredVerts M) : mate M v ≠ v :=
  (mate_adj hM hv).ne.symm

private lemma mate_mem_covered {M : Finset (Sym2 V)}
    {v : V} (hv : v ∈ coveredVerts M) : mate M v ∈ coveredVerts M :=
  (mem_coveredVerts_iff M _).mpr ⟨v, by rw [Sym2.eq_swap]; exact mate_mem_matching hv⟩

private lemma mate_eq_of_mem {G : SimpleGraph V} {M : Finset (Sym2 V)} (hM : IsMatching G M)
    {v w : V} (h : s(v, w) ∈ M) : mate M v = w := by
  have hv : v ∈ coveredVerts M := (mem_coveredVerts_iff M v).mpr ⟨w, h⟩
  have h1 := mate_mem_matching hv
  by_cases heq : s(v, mate M v) = s(v, w)
  · rw [Sym2.eq_iff] at heq
    rcases heq with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact h2
    · exact (mate_ne hM hv h2).elim
  · exact (hM.2 _ h1 _ h heq v (Sym2.mem_mk_left _ _) (Sym2.mem_mk_left _ _)).elim

private lemma mate_mate {G : SimpleGraph V} {M : Finset (Sym2 V)} (hM : IsMatching G M)
    {v : V} (hv : v ∈ coveredVerts M) : mate M (mate M v) = v :=
  mate_eq_of_mem hM (by rw [Sym2.eq_swap]; exact mate_mem_matching hv)

private lemma mate_inj_on {G : SimpleGraph V} {M : Finset (Sym2 V)} (hM : IsMatching G M)
    {u v : V} (hu : u ∈ coveredVerts M) (hv : v ∈ coveredVerts M) (h : mate M u = mate M v) :
    u = v := by
  have := congrArg (mate M) h
  rwa [mate_mate hM hu, mate_mate hM hv] at this

/-- Every connected component of a finite graph on `k ≥ 1` vertices has at least `k - 1` edges
(counted as ordered adjacent pairs, at least `2 * (k - 1)`). -/
private lemma connected_sum_deg_ge {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (C : Finset W) (hC_ne : C.Nonempty)
    (hconn : ∀ u ∈ C, ∀ v ∈ C, H.Reachable u v)
    (hclosed : ∀ u ∈ C, ∀ v : W, H.Adj u v → v ∈ C) :
    2 * (C.card - 1) ≤ ∑ u ∈ C, (C.filter (fun v => H.Adj u v)).card := by
  have hgrow : ∀ m : ℕ, m ≤ C.card → 1 ≤ m →
      ∃ S : Finset W, S ⊆ C ∧ S.card = m ∧
        2 * (m - 1) ≤ ∑ u ∈ S, (S.filter (fun v => H.Adj u v)).card := by
    intro m
    induction m with
    | zero => intro _ h1; omega
    | succ m ih =>
      intro hle _
      cases m with
      | zero =>
        obtain ⟨v₀, hv₀⟩ := hC_ne
        refine ⟨{v₀}, Finset.singleton_subset_iff.mpr hv₀, Finset.card_singleton v₀, by simp⟩
      | succ k =>
        obtain ⟨S, hSC, hScard, hSedges⟩ := ih (by omega) (by omega)
        have hdiff_ne : (C \ S).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hem
          have hsub : C ⊆ S := Finset.sdiff_eq_empty_iff_subset.mp hem
          have := Finset.card_le_card hsub
          omega
        have hS_ne : S.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨u₀, hu₀S⟩ := hS_ne
        obtain ⟨w₀, hw₀CS⟩ := hdiff_ne
        obtain ⟨hw₀C, hw₀nS⟩ := Finset.mem_sdiff.mp hw₀CS
        obtain ⟨p⟩ := hconn u₀ (hSC hu₀S) w₀ hw₀C
        have hex_edge : ∃ x ∈ S, ∃ y ∈ C, y ∉ S ∧ H.Adj x y := by
          have hwalk : ∀ {a b : W} (q : H.Walk a b), a ∈ S → b ∉ S →
              ∃ x ∈ S, ∃ y, y ∉ S ∧ H.Adj x y := by
            intro a b q
            induction q with
            | nil => intro ha hna; exact (hna ha).elim
            | @cons a c b hac q' ihq =>
              intro ha hnb
              by_cases hc : c ∈ S
              · exact ihq hc hnb
              · exact ⟨a, ha, c, hc, hac⟩
          obtain ⟨x, hxS, y, hynS, hxy⟩ := hwalk p hu₀S hw₀nS
          exact ⟨x, hxS, y, hclosed x (hSC hxS) y hxy, hynS, hxy⟩
        obtain ⟨x, hxS, y, hyC, hynS, hxy⟩ := hex_edge
        let S' := insert y S
        refine ⟨S', Finset.insert_subset_iff.mpr ⟨hyC, hSC⟩,
          by rw [Finset.card_insert_of_notMem hynS, hScard], ?_⟩
        have hsum_split : ∑ u ∈ S', (S'.filter (fun v => H.Adj u v)).card =
            (S'.filter (fun v => H.Adj y v)).card +
            ∑ u ∈ S, (S'.filter (fun v => H.Adj u v)).card :=
          Finset.sum_insert hynS
        have hy_deg : 1 ≤ (S'.filter (fun v => H.Adj y v)).card :=
          Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hxS, hxy.symm⟩⟩
        have hx_inc : (S.filter (fun v => H.Adj x v)).card + 1 ≤
            (S'.filter (fun v => H.Adj x v)).card := by
          have hsub : insert y (S.filter (fun v => H.Adj x v)) ⊆ S'.filter (fun v => H.Adj x v) := by
            intro v hv
            rcases Finset.mem_insert.mp hv with hvy | hvS
            · rw [hvy]; exact Finset.mem_filter.mpr ⟨Finset.mem_insert_self y S, hxy⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem (Finset.mem_filter.mp hvS).1,
                (Finset.mem_filter.mp hvS).2⟩
          have hynf : y ∉ S.filter (fun v => H.Adj x v) := fun h => hynS (Finset.mem_filter.mp h).1
          have := Finset.card_le_card hsub
          rwa [Finset.card_insert_of_notMem hynf] at this
        have hother_le : ∀ u ∈ S, (S.filter (fun v => H.Adj u v)).card ≤
            (S'.filter (fun v => H.Adj u v)).card := fun u _ =>
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert y S))
        have hS_inc : (∑ u ∈ S, (S.filter (fun v => H.Adj u v)).card) + 1 ≤
            ∑ u ∈ S, (S'.filter (fun v => H.Adj u v)).card := by
          rw [← Finset.add_sum_erase _ _ hxS, ← Finset.add_sum_erase _ _ hxS]
          have hrest : ∑ u ∈ S.erase x, (S.filter (fun v => H.Adj u v)).card ≤
              ∑ u ∈ S.erase x, (S'.filter (fun v => H.Adj u v)).card :=
            Finset.sum_le_sum fun u hu => hother_le u (Finset.mem_of_mem_erase hu)
          omega
        omega
  obtain ⟨S, hSC, hScard, hSedges⟩ := hgrow C.card le_rfl (Finset.card_pos.mpr hC_ne)
  have hSeq : S = C := Finset.eq_of_subset_of_card_le hSC (by omega)
  rwa [hSeq] at hSedges

/- ### Auxiliary bipartite graph `I'` and its components -/

private noncomputable def edgeSetFin (G : SimpleGraph V) : Finset (Sym2 V) :=
  Finset.univ.filter (fun e => e ∈ G.edgeSet)

private noncomputable def nonEdgeFin (G : SimpleGraph V) : Finset (Sym2 V) :=
  Finset.univ.filter (fun f => ¬ f.IsDiag ∧ f ∉ G.edgeSet)

private noncomputable def remEdges (G : SimpleGraph V) (M : Finset (Sym2 V)) : Finset (Sym2 V) :=
  edgeSetFin G \ M

private noncomputable def critNonEdges (G : SimpleGraph V) : Finset (Sym2 V) :=
  (nonEdgeFin G).filter (IsCritNonEdge G)

private noncomputable def nonCritNonEdges (G : SimpleGraph V) : Finset (Sym2 V) :=
  (nonEdgeFin G).filter (fun f => ¬ IsCritNonEdge G f)

private abbrev AuxVert (G : SimpleGraph V) (M : Finset (Sym2 V)) :=
  {p : Sym2 V // p ∈ remEdges G M ∪ critNonEdges G}

/-- The auxiliary bipartite graph `I'` on `(E \ M) ∪ Fc`. -/
private noncomputable def auxGraph (G : SimpleGraph V) (M : Finset (Sym2 V)) :
    SimpleGraph (AuxVert G M) where
  Adj p q :=
    (p.1 ∈ remEdges G M ∧ q.1 ∈ critNonEdges G ∧ OnCrit2Path G p.1 q.1) ∨
    (q.1 ∈ remEdges G M ∧ p.1 ∈ critNonEdges G ∧ OnCrit2Path G q.1 p.1)
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun p hp => by
    rcases hp with ⟨_, _, he, hf, _⟩ | ⟨_, _, he, hf, _⟩
    · exact hf.2.1 he
    · exact hf.2.1 he⟩

private noncomputable def compVerts (G : SimpleGraph V) (M : Finset (Sym2 V))
    (c : (auxGraph G M).ConnectedComponent) : Finset (AuxVert G M) :=
  Finset.univ.filter (fun p => (auxGraph G M).connectedComponentMk p = c)

private noncomputable def compL (G : SimpleGraph V) (M : Finset (Sym2 V))
    (c : (auxGraph G M).ConnectedComponent) : Finset (AuxVert G M) :=
  (compVerts G M c).filter (fun p => p.1 ∈ remEdges G M)

private noncomputable def compR (G : SimpleGraph V) (M : Finset (Sym2 V))
    (c : (auxGraph G M).ConnectedComponent) : Finset (AuxVert G M) :=
  (compVerts G M c).filter (fun p => p.1 ∈ critNonEdges G)

private noncomputable def leftLopsided (G : SimpleGraph V) (M : Finset (Sym2 V)) :
    Finset (auxGraph G M).ConnectedComponent :=
  Finset.univ.filter (fun c => (compL G M c).card = (compR G M c).card + 1)

private def IsSwitchExit (G : SimpleGraph V) (M : Finset (Sym2 V))
    (c : (auxGraph G M).ConnectedComponent) (p : V × V) : Prop :=
  s(p.1, p.2) ∈ nonCritNonEdges G ∧ p.1 ∈ coveredVerts M ∧
    ∃ h : s(mate M p.1, p.2) ∈ remEdges G M ∪ critNonEdges G,
      (auxGraph G M).connectedComponentMk ⟨s(mate M p.1, p.2), h⟩ = c

private lemma aux_disj (G : SimpleGraph V) (M : Finset (Sym2 V)) (p : AuxVert G M) :
    ¬ (p.1 ∈ remEdges G M ∧ p.1 ∈ critNonEdges G) := by
  rintro ⟨h1, h2⟩
  have he : p.1 ∈ G.edgeSet := (Finset.mem_filter.mp (Finset.mem_sdiff.mp h1).1).2
  have hf : p.1 ∉ G.edgeSet := (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2.2
  exact hf he

private lemma aux_bipartite (G : SimpleGraph V) (M : Finset (Sym2 V)) {p q : AuxVert G M}
    (h : (auxGraph G M).Adj p q) :
    (p.1 ∈ remEdges G M ∧ q.1 ∈ critNonEdges G) ∨
    (p.1 ∈ critNonEdges G ∧ q.1 ∈ remEdges G M) := by
  rcases h with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h2, h1⟩

private lemma aux_deg_right_le (G : SimpleGraph V) (M : Finset (Sym2 V))
    (q : AuxVert G M) (hqFc : q.1 ∈ critNonEdges G) :
    (Finset.univ.filter (fun p => (auxGraph G M).Adj q p)).card ≤ 2 := by
  have hqCrit : IsCritNonEdge G q.1 := (Finset.mem_filter.mp hqFc).2
  obtain ⟨x, y, u, _, _, _, _, _, _, hon_iff⟩ := onCrit2Path_unique_two G hqCrit
  have hsub : (Finset.univ.filter (fun p => (auxGraph G M).Adj q p)).image Subtype.val ⊆
      {s(u, x), s(u, y)} := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    have hadj : (auxGraph G M).Adj q p := (Finset.mem_filter.mp hp).2
    rcases hadj with ⟨hqE', _, _⟩ | ⟨_, _, hon⟩
    · exact (aux_disj G M q ⟨hqE', hqFc⟩).elim
    · simpa using (hon_iff p.1).mp hon
  calc (Finset.univ.filter (fun p => (auxGraph G M).Adj q p)).card
      = ((Finset.univ.filter (fun p => (auxGraph G M).Adj q p)).image Subtype.val).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ ({s(u, x), s(u, y)} : Finset (Sym2 V)).card := Finset.card_le_card hsub
    _ ≤ 2 := Finset.card_le_two

private lemma comp_closed (G : SimpleGraph V) (M : Finset (Sym2 V))
    (c : (auxGraph G M).ConnectedComponent)
    {u : AuxVert G M} (hu : u ∈ compVerts G M c) {v : AuxVert G M}
    (huv : (auxGraph G M).Adj u v) : v ∈ compVerts G M c := by
  simp only [compVerts, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  rw [← hu]
  exact (ConnectedComponent.eq.mpr huv.reachable).symm

private lemma comp_part (G : SimpleGraph V) (M : Finset (Sym2 V))
    (c : (auxGraph G M).ConnectedComponent) :
    (compVerts G M c).card = (compL G M c).card + (compR G M c).card := by
  have hdisj : Disjoint (compL G M c) (compR G M c) := by
    rw [Finset.disjoint_left]; intro p h1 h2
    exact aux_disj G M p ⟨(Finset.mem_filter.mp h1).2, (Finset.mem_filter.mp h2).2⟩
  have hunion : compL G M c ∪ compR G M c = compVerts G M c := by
    ext p
    simp only [compL, compR, Finset.mem_union, Finset.mem_filter]
    have hp := Finset.mem_union.mp p.2
    tauto
  rw [← hunion, Finset.card_union_of_disjoint hdisj]

private lemma comp_sum_L_eq_R (G : SimpleGraph V) (M : Finset (Sym2 V))
    (c : (auxGraph G M).ConnectedComponent) :
    ∑ p ∈ compL G M c, (Finset.univ.filter (fun q => (auxGraph G M).Adj p q)).card =
      ∑ q ∈ compR G M c, (Finset.univ.filter (fun p => (auxGraph G M).Adj q p)).card := by
  have hL : ∀ p ∈ compL G M c, (Finset.univ.filter (fun q => (auxGraph G M).Adj p q)).card =
      ((compR G M c).filter (fun q => (auxGraph G M).Adj p q)).card := by
    intro p hp; congr 1; ext q
    simp only [compR, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hadj
      have hqV := comp_closed G M c (Finset.mem_filter.mp hp).1 hadj
      rcases aux_bipartite G M hadj with ⟨_, hqFc⟩ | ⟨hpFc, _⟩
      · exact ⟨⟨hqV, hqFc⟩, hadj⟩
      · exact (aux_disj G M p ⟨(Finset.mem_filter.mp hp).2, hpFc⟩).elim
    · exact fun h => h.2
  have hR : ∀ q ∈ compR G M c, (Finset.univ.filter (fun p => (auxGraph G M).Adj q p)).card =
      ((compL G M c).filter (fun p => (auxGraph G M).Adj q p)).card := by
    intro q hq; congr 1; ext p
    simp only [compL, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hadj
      have hpV := comp_closed G M c (Finset.mem_filter.mp hq).1 hadj
      rcases aux_bipartite G M hadj with ⟨hqE', _⟩ | ⟨_, hpE'⟩
      · exact (aux_disj G M q ⟨hqE', (Finset.mem_filter.mp hq).2⟩).elim
      · exact ⟨⟨hpV, hpE'⟩, hadj⟩
    · exact fun h => h.2
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR]
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
  simp [adj_comm]

private lemma comp_bipartite_deg (G : SimpleGraph V) (M : Finset (Sym2 V))
    (c : (auxGraph G M).ConnectedComponent) :
    ∑ u ∈ compVerts G M c, ((compVerts G M c).filter (fun v => (auxGraph G M).Adj u v)).card =
      2 * ∑ q ∈ compR G M c, (Finset.univ.filter (fun p => (auxGraph G M).Adj q p)).card := by
  have hdisj : Disjoint (compL G M c) (compR G M c) := by
    rw [Finset.disjoint_left]; intro p h1 h2
    exact aux_disj G M p ⟨(Finset.mem_filter.mp h1).2, (Finset.mem_filter.mp h2).2⟩
  have hunion : compL G M c ∪ compR G M c = compVerts G M c := by
    ext p; simp only [compL, compR, Finset.mem_union, Finset.mem_filter]
    have hp := Finset.mem_union.mp p.2; tauto
  have hdeg_eq : ∀ u ∈ compVerts G M c,
      ((compVerts G M c).filter (fun v => (auxGraph G M).Adj u v)).card =
        (Finset.univ.filter (fun v => (auxGraph G M).Adj u v)).card := by
    intro u hu; congr 1; ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨comp_closed G M c hu h, h⟩⟩
  rw [Finset.sum_congr rfl hdeg_eq, ← hunion, Finset.sum_union hdisj, comp_sum_L_eq_R]
  ring

/-- Lemma 2.2 (part 1): every component satisfies `|L(c)| ≤ |R(c)| + 1`. -/
private lemma comp_card_le (G : SimpleGraph V) (M : Finset (Sym2 V))
    (c : (auxGraph G M).ConnectedComponent) :
    (compL G M c).card ≤ (compR G M c).card + 1 := by
  have hne : (compVerts G M c).Nonempty := by
    obtain ⟨p, rfl⟩ := Quot.exists_rep c
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have hconn : ∀ u ∈ compVerts G M c, ∀ v ∈ compVerts G M c, (auxGraph G M).Reachable u v := by
    intro u hu v hv
    simp only [compVerts, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    exact ConnectedComponent.eq.mp (hu.trans hv.symm)
  have hge := connected_sum_deg_ge (auxGraph G M) (compVerts G M c) hne hconn
    (fun u hu v huv => comp_closed G M c hu huv)
  rw [comp_bipartite_deg, comp_part] at hge
  have hle : ∑ q ∈ compR G M c, (Finset.univ.filter (fun p => (auxGraph G M).Adj q p)).card ≤
      2 * (compR G M c).card := by
    calc ∑ q ∈ compR G M c, (Finset.univ.filter (fun p => (auxGraph G M).Adj q p)).card
        ≤ ∑ _q ∈ compR G M c, 2 :=
          Finset.sum_le_sum fun q hq => aux_deg_right_le G M q (Finset.mem_filter.mp hq).2
      _ = 2 * (compR G M c).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  omega

/-- Lemma 2.2 (part 2): in a left-lopsided component, every right vertex has degree 2,
and if `|L| ≥ 2` then `L` has at least two degree-1 leaves. -/
private lemma left_lop_props (G : SimpleGraph V) (M : Finset (Sym2 V))
    (c : (auxGraph G M).ConnectedComponent) (hcCl : c ∈ leftLopsided G M) :
    (∀ q ∈ compR G M c, (Finset.univ.filter (fun p => (auxGraph G M).Adj q p)).card = 2) ∧
    (2 ≤ (compL G M c).card →
      ∃ e₁ ∈ compL G M c, ∃ e₂ ∈ compL G M c, e₁ ≠ e₂ ∧
        (Finset.univ.filter (fun q => (auxGraph G M).Adj e₁ q)).card = 1 ∧
        (Finset.univ.filter (fun q => (auxGraph G M).Adj e₂ q)).card = 1) := by
  have heq : (compL G M c).card = (compR G M c).card + 1 := (Finset.mem_filter.mp hcCl).2
  have hne : (compVerts G M c).Nonempty := by
    obtain ⟨p, rfl⟩ := Quot.exists_rep c
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have hconn : ∀ u ∈ compVerts G M c, ∀ v ∈ compVerts G M c, (auxGraph G M).Reachable u v := by
    intro u hu v hv
    simp only [compVerts, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    exact ConnectedComponent.eq.mp (hu.trans hv.symm)
  have hge := connected_sum_deg_ge (auxGraph G M) (compVerts G M c) hne hconn
    (fun u hu v huv => comp_closed G M c hu huv)
  rw [comp_bipartite_deg, comp_part] at hge
  have hsum_R_ge : 2 * (compR G M c).card ≤
      ∑ q ∈ compR G M c, (Finset.univ.filter (fun p => (auxGraph G M).Adj q p)).card := by
    omega
  have hdeg2 : ∀ q ∈ compR G M c, (Finset.univ.filter (fun p => (auxGraph G M).Adj q p)).card = 2 := by
    intro q hq
    have hle_q := aux_deg_right_le G M q (Finset.mem_filter.mp hq).2
    by_contra hne2
    have hlt_q : (Finset.univ.filter (fun p => (auxGraph G M).Adj q p)).card < 2 := by omega
    have hsum_lt : ∑ r ∈ compR G M c, (Finset.univ.filter (fun p => (auxGraph G M).Adj r p)).card <
        2 * (compR G M c).card := by
      rw [← Finset.add_sum_erase _ _ hq]
      have hrest : ∑ r ∈ (compR G M c).erase q, (Finset.univ.filter (fun p => (auxGraph G M).Adj r p)).card ≤
          2 * ((compR G M c).card - 1) := by
        calc ∑ r ∈ (compR G M c).erase q, (Finset.univ.filter (fun p => (auxGraph G M).Adj r p)).card
            ≤ ∑ _r ∈ (compR G M c).erase q, 2 :=
              Finset.sum_le_sum fun r hr =>
                aux_deg_right_le G M r (Finset.mem_filter.mp (Finset.mem_of_mem_erase hr)).2
          _ = 2 * ((compR G M c).erase q).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
          _ = 2 * ((compR G M c).card - 1) := by rw [Finset.card_erase_of_mem hq]
      have hpos : 1 ≤ (compR G M c).card := Finset.card_pos.mpr ⟨q, hq⟩
      omega
    omega
  refine ⟨hdeg2, fun hL2 => ?_⟩
  have hsum_L : ∑ p ∈ compL G M c, (Finset.univ.filter (fun q => (auxGraph G M).Adj p q)).card =
      2 * (compR G M c).card := by
    rw [comp_sum_L_eq_R, Finset.sum_congr rfl hdeg2, Finset.sum_const, smul_eq_mul, mul_comm]
  have hdeg_pos : ∀ p ∈ compL G M c, 1 ≤ (Finset.univ.filter (fun q => (auxGraph G M).Adj p q)).card := by
    intro p hp
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (compL G M c).card)
    have hex : ∃ p' ∈ compL G M c, p' ≠ p := by
      by_cases hpa : a = p
      · exact ⟨b, hb, fun h => hab (hpa.trans h.symm)⟩
      · exact ⟨a, ha, hpa⟩
    obtain ⟨p', hp', hne⟩ := hex
    obtain ⟨walk⟩ := hconn p (Finset.mem_filter.mp hp).1 p' (Finset.mem_filter.mp hp').1
    cases walk with
    | nil => exact (hne rfl).elim
    | @cons _ q _ hpq _ =>
      exact Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpq⟩⟩
  let L1 := (compL G M c).filter (fun p => (Finset.univ.filter (fun q => (auxGraph G M).Adj p q)).card = 1)
  let L2 := (compL G M c).filter (fun p => (Finset.univ.filter (fun q => (auxGraph G M).Adj p q)).card ≠ 1)
  have hL1_ge2 : 2 ≤ L1.card := by
    have hdisj : Disjoint L1 L2 := by
      rw [Finset.disjoint_left]; intro p h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hunion : L1 ∪ L2 = compL G M c := by
      ext p; simp only [L1, L2, Finset.mem_union, Finset.mem_filter]; tauto
    have hcard_u : L1.card + L2.card = (compL G M c).card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have hsum_ge : L1.card + 2 * L2.card ≤
        ∑ p ∈ compL G M c, (Finset.univ.filter (fun q => (auxGraph G M).Adj p q)).card := by
      rw [← hunion, Finset.sum_union hdisj]
      have h1 : ∑ p ∈ L1, (Finset.univ.filter (fun q => (auxGraph G M).Adj p q)).card = L1.card := by
        rw [Finset.sum_congr rfl fun p hp => (Finset.mem_filter.mp hp).2, Finset.sum_const, smul_eq_mul, mul_one]
      have h2 : 2 * L2.card ≤ ∑ p ∈ L2, (Finset.univ.filter (fun q => (auxGraph G M).Adj p q)).card := by
        calc 2 * L2.card = ∑ _p ∈ L2, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
          _ ≤ ∑ p ∈ L2, (Finset.univ.filter (fun q => (auxGraph G M).Adj p q)).card := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hp1 := hdeg_pos p (Finset.mem_filter.mp hp).1
            have hpne := (Finset.mem_filter.mp hp).2
            omega
      omega
    omega
  obtain ⟨e₁, he₁, e₂, he₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < L1.card)
  exact ⟨e₁, (Finset.mem_filter.mp he₁).1, e₂, (Finset.mem_filter.mp he₂).1, hne,
    (Finset.mem_filter.mp he₁).2, (Finset.mem_filter.mp he₂).2⟩

/-- Lemma 2.5 (Das--Fox): a non-edge obtained by switching an edge of a left-lopsided component
across a matching edge is automatically noncritical. -/
private lemma auto_noncrit (G : SimpleGraph V) (M : Finset (Sym2 V)) (hM : IsMatching G M)
    (c : (auxGraph G M).ConnectedComponent) (hcCl : c ∈ leftLopsided G M)
    (x y : V) (hxy : x ≠ y) (hna : ¬ G.Adj x y) (hxM : x ∈ coveredVerts M)
    (hmem : s(mate M x, y) ∈ remEdges G M)
    (hcomp : (auxGraph G M).connectedComponentMk ⟨s(mate M x, y), Finset.mem_union_left _ hmem⟩ = c) :
    s(x, y) ∈ nonCritNonEdges G := by
  have hFmem : s(x, y) ∈ nonEdgeFin G :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hxy], hna⟩
  rw [nonCritNonEdges, Finset.mem_filter]
  refine ⟨hFmem, fun hcrit => ?_⟩
  have hFc_mem : s(x, y) ∈ critNonEdges G := Finset.mem_filter.mpr ⟨hFmem, hcrit⟩
  let q : AuxVert G M := ⟨s(x, y), Finset.mem_union_right _ hFc_mem⟩
  let p : AuxVert G M := ⟨s(mate M x, y), Finset.mem_union_left _ hmem⟩
  have hadj_mx_y : G.Adj (mate M x) y := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hmem).1).2
  have hadj_x_mx : G.Adj x (mate M x) := mate_adj hM hxM
  have hon : OnCrit2Path G p.1 q.1 :=
    ⟨hadj_mx_y, hcrit, x, y, mate M x, rfl, hadj_x_mx.symm, hadj_mx_y, Or.inr rfl⟩
  have hpq : (auxGraph G M).Adj p q := Or.inl ⟨hmem, hFc_mem, hon⟩
  have hq_comp : q ∈ compR G M c := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hFc_mem⟩
    rw [← hcomp]
    exact (ConnectedComponent.eq.mpr hpq.reachable).symm
  have hdeg2 := (left_lop_props G M c hcCl).1 q hq_comp
  obtain ⟨x', y', u', hqeq, _, _, hu'x', hu'y', huniq, hon_iff⟩ := onCrit2Path_unique_two G hcrit
  have hu'_eq : u' = mate M x := by
    rw [Sym2.eq_iff] at hqeq
    rcases hqeq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (huniq (mate M x) hadj_x_mx.symm hadj_mx_y).symm
    · exact (huniq (mate M x) hadj_mx_y hadj_x_mx.symm).symm
  have hnotE' : s(mate M x, x) ∉ remEdges G M := by
    intro hE'
    exact (Finset.mem_sdiff.mp hE').2 (by rw [Sym2.eq_swap]; exact mate_mem_matching hxM)
  have hsub : (Finset.univ.filter (fun r => (auxGraph G M).Adj q r)).image Subtype.val ⊆
      {s(mate M x, y)} := by
    intro e he
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp he
    have hrq : (auxGraph G M).Adj q r := (Finset.mem_filter.mp hr).2
    rcases hrq with ⟨hqE', _, _⟩ | ⟨hrE', _, honr⟩
    · exact (aux_disj G M q ⟨hqE', hFc_mem⟩).elim
    · have h2 := (hon_iff r.1).mp honr
      rw [hu'_eq] at h2
      rw [Sym2.eq_iff] at hqeq
      rcases hqeq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases h2 with h2 | h2
        · rw [h2] at hrE'; exact (hnotE' hrE').elim
        · simp [h2]
      · rcases h2 with h2 | h2
        · simp [h2]
        · rw [h2] at hrE'; exact (hnotE' hrE').elim
  have hle1 : (Finset.univ.filter (fun r => (auxGraph G M).Adj q r)).card ≤ 1 := by
    calc (Finset.univ.filter (fun r => (auxGraph G M).Adj q r)).card
        = ((Finset.univ.filter (fun r => (auxGraph G M).Adj q r)).image Subtype.val).card :=
          (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ ≤ ({s(mate M x, y)} : Finset (Sym2 V)).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton _
  omega

/-- Lemma 2.6 (Das--Fox): every single-vertex left-lopsided component has a safe switch exit
or two distinct ordered switch exits. -/
private lemma single_comp_exits (G : SimpleGraph V) (hG : Erdos742.IsDiameter2Critical G)
    (M : Finset (Sym2 V)) (hM : IsMatching G M)
    (hVM_max : ∀ x y : V, G.Adj x y → x ∈ coveredVerts M ∨ y ∈ coveredVerts M)
    (c : (auxGraph G M).ConnectedComponent) (hcCl : c ∈ leftLopsided G M)
    (h1 : (compL G M c).card = 1) :
    (∃ p : V × V, IsSwitchExit G M c p ∧ p.2 ∉ coveredVerts M) ∨
    (∃ p₁ p₂ : V × V, p₁ ≠ p₂ ∧ IsSwitchExit G M c p₁ ∧ IsSwitchExit G M c p₂) := by
  have hce : (compL G M c).card = (compR G M c).card + 1 := (Finset.mem_filter.mp hcCl).2
  have hR0 : (compR G M c).card = 0 := by omega
  obtain ⟨e, heL⟩ := Finset.card_eq_one.mp h1
  have he_mem : e ∈ compL G M c := by rw [heL]; exact Finset.mem_singleton_self e
  have heE' : e.1 ∈ remEdges G M := (Finset.mem_filter.mp he_mem).2
  have heComp : (auxGraph G M).connectedComponentMk e = c :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp he_mem).1).2
  have heAdj : e.1 ∈ G.edgeSet := (Finset.mem_filter.mp (Finset.mem_sdiff.mp heE').1).2
  have heNotM : e.1 ∉ M := (Finset.mem_sdiff.mp heE').2
  have he_no_nbr : ∀ q : AuxVert G M, ¬ (auxGraph G M).Adj e q := by
    intro q hq
    have hqV := comp_closed G M c (Finset.mem_filter.mp he_mem).1 hq
    rcases aux_bipartite G M hq with ⟨_, hqFc⟩ | ⟨heFc, _⟩
    · have hqR : q ∈ compR G M c := Finset.mem_filter.mpr ⟨hqV, hqFc⟩
      have := Finset.card_pos.mpr ⟨q, hqR⟩
      omega
    · exact aux_disj G M e ⟨heE', heFc⟩
  obtain ⟨x, y, hexy⟩ : ∃ x y : V, e.1 = s(x, y) := by
    rcases e with ⟨val, _⟩
    induction val using Sym2.ind with
    | _ x y => exact ⟨x, y, rfl⟩
  have hxy : G.Adj x y := by rw [hexy] at heAdj; exact heAdj
  have hmk_exit : ∀ a b : V, s(a, b) = e.1 → a ∈ coveredVerts M →
      IsSwitchExit G M c (mate M a, b) := by
    intro a b hab haM
    have hab_adj : G.Adj a b := by rw [← SimpleGraph.mem_edgeSet, hab]; exact heAdj
    have hma_ne_b : mate M a ≠ b := by
      intro heq
      have : s(a, b) ∈ M := heq ▸ mate_mem_matching haM
      rw [hab] at this; exact heNotM this
    have hma_not_adj_b : ¬ G.Adj (mate M a) b := by
      intro htri
      have hma_adj_a : G.Adj (mate M a) a := (mate_adj hM haM).symm
      rcases triangle_on_crit_2path G hG hma_adj_a htri hab_adj with
        ⟨z, hcrit, _, hyz⟩ | ⟨z, hcrit, _, hxz⟩
      · have hFmem : s(a, z) ∈ nonEdgeFin G :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcrit.1, hcrit.2.1⟩
        have hFcmem : s(a, z) ∈ critNonEdges G := Finset.mem_filter.mpr ⟨hFmem, hcrit⟩
        have hon : OnCrit2Path G e.1 s(a, z) :=
          ⟨heAdj, hcrit, a, z, b, rfl, hab_adj.symm, hyz, Or.inl (by rw [← hab, Sym2.eq_swap])⟩
        exact he_no_nbr ⟨s(a, z), Finset.mem_union_right _ hFcmem⟩ (Or.inl ⟨heE', hFcmem, hon⟩)
      · have hFmem : s(b, z) ∈ nonEdgeFin G :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcrit.1, hcrit.2.1⟩
        have hFcmem : s(b, z) ∈ critNonEdges G := Finset.mem_filter.mpr ⟨hFmem, hcrit⟩
        have hon : OnCrit2Path G e.1 s(b, z) :=
          ⟨heAdj, hcrit, b, z, a, rfl, hab_adj, hxz, Or.inl (by rw [← hab])⟩
        exact he_no_nbr ⟨s(b, z), Finset.mem_union_right _ hFcmem⟩ (Or.inl ⟨heE', hFcmem, hon⟩)
    have hmaM : mate M a ∈ coveredVerts M := mate_mem_covered haM
    have hmem_e : s(mate M (mate M a), b) ∈ remEdges G M := by
      rw [mate_mate hM haM, hab]; exact heE'
    have hcomp_e : (auxGraph G M).connectedComponentMk
        ⟨s(mate M (mate M a), b), Finset.mem_union_left _ hmem_e⟩ = c := by
      have : (⟨s(mate M (mate M a), b), Finset.mem_union_left _ hmem_e⟩ : AuxVert G M) = e := by
        apply Subtype.ext; simp [mate_mate hM haM, hab]
      rw [this]; exact heComp
    have hFnc_mem := auto_noncrit G M hM c hcCl (mate M a) b hma_ne_b hma_not_adj_b hmaM hmem_e hcomp_e
    exact ⟨hFnc_mem, hmaM, Finset.mem_union_left _ hmem_e, hcomp_e⟩
  rcases hVM_max x y hxy with hxM | hyM
  · by_cases hyM' : y ∈ coveredVerts M
    · right
      refine ⟨(mate M x, y), (mate M y, x), ?_,
        hmk_exit x y hexy.symm hxM, hmk_exit y x (by rw [Sym2.eq_swap]; exact hexy.symm) hyM'⟩
      intro h; exact hxy.ne (congrArg Prod.snd h).symm
    · exact Or.inl ⟨(mate M x, y), hmk_exit x y hexy.symm hxM, hyM'⟩
  · by_cases hxM' : x ∈ coveredVerts M
    · right
      refine ⟨(mate M x, y), (mate M y, x), ?_,
        hmk_exit x y hexy.symm hxM', hmk_exit y x (by rw [Sym2.eq_swap]; exact hexy.symm) hyM⟩
      intro h; exact hxy.ne (congrArg Prod.snd h).symm
    · exact Or.inl ⟨(mate M y, x), hmk_exit y x (by rw [Sym2.eq_swap]; exact hexy.symm) hyM, hxM'⟩

/-- Leaf classification for Lemma 2.7 (Das--Fox). -/
private lemma leaf_analysis (G : SimpleGraph V) (M : Finset (Sym2 V)) (hM : IsMatching G M)
    (hVM_max : ∀ x y : V, G.Adj x y → x ∈ coveredVerts M ∨ y ∈ coveredVerts M)
    (c : (auxGraph G M).ConnectedComponent) (hcCl : c ∈ leftLopsided G M)
    (e : AuxVert G M) (heL : e ∈ compL G M c)
    (hdege : (Finset.univ.filter (fun q => (auxGraph G M).Adj e q)).card = 1) :
    (∃ p : V × V, IsSwitchExit G M c p ∧ p.2 ∉ coveredVerts M) ∨
    (∃ p₁ p₂ : V × V, p₁ ≠ p₂ ∧ IsSwitchExit G M c p₁ ∧ IsSwitchExit G M c p₂) ∨
    (∃ p : V × V, IsSwitchExit G M c p ∧ s(mate M p.1, p.2) = e.1) ∨
    (∃ p : V × V, IsSwitchExit G M c p ∧ s(mate M p.1, p.2) ∈ critNonEdges G ∧
      ∃ u : V, (∀ w : V, G.Adj w (mate M p.1) → G.Adj w p.2 → w = u) ∧ e.1 = s(u, p.2)) := by
  have hdeg2 := (left_lop_props G M c hcCl).1
  have heE' : e.1 ∈ remEdges G M := (Finset.mem_filter.mp heL).2
  have heComp : (auxGraph G M).connectedComponentMk e = c :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp heL).1).2
  obtain ⟨q, hq_eq⟩ := Finset.card_eq_one.mp hdege
  have heq_adj : (auxGraph G M).Adj e q := by
    have : q ∈ Finset.univ.filter (fun r => (auxGraph G M).Adj e r) := by
      rw [hq_eq]; exact Finset.mem_singleton_self q
    exact (Finset.mem_filter.mp this).2
  have hqV : q ∈ compVerts G M c := comp_closed G M c (Finset.mem_filter.mp heL).1 heq_adj
  have hqFc : q.1 ∈ critNonEdges G := by
    rcases aux_bipartite G M heq_adj with ⟨_, hqFc⟩ | ⟨heFc, _⟩
    · exact hqFc
    · exact (aux_disj G M e ⟨heE', heFc⟩).elim
  have hqR : q ∈ compR G M c := Finset.mem_filter.mpr ⟨hqV, hqFc⟩
  have hqComp : (auxGraph G M).connectedComponentMk q = c := (Finset.mem_filter.mp hqV).2
  have hqCrit : IsCritNonEdge G q.1 := (Finset.mem_filter.mp hqFc).2
  obtain ⟨x₀, y₀, u, hq_mk, hx₀y₀, hna₀, hux₀, huy₀, huniq₀, hon_iff₀⟩ := onCrit2Path_unique_two G hqCrit
  have he_on : OnCrit2Path G e.1 q.1 := by
    rcases heq_adj with ⟨_, _, hon⟩ | ⟨hqE', _, _⟩
    · exact hon
    · exact (aux_disj G M q ⟨hqE', hqFc⟩).elim
  obtain ⟨x, y, hq_xy, hxy_ne, hxy_na, hux, huy, huniq, he_uy⟩ :
      ∃ x y : V, q.1 = s(x, y) ∧ x ≠ y ∧ ¬ G.Adj x y ∧ G.Adj u x ∧ G.Adj u y ∧
        (∀ w : V, G.Adj w x → G.Adj w y → w = u) ∧ e.1 = s(u, y) := by
    rcases (hon_iff₀ e.1).mp he_on with heux | heuy
    · exact ⟨y₀, x₀, by rw [hq_mk, Sym2.eq_swap], hx₀y₀.symm, fun h => hna₀ h.symm,
        huy₀, hux₀, fun w hwy hwx => huniq₀ w hwx hwy, heux⟩
    · exact ⟨x₀, y₀, hq_mk, hx₀y₀, hna₀, hux₀, huy₀, huniq₀, heuy⟩
  have hux_E' : s(u, x) ∈ remEdges G M := by
    by_contra hnotE'
    have hsub : (Finset.univ.filter (fun r => (auxGraph G M).Adj q r)).image Subtype.val ⊆ {e.1} := by
      intro rval hrval
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hrval
      have hqr : (auxGraph G M).Adj q r := (Finset.mem_filter.mp hr).2
      rcases hqr with ⟨hqE', _, _⟩ | ⟨hrE', _, honr⟩
      · exact (aux_disj G M q ⟨hqE', hqFc⟩).elim
      · have h2 := (hon_iff₀ r.1).mp honr
        rcases (hon_iff₀ e.1).mp he_on with heux | heuy
        · rcases h2 with h2 | h2
          · simp [heux, h2]
          · exfalso
            have hux_eq : s(u, y₀) = s(u, x) := by
              have h1 : s(x, y) = s(x₀, y₀) := by rw [← hq_xy, hq_mk]
              rw [Sym2.eq_iff] at h1
              rcases h1 with ⟨hx0, hy0⟩ | ⟨hx0, _⟩
              · have : s(u, x₀) = s(u, y₀) := by rw [← heux, he_uy, hy0]
                rw [Sym2.eq_iff] at this
                rcases this with ⟨_, h⟩ | ⟨h, _⟩
                · exact (hx₀y₀ h).elim
                · exact (huy₀.ne h).elim
              · rw [hx0]
            rw [h2, hux_eq] at hrE'
            exact hnotE' hrE'
        · rcases h2 with h2 | h2
          · exfalso
            have hux_eq : s(u, x₀) = s(u, x) := by
              have h1 : s(x, y) = s(x₀, y₀) := by rw [← hq_xy, hq_mk]
              rw [Sym2.eq_iff] at h1
              rcases h1 with ⟨hx0, _⟩ | ⟨hx0, hy0⟩
              · rw [hx0]
              · have : s(u, y₀) = s(u, x₀) := by rw [← heuy, he_uy, hy0]
                rw [Sym2.eq_iff] at this
                rcases this with ⟨_, h⟩ | ⟨h, _⟩
                · exact (hx₀y₀ h.symm).elim
                · exact (hux₀.ne h).elim
            rw [h2, hux_eq] at hrE'
            exact hnotE' hrE'
          · simp [heuy, h2]
    have hle1 : (Finset.univ.filter (fun r => (auxGraph G M).Adj q r)).card ≤ 1 := by
      calc (Finset.univ.filter (fun r => (auxGraph G M).Adj q r)).card
          = ((Finset.univ.filter (fun r => (auxGraph G M).Adj q r)).image Subtype.val).card :=
            (Finset.card_image_of_injective _ Subtype.val_injective).symm
        _ ≤ ({e.1} : Finset (Sym2 V)).card := Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton _
    have := hdeg2 q hqR
    omega
  have hux_notM : s(u, x) ∉ M := (Finset.mem_sdiff.mp hux_E').2
  have huy_notM : s(u, y) ∉ M := by rw [← he_uy]; exact (Finset.mem_sdiff.mp heE').2
  have hux_comp : (auxGraph G M).connectedComponentMk ⟨s(u, x), Finset.mem_union_left _ hux_E'⟩ = c := by
    have hon : OnCrit2Path G s(u, x) q.1 := ⟨hux, hqCrit, x, y, u, hq_xy, hux, huy, Or.inl rfl⟩
    have hadj : (auxGraph G M).Adj ⟨s(u, x), Finset.mem_union_left _ hux_E'⟩ q := Or.inl ⟨hux_E', hqFc, hon⟩
    rw [← hqComp]
    exact ConnectedComponent.eq.mpr hadj.reachable
  have case1 : u ∈ coveredVerts M →
      IsSwitchExit G M c (mate M u, x) ∨
      (IsSwitchExit G M c (mate M u, y) ∧ s(mate M (mate M u), y) = e.1) := by
    intro huM
    have hmu_ne_u : mate M u ≠ u := mate_ne hM huM
    have hnotboth : ¬ (G.Adj (mate M u) x ∧ G.Adj (mate M u) y) := fun ⟨h1, h2⟩ =>
      hmu_ne_u (huniq (mate M u) h1 h2)
    by_cases hmux : G.Adj (mate M u) x
    · right
      have hmuy : ¬ G.Adj (mate M u) y := fun h => hnotboth ⟨hmux, h⟩
      have hmu_ne_y : mate M u ≠ y := fun h => huy_notM (h ▸ mate_mem_matching huM)
      have hmuM : mate M u ∈ coveredVerts M := mate_mem_covered huM
      have hmem : s(mate M (mate M u), y) ∈ remEdges G M := by
        rw [mate_mate hM huM, ← he_uy]; exact heE'
      have hcmp : (auxGraph G M).connectedComponentMk
          ⟨s(mate M (mate M u), y), Finset.mem_union_left _ hmem⟩ = c := by
        have : (⟨s(mate M (mate M u), y), Finset.mem_union_left _ hmem⟩ : AuxVert G M) = e := by
          apply Subtype.ext; simp [mate_mate hM huM, he_uy]
        rw [this]; exact heComp
      have hFnc := auto_noncrit G M hM c hcCl (mate M u) y hmu_ne_y hmuy hmuM hmem hcmp
      exact ⟨⟨hFnc, hmuM, Finset.mem_union_left _ hmem, hcmp⟩, by rw [mate_mate hM huM, he_uy]⟩
    · left
      have hmu_ne_x : mate M u ≠ x := fun h => hux_notM (h ▸ mate_mem_matching huM)
      have hmuM : mate M u ∈ coveredVerts M := mate_mem_covered huM
      have hmem : s(mate M (mate M u), x) ∈ remEdges G M := by rw [mate_mate hM huM]; exact hux_E'
      have hcmp : (auxGraph G M).connectedComponentMk
          ⟨s(mate M (mate M u), x), Finset.mem_union_left _ hmem⟩ = c := by
        have : (⟨s(mate M (mate M u), x), Finset.mem_union_left _ hmem⟩ : AuxVert G M) =
            ⟨s(u, x), Finset.mem_union_left _ hux_E'⟩ := by
          apply Subtype.ext; simp [mate_mate hM huM]
        rw [this]; exact hux_comp
      have hFnc := auto_noncrit G M hM c hcCl (mate M u) x hmu_ne_x hmux hmuM hmem hcmp
      exact ⟨hFnc, hmuM, Finset.mem_union_left _ hmem, hcmp⟩
  have case2 : x ∈ coveredVerts M →
      IsSwitchExit G M c (mate M x, u) ∨
      (IsSwitchExit G M c (mate M x, y) ∧ s(mate M (mate M x), y) ∈ critNonEdges G ∧
        (∀ w : V, G.Adj w (mate M (mate M x)) → G.Adj w y → w = u) ∧ e.1 = s(u, y)) := by
    intro hxM
    have hmx_ne_x : mate M x ≠ x := mate_ne hM hxM
    have hmx_ne_u : mate M x ≠ u := fun h =>
      hux_notM (by rw [Sym2.eq_swap]; exact h ▸ mate_mem_matching hxM)
    have hmxM : mate M x ∈ coveredVerts M := mate_mem_covered hxM
    by_cases hmxu : G.Adj (mate M x) u
    · right
      have hmx_ne_y : mate M x ≠ y := fun h => hxy_na (h ▸ mate_adj hM hxM)
      have hmx_na_y : ¬ G.Adj (mate M x) y := fun h =>
        hmx_ne_u (huniq (mate M x) (mate_adj hM hxM).symm h)
      have hFmem : s(mate M x, y) ∈ nonEdgeFin G :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hmx_ne_y], hmx_na_y⟩
      have hnotcrit : ¬ IsCritNonEdge G s(mate M x, y) := by
        intro hcrit2
        have hFc2 : s(mate M x, y) ∈ critNonEdges G := Finset.mem_filter.mpr ⟨hFmem, hcrit2⟩
        let q2 : AuxVert G M := ⟨s(mate M x, y), Finset.mem_union_right _ hFc2⟩
        have hon2 : OnCrit2Path G e.1 q2.1 :=
          ⟨by rw [he_uy]; exact huy, hcrit2, mate M x, y, u, rfl, hmxu.symm, huy, Or.inr he_uy⟩
        have heq2 : (auxGraph G M).Adj e q2 := Or.inl ⟨heE', hFc2, hon2⟩
        have hq2_eq_q : q2 = q := by
          have hmem : q2 ∈ Finset.univ.filter (fun r => (auxGraph G M).Adj e r) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq2⟩
          rw [hq_eq, Finset.mem_singleton] at hmem
          exact hmem
        have hval : s(mate M x, y) = s(x, y) := by
          have := congrArg Subtype.val hq2_eq_q
          simpa [q2, hq_xy] using this
        rw [Sym2.eq_iff] at hval
        rcases hval with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact hmx_ne_x h1
        · exact hxy_ne h2.symm
      have hFnc2 : s(mate M x, y) ∈ nonCritNonEdges G := Finset.mem_filter.mpr ⟨hFmem, hnotcrit⟩
      have hq_mem : s(mate M (mate M x), y) ∈ critNonEdges G := by
        rw [mate_mate hM hxM, ← hq_xy]; exact hqFc
      have hq_cmp : (auxGraph G M).connectedComponentMk
          ⟨s(mate M (mate M x), y), Finset.mem_union_right _ hq_mem⟩ = c := by
        have : (⟨s(mate M (mate M x), y), Finset.mem_union_right _ hq_mem⟩ : AuxVert G M) = q := by
          apply Subtype.ext; simp [mate_mate hM hxM, hq_xy]
        rw [this]; exact hqComp
      refine ⟨⟨hFnc2, hmxM, Finset.mem_union_right _ hq_mem, hq_cmp⟩, hq_mem, ?_, he_uy⟩
      rw [mate_mate hM hxM]
      exact huniq
    · left
      have hmem : s(mate M (mate M x), u) ∈ remEdges G M := by
        rw [mate_mate hM hxM, Sym2.eq_swap]; exact hux_E'
      have hcmp : (auxGraph G M).connectedComponentMk
          ⟨s(mate M (mate M x), u), Finset.mem_union_left _ hmem⟩ = c := by
        have : (⟨s(mate M (mate M x), u), Finset.mem_union_left _ hmem⟩ : AuxVert G M) =
            ⟨s(u, x), Finset.mem_union_left _ hux_E'⟩ := by
          apply Subtype.ext; simp [mate_mate hM hxM, Sym2.eq_swap]
        rw [this]; exact hux_comp
      have hFnc := auto_noncrit G M hM c hcCl (mate M x) u hmx_ne_u hmxu hmxM hmem hcmp
      exact ⟨hFnc, hmxM, Finset.mem_union_left _ hmem, hcmp⟩
  rcases hVM_max u x hux with huM | hxM
  · rcases case1 huM with h1a | ⟨h1b, hrec⟩
    · by_cases hxM' : x ∈ coveredVerts M
      · rcases case2 hxM' with h2a | ⟨h2b, _⟩
        · right; left
          refine ⟨(mate M u, x), (mate M x, u), ?_, h1a, h2a⟩
          intro heq
          exact hux.ne (mate_inj_on hM huM hxM' (congrArg Prod.fst heq))
        · right; left
          refine ⟨(mate M u, x), (mate M x, y), ?_, h1a, h2b⟩
          intro heq
          exact hxy_ne (congrArg Prod.snd heq)
      · exact Or.inl ⟨(mate M u, x), h1a, hxM'⟩
    · exact Or.inr (Or.inr (Or.inl ⟨(mate M u, y), h1b, hrec⟩))
  · rcases case2 hxM with h2a | ⟨h2b, hfc2b, huniq2b, he2b⟩
    · by_cases huM' : u ∈ coveredVerts M
      · rcases case1 huM' with h1a | ⟨h1b, _⟩
        · right; left
          refine ⟨(mate M x, u), (mate M u, x), ?_, h2a, h1a⟩
          intro heq
          exact hux.ne.symm (mate_inj_on hM hxM huM' (congrArg Prod.fst heq))
        · right; left
          refine ⟨(mate M x, u), (mate M u, y), ?_, h2a, h1b⟩
          intro heq
          exact huy.ne (congrArg Prod.snd heq)
      · exact Or.inl ⟨(mate M x, u), h2a, huM'⟩
    · exact Or.inr (Or.inr (Or.inr ⟨(mate M x, y), h2b, hfc2b, u, huniq2b, he2b⟩))

/-- Lemma 2.7 (Das--Fox): every multi-vertex left-lopsided component has a safe switch exit
or two distinct ordered switch exits. -/
private lemma multi_comp_exits (G : SimpleGraph V) (M : Finset (Sym2 V)) (hM : IsMatching G M)
    (hVM_max : ∀ x y : V, G.Adj x y → x ∈ coveredVerts M ∨ y ∈ coveredVerts M)
    (c : (auxGraph G M).ConnectedComponent) (hcCl : c ∈ leftLopsided G M)
    (hL2 : 2 ≤ (compL G M c).card) :
    (∃ p : V × V, IsSwitchExit G M c p ∧ p.2 ∉ coveredVerts M) ∨
    (∃ p₁ p₂ : V × V, p₁ ≠ p₂ ∧ IsSwitchExit G M c p₁ ∧ IsSwitchExit G M c p₂) := by
  obtain ⟨e₁, he₁L, e₂, he₂L, he₁₂, hdeg_e₁, hdeg_e₂⟩ := (left_lop_props G M c hcCl).2 hL2
  rcases leaf_analysis G M hM hVM_max c hcCl e₁ he₁L hdeg_e₁ with
      hsafe | htwo | ⟨p₁, hp₁, hrec₁⟩ | ⟨p₁, hp₁, hfc₁, u₁, huniq₁, heq₁⟩
  · exact Or.inl hsafe
  · exact Or.inr htwo
  · rcases leaf_analysis G M hM hVM_max c hcCl e₂ he₂L hdeg_e₂ with
        hsafe | htwo | ⟨p₂, hp₂, hrec₂⟩ | ⟨p₂, hp₂, hfc₂, _, _, _⟩
    · exact Or.inl hsafe
    · exact Or.inr htwo
    · right
      refine ⟨p₁, p₂, ?_, hp₁, hp₂⟩
      intro h; subst h
      exact he₁₂ (Subtype.ext (hrec₁.symm.trans hrec₂))
    · right
      refine ⟨p₁, p₂, ?_, hp₁, hp₂⟩
      intro h; subst h
      have he₁E' : e₁.1 ∈ remEdges G M := (Finset.mem_filter.mp he₁L).2
      rw [← hrec₁] at he₁E'
      exact aux_disj G M ⟨s(mate M p₁.1, p₁.2), Finset.mem_union_left _ he₁E'⟩ ⟨he₁E', hfc₂⟩
  · rcases leaf_analysis G M hM hVM_max c hcCl e₂ he₂L hdeg_e₂ with
        hsafe | htwo | ⟨p₂, hp₂, hrec₂⟩ | ⟨p₂, hp₂, _, u₂, huniq₂, heq₂⟩
    · exact Or.inl hsafe
    · exact Or.inr htwo
    · right
      refine ⟨p₁, p₂, ?_, hp₁, hp₂⟩
      intro h; subst h
      have he₂E' : e₂.1 ∈ remEdges G M := (Finset.mem_filter.mp he₂L).2
      rw [← hrec₂] at he₂E'
      exact aux_disj G M ⟨s(mate M p₁.1, p₁.2), Finset.mem_union_left _ he₂E'⟩ ⟨he₂E', hfc₁⟩
    · right
      refine ⟨p₁, p₂, ?_, hp₁, hp₂⟩
      intro h; subst h
      have hu_eq : u₁ = u₂ := by
        have hcrit := (Finset.mem_filter.mp hfc₁).2
        obtain ⟨x', y', u', hmk', _, _, hu'x', hu'y', _, _⟩ := onCrit2Path_unique_two G hcrit
        rw [Sym2.eq_iff] at hmk'
        rcases hmk' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact (huniq₁ u' hu'x' hu'y').symm.trans (huniq₂ u' hu'x' hu'y')
        · exact (huniq₁ u' hu'y' hu'x').symm.trans (huniq₂ u' hu'y' hu'x')
      exact he₁₂ (Subtype.ext (by rw [heq₁, heq₂, hu_eq]))

/-- Lemma 1.1 (Das--Fox): for every diameter-2-critical graph `G` and maximal matching `M`,
`|E(G) \ M| ≤ |E^c(G)|`. -/
private lemma bound_of_maximal_matching (G : SimpleGraph V)
    (hG : Erdos742.IsDiameter2Critical G)
    (M : Finset (Sym2 V)) (hM : IsMatching G M)
    (hMmax : ∀ e ∈ G.edgeSet, e ∉ M → ∃ e' ∈ M, ∃ v : V, v ∈ e ∧ v ∈ e') :
    (remEdges G M).card ≤ (nonEdgeFin G).card := by
  have hF_split : (nonEdgeFin G).card = (critNonEdges G).card + (nonCritNonEdges G).card := by
    have hdisj : Disjoint (critNonEdges G) (nonCritNonEdges G) := by
      rw [Finset.disjoint_left]; intro f h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hunion : critNonEdges G ∪ nonCritNonEdges G = nonEdgeFin G := by
      ext f; simp only [critNonEdges, nonCritNonEdges, Finset.mem_union, Finset.mem_filter]; tauto
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have hVM_max : ∀ x y : V, G.Adj x y → x ∈ coveredVerts M ∨ y ∈ coveredVerts M := by
    intro x y hxy
    by_cases hm : s(x, y) ∈ M
    · exact Or.inl ((mem_coveredVerts_iff M x).mpr ⟨y, hm⟩)
    · obtain ⟨e', he'M, v, hvxy, hve'⟩ := hMmax s(x, y) hxy hm
      rcases Sym2.mem_iff.mp hvxy with rfl | rfl
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, e', he'M, hve'⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, e', he'M, hve'⟩)
  -- Lemma 2.3: |remEdges| ≤ |critNonEdges| + |leftLopsided|
  have hE'_le : (remEdges G M).card ≤ (critNonEdges G).card + (leftLopsided G M).card := by
    have hE'_sum : (remEdges G M).card = ∑ c, (compL G M c).card := by
      have hbij : (remEdges G M).card =
          (Finset.univ.filter (fun p : AuxVert G M => p.1 ∈ remEdges G M)).card := by
        have himg : (Finset.univ.filter (fun p : AuxVert G M => p.1 ∈ remEdges G M)).image Subtype.val =
            remEdges G M := by
          ext e; simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun ⟨p, hp, hpe⟩ => hpe ▸ hp, fun he => ⟨⟨e, Finset.mem_union_left _ he⟩, he, rfl⟩⟩
        calc (remEdges G M).card
            = ((Finset.univ.filter (fun p : AuxVert G M => p.1 ∈ remEdges G M)).image Subtype.val).card :=
              congrArg Finset.card himg.symm
          _ = (Finset.univ.filter (fun p : AuxVert G M => p.1 ∈ remEdges G M)).card :=
              Finset.card_image_of_injective _ Subtype.val_injective
      rw [hbij]
      rw [Finset.card_eq_sum_card_fiberwise
        (s := Finset.univ.filter (fun p : AuxVert G M => p.1 ∈ remEdges G M))
        (t := (Finset.univ : Finset (auxGraph G M).ConnectedComponent))
        (f := (auxGraph G M).connectedComponentMk) (fun _ _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl fun c _ => ?_
      congr 1; ext p; simp [compL, compVerts, and_comm]
    have hFc_sum : (critNonEdges G).card = ∑ c, (compR G M c).card := by
      have hbij : (critNonEdges G).card =
          (Finset.univ.filter (fun p : AuxVert G M => p.1 ∈ critNonEdges G)).card := by
        have himg : (Finset.univ.filter (fun p : AuxVert G M => p.1 ∈ critNonEdges G)).image Subtype.val =
            critNonEdges G := by
          ext f; simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun ⟨p, hp, hpf⟩ => hpf ▸ hp, fun hf => ⟨⟨f, Finset.mem_union_right _ hf⟩, hf, rfl⟩⟩
        calc (critNonEdges G).card
            = ((Finset.univ.filter (fun p : AuxVert G M => p.1 ∈ critNonEdges G)).image Subtype.val).card :=
              congrArg Finset.card himg.symm
          _ = (Finset.univ.filter (fun p : AuxVert G M => p.1 ∈ critNonEdges G)).card :=
              Finset.card_image_of_injective _ Subtype.val_injective
      rw [hbij]
      rw [Finset.card_eq_sum_card_fiberwise
        (s := Finset.univ.filter (fun p : AuxVert G M => p.1 ∈ critNonEdges G))
        (t := (Finset.univ : Finset (auxGraph G M).ConnectedComponent))
        (f := (auxGraph G M).connectedComponentMk) (fun _ _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl fun c _ => ?_
      congr 1; ext p; simp [compR, compVerts, and_comm]
    rw [hE'_sum, hFc_sum]
    have hstep : ∀ c : (auxGraph G M).ConnectedComponent,
        (compL G M c).card ≤ (compR G M c).card + (if c ∈ leftLopsided G M then 1 else 0) := by
      intro c
      have hle := comp_card_le G M c
      by_cases hc : c ∈ leftLopsided G M
      · rw [if_pos hc]; omega
      · rw [if_neg hc]
        have hne : (compL G M c).card ≠ (compR G M c).card + 1 :=
          fun h => hc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        omega
    calc ∑ c, (compL G M c).card
        ≤ ∑ c, ((compR G M c).card + if c ∈ leftLopsided G M then 1 else 0) :=
          Finset.sum_le_sum fun c _ => hstep c
      _ = (∑ c, (compR G M c).card) + ∑ c, (if c ∈ leftLopsided G M then 1 else 0) :=
          Finset.sum_add_distrib
      _ = (∑ c, (compR G M c).card) + (leftLopsided G M).card := by simp
  -- Double counting weights on leftLopsided × FncPairs
  let FncPairs : Finset (V × V) := Finset.univ.filter (fun p : V × V => s(p.1, p.2) ∈ nonCritNonEdges G)
  let wt (c : (auxGraph G M).ConnectedComponent) (p : V × V) : ℕ :=
    if IsSwitchExit G M c p then (if p.2 ∉ coveredVerts M then 2 else 1) else 0
  have hwt_lower : 2 * (leftLopsided G M).card ≤ ∑ c ∈ leftLopsided G M, ∑ p ∈ FncPairs, wt c p := by
    calc 2 * (leftLopsided G M).card = ∑ _c ∈ leftLopsided G M, 2 := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ c ∈ leftLopsided G M, ∑ p ∈ FncPairs, wt c p := by
        refine Finset.sum_le_sum fun c hc => ?_
        have hce : (compL G M c).card = (compR G M c).card + 1 := (Finset.mem_filter.mp hc).2
        have hex : (∃ p : V × V, IsSwitchExit G M c p ∧ p.2 ∉ coveredVerts M) ∨
            (∃ p₁ p₂ : V × V, p₁ ≠ p₂ ∧ IsSwitchExit G M c p₁ ∧ IsSwitchExit G M c p₂) := by
          by_cases h1 : (compL G M c).card = 1
          · exact single_comp_exits G hG M hM hVM_max c hc h1
          · exact multi_comp_exits G M hM hVM_max c hc (by omega)
        rcases hex with ⟨p, hp, hsafe⟩ | ⟨p₁, p₂, hne, hp₁, hp₂⟩
        · have hp_mem : p ∈ FncPairs := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.1⟩
          calc 2 = wt c p := by simp [wt, hp, hsafe]
            _ ≤ ∑ q ∈ FncPairs, wt c q :=
              Finset.single_le_sum (fun _ _ => Nat.zero_le _) hp_mem
        · have hp₁_mem : p₁ ∈ FncPairs := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp₁.1⟩
          have hp₂_mem : p₂ ∈ FncPairs := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp₂.1⟩
          have hsub : ({p₁, p₂} : Finset (V × V)) ⊆ FncPairs := by
            intro q hq; simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl <;> assumption
          have hge1 : ∀ p, IsSwitchExit G M c p → 1 ≤ wt c p := fun p hp => by
            dsimp only [wt]; rw [if_pos hp]; split_ifs <;> omega
          calc 2 ≤ wt c p₁ + wt c p₂ := by have := hge1 p₁ hp₁; have := hge1 p₂ hp₂; omega
            _ = ∑ q ∈ ({p₁, p₂} : Finset (V × V)), wt c q := (Finset.sum_pair hne).symm
            _ ≤ ∑ q ∈ FncPairs, wt c q := Finset.sum_le_sum_of_subset hsub
  have hwt_col : ∀ p ∈ FncPairs,
      ∑ c ∈ leftLopsided G M, wt c p ≤
        if p.1 ∈ coveredVerts M then (if p.2 ∉ coveredVerts M then 2 else 1) else 0 := by
    intro p _
    by_cases hex : ∃ c ∈ leftLopsided G M, IsSwitchExit G M c p
    · obtain ⟨c₀, hc₀, hp₀⟩ := hex
      have huniq_c : ∀ c ∈ leftLopsided G M, IsSwitchExit G M c p → c = c₀ := by
        intro c _ hpc
        obtain ⟨_, _, _, heq1⟩ := hpc
        obtain ⟨_, _, _, heq2⟩ := hp₀
        rw [← heq1, ← heq2]
      have hsum_single : ∑ c ∈ leftLopsided G M, wt c p = wt c₀ p := by
        rw [Finset.sum_eq_single c₀]
        · intro c hc hne
          dsimp only [wt]
          rw [if_neg (fun h => hne (huniq_c c hc h))]
        · intro h; exact (h hc₀).elim
      rw [hsum_single]
      dsimp only [wt]
      rw [if_pos hp₀, if_pos hp₀.2.1]
    · push Not at hex
      have h0 : ∑ c ∈ leftLopsided G M, wt c p = 0 := Finset.sum_eq_zero fun c hc => by
        dsimp only [wt]; rw [if_neg (hex c hc)]
      rw [h0]
      exact Nat.zero_le _
  have hwt_upper : ∑ p ∈ FncPairs,
      (if p.1 ∈ coveredVerts M then (if p.2 ∉ coveredVerts M then 2 else 1) else 0) ≤
        2 * (nonCritNonEdges G).card := by
    have hfiber := Finset.sum_fiberwise_of_maps_to (s := FncPairs) (t := nonCritNonEdges G)
      (g := fun p : V × V => s(p.1, p.2))
      (f := fun p : V × V => if p.1 ∈ coveredVerts M then (if p.2 ∉ coveredVerts M then 2 else 1) else 0)
      (fun p hp => (Finset.mem_filter.mp hp).2)
    rw [← hfiber]
    calc ∑ f ∈ nonCritNonEdges G, ∑ p ∈ FncPairs.filter (fun p => s(p.1, p.2) = f),
            (if p.1 ∈ coveredVerts M then (if p.2 ∉ coveredVerts M then 2 else 1) else 0)
        ≤ ∑ _f ∈ nonCritNonEdges G, 2 := by
          refine Finset.sum_le_sum fun f hf => ?_
          have hf_nd : ¬ f.IsDiag := (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2.1
          induction f using Sym2.ind with
          | _ x y =>
            have hxy : x ≠ y := by simpa [Sym2.mk_isDiag_iff] using hf_nd
            have hfib_eq : FncPairs.filter (fun p => s(p.1, p.2) = s(x, y)) = {(x, y), (y, x)} := by
              ext ⟨a, b⟩
              simp only [FncPairs, Finset.mem_filter, Finset.mem_univ, true_and,
                Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Sym2.eq_iff]
              constructor
              · exact fun h => h.2
              · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
                · exact ⟨hf, Or.inl ⟨rfl, rfl⟩⟩
                · exact ⟨by rwa [Sym2.eq_swap], Or.inr ⟨rfl, rfl⟩⟩
            have hne_pair : (x, y) ≠ (y, x) := fun h => hxy (congrArg Prod.fst h)
            rw [hfib_eq, Finset.sum_pair hne_pair]
            by_cases hx : x ∈ coveredVerts M <;> by_cases hy : y ∈ coveredVerts M <;>
              simp [hx, hy]
      _ = 2 * (nonCritNonEdges G).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hCl_le_Fnc : (leftLopsided G M).card ≤ (nonCritNonEdges G).card := by
    have hsw : ∑ c ∈ leftLopsided G M, ∑ p ∈ FncPairs, wt c p =
        ∑ p ∈ FncPairs, ∑ c ∈ leftLopsided G M, wt c p := Finset.sum_comm
    have htot := le_trans (le_trans hwt_lower (hsw ▸ Finset.sum_le_sum hwt_col)) hwt_upper
    omega
  omega

/-- Main theorem (Das--Fox, arXiv:2610.39032): every diameter-2-critical graph on `n` vertices
has at most `⌊n^2 / 4⌋` edges. -/
private theorem murty_simon_aux (G : SimpleGraph V)
    (hG : Erdos742.IsDiameter2Critical G) :
    (edgeSetFin G).card ≤ (Fintype.card V) ^ 2 / 4 := by
  obtain ⟨M, hM, hMmax⟩ := exists_maximal_matching G
  have hbound := bound_of_maximal_matching G hG M hM hMmax
  have hM_sub : M ⊆ edgeSetFin G := fun e he => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hM.1 e he⟩
  have hE_sdiff : (remEdges G M).card = (edgeSetFin G).card - M.card := by
    rw [remEdges, Finset.card_sdiff, Finset.inter_eq_left.mpr hM_sub]
  have hM_le_E : M.card ≤ (edgeSetFin G).card := Finset.card_le_card hM_sub
  have hEF_card : (edgeSetFin G).card + (nonEdgeFin G).card =
      Fintype.card V * (Fintype.card V - 1) / 2 := by
    have hdisj : Disjoint (edgeSetFin G) (nonEdgeFin G) := by
      rw [Finset.disjoint_left]; intro e h1 h2
      exact (Finset.mem_filter.mp h2).2.2 (Finset.mem_filter.mp h1).2
    have hunion : edgeSetFin G ∪ nonEdgeFin G = Finset.univ.filter (fun f : Sym2 V => ¬ f.IsDiag) := by
      ext f
      simp only [edgeSetFin, nonEdgeFin, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (he | ⟨hnd, _⟩)
        · exact G.not_isDiag_of_mem_edgeSet he
        · exact hnd
      · intro hnd
        by_cases he : f ∈ G.edgeSet
        · exact Or.inl he
        · exact Or.inr ⟨hnd, he⟩
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have hdiag_card : (Finset.univ.filter (fun f : Sym2 V => f.IsDiag)).card = Fintype.card V := by
      have himg : Finset.univ.filter (fun f : Sym2 V => f.IsDiag) =
          Finset.univ.image (fun v : V => s(v, v)) := by
        ext f
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        induction f using Sym2.ind with
        | _ a b =>
          simp only [Sym2.mk_isDiag_iff, Sym2.eq_iff]
          constructor
          · rintro rfl; exact ⟨a, Or.inl ⟨rfl, rfl⟩⟩
          · rintro ⟨v, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;> rfl
      rw [himg, Finset.card_image_of_injective]
      · simp
      · intro a b hab
        rw [Sym2.eq_iff] at hab
        rcases hab with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h
    have hpart : (Finset.univ.filter (fun f : Sym2 V => f.IsDiag)).card +
        (Finset.univ.filter (fun f : Sym2 V => ¬ f.IsDiag)).card = Fintype.card (Sym2 V) := by
      rw [← Finset.card_union_of_disjoint]
      · rw [show Finset.univ.filter (fun f : Sym2 V => f.IsDiag) ∪
              Finset.univ.filter (fun f : Sym2 V => ¬ f.IsDiag) = Finset.univ by
            ext f; simp [em], Finset.card_univ]
      · rw [Finset.disjoint_left]; intro f h1 h2
        exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    rw [hdiag_card, Sym2.card] at hpart
    have hchoose : (Fintype.card V + 1).choose 2 =
        Fintype.card V + Fintype.card V * (Fintype.card V - 1) / 2 := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.choose_two_right, add_comm]
    omega
  have hM_bound : 2 * M.card ≤ Fintype.card V := matching_card_bound G M hM
  have harith : Fintype.card V * (Fintype.card V - 1) / 2 + Fintype.card V / 2 =
      2 * ((Fintype.card V) ^ 2 / 4) := by
    rcases Nat.even_or_odd' (Fintype.card V) with ⟨k, hk | hk⟩
    · rw [hk]
      cases k with
      | zero => simp
      | succ k' =>
        have h1 : 2 * (k' + 1) * (2 * (k' + 1) - 1) / 2 = (k' + 1) * (2 * k' + 1) := by
          have hsub : 2 * (k' + 1) - 1 = 2 * k' + 1 := by omega
          rw [hsub, mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
        have h2 : (2 * (k' + 1)) ^ 2 / 4 = (k' + 1) ^ 2 := by
          have hsq : (2 * (k' + 1)) ^ 2 = 4 * (k' + 1) ^ 2 := by ring
          rw [hsq, Nat.mul_div_cancel_left _ (by norm_num)]
        have h3 : 2 * (k' + 1) / 2 = k' + 1 := Nat.mul_div_cancel_left _ (by norm_num)
        rw [h1, h2, h3]; ring
    · rw [hk]
      have h1 : (2 * k + 1) * (2 * k + 1 - 1) / 2 = (2 * k + 1) * k := by
        have hsub : 2 * k + 1 - 1 = 2 * k := by omega
        have hmul : (2 * k + 1) * (2 * k) = 2 * ((2 * k + 1) * k) := by ring
        rw [hsub, hmul, Nat.mul_div_cancel_left _ (by norm_num)]
      have h2 : (2 * k + 1) ^ 2 / 4 = k ^ 2 + k := by
        have hsq : (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 := by ring
        rw [hsq]; omega
      have h3 : (2 * k + 1) / 2 = k := by omega
      rw [h1, h2, h3]; ring
  omega

omit [DecidableEq V] in
private lemma mem_edgeSetFin (G : SimpleGraph V) (e : Sym2 V) :
    e ∈ edgeSetFin G ↔ e ∈ G.edgeSet := by
  simp [edgeSetFin]

private theorem murty_simon (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : Erdos742.IsDiameter2Critical G) :
    G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4 := by
  have hE_eq : G.edgeFinset.card = (edgeSetFin G).card := by
    apply Finset.card_bij (fun e _ => e)
    · intro e he; exact (mem_edgeSetFin G e).mpr (G.mem_edgeFinset.mp he)
    · intro _ _ _ _ h; exact h
    · intro e he; exact ⟨e, G.mem_edgeFinset.mpr ((mem_edgeSetFin G e).mp he), rfl⟩
  rw [hE_eq]
  exact murty_simon_aux G hG

end OMA.MurtySimon

theorem OMA.solution : type_of% @Erdos742.erdos_742 :=
  fun _ _ _ G _ hG => OMA.MurtySimon.murty_simon G hG
