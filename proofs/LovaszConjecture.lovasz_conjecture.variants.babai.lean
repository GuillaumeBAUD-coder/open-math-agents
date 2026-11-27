import FormalConjectures.Wikipedia.LovaszConjecture

/-!
# Proof of Babai (1979): long cycles in vertex-transitive graphs

Every finite connected vertex-transitive graph on $n \ge 3$ vertices contains a cycle of length
at least $\sqrt{3n}$.

The proof proceeds in four self-contained parts:
1. Degree regularity ($d \ge 2$) and the $2$-regular case (a Hamiltonian cycle of length $n$).
2. Watkins's connectivity bound: a connected vertex-transitive graph of degree $d \ge 3$ is
   $3$-connected (proved via atomic parts).
3. Menger's theorem for $k = 2$ (proved by Göring's edge-deletion induction).
4. Any two longest cycles in a $3$-connected graph share at least $3$ vertices, yielding
   $k^2 \ge 3n$ by double counting over $\mathrm{Aut}(G)$.
-/

-- Problem: Babai (1979): long cycles in vertex-transitive graphs.
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/LovaszConjecture.lean:74 (declaration LovaszConjecture.lovasz_conjecture.variants.babai)
-- Credit: @liuweid95-hash (the owner of the agent is credited as the solver)

namespace OMABabai

open SimpleGraph LovaszConjecture Finset

/- ### Section 1: Vertex-transitivity basics, existence of a cycle, and the 2-regular case -/

section Basic

variable {V : Type*} [Fintype V]

lemma degree_eq_of_iso [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (φ : G ≃g G) (u : V) : G.degree (φ u) = G.degree u := by
  have h : G.neighborFinset (φ u) = (G.neighborFinset u).map φ.toEquiv.toEmbedding := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, mem_map, Equiv.coe_toEmbedding]
    constructor
    · intro hadj
      refine ⟨φ.symm w, ?_, φ.apply_symm_apply w⟩
      exact φ.map_rel_iff.mp (by simpa using hadj : G.Adj (φ u) (φ (φ.symm w)))
    · rintro ⟨x, hx, rfl⟩
      exact φ.map_rel_iff.mpr hx
  rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree, h, card_map]

lemma degree_eq_of_isVertexTransitive [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (htrans : IsVertexTransitive G) (u v : V) : G.degree u = G.degree v := by
  obtain ⟨φ, rfl⟩ := htrans u v
  exact (degree_eq_of_iso G φ u).symm

lemma one_le_degree_of_connected (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hcard : 2 ≤ Fintype.card V) (u : V) : 1 ≤ G.degree u := by
  have hne : ∃ v, v ≠ u := by
    by_contra h
    push Not at h
    have : Fintype.card V ≤ 1 := Fintype.card_le_one_iff.mpr fun a b => by rw [h a, h b]
    omega
  obtain ⟨v, hvu⟩ := hne
  obtain ⟨p⟩ := hconn u v
  cases p with
  | nil => exact absurd rfl hvu
  | cons hadj _ =>
    rw [← card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨_, (G.mem_neighborFinset u _).mpr hadj⟩

lemma two_le_degree_of_connected_vt [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (htrans : IsVertexTransitive G)
    (hcard : 3 ≤ Fintype.card V) (u : V) : 2 ≤ G.degree u := by
  have h1 := one_le_degree_of_connected G hconn (by omega) u
  by_contra hlt
  have hdu : G.degree u = 1 := by omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp
    (by rw [card_neighborFinset_eq_degree]; omega : 0 < (G.neighborFinset u).card)
  have huv : G.Adj u v := (G.mem_neighborFinset u v).mp hv
  have hdv : G.degree v = 1 := (degree_eq_of_isVertexTransitive G htrans u v).symm.trans hdu
  have hnu : G.neighborFinset u = {v} := by
    have hcard1 : (G.neighborFinset u).card = 1 := by rw [card_neighborFinset_eq_degree]; exact hdu
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard1
    rw [ha, Finset.mem_singleton] at hv
    rw [ha, hv]
  have hnv : G.neighborFinset v = {u} := by
    have hu_mem : u ∈ G.neighborFinset v := (G.mem_neighborFinset v u).mpr huv.symm
    have hcard1 : (G.neighborFinset v).card = 1 := by rw [card_neighborFinset_eq_degree]; exact hdv
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard1
    rw [ha, Finset.mem_singleton] at hu_mem
    rw [ha, hu_mem]
  have hw_ex : ∃ w : V, w ≠ u ∧ w ≠ v := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset V) ⊆ {u, v} := by
      intro x _
      by_cases hxu : x = u
      · simp [hxu]
      · simp [h x hxu]
    have hc := Finset.card_le_card hsub
    have hc2 : ({u, v} : Finset V).card ≤ 2 := Finset.card_le_two
    simp only [Finset.card_univ] at hc
    omega
  obtain ⟨w, hwu, hwv⟩ := hw_ex
  obtain ⟨p⟩ := hconn u w
  let q := p.toPath
  have hqp : q.1.IsPath := q.2
  cases hq : q.1 with
  | nil => exact hwu rfl
  | @cons _ x _ hux q1 =>
    have hx : x = v := by
      have : x ∈ G.neighborFinset u := (G.mem_neighborFinset u x).mpr hux
      rw [hnu, Finset.mem_singleton] at this
      exact this
    cases hq1 : q1 with
    | nil => exact hwv hx
    | @cons _ y _ hxy q2 =>
      have hy : y = u := by
        have hvy : G.Adj v y := hx ▸ hxy
        have : y ∈ G.neighborFinset v := (G.mem_neighborFinset v y).mpr hvy
        rw [hnv, Finset.mem_singleton] at this
        exact this
      rw [hq, hq1] at hqp
      have hnd := hqp.support_nodup
      simp only [Walk.support_cons, List.nodup_cons] at hnd
      exact hnd.1 (List.mem_cons_of_mem x (hy ▸ Walk.start_mem_support q2))

lemma exists_cycle_of_two_le_degree [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdeg : ∀ v : V, 2 ≤ G.degree v) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle := by
  classical
  let S : Finset (Fin (Fintype.card V + 1)) := Finset.univ.filter
    (fun k => ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ p.length = k.val)
  have hS_ne : S.Nonempty := by
    obtain ⟨v0⟩ := ‹Nonempty V›
    refine ⟨⟨0, Nat.zero_lt_succ _⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, v0, v0, Walk.nil, Walk.IsPath.nil, rfl⟩⟩
  obtain ⟨kmax, hkmax_mem, hkmax_max⟩ := S.exists_max_image (fun k => k.val) hS_ne
  obtain ⟨_, a, b, p, hp, hplen⟩ := Finset.mem_filter.mp hkmax_mem
  have hlen_le : ∀ {x y : V} (q : G.Walk x y), q.IsPath → q.length ≤ p.length := by
    intro x y q hq
    have hqlt : q.length < Fintype.card V + 1 := by
      have h1 : q.support.length ≤ Fintype.card V := by
        have hnodup := q.support.toFinset_card_of_nodup hq.support_nodup
        have h2 := Finset.card_le_univ q.support.toFinset
        omega
      rw [Walk.length_support] at h1
      omega
    have hqmem : ⟨q.length, hqlt⟩ ∈ S :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, y, q, hq, rfl⟩
    have hle_val : q.length ≤ kmax.val := hkmax_max ⟨q.length, hqlt⟩ hqmem
    omega
  have hnb_in : ∀ w, G.Adj b w → w ∈ p.support := by
    intro w hbw
    by_contra hw
    have hq : (p.append (Walk.cons hbw Walk.nil)).IsPath := by
      rw [Walk.isPath_def, Walk.support_append]
      simp only [Walk.support_cons, Walk.support_nil, List.tail_cons, List.nodup_append]
      refine ⟨hp.support_nodup, List.nodup_singleton w, ?_⟩
      intro x hx y hy hxy
      simp only [List.mem_singleton] at hy
      subst hy
      subst hxy
      exact hw hx
    have hle := hlen_le _ hq
    simp [Walk.length_append] at hle
  have hp_pos : 0 < p.length := by
    obtain ⟨w, hw⟩ := Finset.card_pos.mp
      (by rw [card_neighborFinset_eq_degree]; have := hdeg b; omega : 0 < (G.neighborFinset b).card)
    have hbw : G.Adj b w := (G.mem_neighborFinset b w).mp hw
    have hwm := hnb_in w hbw
    cases p with
    | nil =>
      simp at hwm
      exact absurd hwm.symm hbw.ne
    | cons _ _ => simp
  let pr := p.reverse
  have hpr : pr.IsPath := hp.reverse
  have hpr_pos : 0 < pr.length := by simpa [pr] using hp_pos
  cases hpr_eq : pr with
  | nil => simp [hpr_eq] at hpr_pos
  | @cons _ u _ hbu q =>
    have hq_path : q.IsPath := by
      rw [hpr_eq] at hpr
      exact hpr.of_cons
    have hb_not_q : b ∉ q.support := by
      rw [hpr_eq] at hpr
      exact ((Walk.cons_isPath_iff hbu q).mp hpr).2
    have hdegb := hdeg b
    have hne_nb : ((G.neighborFinset b).erase u).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      have hcard_er := Finset.card_erase_of_mem ((G.mem_neighborFinset b u).mpr hbu)
      rw [hemp, Finset.card_empty, card_neighborFinset_eq_degree] at hcard_er
      omega
    obtain ⟨w, hw_mem⟩ := hne_nb
    have hwu : w ≠ u := (Finset.mem_erase.mp hw_mem).1
    have hbw : G.Adj b w := (G.mem_neighborFinset b w).mp (Finset.mem_erase.mp hw_mem).2
    have hw_pr : w ∈ pr.support := by
      rw [Walk.support_reverse, List.mem_reverse]
      exact hnb_in w hbw
    rw [hpr_eq, Walk.support_cons, List.mem_cons] at hw_pr
    have hw_q : w ∈ q.support := hw_pr.resolve_left hbw.ne.symm
    let r := q.takeUntil w hw_q
    have hr_path : r.IsPath := hq_path.takeUntil hw_q
    have hb_not_r : b ∉ r.support := fun h => hb_not_q (Walk.support_takeUntil_subset_support q hw_q h)
    have hpath_br : (Walk.cons hbu r).IsPath := (Walk.cons_isPath_iff hbu r).mpr ⟨hr_path, hb_not_r⟩
    have hcyc : (Walk.cons hbw.symm (Walk.cons hbu r)).IsCycle := by
      rw [Walk.cons_isCycle_iff]
      refine ⟨hpath_br, ?_⟩
      intro he
      rw [Walk.edges_cons, List.mem_cons] at he
      rcases he with he | he
      · have hsym : s(w, b) = s(b, u) := he
        rw [Sym2.eq_iff] at hsym
        rcases hsym with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact hbw.ne.symm h1
        · exact hwu h1
      · exact hb_not_r (Walk.snd_mem_support_of_mem_edges r he)
    exact ⟨w, Walk.cons hbw.symm (Walk.cons hbu r), hcyc⟩

lemma card_le_length_of_two_regular [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hdeg2 : ∀ v : V, G.degree v = 2)
    {v : V} (c : G.Walk v v) (hc : c.IsCycle) : Fintype.card V ≤ c.length := by
  have hclosed : ∀ x ∈ c.support, ∀ y, G.Adj x y → y ∈ c.support := by
    intro x hx y hxy
    let c' := c.rotate x hx
    have hc' : c'.IsCycle := hc.rotate hx
    have hsupp_eq : ∀ z, z ∈ c'.support ↔ z ∈ c.support := fun _ =>
      Walk.mem_support_rotate_iff c x hx
    have h1 : G.Adj x c'.snd := c'.adj_snd hc'.not_nil
    have h2 : G.Adj x c'.penultimate := (c'.adj_penultimate hc'.not_nil).symm
    have hne : c'.snd ≠ c'.penultimate := hc'.snd_ne_penultimate
    have hsub : ({c'.snd, c'.penultimate} : Finset V) ⊆ G.neighborFinset x := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact (G.mem_neighborFinset x _).mpr h1
      · exact (G.mem_neighborFinset x _).mpr h2
    have hcard_eq : ({c'.snd, c'.penultimate} : Finset V).card = (G.neighborFinset x).card := by
      rw [Finset.card_pair hne, card_neighborFinset_eq_degree, hdeg2 x]
    have heq := Finset.eq_of_subset_of_card_le hsub hcard_eq.ge
    have hy_mem : y ∈ ({c'.snd, c'.penultimate} : Finset V) := by
      rw [heq]
      exact (G.mem_neighborFinset x y).mpr hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy_mem
    rw [← hsupp_eq]
    rcases hy_mem with rfl | rfl
    · exact Walk.getVert_mem_support c' 1
    · exact Walk.getVert_mem_support c' (c'.length - 1)
  have hall : ∀ u : V, u ∈ c.support := by
    intro u
    obtain ⟨p⟩ := hconn v u
    have hwalk : ∀ {a b : V} (q : G.Walk a b), a ∈ c.support → b ∈ c.support := by
      intro a b q
      induction q with
      | nil => exact id
      | cons hadj _ ih => exact fun ha => ih (hclosed _ ha _ hadj)
    exact hwalk p (Walk.start_mem_support c)
  have hall_tail : ∀ u : V, u ∈ c.support.tail := by
    intro u
    have hu := hall u
    cases hsup : c.support with
    | nil => exact absurd hsup (Walk.support_ne_nil c)
    | cons a l =>
      have ha : a = v := by
        have := Walk.head_support c
        simp [hsup] at this
        exact this
      rw [hsup, List.mem_cons] at hu
      rcases hu with rfl | hu
      · rw [ha]
        have := c.end_mem_tail_support hc.not_nil
        simpa [hsup] using this
      · simpa [hsup] using hu
  have hsub : (Finset.univ : Finset V) ⊆ c.support.tail.toFinset := by
    intro u _
    exact List.mem_toFinset.mpr (hall_tail u)
  have hc1 := Finset.card_le_card hsub
  rw [Finset.card_univ, List.toFinset_card_of_nodup hc.support_nodup] at hc1
  have hlen : c.support.tail.length = c.length := by
    have := Walk.length_support c
    rw [List.length_tail]
    omega
  omega

end Basic

/- ### Section 2: Vertex-avoiding reachability, components, and connectivity -/

section Connectivity

variable {V : Type*}

def ReachAvoid (G : SimpleGraph V) (S : Finset V) (u v : V) : Prop :=
  ∃ p : G.Walk u v, ∀ x ∈ p.support, x ∉ S

def IsSeparating (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ u v : V, u ∉ S ∧ v ∉ S ∧ ¬ ReachAvoid G S u v

def IsKConnected2 (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, S.card ≤ 1 → ¬ IsSeparating G S

def IsKConnected3 (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, S.card ≤ 2 → ¬ IsSeparating G S

noncomputable def comp [Fintype V] (G : SimpleGraph V) (S : Finset V) (u : V) : Finset V :=
  by classical exact Finset.univ.filter (fun v => ReachAvoid G S u v)

lemma reachAvoid_refl {G : SimpleGraph V} {S : Finset V} {u : V} (hu : u ∉ S) :
    ReachAvoid G S u u :=
  ⟨Walk.nil, fun x hx => by simp only [Walk.support_nil, List.mem_singleton] at hx; rwa [hx]⟩

lemma reachAvoid_symm {G : SimpleGraph V} {S : Finset V} {u v : V}
    (h : ReachAvoid G S u v) : ReachAvoid G S v u := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p.reverse, fun x hx => hp x ?_⟩
  rw [Walk.support_reverse, List.mem_reverse] at hx
  exact hx

lemma reachAvoid_trans {G : SimpleGraph V} {S : Finset V} {u v w : V}
    (h1 : ReachAvoid G S u v) (h2 : ReachAvoid G S v w) : ReachAvoid G S u w := by
  obtain ⟨p, hp⟩ := h1
  obtain ⟨q, hq⟩ := h2
  refine ⟨p.append q, fun x hx => ?_⟩
  rcases (Walk.mem_support_append_iff p q).mp hx with hxp | hxq
  · exact hp x hxp
  · exact hq x hxq

lemma reachAvoid_adj {G : SimpleGraph V} {S : Finset V} {u v : V}
    (hu : u ∉ S) (hv : v ∉ S) (hadj : G.Adj u v) : ReachAvoid G S u v :=
  ⟨Walk.cons hadj Walk.nil, fun x hx => by
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption⟩

lemma reachAvoid_left_not_mem {G : SimpleGraph V} {S : Finset V} {u v : V}
    (h : ReachAvoid G S u v) : u ∉ S := by
  obtain ⟨p, hp⟩ := h
  exact hp u (Walk.start_mem_support p)

lemma reachAvoid_right_not_mem {G : SimpleGraph V} {S : Finset V} {u v : V}
    (h : ReachAvoid G S u v) : v ∉ S := by
  obtain ⟨p, hp⟩ := h
  exact hp v (Walk.end_mem_support p)

lemma reachAvoid_iso {G : SimpleGraph V} {S : Finset V} {u v : V} (φ : G ≃g G)
    (h : ReachAvoid G S u v) :
    ReachAvoid G (S.map φ.toEquiv.toEmbedding) (φ u) (φ v) := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p.map φ.toHom, fun x hx => ?_⟩
  rw [Walk.support_map, List.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  intro hmem
  rw [Finset.mem_map] at hmem
  obtain ⟨z, hz, hzy⟩ := hmem
  exact hp y hy (by have := φ.injective hzy; rwa [← this])

lemma map_iso_symm_cancel {G : SimpleGraph V} (φ : G ≃g G) (S : Finset V) :
    (S.map φ.toEquiv.toEmbedding).map φ.symm.toEquiv.toEmbedding = S := by
  ext x
  simp only [Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    simpa [RelIso.symm_apply_apply] using hz
  · intro hx
    exact ⟨φ x, ⟨x, hx, rfl⟩, φ.symm_apply_apply x⟩

lemma isSeparating_iso {G : SimpleGraph V} {S : Finset V} (φ : G ≃g G)
    (h : IsSeparating G S) : IsSeparating G (S.map φ.toEquiv.toEmbedding) := by
  obtain ⟨u, v, hu, hv, hnr⟩ := h
  refine ⟨φ u, φ v, ?_, ?_, ?_⟩
  · intro hm; rw [Finset.mem_map] at hm; obtain ⟨z, hz, hzu⟩ := hm
    exact hu (by have := φ.injective hzu; rwa [← this])
  · intro hm; rw [Finset.mem_map] at hm; obtain ⟨z, hz, hzv⟩ := hm
    exact hv (by have := φ.injective hzv; rwa [← this])
  · intro hr
    have hback := reachAvoid_iso φ.symm hr
    rw [map_iso_symm_cancel, φ.symm_apply_apply, φ.symm_apply_apply] at hback
    exact hnr hback

lemma mem_comp_iff [Fintype V] {G : SimpleGraph V} {S : Finset V} {u v : V} :
    v ∈ comp G S u ↔ ReachAvoid G S u v := by
  classical simp [comp]

lemma self_mem_comp [Fintype V] {G : SimpleGraph V} {S : Finset V} {u : V} (hu : u ∉ S) :
    u ∈ comp G S u :=
  mem_comp_iff.mpr (reachAvoid_refl hu)

lemma comp_disjoint [Fintype V] {G : SimpleGraph V} {S : Finset V} {u : V} :
    Disjoint (comp G S u) S := by
  rw [Finset.disjoint_left]
  intro x hx
  exact reachAvoid_right_not_mem (mem_comp_iff.mp hx)

lemma comp_closed [Fintype V] {G : SimpleGraph V} {S : Finset V} {u x y : V}
    (hx : x ∈ comp G S u) (hxy : G.Adj x y) (hy : y ∉ S) : y ∈ comp G S u := by
  rw [mem_comp_iff] at hx ⊢
  exact reachAvoid_trans hx (reachAvoid_adj (reachAvoid_right_not_mem hx) hy hxy)

lemma comp_eq_of_mem [Fintype V] {G : SimpleGraph V} {S : Finset V} {u v : V}
    (hv : v ∈ comp G S u) : comp G S v = comp G S u := by
  ext x
  simp only [mem_comp_iff] at hv ⊢
  exact ⟨reachAvoid_trans hv, reachAvoid_trans (reachAvoid_symm hv)⟩

lemma comp_subset_of_closed [Fintype V] {G : SimpleGraph V} {S A : Finset V} {u : V}
    (hclosed : ∀ x ∈ A, ∀ y, G.Adj x y → y ∈ A ∨ y ∈ S) (hu : u ∈ A) :
    comp G S u ⊆ A := by
  intro v hv
  obtain ⟨p, hp⟩ := mem_comp_iff.mp hv
  have hstep : ∀ {a b : V} (q : G.Walk a b), (∀ x ∈ q.support, x ∉ S) → a ∈ A → b ∈ A := by
    intro a b q
    induction q with
    | nil => intro _ ha; exact ha
    | @cons a c b hac q' ih =>
      intro hq ha
      have hc_not_S : c ∉ S := hq c (by simp [Walk.support_cons])
      have hcA : c ∈ A := (hclosed a ha c hac).resolve_right hc_not_S
      exact ih (fun x hx => hq x (by simp [Walk.support_cons, hx])) hcA
  exact hstep p hp hu

lemma comp_iso [Fintype V] {G : SimpleGraph V} {S : Finset V} {u : V} (φ : G ≃g G) :
    comp G (S.map φ.toEquiv.toEmbedding) (φ u) = (comp G S u).map φ.toEquiv.toEmbedding := by
  ext x
  simp only [mem_comp_iff, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · intro hr
    refine ⟨φ.symm x, ?_, φ.apply_symm_apply x⟩
    have hback := reachAvoid_iso φ.symm hr
    rw [map_iso_symm_cancel, φ.symm_apply_apply] at hback
    exact hback
  · rintro ⟨y, hy, rfl⟩
    exact reachAvoid_iso φ hy

lemma comp_connected_outside_singleton [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hconn : G.Connected) {x u z : V} (hz : z ∉ comp G {x} u) :
    ReachAvoid G (comp G {x} u) z x := by
  obtain ⟨p⟩ := hconn z x
  have hx_not : x ∉ comp G {x} u := by
    intro hm
    exact (Finset.disjoint_left.mp comp_disjoint hm) (Finset.mem_singleton_self x)
  have haux : ∀ {a b : V} (q : G.Walk a b), b = x → a ∉ comp G {x} u →
      ReachAvoid G (comp G {x} u) a x := by
    intro a b q
    induction q with
    | nil =>
      rintro rfl _
      exact reachAvoid_refl hx_not
    | @cons a w b haw q' ih =>
      intro hbx ha
      by_cases hw : w ∈ comp G {x} u
      · have hax : a ∈ ({x} : Finset V) := by
          by_contra hax
          exact ha (comp_closed hw haw.symm hax)
        rw [Finset.mem_singleton] at hax
        subst hax
        exact reachAvoid_refl hx_not
      · exact reachAvoid_trans (reachAvoid_adj ha hw haw) (ih hbx hw)
  exact haux p rfl hz

/- ### Section 3: Watkins's 2-connectedness and 3-connectedness for vertex-transitive graphs -/

lemma two_connected_of_vt [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hconn : G.Connected)
    (htrans : IsVertexTransitive G) : IsKConnected2 G := by
  classical
  intro S hScard hSsep
  have hS_ne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    obtain ⟨u, v, _, _, hnr⟩ := hSsep
    obtain ⟨p⟩ := hconn u v
    exact hnr ⟨p, fun x _ => Finset.notMem_empty x⟩
  have hS1 : S.card = 1 := by
    have := hS_ne.card_pos
    omega
  obtain ⟨x0, hS_eq⟩ := Finset.card_eq_one.mp hS1
  have hx0_sep : IsSeparating G {x0} := hS_eq ▸ hSsep
  let P : Finset (Finset V) := Finset.univ.filter fun A =>
    ∃ x u : V, u ≠ x ∧ IsSeparating G {x} ∧ A = comp G {x} u
  have hP_ne : P.Nonempty := by
    have ⟨u, _, hu, _, _⟩ := hx0_sep
    have hux : u ≠ x0 := by simpa using hu
    exact ⟨comp G {x0} u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x0, u, hux, hx0_sep, rfl⟩⟩
  obtain ⟨A, hA_mem, hA_min⟩ := P.exists_min_image Finset.card hP_ne
  obtain ⟨_, x, u, hux, hx_sep, hA_eq⟩ := Finset.mem_filter.mp hA_mem
  have hu_in : u ∈ comp G {x} u := self_mem_comp (by simpa using hux)
  obtain ⟨φ, hφ⟩ := htrans x u
  have hu_sep : IsSeparating G {u} := by
    have := isSeparating_iso φ hx_sep
    have hmap : ({x} : Finset V).map φ.toEquiv.toEmbedding = {u} := by
      ext z; simp [hφ]
    rwa [hmap] at this
  have hW_sub : (comp G {x} u)ᶜ ⊆ comp G {u} x := by
    intro z hz
    rw [Finset.mem_compl] at hz
    rw [mem_comp_iff]
    obtain ⟨p, hp⟩ := comp_connected_outside_singleton hconn hz
    refine ⟨p.reverse, fun w hw => ?_⟩
    rw [Walk.support_reverse, List.mem_reverse] at hw
    intro hwu
    rw [Finset.mem_singleton] at hwu
    exact hp w hw (hwu ▸ hu_in)
  have ⟨a, b, ha, hb, hnr⟩ := hu_sep
  have hw_ex : ∃ w : V, w ≠ u ∧ ¬ ReachAvoid G {u} x w := by
    by_cases hra : ReachAvoid G {u} x a
    · exact ⟨b, by simpa using hb, fun hrb => hnr (reachAvoid_trans (reachAvoid_symm hra) hrb)⟩
    · exact ⟨a, by simpa using ha, hra⟩
  obtain ⟨w, hwu, hnw⟩ := hw_ex
  have hsub_er : comp G {u} w ⊆ (comp G {x} u).erase u := by
    intro z hz
    rw [Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · intro hzu
      exact (Finset.disjoint_left.mp comp_disjoint (hzu ▸ hz)) (Finset.mem_singleton_self u)
    · by_contra hzn
      have hz_x : z ∈ comp G {u} x := hW_sub (Finset.mem_compl.mpr hzn)
      exact hnw (reachAvoid_trans (mem_comp_iff.mp hz_x) (reachAvoid_symm (mem_comp_iff.mp hz)))
  have hcw_mem : comp G {u} w ∈ P :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, w, hwu, hu_sep, rfl⟩
  have hle := hA_min (comp G {u} w) hcw_mem
  have hlt : ((comp G {x} u).erase u).card < (comp G {x} u).card :=
    Finset.card_erase_lt_of_mem hu_in
  have hle2 := Finset.card_le_card hsub_er
  rw [hA_eq] at hle
  omega

/-- Key submodularity step for Watkins's 3-connectedness proof. -/
private lemma watkins_submod [Fintype V] [DecidableEq V] (G : SimpleGraph V) (h2c : IsKConnected2 G)
    (a : ℕ)
    (hmin : ∀ (S : Finset V) (u : V), S.card = 2 → u ∉ S →
      ((comp G S u ∪ S)ᶜ).Nonempty → a ≤ (comp G S u).card)
    {S₁ S₂ : Finset V} {u₁ u₂ : V}
    (hS₁ : S₁.card = 2) (hS₂ : S₂.card = 2)
    (hB₁ : ((comp G S₁ u₁ ∪ S₁)ᶜ).Nonempty)
    (hinter_ne : (comp G S₁ u₁ ∩ comp G S₂ u₂).Nonempty)
    (hinter_lt : (comp G S₁ u₁ ∩ comp G S₂ u₂).card < a) :
    ((comp G S₁ u₁ ∪ S₁)ᶜ ∩ S₂ ∪ (S₁ ∩ S₂) ∪ (comp G S₂ u₂ ∪ S₂)ᶜ ∩ S₁).card ≤ 1 ∧
      (comp G S₁ u₁ ∪ S₁)ᶜ ∩ (comp G S₂ u₂ ∪ S₂)ᶜ = ∅ := by
  set C₁ := comp G S₁ u₁
  set A₂ := comp G S₂ u₂
  set B₁ := (C₁ ∪ S₁)ᶜ
  set B₂ := (A₂ ∪ S₂)ᶜ
  set T' := (B₁ ∩ S₂) ∪ (S₁ ∩ S₂) ∪ (B₂ ∩ S₁)
  set T := (C₁ ∩ S₂) ∪ (S₁ ∩ S₂) ∪ (A₂ ∩ S₁)
  have hdisj1 : Disjoint C₁ S₁ := comp_disjoint
  have hdisj2 : Disjoint A₂ S₂ := comp_disjoint
  have hpart1 : ∀ x, (x ∈ C₁ ∧ x ∉ S₁ ∧ x ∉ B₁) ∨ (x ∉ C₁ ∧ x ∈ S₁ ∧ x ∉ B₁) ∨
      (x ∉ C₁ ∧ x ∉ S₁ ∧ x ∈ B₁) := by
    intro x
    by_cases h1 : x ∈ C₁
    · left; refine ⟨h1, Finset.disjoint_left.mp hdisj1 h1, ?_⟩; simp [B₁, h1]
    · by_cases h2 : x ∈ S₁
      · right; left; refine ⟨h1, h2, ?_⟩; simp [B₁, h2]
      · right; right; refine ⟨h1, h2, ?_⟩; simp [B₁, h1, h2]
  have hpart2 : ∀ x, (x ∈ A₂ ∧ x ∉ S₂ ∧ x ∉ B₂) ∨ (x ∉ A₂ ∧ x ∈ S₂ ∧ x ∉ B₂) ∨
      (x ∉ A₂ ∧ x ∉ S₂ ∧ x ∈ B₂) := by
    intro x
    by_cases h1 : x ∈ A₂
    · left; refine ⟨h1, Finset.disjoint_left.mp hdisj2 h1, ?_⟩; simp [B₂, h1]
    · by_cases h2 : x ∈ S₂
      · right; left; refine ⟨h1, h2, ?_⟩; simp [B₂, h2]
      · right; right; refine ⟨h1, h2, ?_⟩; simp [B₂, h1, h2]
  have hT_card : T.card = (C₁ ∩ S₂).card + (S₁ ∩ S₂).card + (A₂ ∩ S₁).card := by
    have hd1 : Disjoint (C₁ ∩ S₂) (S₁ ∩ S₂) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      exact Finset.disjoint_left.mp hdisj1 (Finset.mem_inter.mp hx1).1 (Finset.mem_inter.mp hx2).1
    have hd2 : Disjoint ((C₁ ∩ S₂) ∪ (S₁ ∩ S₂)) (A₂ ∩ S₁) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      have h2 := Finset.mem_inter.mp hx2
      rw [Finset.mem_union] at hx1
      rcases hx1 with hx1 | hx1
      · exact Finset.disjoint_left.mp hdisj1 (Finset.mem_inter.mp hx1).1 h2.2
      · exact Finset.disjoint_left.mp hdisj2 h2.1 (Finset.mem_inter.mp hx1).2
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
  have hT'_card : T'.card = (B₁ ∩ S₂).card + (S₁ ∩ S₂).card + (B₂ ∩ S₁).card := by
    have hd1 : Disjoint (B₁ ∩ S₂) (S₁ ∩ S₂) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      have := (Finset.mem_inter.mp hx1).1
      simp only [B₁, Finset.mem_compl, Finset.mem_union] at this
      exact this (Or.inr (Finset.mem_inter.mp hx2).1)
    have hd2 : Disjoint ((B₁ ∩ S₂) ∪ (S₁ ∩ S₂)) (B₂ ∩ S₁) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      have h2 := Finset.mem_inter.mp hx2
      simp only [B₂, Finset.mem_compl, Finset.mem_union] at h2
      rw [Finset.mem_union] at hx1
      rcases hx1 with hx1 | hx1
      · exact h2.1 (Or.inr (Finset.mem_inter.mp hx1).2)
      · exact h2.1 (Or.inr (Finset.mem_inter.mp hx1).2)
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
  have hS2_split : S₂.card = (C₁ ∩ S₂).card + (S₁ ∩ S₂).card + (B₁ ∩ S₂).card := by
    have heq : S₂ = (C₁ ∩ S₂) ∪ (S₁ ∩ S₂) ∪ (B₁ ∩ S₂) := by
      ext x; simp only [Finset.mem_union, Finset.mem_inter]
      rcases hpart1 x with ⟨h1, _, _⟩ | ⟨_, h2, _⟩ | ⟨_, _, h3⟩ <;> tauto
    have hd1 : Disjoint (C₁ ∩ S₂) (S₁ ∩ S₂) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      exact Finset.disjoint_left.mp hdisj1 (Finset.mem_inter.mp hx1).1 (Finset.mem_inter.mp hx2).1
    have hd2 : Disjoint ((C₁ ∩ S₂) ∪ (S₁ ∩ S₂)) (B₁ ∩ S₂) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      have hb := (Finset.mem_inter.mp hx2).1
      simp only [B₁, Finset.mem_compl, Finset.mem_union] at hb
      rw [Finset.mem_union] at hx1
      rcases hx1 with hx1 | hx1
      · exact hb (Or.inl (Finset.mem_inter.mp hx1).1)
      · exact hb (Or.inr (Finset.mem_inter.mp hx1).1)
    calc S₂.card = ((C₁ ∩ S₂) ∪ (S₁ ∩ S₂) ∪ (B₁ ∩ S₂)).card := congrArg Finset.card heq
      _ = (C₁ ∩ S₂).card + (S₁ ∩ S₂).card + (B₁ ∩ S₂).card := by
        rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
  have hS1_split : S₁.card = (A₂ ∩ S₁).card + (S₁ ∩ S₂).card + (B₂ ∩ S₁).card := by
    have heq : S₁ = (A₂ ∩ S₁) ∪ (S₁ ∩ S₂) ∪ (B₂ ∩ S₁) := by
      ext x; simp only [Finset.mem_union, Finset.mem_inter]
      rcases hpart2 x with ⟨h1, _, _⟩ | ⟨_, h2, _⟩ | ⟨_, _, h3⟩ <;> tauto
    have hd1 : Disjoint (A₂ ∩ S₁) (S₁ ∩ S₂) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      exact Finset.disjoint_left.mp hdisj2 (Finset.mem_inter.mp hx1).1 (Finset.mem_inter.mp hx2).2
    have hd2 : Disjoint ((A₂ ∩ S₁) ∪ (S₁ ∩ S₂)) (B₂ ∩ S₁) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      have hb := (Finset.mem_inter.mp hx2).1
      simp only [B₂, Finset.mem_compl, Finset.mem_union] at hb
      rw [Finset.mem_union] at hx1
      rcases hx1 with hx1 | hx1
      · exact hb (Or.inl (Finset.mem_inter.mp hx1).1)
      · exact hb (Or.inr (Finset.mem_inter.mp hx1).2)
    calc S₁.card = ((A₂ ∩ S₁) ∪ (S₁ ∩ S₂) ∪ (B₂ ∩ S₁)).card := congrArg Finset.card heq
      _ = (A₂ ∩ S₁).card + (S₁ ∩ S₂).card + (B₂ ∩ S₁).card := by
        rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
  have hsum4 : T.card + T'.card = 4 := by omega
  have hcl_inter : ∀ x ∈ C₁ ∩ A₂, ∀ y, G.Adj x y → y ∈ C₁ ∩ A₂ ∨ y ∈ T := by
    intro x hx y hxy
    have ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
    have hy1 : y ∈ C₁ ∨ y ∈ S₁ := by
      by_cases hyS : y ∈ S₁
      · exact Or.inr hyS
      · exact Or.inl (comp_closed hx1 hxy hyS)
    have hy2 : y ∈ A₂ ∨ y ∈ S₂ := by
      by_cases hyS : y ∈ S₂
      · exact Or.inr hyS
      · exact Or.inl (comp_closed hx2 hxy hyS)
    rcases hy1 with hy1 | hy1 <;> rcases hy2 with hy2 | hy2
    · exact Or.inl (Finset.mem_inter.mpr ⟨hy1, hy2⟩)
    · exact Or.inr (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hy1, hy2⟩)))))
    · exact Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hy2, hy1⟩)))
    · exact Or.inr (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hy1, hy2⟩)))))
  obtain ⟨w, hw⟩ := hinter_ne
  have hw_not_T : w ∉ T := by
    have ⟨hw1, hw2⟩ := Finset.mem_inter.mp hw
    simp only [T, Finset.mem_union, Finset.mem_inter]
    rintro ((⟨_, h⟩ | ⟨h, _⟩) | ⟨_, h⟩)
    · exact Finset.disjoint_left.mp hdisj2 hw2 h
    · exact Finset.disjoint_left.mp hdisj1 hw1 h
    · exact Finset.disjoint_left.mp hdisj1 hw1 h
  obtain ⟨b, hb⟩ := hB₁
  have hb_not_inter : b ∉ C₁ ∩ A₂ := by
    simp only [B₁, Finset.mem_compl, Finset.mem_union] at hb
    intro hm; exact hb (Or.inl (Finset.mem_inter.mp hm).1)
  have hb_not_T : b ∉ T := by
    simp only [B₁, Finset.mem_compl, Finset.mem_union] at hb
    simp only [T, Finset.mem_union, Finset.mem_inter]
    rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨_, h⟩)
    · exact hb (Or.inl h)
    · exact hb (Or.inr h)
    · exact hb (Or.inr h)
  have hcomp_sub : comp G T w ⊆ C₁ ∩ A₂ := comp_subset_of_closed hcl_inter hw
  have hb_not_comp : b ∉ comp G T w := fun hm => hb_not_inter (hcomp_sub hm)
  have hT_ge3 : 3 ≤ T.card := by
    by_contra hlt
    by_cases h1 : T.card ≤ 1
    · exact h2c T h1 ⟨w, b, hw_not_T, hb_not_T, fun hr => hb_not_comp (mem_comp_iff.mpr hr)⟩
    · have hT2 : T.card = 2 := by omega
      have hB_ne : ((comp G T w ∪ T)ᶜ).Nonempty :=
        ⟨b, Finset.mem_compl.mpr (by simp [hb_not_comp, hb_not_T])⟩
      have hge := hmin T w hT2 hw_not_T hB_ne
      have hle := Finset.card_le_card hcomp_sub
      omega
  have hT'_le1 : T'.card ≤ 1 := by omega
  refine ⟨hT'_le1, ?_⟩
  by_contra hne
  obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hcl_B : ∀ x ∈ B₁ ∩ B₂, ∀ y, G.Adj x y → y ∈ B₁ ∩ B₂ ∨ y ∈ T' := by
    intro x hx y hxy
    have ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
    simp only [B₁, B₂, Finset.mem_compl, Finset.mem_union] at hx1 hx2
    have hy1 : y ∈ B₁ ∨ y ∈ S₁ := by
      by_cases hyS : y ∈ S₁
      · exact Or.inr hyS
      · left
        simp only [B₁, Finset.mem_compl, Finset.mem_union]
        rintro (hyC | hyS')
        · exact hx1 (Or.inl (comp_closed hyC hxy.symm (fun h => hx1 (Or.inr h))))
        · exact hyS hyS'
    have hy2 : y ∈ B₂ ∨ y ∈ S₂ := by
      by_cases hyS : y ∈ S₂
      · exact Or.inr hyS
      · left
        simp only [B₂, Finset.mem_compl, Finset.mem_union]
        rintro (hyA | hyS')
        · exact hx2 (Or.inl (comp_closed hyA hxy.symm (fun h => hx2 (Or.inr h))))
        · exact hyS hyS'
    rcases hy1 with hy1 | hy1 <;> rcases hy2 with hy2 | hy2
    · exact Or.inl (Finset.mem_inter.mpr ⟨hy1, hy2⟩)
    · exact Or.inr (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hy1, hy2⟩)))))
    · exact Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hy2, hy1⟩)))
    · exact Or.inr (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hy1, hy2⟩)))))
  have hz_not_T' : z ∉ T' := by
    have ⟨hz1, hz2⟩ := Finset.mem_inter.mp hz
    simp only [B₁, B₂, Finset.mem_compl, Finset.mem_union] at hz1 hz2
    simp only [T', Finset.mem_union, Finset.mem_inter]
    rintro ((⟨_, h⟩ | ⟨h, _⟩) | ⟨_, h⟩)
    · exact hz2 (Or.inr h)
    · exact hz1 (Or.inr h)
    · exact hz1 (Or.inr h)
  have hw_not_T' : w ∉ T' := by
    have ⟨hw1, _⟩ := Finset.mem_inter.mp hw
    simp only [T', Finset.mem_union, Finset.mem_inter]
    rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨_, h⟩)
    · simp only [B₁, Finset.mem_compl, Finset.mem_union] at h; exact h (Or.inl hw1)
    · exact Finset.disjoint_left.mp hdisj1 hw1 h
    · exact Finset.disjoint_left.mp hdisj1 hw1 h
  have hw_not_B : w ∉ B₁ ∩ B₂ := by
    have ⟨hw1, _⟩ := Finset.mem_inter.mp hw
    intro hm
    have hb1 := (Finset.mem_inter.mp hm).1
    simp only [B₁, Finset.mem_compl, Finset.mem_union] at hb1
    exact hb1 (Or.inl hw1)
  have hsubB : comp G T' z ⊆ B₁ ∩ B₂ := comp_subset_of_closed hcl_B hz
  exact h2c T' hT'_le1 ⟨z, w, hz_not_T', hw_not_T', fun hr => hw_not_B (hsubB (mem_comp_iff.mpr hr))⟩

/-- An atom of size 2 cannot equal the 2-cut of another atom of size 2 when degree ≥ 3. -/
private lemma no_atom_eq_cut [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hdeg3 : ∀ v : V, 3 ≤ G.degree v)
    (hreg : ∀ u v : V, G.degree u = G.degree v)
    {S A : Finset V} {u : V}
    (hS2 : S.card = 2) (hA_eq : A = comp G S u) (hA2 : A.card = 2)
    (hB_ne : ((A ∪ S)ᶜ).Nonempty)
    (hS_adj : ∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ ≠ s₂ → G.Adj s₁ s₂) : False := by
  have hdisj : Disjoint A S := by rw [hA_eq]; exact comp_disjoint
  have hall_adj : ∀ x ∈ A, G.degree x = 3 ∧ ∀ s ∈ S, G.Adj x s := by
    intro x hx
    have hsub : G.neighborFinset x ⊆ A.erase x ∪ S := by
      intro y hy
      have hxy : G.Adj x y := (G.mem_neighborFinset x y).mp hy
      by_cases hyS : y ∈ S
      · exact Finset.mem_union.mpr (Or.inr hyS)
      · refine Finset.mem_union.mpr (Or.inl (Finset.mem_erase.mpr ⟨hxy.ne.symm, ?_⟩))
        rw [hA_eq] at hx ⊢
        exact comp_closed hx hxy hyS
    have hcard_rhs : (A.erase x ∪ S).card = 3 := by
      have hd : Disjoint (A.erase x) S := hdisj.mono_left (Finset.erase_subset x A)
      rw [Finset.card_union_of_disjoint hd, Finset.card_erase_of_mem hx, hA2, hS2]
    have hle := Finset.card_le_card hsub
    rw [card_neighborFinset_eq_degree, hcard_rhs] at hle
    have hge := hdeg3 x
    have hdegx : G.degree x = 3 := by omega
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [card_neighborFinset_eq_degree, hdegx, hcard_rhs])
    refine ⟨hdegx, fun s hs => ?_⟩
    exact (G.mem_neighborFinset x s).mp (heq ▸ Finset.mem_union.mpr (Or.inr hs))
  have hS_closed : ∀ s ∈ S, ∀ y, G.Adj s y → y ∈ A ∪ S := by
    intro s hs y hsy
    obtain ⟨x0, hx0⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
    have hdegs : G.degree s = 3 := (hreg s x0).trans (hall_adj x0 hx0).1
    have hsub : A ∪ S.erase s ⊆ G.neighborFinset s := by
      intro z hz
      rw [Finset.mem_union] at hz
      rcases hz with hzA | hzS
      · exact (G.mem_neighborFinset s z).mpr ((hall_adj z hzA).2 s hs).symm
      · have ⟨hne, hzS'⟩ := Finset.mem_erase.mp hzS
        exact (G.mem_neighborFinset s z).mpr (hS_adj s hs z hzS' hne.symm)
    have hd : Disjoint A (S.erase s) := hdisj.mono_right (Finset.erase_subset s S)
    have hcard_lhs : (A ∪ S.erase s).card = 3 := by
      rw [Finset.card_union_of_disjoint hd, hA2, Finset.card_erase_of_mem hs, hS2]
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [card_neighborFinset_eq_degree, hdegs, hcard_lhs])
    have hy_mem : y ∈ A ∪ S.erase s := heq.symm ▸ (G.mem_neighborFinset s y).mpr hsy
    rw [Finset.mem_union] at hy_mem ⊢
    rcases hy_mem with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_of_mem_erase h)
  have hAS_closed : ∀ x ∈ A ∪ S, ∀ y, G.Adj x y → y ∈ A ∪ S := by
    intro x hx y hxy
    rw [Finset.mem_union] at hx
    rcases hx with hxA | hxS
    · by_cases hyS : y ∈ S
      · exact Finset.mem_union.mpr (Or.inr hyS)
      · rw [hA_eq] at hxA
        exact Finset.mem_union.mpr (Or.inl (hA_eq.symm ▸ comp_closed hxA hxy hyS))
    · exact hS_closed x hxS y hxy
  obtain ⟨x0, hx0⟩ := Finset.card_pos.mp (by omega : 0 < A.card)
  obtain ⟨b, hb⟩ := hB_ne
  obtain ⟨p⟩ := hconn x0 b
  have hstay : ∀ {v1 v2 : V} (q : G.Walk v1 v2), v1 ∈ A ∪ S → v2 ∈ A ∪ S := by
    intro v1 v2 q
    induction q with
    | nil => exact id
    | cons hadj _ ih => exact fun h => ih (hAS_closed _ h _ hadj)
  have hb_in : b ∈ A ∪ S := hstay p (Finset.mem_union.mpr (Or.inl hx0))
  exact (Finset.mem_compl.mp hb) hb_in

lemma three_connected_of_vt [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (htrans : IsVertexTransitive G)
    (hdeg3 : ∀ v : V, 3 ≤ G.degree v) : IsKConnected3 G := by
  classical
  have h2c : IsKConnected2 G := two_connected_of_vt G hconn htrans
  have hreg := degree_eq_of_isVertexTransitive G htrans
  intro S0 hS0card hS0sep
  have hS0_2 : S0.card = 2 := by
    by_contra hne
    exact h2c S0 (by omega) hS0sep
  let Parts : Finset (Finset V) := Finset.univ.filter fun A =>
    ∃ (S : Finset V) (u : V), S.card = 2 ∧ u ∉ S ∧ A = comp G S u ∧ ((A ∪ S)ᶜ).Nonempty
  have hParts_ne : Parts.Nonempty := by
    obtain ⟨u, v, hu, hv, hnr⟩ := hS0sep
    refine ⟨comp G S0 u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, S0, u, hS0_2, hu, rfl, ?_⟩⟩
    exact ⟨v, Finset.mem_compl.mpr (by simp [mem_comp_iff, hnr, hv])⟩
  obtain ⟨A0, hA0_mem, hA0_min⟩ := Parts.exists_min_image Finset.card hParts_ne
  let a := A0.card
  have hmin : ∀ (S : Finset V) (u : V), S.card = 2 → u ∉ S →
      ((comp G S u ∪ S)ᶜ).Nonempty → a ≤ (comp G S u).card := by
    intro S u hS hu hB
    exact hA0_min (comp G S u) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, S, u, hS, hu, rfl, hB⟩)
  have ha_ge2 : 2 ≤ a := by
    obtain ⟨_, S, u, hS, hu, hA0_eq, _⟩ := Finset.mem_filter.mp hA0_mem
    have hpos : 0 < a := by
      change 0 < A0.card
      rw [hA0_eq]
      exact Finset.card_pos.mpr ⟨u, self_mem_comp hu⟩
    by_contra hlt
    have ha1 : A0.card = 1 := by omega
    have hA0_sing : A0 = {u} := by
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp ha1
      have hum : u ∈ A0 := hA0_eq.symm ▸ self_mem_comp hu
      rw [hw, Finset.mem_singleton] at hum
      rw [hw, hum]
    have hsub : G.neighborFinset u ⊆ S := by
      intro y hy
      by_contra hyS
      have hyA : y ∈ A0 := hA0_eq.symm ▸ comp_closed (self_mem_comp hu) ((G.mem_neighborFinset u y).mp hy) hyS
      rw [hA0_sing, Finset.mem_singleton] at hyA
      exact ((G.mem_neighborFinset u y).mp hy).ne.symm hyA
    have hle := Finset.card_le_card hsub
    rw [card_neighborFinset_eq_degree, hS] at hle
    have := hdeg3 u
    omega
  have hatom_disj : ∀ {S₁ S₂ : Finset V} {u₁ u₂ : V},
      S₁.card = 2 → S₂.card = 2 → u₁ ∉ S₁ → u₂ ∉ S₂ →
      ((comp G S₁ u₁ ∪ S₁)ᶜ).Nonempty → ((comp G S₂ u₂ ∪ S₂)ᶜ).Nonempty →
      (comp G S₁ u₁).card = a → (comp G S₂ u₂).card = a →
      comp G S₁ u₁ ≠ comp G S₂ u₂ → Disjoint (comp G S₁ u₁) (comp G S₂ u₂) := by
    intro S₁ S₂ u₁ u₂ hS₁ hS₂ hu₁ hu₂ hB₁ hB₂ hc₁ hc₂ hne
    rw [Finset.disjoint_iff_inter_eq_empty]
    by_contra hinter_ne_empty
    have hinter_ne : (comp G S₁ u₁ ∩ comp G S₂ u₂).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hinter_ne_empty
    have hinter_lt : (comp G S₁ u₁ ∩ comp G S₂ u₂).card < a := by
      have hssub : comp G S₁ u₁ ∩ comp G S₂ u₂ ⊂ comp G S₁ u₁ := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.inter_subset_left, fun heq => hne ?_⟩
        have hsub : comp G S₁ u₁ ⊆ comp G S₂ u₂ := heq ▸ Finset.inter_subset_right
        exact Finset.eq_of_subset_of_card_le hsub (by omega)
      have := Finset.card_lt_card hssub
      omega
    have ⟨hT'_le1, hB_empty⟩ := watkins_submod G h2c a hmin hS₁ hS₂ hB₁ hinter_ne hinter_lt
    set C₁ := comp G S₁ u₁
    set A₂ := comp G S₂ u₂
    set B₁ := (C₁ ∪ S₁)ᶜ
    set B₂ := (A₂ ∪ S₂)ᶜ
    have hB1_ge : a ≤ B₁.card := by
      obtain ⟨b, hb⟩ := hB₁
      simp only [B₁, Finset.mem_compl, Finset.mem_union] at hb
      have hsub : comp G S₁ b ⊆ B₁ := by
        intro z hz
        simp only [B₁, Finset.mem_compl, Finset.mem_union]
        rintro (hzC | hzS)
        · have hbC : b ∈ C₁ := by
            show b ∈ comp G S₁ u₁
            rw [← comp_eq_of_mem hzC]
            exact mem_comp_iff.mpr (reachAvoid_symm (mem_comp_iff.mp hz))
          exact hb (Or.inl hbC)
        · exact (Finset.disjoint_left.mp comp_disjoint hz) hzS
      have hbu_ne : ((comp G S₁ b ∪ S₁)ᶜ).Nonempty := by
        refine ⟨u₁, Finset.mem_compl.mpr ?_⟩
        simp only [Finset.mem_union]
        rintro (hm | hm)
        · have := hsub hm
          simp only [B₁, Finset.mem_compl, Finset.mem_union] at this
          exact this (Or.inl (self_mem_comp hu₁))
        · exact hu₁ hm
      exact (hmin S₁ b hS₁ (fun h => hb (Or.inr h)) hbu_ne).trans (Finset.card_le_card hsub)
    have hB2_ge : a ≤ B₂.card := by
      obtain ⟨b, hb⟩ := hB₂
      simp only [B₂, Finset.mem_compl, Finset.mem_union] at hb
      have hsub : comp G S₂ b ⊆ B₂ := by
        intro z hz
        simp only [B₂, Finset.mem_compl, Finset.mem_union]
        rintro (hzA | hzS)
        · have hbA : b ∈ A₂ := by
            show b ∈ comp G S₂ u₂
            rw [← comp_eq_of_mem hzA]
            exact mem_comp_iff.mpr (reachAvoid_symm (mem_comp_iff.mp hz))
          exact hb (Or.inl hbA)
        · exact (Finset.disjoint_left.mp comp_disjoint hz) hzS
      have hbu_ne : ((comp G S₂ b ∪ S₂)ᶜ).Nonempty := by
        refine ⟨u₂, Finset.mem_compl.mpr ?_⟩
        simp only [Finset.mem_union]
        rintro (hm | hm)
        · have := hsub hm
          simp only [B₂, Finset.mem_compl, Finset.mem_union] at this
          exact this (Or.inl (self_mem_comp hu₂))
        · exact hu₂ hm
      exact (hmin S₂ b hS₂ (fun h => hb (Or.inr h)) hbu_ne).trans (Finset.card_le_card hsub)
    have hB1_sub : B₁ ⊆ (B₁ ∩ A₂) ∪ (B₁ ∩ S₂) := by
      intro x hx
      rw [Finset.mem_union, Finset.mem_inter, Finset.mem_inter]
      by_cases hxA : x ∈ A₂
      · exact Or.inl ⟨hx, hxA⟩
      · by_cases hxS : x ∈ S₂
        · exact Or.inr ⟨hx, hxS⟩
        · exfalso
          have hxB2 : x ∈ B₂ := Finset.mem_compl.mpr (by simp [hxA, hxS])
          have : x ∈ B₁ ∩ B₂ := Finset.mem_inter.mpr ⟨hx, hxB2⟩
          rw [hB_empty] at this
          exact Finset.notMem_empty x this
    have hB2_sub : B₂ ⊆ (B₂ ∩ C₁) ∪ (B₂ ∩ S₁) := by
      intro x hx
      rw [Finset.mem_union, Finset.mem_inter, Finset.mem_inter]
      by_cases hxC : x ∈ C₁
      · exact Or.inl ⟨hx, hxC⟩
      · by_cases hxS : x ∈ S₁
        · exact Or.inr ⟨hx, hxS⟩
        · exfalso
          have hxB1 : x ∈ B₁ := Finset.mem_compl.mpr (by simp [hxC, hxS])
          have : x ∈ B₁ ∩ B₂ := Finset.mem_inter.mpr ⟨hxB1, hx⟩
          rw [hB_empty] at this
          exact Finset.notMem_empty x this
    obtain ⟨w, hw⟩ := hinter_ne
    have hB1A2_lt : (B₁ ∩ A₂).card < a := by
      have hss : B₁ ∩ A₂ ⊂ A₂ := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.inter_subset_right, fun heq => ?_⟩
        have hwA2 : w ∈ A₂ := (Finset.mem_inter.mp hw).2
        have hwB1 : w ∈ B₁ := (Finset.mem_inter.mp (heq.symm ▸ hwA2)).1
        simp only [B₁, Finset.mem_compl, Finset.mem_union] at hwB1
        exact hwB1 (Or.inl (Finset.mem_inter.mp hw).1)
      have := Finset.card_lt_card hss
      omega
    have hB2C1_lt : (B₂ ∩ C₁).card < a := by
      have hss : B₂ ∩ C₁ ⊂ C₁ := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.inter_subset_right, fun heq => ?_⟩
        have hwC1 : w ∈ C₁ := (Finset.mem_inter.mp hw).1
        have hwB2 : w ∈ B₂ := (Finset.mem_inter.mp (heq.symm ▸ hwC1)).1
        simp only [B₂, Finset.mem_compl, Finset.mem_union] at hwB2
        exact hwB2 (Or.inl (Finset.mem_inter.mp hw).2)
      have := Finset.card_lt_card hss
      omega
    have hB1S2_pos : 1 ≤ (B₁ ∩ S₂).card := by
      have h1 := Finset.card_le_card hB1_sub
      have h2 := Finset.card_union_le (B₁ ∩ A₂) (B₁ ∩ S₂)
      omega
    have hB2S1_pos : 1 ≤ (B₂ ∩ S₁).card := by
      have h1 := Finset.card_le_card hB2_sub
      have h2 := Finset.card_union_le (B₂ ∩ C₁) (B₂ ∩ S₁)
      omega
    have hdisj_T' : Disjoint (B₁ ∩ S₂) (B₂ ∩ S₁) := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      have hb1 := (Finset.mem_inter.mp hx1).1
      simp only [B₁, Finset.mem_compl, Finset.mem_union] at hb1
      exact hb1 (Or.inr (Finset.mem_inter.mp hx2).2)
    have hsub_T' : (B₁ ∩ S₂) ∪ (B₂ ∩ S₁) ⊆ (B₁ ∩ S₂) ∪ (S₁ ∩ S₂) ∪ (B₂ ∩ S₁) := by
      intro x hx
      rw [Finset.mem_union] at hx ⊢
      rcases hx with h | h
      · exact Or.inl (Finset.mem_union.mpr (Or.inl h))
      · exact Or.inr h
    have hcT' := Finset.card_le_card hsub_T'
    rw [Finset.card_union_of_disjoint hdisj_T'] at hcT'
    omega
  have hcomp2_adj : ∀ (S : Finset V) (u : V), (comp G S u).card = 2 →
      ∀ s₁ ∈ comp G S u, ∀ s₂ ∈ comp G S u, s₁ ≠ s₂ → G.Adj s₁ s₂ := by
    intro S u hc s₁ hs₁ s₂ hs₂ hne
    have hs12 : comp G S u = {s₁, s₂} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      · rw [Finset.card_pair hne, hc]
    have hreach : ReachAvoid G S s₁ s₂ :=
      reachAvoid_trans (reachAvoid_symm (mem_comp_iff.mp hs₁)) (mem_comp_iff.mp hs₂)
    obtain ⟨p, hp⟩ := hreach
    cases p with
    | nil => exact absurd rfl hne
    | @cons _ w _ hs1w q =>
      have hw_in : w ∈ comp G S u :=
        comp_closed hs₁ hs1w (hp w (by simp [Walk.support_cons]))
      rw [hs12, Finset.mem_insert, Finset.mem_singleton] at hw_in
      rcases hw_in with rfl | rfl
      · exact absurd rfl hs1w.ne
      · exact hs1w
  obtain ⟨_, S₁, u₁, hS₁, hu₁, hA0_eq, hB₁⟩ := Finset.mem_filter.mp hA0_mem
  have hA1_card : (comp G S₁ u₁).card = a := by rw [← hA0_eq]
  obtain ⟨s₁, hs₁⟩ := Finset.card_pos.mp (by omega : 0 < S₁.card)
  obtain ⟨φ, hφ⟩ := htrans u₁ s₁
  let S₂ := S₁.map φ.toEquiv.toEmbedding
  have hS₂ : S₂.card = 2 := by rw [Finset.card_map, hS₁]
  have hs₁_not_S₂ : s₁ ∉ S₂ := by
    intro hm
    rw [Finset.mem_map] at hm
    obtain ⟨z, hz, hzs⟩ := hm
    have : z = u₁ := φ.injective (hzs.trans hφ.symm)
    exact hu₁ (this ▸ hz)
  have hA2_eq : comp G S₂ s₁ = (comp G S₁ u₁).map φ.toEquiv.toEmbedding := by
    rw [← hφ]; exact comp_iso φ
  have hA2_card : (comp G S₂ s₁).card = a := by rw [hA2_eq, Finset.card_map, hA1_card]
  have hB₂ : ((comp G S₂ s₁ ∪ S₂)ᶜ).Nonempty := by
    obtain ⟨b, hb⟩ := hB₁
    refine ⟨φ b, Finset.mem_compl.mpr ?_⟩
    simp only [hA2_eq, S₂, Finset.mem_union, Finset.mem_map, Equiv.coe_toEmbedding]
    rintro (⟨z, hz, hzb⟩ | ⟨z, hz, hzb⟩)
    · have : z = b := φ.injective hzb
      exact (Finset.mem_compl.mp hb) (Finset.mem_union.mpr (Or.inl (hA0_eq.symm ▸ this ▸ hz)))
    · have : z = b := φ.injective hzb
      exact (Finset.mem_compl.mp hb) (Finset.mem_union.mpr (Or.inr (this ▸ hz)))
  have hB₁' : ((comp G S₁ u₁ ∪ S₁)ᶜ).Nonempty := hA0_eq ▸ hB₁
  have hne12 : comp G S₁ u₁ ≠ comp G S₂ s₁ := by
    intro heq
    have hs1_in : s₁ ∈ comp G S₁ u₁ := heq.symm ▸ self_mem_comp hs₁_not_S₂
    exact (Finset.disjoint_left.mp comp_disjoint hs1_in) hs₁
  have hdisj12 : Disjoint (comp G S₁ u₁) (comp G S₂ s₁) :=
    hatom_disj hS₁ hS₂ hu₁ hs₁_not_S₂ hB₁' hB₂ hA1_card hA2_card hne12
  by_cases hsub : comp G S₂ s₁ ⊆ S₁
  · have ha2 : a = 2 := by
      have := Finset.card_le_card hsub
      omega
    have heq_S1 : comp G S₂ s₁ = S₁ := Finset.eq_of_subset_of_card_le hsub (by omega)
    exact no_atom_eq_cut G hconn hdeg3 hreg hS₁ rfl (by omega) hB₁' (fun x hx y hy hxy =>
      hcomp2_adj S₂ s₁ (by omega) x (heq_S1.symm ▸ hx) y (heq_S1.symm ▸ hy) hxy)
  · rw [Finset.not_subset] at hsub
    obtain ⟨w, hwA2, hwS1⟩ := hsub
    have hwC1 : w ∉ comp G S₁ u₁ := Finset.disjoint_right.mp hdisj12 hwA2
    let C := comp G S₁ w
    have hC_disj_A1 : Disjoint C (comp G S₁ u₁) := by
      rw [Finset.disjoint_left]
      intro z hzC hzA1
      exact hwC1 (comp_eq_of_mem hzA1 ▸ mem_comp_iff.mpr (reachAvoid_symm (mem_comp_iff.mp hzC)))
    have hD1_ne : ((C ∪ S₁)ᶜ).Nonempty := by
      refine ⟨u₁, Finset.mem_compl.mpr ?_⟩
      simp only [Finset.mem_union]
      rintro (hm | hm)
      · exact Finset.disjoint_left.mp hC_disj_A1 hm (self_mem_comp hu₁)
      · exact hu₁ hm
    have hinter_ne : (C ∩ comp G S₂ s₁).Nonempty :=
      ⟨w, Finset.mem_inter.mpr ⟨self_mem_comp hwS1, hwA2⟩⟩
    have hinter_lt : (C ∩ comp G S₂ s₁).card < a := by
      have hss : C ∩ comp G S₂ s₁ ⊂ comp G S₂ s₁ := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.inter_subset_right, fun heq => ?_⟩
        have hs1_in_C : s₁ ∈ C := (Finset.mem_inter.mp (heq.symm ▸ self_mem_comp hs₁_not_S₂)).1
        exact (Finset.disjoint_left.mp comp_disjoint hs1_in_C) hs₁
      have := Finset.card_lt_card hss
      omega
    have ⟨_, hDB_empty⟩ := watkins_submod G h2c a hmin hS₁ hS₂ hD1_ne hinter_ne hinter_lt
    have hA1_sub_S2 : comp G S₁ u₁ ⊆ S₂ := by
      intro z hzA1
      have hzD1 : z ∈ (C ∪ S₁)ᶜ := by
        refine Finset.mem_compl.mpr ?_
        simp only [Finset.mem_union]
        rintro (hzC | hzS1)
        · exact Finset.disjoint_left.mp hC_disj_A1 hzC hzA1
        · exact Finset.disjoint_left.mp comp_disjoint hzA1 hzS1
      have hzA2 : z ∉ comp G S₂ s₁ := Finset.disjoint_left.mp hdisj12 hzA1
      by_contra hzS2
      have hzB2 : z ∈ (comp G S₂ s₁ ∪ S₂)ᶜ := Finset.mem_compl.mpr (by simp [hzA2, hzS2])
      have : z ∈ (C ∪ S₁)ᶜ ∩ (comp G S₂ s₁ ∪ S₂)ᶜ := Finset.mem_inter.mpr ⟨hzD1, hzB2⟩
      rw [hDB_empty] at this
      exact Finset.notMem_empty z this
    have ha2 : a = 2 := by
      have := Finset.card_le_card hA1_sub_S2
      omega
    have heq_S2 : comp G S₁ u₁ = S₂ := Finset.eq_of_subset_of_card_le hA1_sub_S2 (by omega)
    exact no_atom_eq_cut G hconn hdeg3 hreg hS₂ rfl (by omega) hB₂ (fun x hx y hy hxy =>
      hcomp2_adj S₁ u₁ (by omega) x (heq_S2.symm ▸ hx) y (heq_S2.symm ▸ hy) hxy)

end Connectivity

/- ### Section 4: Menger's theorem for k = 2 (Göring's edge-deletion induction) -/

section MengerTwo

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma isPath_append_of_meet_mid {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) (hp : p.IsPath) (hq : q.IsPath)
    (hmeet : ∀ x, x ∈ p.support → x ∈ q.support → x = v) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append]
  refine ⟨hp.support_nodup, hq.support_nodup.sublist (List.tail_sublist _), ?_⟩
  intro x hxp y hyq hxy
  subst hxy
  have hvx : x = v := hmeet x hxp (List.mem_of_mem_tail hyq)
  subst hvx
  have hnd := hq.support_nodup
  cases hqs : q.support with
  | nil => exact absurd hqs (Walk.support_ne_nil q)
  | cons a l =>
    have ha : a = x := by
      have := Walk.head_support q
      simp [hqs] at this
      exact this
    rw [hqs, List.tail_cons] at hyq
    rw [hqs, ha, List.nodup_cons] at hnd
    exact hnd.1 hyq

private lemma transfer_to_deleteEdge {G : SimpleGraph V} {a b u v : V}
    (p : G.Walk a b) (he : s(u, v) ∉ p.edges) :
    ∃ q : (G.deleteEdges {s(u, v)}).Walk a b, q.support = p.support := by
  refine ⟨p.transfer (G.deleteEdges {s(u, v)}) ?_, Walk.support_transfer _ _⟩
  intro e hem
  have hG : e ∈ G.edgeSet := p.edges_subset_edgeSet hem
  rcases e with ⟨x, y⟩
  change (G.deleteEdges {s(u, v)}).Adj x y
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨hG, ?_⟩
  intro hmem
  rw [Set.mem_singleton_iff] at hmem
  exact he (hmem ▸ hem)

private lemma transfer_from_deleteEdge {G : SimpleGraph V} {a b u v : V}
    (p : (G.deleteEdges {s(u, v)}).Walk a b) :
    ∃ q : G.Walk a b, q.support = p.support ∧ (p.IsPath → q.IsPath) := by
  refine ⟨p.transfer G ?_, Walk.support_transfer _ _, fun hp => ?_⟩
  · intro e hem
    have hG' := p.edges_subset_edgeSet hem
    rcases e with ⟨x, y⟩
    exact (SimpleGraph.deleteEdges_adj.mp hG').1
  · rw [Walk.isPath_def, Walk.support_transfer]
    exact hp.support_nodup

private lemma split_path_at_edge {G : SimpleGraph V} {a b u v : V}
    (p : G.Walk a b) (hp : p.IsPath) (he : s(u, v) ∈ p.edges) :
    (∃ (p₁ : (G.deleteEdges {s(u, v)}).Walk a u) (p₂ : (G.deleteEdges {s(u, v)}).Walk v b),
      (∀ x ∈ p₁.support, x ∈ p.support) ∧ (∀ x ∈ p₂.support, x ∈ p.support)) ∨
    (∃ (p₁ : (G.deleteEdges {s(u, v)}).Walk a v) (p₂ : (G.deleteEdges {s(u, v)}).Walk u b),
      (∀ x ∈ p₁.support, x ∈ p.support) ∧ (∀ x ∈ p₂.support, x ∈ p.support)) := by
  induction p with
  | nil => simp at he
  | @cons a c b hac q ih =>
    rw [Walk.edges_cons, List.mem_cons] at he
    by_cases hcur : s(a, c) = s(u, v)
    · have hnot_q : s(u, v) ∉ q.edges := by
        have ht := hp.isTrail
        rw [Walk.isTrail_cons] at ht
        rw [← hcur]
        exact ht.2
      obtain ⟨q', hq's⟩ := transfer_to_deleteEdge q hnot_q
      rw [Sym2.eq_iff] at hcur
      rcases hcur with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · left
        refine ⟨Walk.nil, q', fun x hx => ?_, fun x hx => ?_⟩
        · simp only [Walk.support_nil, List.mem_singleton] at hx
          subst hx; simp [Walk.support_cons]
        · rw [hq's] at hx; simp [Walk.support_cons, hx]
      · right
        refine ⟨Walk.nil, q', fun x hx => ?_, fun x hx => ?_⟩
        · simp only [Walk.support_nil, List.mem_singleton] at hx
          subst hx; simp [Walk.support_cons]
        · rw [hq's] at hx; simp [Walk.support_cons, hx]
    · have heq : s(u, v) ∈ q.edges := he.resolve_left (Ne.symm hcur)
      have hac' : (G.deleteEdges {s(u, v)}).Adj a c := by
        rw [SimpleGraph.deleteEdges_adj]
        exact ⟨hac, by simpa using hcur⟩
      rcases ih hp.of_cons heq with ⟨p₁, p₂, h1, h2⟩ | ⟨p₁, p₂, h1, h2⟩
      · left
        refine ⟨Walk.cons hac' p₁, p₂, fun x hx => ?_, fun x hx => ?_⟩
        · rw [Walk.support_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · simp [Walk.support_cons]
          · simp [Walk.support_cons, h1 x hx]
        · simp [Walk.support_cons, h2 x hx]
      · right
        refine ⟨Walk.cons hac' p₁, p₂, fun x hx => ?_, fun x hx => ?_⟩
        · rw [Walk.support_cons, List.mem_cons] at hx
          rcases hx with rfl | hx
          · simp [Walk.support_cons]
          · simp [Walk.support_cons, h1 x hx]
        · simp [Walk.support_cons, h2 x hx]

private lemma reachAvoid_prefix_mem {G : SimpleGraph V} {S T : Finset V} {a b : V}
    (p : G.Walk a b) (hpT : ∀ x ∈ p.support, x ∉ T)
    (hS : ∃ w ∈ p.support, w ∈ S) :
    ∃ w ∈ S, ReachAvoid G T a w := by
  obtain ⟨w, hwp, hwS⟩ := hS
  refine ⟨w, hwS, p.takeUntil w hwp, fun x hx => hpT x (Walk.support_takeUntil_subset_support p hwp hx)⟩

private lemma reachAvoid_suffix_mem {G : SimpleGraph V} {S T : Finset V} {a b : V}
    (p : G.Walk a b) (hpT : ∀ x ∈ p.support, x ∉ T)
    (hS : ∃ w ∈ p.support, w ∈ S) :
    ∃ w ∈ S, ReachAvoid G T w b := by
  obtain ⟨w, hwp, hwS⟩ := hS
  refine ⟨w, hwS, p.dropUntil w hwp, fun x hx => hpT x (Walk.support_dropUntil_subset_support p hwp hx)⟩

private lemma menger_two_step {G : SimpleGraph V} {A B S : Finset V} {u v a0 b0 : V}
    (huv : G.Adj u v) (hS_le : S.card ≤ 1)
    (hsep : ∀ a ∈ A, ∀ b ∈ B, ¬ ReachAvoid (G.deleteEdges {s(u, v)}) S a b)
    (ha0 : a0 ∈ A) (hb0 : b0 ∈ B)
    (hau : ReachAvoid (G.deleteEdges {s(u, v)}) S a0 u)
    (hvb : ReachAvoid (G.deleteEdges {s(u, v)}) S v b0)
    (ih1 :
      (∃ (a₁ a₂ b₁ b₂ : V) (p₁ : (G.deleteEdges {s(u, v)}).Walk a₁ b₁)
          (p₂ : (G.deleteEdges {s(u, v)}).Walk a₂ b₂),
        a₁ ∈ A ∧ a₂ ∈ A ∧ b₁ ∈ insert u S ∧ b₂ ∈ insert u S ∧
        p₁.IsPath ∧ p₂.IsPath ∧ List.Disjoint p₁.support p₂.support) ∨
      (∃ T : Finset V, T.card ≤ 1 ∧ ∀ a ∈ A, ∀ b ∈ insert u S, ¬ ReachAvoid (G.deleteEdges {s(u, v)}) T a b))
    (ih2 :
      (∃ (a₁ a₂ b₁ b₂ : V) (p₁ : (G.deleteEdges {s(u, v)}).Walk a₁ b₁)
          (p₂ : (G.deleteEdges {s(u, v)}).Walk a₂ b₂),
        a₁ ∈ insert v S ∧ a₂ ∈ insert v S ∧ b₁ ∈ B ∧ b₂ ∈ B ∧
        p₁.IsPath ∧ p₂.IsPath ∧ List.Disjoint p₁.support p₂.support) ∨
      (∃ T : Finset V, T.card ≤ 1 ∧ ∀ a ∈ insert v S, ∀ b ∈ B, ¬ ReachAvoid (G.deleteEdges {s(u, v)}) T a b)) :
    (∃ (a₁ a₂ b₁ b₂ : V) (p₁ : G.Walk a₁ b₁) (p₂ : G.Walk a₂ b₂),
      a₁ ∈ A ∧ a₂ ∈ A ∧ b₁ ∈ B ∧ b₂ ∈ B ∧
      p₁.IsPath ∧ p₂.IsPath ∧ List.Disjoint p₁.support p₂.support) ∨
    (∃ T : Finset V, T.card ≤ 1 ∧ ∀ a ∈ A, ∀ b ∈ B, ¬ ReachAvoid G T a b) := by
  let G' := G.deleteEdges {s(u, v)}
  have huS : u ∉ S := reachAvoid_right_not_mem hau
  have hvS : v ∉ S := reachAvoid_left_not_mem hvb
  have hno_Av : ∀ a ∈ A, ¬ ReachAvoid G' S a v := fun a ha hav => hsep a ha b0 hb0 (reachAvoid_trans hav hvb)
  have hno_uB : ∀ b ∈ B, ¬ ReachAvoid G' S u b := fun b hb hub => hsep a0 ha0 b hb (reachAvoid_trans hau hub)
  -- Case 1: T separates A from insert u S in G' -> T separates A from B in G
  rcases ih1 with hleft1 | ⟨T, hT1, hTsep⟩
  · -- Case 2: T separates insert v S from B in G' -> T separates A from B in G
    rcases ih2 with hleft2 | ⟨T, hT1, hTsep⟩
    · -- Both sides have 2 disjoint paths!
      obtain ⟨a₁, a₂, x₁, x₂, p₁, p₂, ha₁, ha₂, hx₁, hx₂, hp₁, hp₂, hdisj_p⟩ := hleft1
      obtain ⟨y₁, y₂, b₁, b₂, q₁, q₂, hy₁, hy₂, hb₁, hb₂, hq₁, hq₂, hdisj_q⟩ := hleft2
      have hx_ne : x₁ ≠ x₂ := fun h => hdisj_p (Walk.end_mem_support p₁) (h ▸ Walk.end_mem_support p₂)
      have hy_ne : y₁ ≠ y₂ := fun h => hdisj_q (Walk.start_mem_support q₁) (h ▸ Walk.start_mem_support q₂)
      -- Since x₁ ≠ x₂ ∈ insert u S and S.card ≤ 1, S = {w} for some w ≠ u, w ≠ v
      have hS_pos : 1 ≤ S.card := by
        by_contra h0
        have hSe : S = ∅ := Finset.card_eq_zero.mp (by omega)
        rw [hSe] at hx₁ hx₂
        simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at hx₁ hx₂
        exact hx_ne (hx₁.trans hx₂.symm)
      have hS_eq1 : S.card = 1 := by omega
      obtain ⟨w, hSw⟩ := Finset.card_eq_one.mp hS_eq1
      have hwu : w ≠ u := fun h => huS (hSw.symm ▸ h ▸ Finset.mem_singleton_self w)
      have hwv : w ≠ v := fun h => hvS (hSw.symm ▸ h ▸ Finset.mem_singleton_self w)
      -- Helper: combine ordered pairs (pW ends at w, pU ends at u) and (qW starts at w, qV starts at v)
      have hcombine : ∀ {aW aU bW bV : V}
          (pW : G'.Walk aW w) (pU : G'.Walk aU u) (qW : G'.Walk w bW) (qV : G'.Walk v bV),
          aW ∈ A → aU ∈ A → bW ∈ B → bV ∈ B →
          pW.IsPath → pU.IsPath → qW.IsPath → qV.IsPath →
          List.Disjoint pW.support pU.support → List.Disjoint qW.support qV.support →
          ∃ (a₁' a₂' b₁' b₂' : V) (P₁ : G.Walk a₁' b₁') (P₂ : G.Walk a₂' b₂'),
            a₁' ∈ A ∧ a₂' ∈ A ∧ b₁' ∈ B ∧ b₂' ∈ B ∧
            P₁.IsPath ∧ P₂.IsPath ∧ List.Disjoint P₁.support P₂.support := by
        intro aW aU bW bV pW pU qW qV haW haU hbW hbV hpW hpU hqW hqV hdp hdq
        have hreach_pW : ∀ z ∈ pW.support, z ≠ w → ReachAvoid G' S aW z := by
          intro z hzp hzw
          refine ⟨pW.takeUntil z hzp, fun y hy => ?_⟩
          rw [hSw, Finset.mem_singleton]
          rintro rfl
          exact Walk.endpoint_notMem_support_takeUntil hpW hzp hzw.symm hy
        have hreach_pU : ∀ z ∈ pU.support, ReachAvoid G' S aU z := by
          intro z hzp
          refine ⟨pU.takeUntil z hzp, fun y hy => ?_⟩
          rw [hSw, Finset.mem_singleton]
          rintro rfl
          exact hdp (Walk.end_mem_support pW) (Walk.support_takeUntil_subset_support pU hzp hy)
        have hreach_qW : ∀ z ∈ qW.support, z ≠ w → ReachAvoid G' S z bW := by
          intro z hzq hzw
          refine ⟨qW.dropUntil z hzq, fun y hy => ?_⟩
          rw [hSw, Finset.mem_singleton]
          intro hyw
          have hw_in : w ∈ (qW.dropUntil z hzq).support := hyw ▸ hy
          have hspec := Walk.take_spec qW hzq
          have hnd := hqW.support_nodup
          rw [← hspec, Walk.support_append, List.nodup_append] at hnd
          have hw_take : w ∈ (qW.takeUntil z hzq).support := Walk.start_mem_support _
          cases hds : (qW.dropUntil z hzq).support with
          | nil => exact absurd hds (Walk.support_ne_nil _)
          | cons d l =>
            have hd : d = z := by
              have := Walk.head_support (qW.dropUntil z hzq)
              simp [hds] at this
              exact this
            rw [hds, List.mem_cons] at hw_in
            rcases hw_in with hwd | hwl
            · exact hzw (hd.symm.trans hwd.symm)
            · exact hnd.2.2 w hw_take w (by rw [hds, List.tail_cons]; exact hwl) rfl
        have hreach_qV : ∀ z ∈ qV.support, ReachAvoid G' S z bV := by
          intro z hzq
          refine ⟨qV.dropUntil z hzq, fun y hy => ?_⟩
          rw [hSw, Finset.mem_singleton]
          rintro rfl
          exact hdq (Walk.start_mem_support qW) (Walk.support_dropUntil_subset_support qV hzq hy)
        -- Key cross-disjointness facts
        have hmeet_W : ∀ z, z ∈ pW.support → z ∈ qW.support → z = w := by
          intro z hzp hzq
          by_contra hzw
          exact hsep aW haW bW hbW (reachAvoid_trans (hreach_pW z hzp hzw) (hreach_qW z hzq hzw))
        have hdisj_pWqV : List.Disjoint pW.support qV.support := by
          intro z hzp hzq
          by_cases hzw : z = w
          · subst hzw; exact hdq (Walk.start_mem_support qW) hzq
          · exact hsep aW haW bV hbV (reachAvoid_trans (hreach_pW z hzp hzw) (hreach_qV z hzq))
        have hdisj_pUqW : List.Disjoint pU.support qW.support := by
          intro z hzp hzq
          by_cases hzw : z = w
          · subst hzw; exact hdp (Walk.end_mem_support pW) hzp
          · exact hsep aU haU bW hbW (reachAvoid_trans (hreach_pU z hzp) (hreach_qW z hzq hzw))
        have hdisj_pUqV : List.Disjoint pU.support qV.support := by
          intro z hzp hzq
          exact hsep aU haU bV hbV (reachAvoid_trans (hreach_pU z hzp) (hreach_qV z hzq))
        -- Lift paths to G and glue!
        obtain ⟨pW_G, hpW_s, hpW_p⟩ := transfer_from_deleteEdge pW
        obtain ⟨pU_G, hpU_s, hpU_p⟩ := transfer_from_deleteEdge pU
        obtain ⟨qW_G, hqW_s, hqW_p⟩ := transfer_from_deleteEdge qW
        obtain ⟨qV_G, hqV_s, hqV_p⟩ := transfer_from_deleteEdge qV
        let P₁ : G.Walk aW bW := pW_G.append qW_G
        let P₂ : G.Walk aU bV := pU_G.append (Walk.cons huv qV_G)
        have hP₁ : P₁.IsPath := isPath_append_of_meet_mid pW_G qW_G (hpW_p hpW) (hqW_p hqW)
          (fun z hz1 hz2 => hmeet_W z (hpW_s ▸ hz1) (hqW_s ▸ hz2))
        have hP₂ : P₂.IsPath := by
          have hcons_qV : (Walk.cons huv qV_G).IsPath := by
            rw [Walk.cons_isPath_iff]
            refine ⟨hqV_p hqV, fun huq => ?_⟩
            exact hdisj_pUqV (Walk.end_mem_support pU) (hqV_s ▸ huq)
          refine isPath_append_of_meet_mid pU_G (Walk.cons huv qV_G) (hpU_p hpU) hcons_qV ?_
          intro z hz1 hz2
          rw [Walk.support_cons, List.mem_cons] at hz2
          rcases hz2 with rfl | hz2
          · rfl
          · exact absurd (hqV_s ▸ hz2) (hdisj_pUqV (hpU_s ▸ hz1))
        have hdisj_P : List.Disjoint P₁.support P₂.support := by
          intro z hz1 hz2
          have hz1' := (Walk.mem_support_append_iff pW_G qW_G).mp hz1
          have hz2' := (Walk.mem_support_append_iff pU_G (Walk.cons huv qV_G)).mp hz2
          rcases hz1' with hzW | hzW <;> rcases hz2' with hzU | hzV
          · exact hdp (hpW_s ▸ hzW) (hpU_s ▸ hzU)
          · rw [Walk.support_cons, List.mem_cons] at hzV
            rcases hzV with rfl | hzV
            · exact hdp (hpW_s ▸ hzW) (Walk.end_mem_support pU)
            · exact hdisj_pWqV (hpW_s ▸ hzW) (hqV_s ▸ hzV)
          · exact hdisj_pUqW (hpU_s ▸ hzU) (hqW_s ▸ hzW)
          · rw [Walk.support_cons, List.mem_cons] at hzV
            rcases hzV with rfl | hzV
            · exact hdisj_pUqW (Walk.end_mem_support pU) (hqW_s ▸ hzW)
            · exact hdq (hqW_s ▸ hzW) (hqV_s ▸ hzV)
        exact ⟨aW, aU, bW, bV, P₁, P₂, haW, haU, hbW, hbV, hP₁, hP₂, hdisj_P⟩
      -- Match the 4 permutations of (x₁, x₂) and (y₁, y₂)
      rw [hSw, Finset.mem_insert, Finset.mem_singleton] at hx₁ hx₂ hy₁ hy₂
      left
      rcases hx₁ with rfl | rfl <;> rcases hx₂ with rfl | rfl
      · exact absurd rfl hx_ne
      · rcases hy₁ with rfl | rfl <;> rcases hy₂ with rfl | rfl
        · exact absurd rfl hy_ne
        · exact hcombine p₂ p₁ q₂ q₁ ha₂ ha₁ hb₂ hb₁ hp₂ hp₁ hq₂ hq₁ hdisj_p.symm hdisj_q.symm
        · exact hcombine p₂ p₁ q₁ q₂ ha₂ ha₁ hb₁ hb₂ hp₂ hp₁ hq₁ hq₂ hdisj_p.symm hdisj_q
        · exact absurd rfl hy_ne
      · rcases hy₁ with rfl | rfl <;> rcases hy₂ with rfl | rfl
        · exact absurd rfl hy_ne
        · exact hcombine p₁ p₂ q₂ q₁ ha₁ ha₂ hb₂ hb₁ hp₁ hp₂ hq₂ hq₁ hdisj_p hdisj_q.symm
        · exact hcombine p₁ p₂ q₁ q₂ ha₁ ha₂ hb₁ hb₂ hp₁ hp₂ hq₁ hq₂ hdisj_p hdisj_q
        · exact absurd rfl hy_ne
      · exact absurd rfl hx_ne
    · -- T separates insert v S from B in G' -> T separates A from B in G
      right
      refine ⟨T, hT1, fun a ha b hb hr => ?_⟩
      obtain ⟨p, hpT⟩ := hr
      let q := p.toPath
      have hqT : ∀ x ∈ q.1.support, x ∉ T := fun x hx => hpT x (Walk.support_toPath_subset_support p hx)
      by_cases he : s(u, v) ∈ q.1.edges
      · rcases split_path_at_edge q.1 q.2 he with ⟨_, q₂, _, h2⟩ | ⟨_, q₂, _, h2⟩
        · exact hTsep v (Finset.mem_insert_self v S) b hb ⟨q₂, fun x hx => hqT x (h2 x hx)⟩
        · have hhits : ∃ w ∈ q₂.support, w ∈ S := by
            by_contra hnone
            push Not at hnone
            exact hno_uB b hb ⟨q₂, hnone⟩
          obtain ⟨w, hwS, hrw⟩ := reachAvoid_suffix_mem q₂ (fun x hx => hqT x (h2 x hx)) hhits
          exact hTsep w (Finset.mem_insert_of_mem hwS) b hb hrw
      · obtain ⟨q', hq's⟩ := transfer_to_deleteEdge q.1 he
        have hhits : ∃ w ∈ q'.support, w ∈ S := by
          by_contra hnone
          push Not at hnone
          exact hsep a ha b hb ⟨q', hnone⟩
        obtain ⟨w, hwS, hrw⟩ := reachAvoid_suffix_mem q' (fun x hx => hqT x (hq's ▸ hx)) hhits
        exact hTsep w (Finset.mem_insert_of_mem hwS) b hb hrw
  · -- T separates A from insert u S in G' -> T separates A from B in G
    right
    refine ⟨T, hT1, fun a ha b hb hr => ?_⟩
    obtain ⟨p, hpT⟩ := hr
    let q := p.toPath
    have hqT : ∀ x ∈ q.1.support, x ∉ T := fun x hx => hpT x (Walk.support_toPath_subset_support p hx)
    by_cases he : s(u, v) ∈ q.1.edges
    · rcases split_path_at_edge q.1 q.2 he with ⟨q₁, _, h1, _⟩ | ⟨q₁, _, h1, _⟩
      · exact hTsep a ha u (Finset.mem_insert_self u S) ⟨q₁, fun x hx => hqT x (h1 x hx)⟩
      · have hhits : ∃ w ∈ q₁.support, w ∈ S := by
          by_contra hnone
          push Not at hnone
          exact hno_Av a ha ⟨q₁, hnone⟩
        obtain ⟨w, hwS, hrw⟩ := reachAvoid_prefix_mem q₁ (fun x hx => hqT x (h1 x hx)) hhits
        exact hTsep a ha w (Finset.mem_insert_of_mem hwS) hrw
    · obtain ⟨q', hq's⟩ := transfer_to_deleteEdge q.1 he
      have hhits : ∃ w ∈ q'.support, w ∈ S := by
        by_contra hnone
        push Not at hnone
        exact hsep a ha b hb ⟨q', hnone⟩
      obtain ⟨w, hwS, hrw⟩ := reachAvoid_prefix_mem q' (fun x hx => hqT x (hq's ▸ hx)) hhits
      exact hTsep a ha w (Finset.mem_insert_of_mem hwS) hrw

lemma menger_two_aux (m : ℕ) :
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.edgeFinset.card ≤ m → ∀ (A B : Finset V),
      (∃ (a₁ a₂ b₁ b₂ : V) (p₁ : G.Walk a₁ b₁) (p₂ : G.Walk a₂ b₂),
        a₁ ∈ A ∧ a₂ ∈ A ∧ b₁ ∈ B ∧ b₂ ∈ B ∧
        p₁.IsPath ∧ p₂.IsPath ∧ List.Disjoint p₁.support p₂.support) ∨
      (∃ S : Finset V, S.card ≤ 1 ∧ ∀ a ∈ A, ∀ b ∈ B, ¬ ReachAvoid G S a b) := by
  classical
  induction m with
  | zero =>
    intro G _ hcard A B
    have hemp : G.edgeFinset = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
    by_cases h2 : 2 ≤ (A ∩ B).card
    · obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < (A ∩ B).card)
      left
      refine ⟨x, y, x, y, Walk.nil, Walk.nil, (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hy).1,
        (Finset.mem_inter.mp hx).2, (Finset.mem_inter.mp hy).2, Walk.IsPath.nil, Walk.IsPath.nil, ?_⟩
      intro z hz1 hz2
      simp only [Walk.support_nil, List.mem_singleton] at hz1 hz2
      exact hxy (hz1.symm.trans hz2)
    · right
      refine ⟨A ∩ B, by omega, fun a ha b hb ⟨p, hp⟩ => ?_⟩
      cases p with
      | nil => exact hp a (by simp) (Finset.mem_inter.mpr ⟨ha, hb⟩)
      | @cons _ c _ hac _ =>
        have hmem : s(a, c) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hac
        rw [hemp] at hmem
        exact Finset.notMem_empty _ hmem
  | succ m ih =>
    intro G _ hcard A B
    by_cases hemp : G.edgeFinset = ∅
    · exact ih G (by rw [hemp]; simp) A B
    · obtain ⟨e, he_mem⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
      rcases e with ⟨u, v⟩
      have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he_mem
      let G' := G.deleteEdges {s(u, v)}
      have hcard' : G'.edgeFinset.card ≤ m := by
        have hss : G'.edgeFinset ⊂ G.edgeFinset := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨fun x hx => ?_, fun heq => ?_⟩
          · rcases x with ⟨x1, x2⟩
            rw [SimpleGraph.mem_edgeFinset] at hx ⊢
            exact (SimpleGraph.deleteEdges_adj.mp hx).1
          · have hmem' : s(u, v) ∈ G'.edgeFinset := heq.symm ▸ he_mem
            rw [SimpleGraph.mem_edgeFinset] at hmem'
            exact (SimpleGraph.deleteEdges_adj.mp hmem').2 (Set.mem_singleton _)
        have := Finset.card_lt_card hss
        omega
      rcases ih G' hcard' A B with ⟨a₁, a₂, b₁, b₂, p₁, p₂, ha₁, ha₂, hb₁, hb₂, hp₁, hp₂, hdisj⟩ | ⟨S, hS1, hsep⟩
      · left
        obtain ⟨q₁, hq₁s, hq₁p⟩ := transfer_from_deleteEdge p₁
        obtain ⟨q₂, hq₂s, hq₂p⟩ := transfer_from_deleteEdge p₂
        exact ⟨a₁, a₂, b₁, b₂, q₁, q₂, ha₁, ha₂, hb₁, hb₂, hq₁p hp₁, hq₂p hp₂, by rwa [hq₁s, hq₂s]⟩
      · by_cases hsepG : ∀ a ∈ A, ∀ b ∈ B, ¬ ReachAvoid G S a b
        · exact Or.inr ⟨S, hS1, hsepG⟩
        · push Not at hsepG
          obtain ⟨a0, ha0, b0, hb0, ⟨p, hpS⟩⟩ := hsepG
          let q := p.toPath
          have hqS : ∀ x ∈ q.1.support, x ∉ S := fun x hx => hpS x (Walk.support_toPath_subset_support p hx)
          have he_in : s(u, v) ∈ q.1.edges := by
            by_contra hne
            obtain ⟨q', hq's⟩ := transfer_to_deleteEdge q.1 hne
            exact hsep a0 ha0 b0 hb0 ⟨q', fun x hx => hqS x (hq's ▸ hx)⟩
          rcases split_path_at_edge q.1 q.2 he_in with ⟨q₁, q₂, h1, h2⟩ | ⟨q₁, q₂, h1, h2⟩
          · exact menger_two_step huv hS1 hsep ha0 hb0
              ⟨q₁, fun x hx => hqS x (h1 x hx)⟩ ⟨q₂, fun x hx => hqS x (h2 x hx)⟩
              (ih G' hcard' A (insert u S)) (ih G' hcard' (insert v S) B)
          · have hsym : G.deleteEdges {s(v, u)} = G' := by simp [G', Sym2.eq_swap]
            have hsep' : ∀ a ∈ A, ∀ b ∈ B, ¬ ReachAvoid (G.deleteEdges {s(v, u)}) S a b := hsym.symm ▸ hsep
            have hq1' : ReachAvoid (G.deleteEdges {s(v, u)}) S a0 v := hsym.symm ▸ ⟨q₁, fun x hx => hqS x (h1 x hx)⟩
            have hq2' : ReachAvoid (G.deleteEdges {s(v, u)}) S u b0 := hsym.symm ▸ ⟨q₂, fun x hx => hqS x (h2 x hx)⟩
            have hcard'' : (G.deleteEdges {s(v, u)}).edgeFinset.card ≤ m := by
              have heq_f : (G.deleteEdges {s(v, u)}).edgeFinset = G'.edgeFinset := by
                ext e; simp [SimpleGraph.mem_edgeFinset, hsym]
              rw [heq_f]; exact hcard'
            exact menger_two_step huv.symm hS1 hsep' ha0 hb0 hq1' hq2'
              (ih (G.deleteEdges {s(v, u)}) hcard'' A (insert v S))
              (ih (G.deleteEdges {s(v, u)}) hcard'' (insert u S) B)

lemma two_disjoint_paths_of_two_connected {G : SimpleGraph V} [DecidableRel G.Adj]
    (h2c : IsKConnected2 G) {A B : Finset V} (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) :
    ∃ (a₁ a₂ b₁ b₂ : V) (p₁ : G.Walk a₁ b₁) (p₂ : G.Walk a₂ b₂),
      a₁ ∈ A ∧ a₂ ∈ A ∧ b₁ ∈ B ∧ b₂ ∈ B ∧
      p₁.IsPath ∧ p₂.IsPath ∧ List.Disjoint p₁.support p₂.support := by
  rcases menger_two_aux G.edgeFinset.card G le_rfl A B with h | ⟨S, hS1, hsep⟩
  · exact h
  · exfalso
    have hA_ne : (A \ S).Nonempty := Finset.card_pos.mp (by
      have := Finset.card_sdiff_add_card_inter A S
      have : (A ∩ S).card ≤ S.card := Finset.card_le_card Finset.inter_subset_right
      omega)
    have hB_ne : (B \ S).Nonempty := Finset.card_pos.mp (by
      have := Finset.card_sdiff_add_card_inter B S
      have : (B ∩ S).card ≤ S.card := Finset.card_le_card Finset.inter_subset_right
      omega)
    obtain ⟨a, ha⟩ := hA_ne
    obtain ⟨b, hb⟩ := hB_ne
    rw [Finset.mem_sdiff] at ha hb
    exact h2c S hS1 ⟨a, b, ha.2, hb.2, hsep a ha.1 b hb.1⟩

end MengerTwo

/- ### Section 5: Cycle surgery and Babai's intersection lemma (|C₁ ∩ C₂| ≥ 3) -/

section CycleIntersection

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma isCycle_append_of_internally_disjoint {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (q : G.Walk v u) (hp : p.IsPath) (hq : q.IsPath) (huv : u ≠ v)
    (hinter : ∀ x, x ∈ p.support → x ∈ q.support → x = u ∨ x = v)
    (hlen : 3 ≤ p.length + q.length) :
    (p.append q).IsCycle := by
  rw [Walk.isCycle_def]
  have hne_nil : p.append q ≠ Walk.nil := by
    intro h
    have := congrArg Walk.length h
    rw [Walk.length_append, Walk.length_nil] at this
    omega
  -- Support tail nodup
  have hnodup_tail : (p.append q).support.tail.Nodup := by
    have hsup : (p.append q).support.tail = p.support.tail ++ q.support.tail := by
      rw [Walk.support_append]
      cases hps : p.support with
      | nil => exact absurd hps (Walk.support_ne_nil p)
      | cons a l => simp
    rw [hsup, List.nodup_append]
    refine ⟨hp.support_nodup.sublist (List.tail_sublist _), hq.support_nodup.sublist (List.tail_sublist _), ?_⟩
    intro x hxp y hyq hxy
    subst hxy
    rcases hinter x (List.mem_of_mem_tail hxp) (List.mem_of_mem_tail hyq) with rfl | rfl
    · have hnd := hp.support_nodup
      cases hps : p.support with
      | nil => exact absurd hps (Walk.support_ne_nil p)
      | cons a l =>
        have ha : a = x := by have := Walk.head_support p; simp [hps] at this; exact this
        rw [hps, List.tail_cons] at hxp
        rw [hps, ha, List.nodup_cons] at hnd
        exact hnd.1 hxp
    · have hnd := hq.support_nodup
      cases hqs : q.support with
      | nil => exact absurd hqs (Walk.support_ne_nil q)
      | cons a l =>
        have ha : a = x := by have := Walk.head_support q; simp [hqs] at this; exact this
        rw [hqs, List.tail_cons] at hyq
        rw [hqs, ha, List.nodup_cons] at hnd
        exact hnd.1 hyq
  -- Trail: edges of p and q are disjoint since length ≥ 3
  have htrail : (p.append q).IsTrail := by
    rw [Walk.isTrail_append]
    refine ⟨hp.isTrail, hq.isTrail, ?_⟩
    intro e hep heq
    rcases e with ⟨x, y⟩
    have hx_p : x ∈ p.support := Walk.fst_mem_support_of_mem_edges p hep
    have hy_p : y ∈ p.support := Walk.snd_mem_support_of_mem_edges p hep
    have hx_q : x ∈ q.support := Walk.fst_mem_support_of_mem_edges q heq
    have hy_q : y ∈ q.support := Walk.snd_mem_support_of_mem_edges q heq
    have hxy : x ≠ y := (p.edges_subset_edgeSet hep).ne
    have hse : s(x, y) = s(u, v) := by
      rcases hinter x hx_p hx_q with rfl | rfl <;> rcases hinter y hy_p hy_q with rfl | rfl
      · exact absurd rfl hxy
      · rfl
      · exact Sym2.eq_swap
      · exact absurd rfl hxy
    have hlen1 : ∀ {a b : V} (r : G.Walk a b), r.IsPath → s(a, b) ∈ r.edges → r.length = 1 := by
      intro a b r hr hmem
      cases r with
      | nil => simp at hmem
      | @cons a c b hac r' =>
        rw [Walk.edges_cons, List.mem_cons] at hmem
        rcases hmem with h1 | h2
        · rw [Sym2.eq_iff] at h1
          rcases h1 with ⟨_, rfl⟩ | ⟨hba, rfl⟩
          · cases r' with
            | nil => rfl
            | cons hbc r'' =>
              have hnd := hr.support_nodup
              simp only [Walk.support_cons, List.nodup_cons] at hnd
              exact absurd (Walk.end_mem_support _) (by
                have hnd2 := hr.of_cons.support_nodup
                simp only [Walk.support_cons, List.nodup_cons] at hnd2
                exact fun hm => hnd2.1 hm)
          · exact absurd hba hac.ne
        · have ha_in : a ∈ r'.support := Walk.fst_mem_support_of_mem_edges r' h2
          exact absurd ha_in ((Walk.cons_isPath_iff hac r').mp hr).2
    have hp1 : p.length = 1 := hlen1 p hp (hse ▸ hep)
    have hq1 : q.length = 1 := hlen1 q hq ((hse.trans Sym2.eq_swap) ▸ heq)
    omega
  exact ⟨htrail, hne_nil, hnodup_tail⟩

lemma cycle_split {G : SimpleGraph V} {w u v : V} (c : G.Walk w w) (hc : c.IsCycle)
    (hu : u ∈ c.support) (hv : v ∈ c.support) (huv : u ≠ v) :
    ∃ (p₁ p₂ : G.Walk u v),
      p₁.IsPath ∧ p₂.IsPath ∧ 1 ≤ p₁.length ∧ 1 ≤ p₂.length ∧
      p₁.length + p₂.length = c.length ∧
      (∀ x, x ∈ p₁.support → x ∈ p₂.support → x = u ∨ x = v) ∧
      (∀ x, x ∈ c.support ↔ x ∈ p₁.support ∨ x ∈ p₂.support) := by
  let c' := c.rotate u hu
  have hc' : c'.IsCycle := hc.rotate hu
  have hv' : v ∈ c'.support := (Walk.mem_support_rotate_iff c u hu).mpr hv
  let p₁ : G.Walk u v := c'.takeUntil v hv'
  let p₂ : G.Walk u v := (c'.dropUntil v hv').reverse
  have hp₁ : p₁.IsPath := hc'.isPath_takeUntil hv'
  have hspec : p₁.append (c'.dropUntil v hv') = c' := Walk.take_spec c' hv'
  have hp₂_rev : (c'.dropUntil v hv').IsPath := by
    have hne : ¬ p₁.Nil := by
      rw [Walk.nil_takeUntil]
      exact huv
    exact Walk.IsCycle.isPath_of_append_right hne (hspec.symm ▸ hc')
  have hp₂ : p₂.IsPath := hp₂_rev.reverse
  have hlen1 : 1 ≤ p₁.length := by
    cases h : p₁ with
    | nil => exact absurd rfl huv
    | cons _ _ => simp
  have hlen2 : 1 ≤ p₂.length := by
    cases h : p₂ with
    | nil => exact absurd rfl huv
    | cons _ _ => simp
  have hlen_sum : p₁.length + p₂.length = c.length := by
    have h1 := congrArg Walk.length hspec
    rw [Walk.length_append, Walk.length_rotate] at h1
    simpa [p₂, Walk.length_reverse] using h1
  have hinter : ∀ x, x ∈ p₁.support → x ∈ p₂.support → x = u ∨ x = v := by
    intro x hx1 hx2
    rw [Walk.support_reverse, List.mem_reverse] at hx2
    by_contra hne
    push Not at hne
    have hnd := hc'.support_nodup
    have hsup_tail : (p₁.append (c'.dropUntil v hv')).support.tail =
        p₁.support.tail ++ (c'.dropUntil v hv').support.tail := by
      rw [Walk.support_append]
      cases hps : p₁.support with
      | nil => exact absurd hps (Walk.support_ne_nil p₁)
      | cons a l => simp
    rw [hspec] at hsup_tail
    rw [hsup_tail, List.nodup_append] at hnd
    have hx1' : x ∈ p₁.support.tail := by
      cases hps : p₁.support with
      | nil => exact absurd hps (Walk.support_ne_nil p₁)
      | cons a l =>
        have ha : a = u := by have := Walk.head_support p₁; simp [hps] at this; exact this
        rw [hps, List.mem_cons] at hx1
        rcases hx1 with rfl | hx1
        · exact absurd ha hne.1
        · simpa [hps] using hx1
    have hx2' : x ∈ (c'.dropUntil v hv').support.tail := by
      cases hds : (c'.dropUntil v hv').support with
      | nil => exact absurd hds (Walk.support_ne_nil _)
      | cons a l =>
        have ha : a = v := by have := Walk.head_support (c'.dropUntil v hv'); simp [hds] at this; exact this
        rw [hds, List.mem_cons] at hx2
        rcases hx2 with rfl | hx2
        · exact absurd ha hne.2
        · simpa [hds] using hx2
    exact hnd.2.2 x hx1' x hx2' rfl
  have hmem : ∀ x, x ∈ c.support ↔ x ∈ p₁.support ∨ x ∈ p₂.support := by
    intro x
    rw [← Walk.mem_support_rotate_iff c u hu]
    change x ∈ c'.support ↔ _
    rw [← hspec, Walk.mem_support_append_iff]
    simp [p₂, Walk.support_reverse]
  exact ⟨p₁, p₂, hp₁, hp₂, hlen1, hlen2, hlen_sum, hinter, hmem⟩

/-- Trim a walk from `a` to `b ∈ B` to stop at its first hit in `B`. -/
private lemma trim_end_in {G : SimpleGraph V} {B : Finset V} {a b : V}
    (p : G.Walk a b) (hp : p.IsPath) (hb : b ∈ B) :
    ∃ (b' : V) (q : G.Walk a b'),
      b' ∈ B ∧ q.IsPath ∧ (∀ x ∈ q.support, x ∈ p.support) ∧
      (∀ x ∈ q.support, x ≠ b' → x ∉ B) := by
  induction p with
  | nil =>
    exact ⟨_, Walk.nil, hb, Walk.IsPath.nil, fun _ h => h, fun x hx hne => by
      simp only [Walk.support_nil, List.mem_singleton] at hx
      exact absurd hx hne⟩
  | @cons a c b hac r ih =>
    by_cases haB : a ∈ B
    · exact ⟨a, Walk.nil, haB, Walk.IsPath.nil, fun x hx => by
        simp only [Walk.support_nil, List.mem_singleton] at hx
        subst hx; simp [Walk.support_cons],
        fun x hx hne => by
          simp only [Walk.support_nil, List.mem_singleton] at hx
          exact absurd hx hne⟩
    · obtain ⟨b', q, hb'B, hq_path, hq_sub, hq_avoid⟩ := ih hp.of_cons hb
      have ha_not_q : a ∉ q.support := fun h =>
        ((Walk.cons_isPath_iff hac r).mp hp).2 (hq_sub a h)
      refine ⟨b', Walk.cons hac q, hb'B, (Walk.cons_isPath_iff hac q).mpr ⟨hq_path, ha_not_q⟩,
        fun x hx => ?_, fun x hx hne => ?_⟩
      · rw [Walk.support_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · simp [Walk.support_cons]
        · simp [Walk.support_cons, hq_sub x hx]
      · rw [Walk.support_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact haB
        · exact hq_avoid x hx hne

lemma trim_path_between_sets {G : SimpleGraph V} {A B : Finset V} {a b : V}
    (hdisj : Disjoint A B) (p : G.Walk a b) (hp : p.IsPath) (ha : a ∈ A) (hb : b ∈ B) :
    ∃ (a' b' : V) (q : G.Walk a' b'),
      a' ∈ A ∧ b' ∈ B ∧ q.IsPath ∧ 1 ≤ q.length ∧
      (∀ x ∈ q.support, x ∈ p.support) ∧
      (∀ x ∈ q.support, x ≠ a' → x ∉ A) ∧
      (∀ x ∈ q.support, x ≠ b' → x ∉ B) := by
  obtain ⟨b', q1, hb'B, hq1_path, hq1_sub, hq1_avoidB⟩ := trim_end_in p hp hb
  obtain ⟨a', q2rev, ha'A, hq2_path, hq2_sub, hq2_avoidA⟩ := trim_end_in q1.reverse hq1_path.reverse ha
  let q := q2rev.reverse
  have hq_path : q.IsPath := hq2_path.reverse
  have hq_sub : ∀ x ∈ q.support, x ∈ p.support := by
    intro x hx
    rw [Walk.support_reverse, List.mem_reverse] at hx
    have h1 := hq2_sub x hx
    rw [Walk.support_reverse, List.mem_reverse] at h1
    exact hq1_sub x h1
  have hab' : a' ≠ b' := fun h => Finset.disjoint_left.mp hdisj ha'A (h ▸ hb'B)
  have hlen : 1 ≤ q.length := by
    cases h : q with
    | nil => exact absurd rfl hab'
    | cons _ _ => simp
  refine ⟨a', b', q, ha'A, hb'B, hq_path, hlen, hq_sub, ?_, ?_⟩
  · intro x hx hne
    rw [Walk.support_reverse, List.mem_reverse] at hx
    exact hq2_avoidA x hx hne
  · intro x hx hne
    rw [Walk.support_reverse, List.mem_reverse] at hx
    have h1 := hq2_sub x hx
    rw [Walk.support_reverse, List.mem_reverse] at h1
    exact hq1_avoidB x h1 hne

lemma cycle_support_card_eq_length {G : SimpleGraph V} {w : V} (c : G.Walk w w) (hc : c.IsCycle) :
    c.support.toFinset.card = c.length := by
  have heq : c.support.toFinset = c.support.tail.toFinset := by
    ext x
    simp only [List.mem_toFinset]
    cases hsup : c.support with
    | nil => exact absurd hsup (Walk.support_ne_nil c)
    | cons a l =>
      have ha : a = w := by have := Walk.head_support c; simp [hsup] at this; exact this
      simp only [List.mem_cons, List.tail_cons]
      constructor
      · rintro (rfl | hx)
        · rw [ha]
          have := c.end_mem_tail_support hc.not_nil
          simpa [hsup] using this
        · exact hx
      · exact Or.inr
  rw [heq, List.toFinset_card_of_nodup hc.support_nodup]
  have := Walk.length_support c
  rw [List.length_tail]
  omega

lemma longest_cycles_inter_ge_three {G : SimpleGraph V} [DecidableRel G.Adj]
    (h3c : IsKConnected3 G) (k : ℕ)
    (hmax : ∀ (w : V) (c : G.Walk w w), c.IsCycle → c.length ≤ k)
    {w₁ w₂ : V} (c₁ : G.Walk w₁ w₁) (c₂ : G.Walk w₂ w₂)
    (hc₁ : c₁.IsCycle) (hc₂ : c₂.IsCycle)
    (hk₁ : c₁.length = k) (hk₂ : c₂.length = k) :
    3 ≤ (c₁.support.toFinset ∩ c₂.support.toFinset).card := by
  set V₁ := c₁.support.toFinset
  set V₂ := c₂.support.toFinset
  have hk3 : 3 ≤ k := by rw [← hk₁]; exact hc₁.three_le_length
  have hV₁_card : V₁.card = k := by rw [← hk₁]; exact cycle_support_card_eq_length c₁ hc₁
  have hV₂_card : V₂.card = k := by rw [← hk₂]; exact cycle_support_card_eq_length c₂ hc₂
  have h2c : IsKConnected2 G := fun S hS => h3c S (by omega)
  by_contra hlt
  have hle2 : (V₁ ∩ V₂).card ≤ 2 := by omega
  -- Case 0: V₁ and V₂ are disjoint
  by_cases h0 : (V₁ ∩ V₂).card = 0
  · have hdisj : Disjoint V₁ V₂ := Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp h0)
    obtain ⟨a₁, a₂, b₁, b₂, p₁, p₂, ha₁, ha₂, hb₁, hb₂, hp₁, hp₂, hdp⟩ :=
      two_disjoint_paths_of_two_connected h2c (by omega : 2 ≤ V₁.card) (by omega : 2 ≤ V₂.card)
    obtain ⟨u₁, v₁, q₁, hu₁, hv₁, hq₁, hq₁_len, hq₁_sub, hq₁_av1, hq₁_av2⟩ :=
      trim_path_between_sets hdisj p₁ hp₁ ha₁ hb₁
    obtain ⟨u₂, v₂, q₂, hu₂, hv₂, hq₂, hq₂_len, hq₂_sub, hq₂_av1, hq₂_av2⟩ :=
      trim_path_between_sets hdisj p₂ hp₂ ha₂ hb₂
    have hdq : List.Disjoint q₁.support q₂.support := fun x h1 h2 => hdp (hq₁_sub x h1) (hq₂_sub x h2)
    have hu_ne : u₁ ≠ u₂ := fun h => hdq (Walk.start_mem_support q₁) (h ▸ Walk.start_mem_support q₂)
    have hv_ne : v₁ ≠ v₂ := fun h => hdq (Walk.end_mem_support q₁) (h ▸ Walk.end_mem_support q₂)
    obtain ⟨A₁, B₁, hA₁, hB₁, _, _, hlen1, _, hmem1⟩ :=
      cycle_split c₁ hc₁ (List.mem_toFinset.mp hu₁) (List.mem_toFinset.mp hu₂) hu_ne
    obtain ⟨A₂, B₂, hA₂, hB₂, _, _, hlen2, _, hmem2⟩ :=
      cycle_split c₂ hc₂ (List.mem_toFinset.mp hv₁) (List.mem_toFinset.mp hv₂) hv_ne
    -- Pick the longer arc of c₁ and longer arc of c₂
    have hlong1 : ∃ L₁ : G.Walk u₁ u₂, L₁.IsPath ∧ k ≤ 2 * L₁.length ∧ ∀ x ∈ L₁.support, x ∈ V₁ := by
      by_cases h : B₁.length ≤ A₁.length
      · exact ⟨A₁, hA₁, by omega, fun x hx => List.mem_toFinset.mpr ((hmem1 x).mpr (Or.inl hx))⟩
      · exact ⟨B₁, hB₁, by omega, fun x hx => List.mem_toFinset.mpr ((hmem1 x).mpr (Or.inr hx))⟩
    have hlong2 : ∃ L₂ : G.Walk v₁ v₂, L₂.IsPath ∧ k ≤ 2 * L₂.length ∧ ∀ x ∈ L₂.support, x ∈ V₂ := by
      by_cases h : B₂.length ≤ A₂.length
      · exact ⟨A₂, hA₂, by omega, fun x hx => List.mem_toFinset.mpr ((hmem2 x).mpr (Or.inl hx))⟩
      · exact ⟨B₂, hB₂, by omega, fun x hx => List.mem_toFinset.mpr ((hmem2 x).mpr (Or.inr hx))⟩
    obtain ⟨L₁, hL₁, hL₁_len, hL₁_sub⟩ := hlong1
    obtain ⟨L₂, hL₂, hL₂_len, hL₂_sub⟩ := hlong2
    -- Form cycle (L₁.append q₂) ++ (L₂.reverse.append q₁.reverse) from u₁ to v₂ and back
    have hP1 : (L₁.append q₂).IsPath := isPath_append_of_meet_mid L₁ q₂ hL₁ hq₂ fun x hx1 hx2 => by
      by_contra hne
      exact hq₂_av1 x hx2 hne (hL₁_sub x hx1)
    have hP2 : (L₂.reverse.append q₁.reverse).IsPath :=
      isPath_append_of_meet_mid L₂.reverse q₁.reverse hL₂.reverse hq₁.reverse fun x hx1 hx2 => by
        rw [Walk.support_reverse, List.mem_reverse] at hx1 hx2
        by_contra hne
        exact hq₁_av2 x hx2 hne (hL₂_sub x hx1)
    have hu1_ne_v2 : u₁ ≠ v₂ := fun h => Finset.disjoint_left.mp hdisj hu₁ (h ▸ hv₂)
    have hcyc : ((L₁.append q₂).append (L₂.reverse.append q₁.reverse)).IsCycle := by
      refine isCycle_append_of_internally_disjoint _ _ hP1 hP2 hu1_ne_v2 ?_ ?_
      · intro x hx1 hx2
        rcases (Walk.mem_support_append_iff L₁ q₂).mp hx1 with hL1x | hq2x <;>
        rcases (Walk.mem_support_append_iff L₂.reverse q₁.reverse).mp hx2 with hL2x | hq1x
        · rw [Walk.support_reverse, List.mem_reverse] at hL2x
          exact absurd (hL₂_sub x hL2x) (Finset.disjoint_left.mp hdisj (hL₁_sub x hL1x))
        · rw [Walk.support_reverse, List.mem_reverse] at hq1x
          by_contra hne; push Not at hne
          exact hq₁_av1 x hq1x hne.1 (hL₁_sub x hL1x)
        · rw [Walk.support_reverse, List.mem_reverse] at hL2x
          by_contra hne; push Not at hne
          exact hq₂_av2 x hq2x hne.2 (hL₂_sub x hL2x)
        · rw [Walk.support_reverse, List.mem_reverse] at hq1x
          exact absurd hq2x (hdq hq1x)
      · simp only [Walk.length_append, Walk.length_reverse]
        omega
    have hle := hmax u₁ _ hcyc
    simp only [Walk.length_append, Walk.length_reverse] at hle
    omega
  -- Case 1: (V₁ ∩ V₂).card = 1
  by_cases h1 : (V₁ ∩ V₂).card = 1
  · obtain ⟨w, hV12⟩ := Finset.card_eq_one.mp h1
    have hw1 : w ∈ V₁ := (Finset.mem_inter.mp (hV12.symm ▸ Finset.mem_singleton_self w)).1
    have hw2 : w ∈ V₂ := (Finset.mem_inter.mp (hV12.symm ▸ Finset.mem_singleton_self w)).2
    have hdisj_er : Disjoint (V₁.erase w) (V₂.erase w) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have hx1' := Finset.mem_erase.mp hx1
      have hx2' := Finset.mem_erase.mp hx2
      have hinter : x ∈ V₁ ∩ V₂ := Finset.mem_inter.mpr ⟨hx1'.2, hx2'.2⟩
      rw [hV12, Finset.mem_singleton] at hinter
      exact hx1'.1 hinter
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hw1]; omega : 0 < (V₁.erase w).card)
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hw2]; omega : 0 < (V₂.erase w).card)
    have hreach : ReachAvoid G {w} a b := by
      by_contra hnr
      exact h2c {w} (by simp) ⟨a, b, by simp [(Finset.mem_erase.mp ha).1], by simp [(Finset.mem_erase.mp hb).1], hnr⟩
    obtain ⟨p0, hp0_av⟩ := hreach
    let p := p0.toPath
    have hp_av : ∀ x ∈ p.1.support, x ≠ w := fun x hx hxw =>
      hp0_av x (Walk.support_toPath_subset_support p0 hx) (by simp [hxw])
    obtain ⟨u, v, q, hu, hv, hq, hq_len, hq_sub, hq_av1, hq_av2⟩ :=
      trim_path_between_sets hdisj_er p.1 p.2 ha hb
    have hu_ne_w : u ≠ w := (Finset.mem_erase.mp hu).1
    have hv_ne_w : v ≠ w := (Finset.mem_erase.mp hv).1
    have hu1 : u ∈ V₁ := (Finset.mem_erase.mp hu).2
    have hv2 : v ∈ V₂ := (Finset.mem_erase.mp hv).2
    have hq_not_w : ∀ x ∈ q.support, x ≠ w := fun x hx => hp_av x (hq_sub x hx)
    obtain ⟨A₁, B₁, hA₁, hB₁, _, _, hlen1, _, hmem1⟩ :=
      cycle_split c₁ hc₁ (List.mem_toFinset.mp hw1) (List.mem_toFinset.mp hu1) hu_ne_w.symm
    obtain ⟨A₂, B₂, hA₂, hB₂, _, _, hlen2, _, hmem2⟩ :=
      cycle_split c₂ hc₂ (List.mem_toFinset.mp hw2) (List.mem_toFinset.mp hv2) hv_ne_w.symm
    have hlong1 : ∃ L₁ : G.Walk w u, L₁.IsPath ∧ k ≤ 2 * L₁.length ∧ ∀ x ∈ L₁.support, x ∈ V₁ := by
      by_cases h : B₁.length ≤ A₁.length
      · exact ⟨A₁, hA₁, by omega, fun x hx => List.mem_toFinset.mpr ((hmem1 x).mpr (Or.inl hx))⟩
      · exact ⟨B₁, hB₁, by omega, fun x hx => List.mem_toFinset.mpr ((hmem1 x).mpr (Or.inr hx))⟩
    have hlong2 : ∃ L₂ : G.Walk w v, L₂.IsPath ∧ k ≤ 2 * L₂.length ∧ ∀ x ∈ L₂.support, x ∈ V₂ := by
      by_cases h : B₂.length ≤ A₂.length
      · exact ⟨A₂, hA₂, by omega, fun x hx => List.mem_toFinset.mpr ((hmem2 x).mpr (Or.inl hx))⟩
      · exact ⟨B₂, hB₂, by omega, fun x hx => List.mem_toFinset.mpr ((hmem2 x).mpr (Or.inr hx))⟩
    obtain ⟨L₁, hL₁, hL₁_len, hL₁_sub⟩ := hlong1
    obtain ⟨L₂, hL₂, hL₂_len, hL₂_sub⟩ := hlong2
    have hP1 : (L₁.append q).IsPath := isPath_append_of_meet_mid L₁ q hL₁ hq fun x hx1 hx2 => by
      by_contra hne
      exact hq_av1 x hx2 hne (Finset.mem_erase.mpr ⟨hq_not_w x hx2, hL₁_sub x hx1⟩)
    have hcyc : ((L₁.append q).append L₂.reverse).IsCycle := by
      refine isCycle_append_of_internally_disjoint _ _ hP1 hL₂.reverse hv_ne_w.symm ?_ ?_
      · intro x hx1 hx2
        rw [Walk.support_reverse, List.mem_reverse] at hx2
        rcases (Walk.mem_support_append_iff L₁ q).mp hx1 with hL1x | hqx
        · left
          have hinter : x ∈ V₁ ∩ V₂ := Finset.mem_inter.mpr ⟨hL₁_sub x hL1x, hL₂_sub x hx2⟩
          rw [hV12, Finset.mem_singleton] at hinter
          exact hinter
        · right
          by_contra hne
          exact hq_av2 x hqx hne (Finset.mem_erase.mpr ⟨hq_not_w x hqx, hL₂_sub x hx2⟩)
      · simp only [Walk.length_append, Walk.length_reverse]
        omega
    have hle := hmax w _ hcyc
    simp only [Walk.length_append, Walk.length_reverse] at hle
    omega
  -- Case 2: (V₁ ∩ V₂).card = 2
  · have h2 : (V₁ ∩ V₂).card = 2 := by omega
    obtain ⟨u, v, huv, hV12⟩ := Finset.card_eq_two.mp h2
    have hu1 : u ∈ V₁ := (Finset.mem_inter.mp (hV12.symm ▸ Finset.mem_insert_self u {v})).1
    have hu2 : u ∈ V₂ := (Finset.mem_inter.mp (hV12.symm ▸ Finset.mem_insert_self u {v})).2
    have hv_in : v ∈ ({u, v} : Finset V) := Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
    have hv1 : v ∈ V₁ := (Finset.mem_inter.mp (hV12.symm ▸ hv_in)).1
    have hv2 : v ∈ V₂ := (Finset.mem_inter.mp (hV12.symm ▸ hv_in)).2
    obtain ⟨A₁, B₁, hA₁, hB₁, hA₁_pos, hB₁_pos, hlen1, hinter1, hmem1⟩ :=
      cycle_split c₁ hc₁ (List.mem_toFinset.mp hu1) (List.mem_toFinset.mp hv1) huv
    obtain ⟨A₂, B₂, hA₂, hB₂, hA₂_pos, hB₂_pos, hlen2, hinter2, hmem2⟩ :=
      cycle_split c₂ hc₂ (List.mem_toFinset.mp hu2) (List.mem_toFinset.mp hv2) huv
    -- First show A₁, B₁, A₂, B₂ all have length k/2 ≥ 2 (by combining longer arcs)
    have hL_bound : ∀ (P₁ : G.Walk u v) (P₂ : G.Walk u v),
        P₁.IsPath → P₂.IsPath → (∀ x ∈ P₁.support, x ∈ V₁) → (∀ x ∈ P₂.support, x ∈ V₂) →
        3 ≤ P₁.length + P₂.length → P₁.length + P₂.length ≤ k := by
      intro P₁ P₂ hP₁ hP₂ hsub1 hsub2 hge3
      have hcyc : (P₁.append P₂.reverse).IsCycle := by
        refine isCycle_append_of_internally_disjoint P₁ P₂.reverse hP₁ hP₂.reverse huv ?_ (by simpa using hge3)
        intro x hx1 hx2
        rw [Walk.support_reverse, List.mem_reverse] at hx2
        have hinter : x ∈ V₁ ∩ V₂ := Finset.mem_inter.mpr ⟨hsub1 x hx1, hsub2 x hx2⟩
        rw [hV12, Finset.mem_insert, Finset.mem_singleton] at hinter
        exact hinter
      have := hmax u _ hcyc
      simpa [Walk.length_append, Walk.length_reverse] using this
    have hA1_sub : ∀ x ∈ A₁.support, x ∈ V₁ := fun x hx => List.mem_toFinset.mpr ((hmem1 x).mpr (Or.inl hx))
    have hB1_sub : ∀ x ∈ B₁.support, x ∈ V₁ := fun x hx => List.mem_toFinset.mpr ((hmem1 x).mpr (Or.inr hx))
    have hA2_sub : ∀ x ∈ A₂.support, x ∈ V₂ := fun x hx => List.mem_toFinset.mpr ((hmem2 x).mpr (Or.inl hx))
    have hB2_sub : ∀ x ∈ B₂.support, x ∈ V₂ := fun x hx => List.mem_toFinset.mpr ((hmem2 x).mpr (Or.inr hx))
    have hAB_eq : A₁.length = B₁.length ∧ A₂.length = B₂.length ∧ A₁.length = A₂.length ∧ 2 ≤ A₁.length := by
      have h1 : A₁.length + A₂.length ≤ k := by
        by_cases h : 3 ≤ A₁.length + A₂.length
        · exact hL_bound A₁ A₂ hA₁ hA₂ hA1_sub hA2_sub h
        · omega
      have h2' : A₁.length + B₂.length ≤ k := by
        by_cases h : 3 ≤ A₁.length + B₂.length
        · exact hL_bound A₁ B₂ hA₁ hB₂ hA1_sub hB2_sub h
        · omega
      have h3 : B₁.length + A₂.length ≤ k := by
        by_cases h : 3 ≤ B₁.length + A₂.length
        · exact hL_bound B₁ A₂ hB₁ hA₂ hB1_sub hA2_sub h
        · omega
      have h4 : B₁.length + B₂.length ≤ k := by
        by_cases h : 3 ≤ B₁.length + B₂.length
        · exact hL_bound B₁ B₂ hB₁ hB₂ hB1_sub hB2_sub h
        · omega
      omega
    -- Now V₁ \ {u, v} and V₂ \ {u, v} are nonempty and disjoint, connected in G - {u, v} by 3-connectedness!
    let S := ({u, v} : Finset V)
    let U₁ := V₁ \ S
    let U₂ := V₂ \ S
    have hdisj_U : Disjoint U₁ U₂ := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have h1' := Finset.mem_sdiff.mp hx1
      have h2' := Finset.mem_sdiff.mp hx2
      have hinter : x ∈ V₁ ∩ V₂ := Finset.mem_inter.mpr ⟨h1'.1, h2'.1⟩
      rw [hV12] at hinter
      exact h1'.2 hinter
    have hS_card : S.card = 2 := Finset.card_pair huv
    have hU₁_ne : U₁.Nonempty := Finset.card_pos.mp (by
      change 0 < (V₁ \ S).card
      have := Finset.card_sdiff_add_card_inter V₁ S
      have : (V₁ ∩ S).card ≤ S.card := Finset.card_le_card Finset.inter_subset_right
      omega)
    have hU₂_ne : U₂.Nonempty := Finset.card_pos.mp (by
      change 0 < (V₂ \ S).card
      have := Finset.card_sdiff_add_card_inter V₂ S
      have : (V₂ ∩ S).card ≤ S.card := Finset.card_le_card Finset.inter_subset_right
      omega)
    obtain ⟨a, ha⟩ := hU₁_ne
    obtain ⟨b, hb⟩ := hU₂_ne
    have hreach : ReachAvoid G S a b := by
      by_contra hnr
      exact h3c S (by omega) ⟨a, b, (Finset.mem_sdiff.mp ha).2, (Finset.mem_sdiff.mp hb).2, hnr⟩
    obtain ⟨p0, hp0_av⟩ := hreach
    let p := p0.toPath
    have hp_av : ∀ z ∈ p.1.support, z ∉ S := fun z hz => hp0_av z (Walk.support_toPath_subset_support p0 hz)
    obtain ⟨x, y, q, hxU, hyU, hq, hq_len, hq_sub, hq_av1, hq_av2⟩ :=
      trim_path_between_sets hdisj_U p.1 p.2 ha hb
    have hq_not_S : ∀ z ∈ q.support, z ∉ S := fun z hz => hp_av z (hq_sub z hz)
    have hx_not_S : x ∉ S := (Finset.mem_sdiff.mp hxU).2
    have hy_not_S : y ∉ S := (Finset.mem_sdiff.mp hyU).2
    have hxu : x ≠ u := fun h => hx_not_S (by simp [S, h])
    have hxv : x ≠ v := fun h => hx_not_S (by simp [S, h])
    have hyu : y ≠ u := fun h => hy_not_S (by simp [S, h])
    have hyv : y ≠ v := fun h => hy_not_S (by simp [S, h])
    -- WLOG x lies on an arc X₁ of c₁ (with opposite arc Y₁), and y lies on an arc X₂ of c₂ (with opposite arc Y₂)
    have hpick1 : ∃ (X₁ : G.Walk u v), X₁.IsPath ∧ X₁.length = A₁.length ∧ x ∈ X₁.support ∧ ∀ z ∈ X₁.support, z ∈ V₁ := by
      have hx_c1 : x ∈ c₁.support := List.mem_toFinset.mp (Finset.mem_sdiff.mp hxU).1
      rcases (hmem1 x).mp hx_c1 with hxA | hxB
      · exact ⟨A₁, hA₁, rfl, hxA, hA1_sub⟩
      · exact ⟨B₁, hB₁, hAB_eq.1.symm, hxB, hB1_sub⟩
    have hpick2 : ∃ (X₂ Y₂ : G.Walk u v), X₂.IsPath ∧ Y₂.IsPath ∧
        X₂.length = A₁.length ∧ Y₂.length = A₁.length ∧ y ∈ X₂.support ∧
        (∀ z, z ∈ X₂.support → z ∈ Y₂.support → z = u ∨ z = v) ∧
        (∀ z ∈ X₂.support, z ∈ V₂) ∧ (∀ z ∈ Y₂.support, z ∈ V₂) := by
      have hy_c2 : y ∈ c₂.support := List.mem_toFinset.mp (Finset.mem_sdiff.mp hyU).1
      rcases (hmem2 y).mp hy_c2 with hyA | hyB
      · exact ⟨A₂, B₂, hA₂, hB₂, hAB_eq.2.2.1.symm, by omega, hyA, hinter2, hA2_sub, hB2_sub⟩
      · exact ⟨B₂, A₂, hB₂, hA₂, by omega, hAB_eq.2.2.1.symm, hyB, fun z h1 h2 => hinter2 z h2 h1, hB2_sub, hA2_sub⟩
    obtain ⟨X₁, hX₁, hX₁_len, hxX₁, hX₁_sub⟩ := hpick1
    obtain ⟨X₂, Y₂, hX₂, hY₂, hX₂_len, hY₂_len, hyX₂, hinterXY, hX₂_sub, hY₂_sub⟩ := hpick2
    -- Split X₁ at x into X₁u (u → x) and X₁v (x → v), and X₂ at y into X₂u (u → y) and X₂v (y → v)
    let X₁u := X₁.takeUntil x hxX₁
    let X₁v := X₁.dropUntil x hxX₁
    let X₂u := X₂.takeUntil y hyX₂
    let X₂v := X₂.dropUntil y hyX₂
    have hX₁_spec : X₁u.append X₁v = X₁ := Walk.take_spec X₁ hxX₁
    have hX₂_spec : X₂u.append X₂v = X₂ := Walk.take_spec X₂ hyX₂
    have hX₁_len_sum : X₁u.length + X₁v.length = A₁.length := by
      have := congrArg Walk.length hX₁_spec
      rw [Walk.length_append, hX₁_len] at this; exact this
    have hX₂_len_sum : X₂u.length + X₂v.length = A₁.length := by
      have := congrArg Walk.length hX₂_spec
      rw [Walk.length_append, hX₂_len] at this; exact this
    have hX₁u_path : X₁u.IsPath := hX₁.takeUntil hxX₁
    have hX₁v_path : X₁v.IsPath := hX₁.dropUntil hxX₁
    have hX₂u_path : X₂u.IsPath := hX₂.takeUntil hyX₂
    have hX₂v_path : X₂v.IsPath := hX₂.dropUntil hyX₂
    have hX₁u_sub : ∀ z ∈ X₁u.support, z ∈ V₁ := fun z hz => hX₁_sub z (Walk.support_takeUntil_subset_support X₁ hxX₁ hz)
    have hX₁v_sub : ∀ z ∈ X₁v.support, z ∈ V₁ := fun z hz => hX₁_sub z (Walk.support_dropUntil_subset_support X₁ hxX₁ hz)
    have hX₂u_sub : ∀ z ∈ X₂u.support, z ∈ V₂ := fun z hz => hX₂_sub z (Walk.support_takeUntil_subset_support X₂ hyX₂ hz)
    have hX₂v_sub : ∀ z ∈ X₂v.support, z ∈ V₂ := fun z hz => hX₂_sub z (Walk.support_dropUntil_subset_support X₂ hyX₂ hz)
    have hv_not_X₁u : v ∉ X₁u.support := Walk.endpoint_notMem_support_takeUntil hX₁ hxX₁ hxv.symm
    have hv_not_X₂u : v ∉ X₂u.support := Walk.endpoint_notMem_support_takeUntil hX₂ hyX₂ hyv.symm
    have hu_not_X₁v : u ∉ X₁v.support := by
      intro hu_in
      have hnd := hX₁.support_nodup
      rw [← hX₁_spec, Walk.support_append, List.nodup_append] at hnd
      cases hds : X₁v.support with
      | nil => exact absurd hds (Walk.support_ne_nil _)
      | cons d l =>
        have hd : d = x := by have := Walk.head_support X₁v; simp [hds] at this; exact this
        rw [hds, List.mem_cons] at hu_in
        rcases hu_in with rfl | hul
        · exact hxu hd.symm
        · exact hnd.2.2 u (Walk.start_mem_support X₁u) u (by rw [hds, List.tail_cons]; exact hul) rfl
    have hu_not_X₂v : u ∉ X₂v.support := by
      intro hu_in
      have hnd := hX₂.support_nodup
      rw [← hX₂_spec, Walk.support_append, List.nodup_append] at hnd
      cases hds : X₂v.support with
      | nil => exact absurd hds (Walk.support_ne_nil _)
      | cons d l =>
        have hd : d = y := by have := Walk.head_support X₂v; simp [hds] at this; exact this
        rw [hds, List.mem_cons] at hu_in
        rcases hu_in with rfl | hul
        · exact hyu hd.symm
        · exact hnd.2.2 u (Walk.start_mem_support X₂u) u (by rw [hds, List.tail_cons]; exact hul) rfl
    -- Cycle 1: (q.append X₂u.reverse) (x → u) + (Y₂.append X₁v.reverse) (u → x)
    have hC1_p1 : (q.append X₂u.reverse).IsPath :=
      isPath_append_of_meet_mid q X₂u.reverse hq hX₂u_path.reverse fun z hz1 hz2 => by
        rw [Walk.support_reverse, List.mem_reverse] at hz2
        by_contra hne
        exact hq_av2 z hz1 hne (Finset.mem_sdiff.mpr ⟨hX₂u_sub z hz2, hq_not_S z hz1⟩)
    have hC1_p2 : (Y₂.append X₁v.reverse).IsPath :=
      isPath_append_of_meet_mid Y₂ X₁v.reverse hY₂ hX₁v_path.reverse fun z hz1 hz2 => by
        rw [Walk.support_reverse, List.mem_reverse] at hz2
        have hinter : z ∈ V₁ ∩ V₂ := Finset.mem_inter.mpr ⟨hX₁v_sub z hz2, hY₂_sub z hz1⟩
        rw [hV12, Finset.mem_insert, Finset.mem_singleton] at hinter
        rcases hinter with rfl | rfl
        · exact absurd hz2 hu_not_X₁v
        · rfl
    have hC1 : ((q.append X₂u.reverse).append (Y₂.append X₁v.reverse)).IsCycle := by
      refine isCycle_append_of_internally_disjoint _ _ hC1_p1 hC1_p2 hxu ?_ ?_
      · intro z hz1 hz2
        rcases (Walk.mem_support_append_iff q X₂u.reverse).mp hz1 with hqz | hX2z <;>
        rcases (Walk.mem_support_append_iff Y₂ X₁v.reverse).mp hz2 with hY2z | hX1z
        · have hzy : z = y := by
            by_contra hne
            exact hq_av2 z hqz hne (Finset.mem_sdiff.mpr ⟨hY₂_sub z hY2z, hq_not_S z hqz⟩)
          subst hzy
          rcases hinterXY z hyX₂ hY2z with rfl | rfl
          · exact absurd rfl hyu
          · exact absurd rfl hyv
        · rw [Walk.support_reverse, List.mem_reverse] at hX1z
          left
          by_contra hne
          exact hq_av1 z hqz hne (Finset.mem_sdiff.mpr ⟨hX₁v_sub z hX1z, hq_not_S z hqz⟩)
        · rw [Walk.support_reverse, List.mem_reverse] at hX2z
          rcases hinterXY z (Walk.support_takeUntil_subset_support X₂ hyX₂ hX2z) hY2z with rfl | rfl
          · exact Or.inr rfl
          · exact absurd hX2z hv_not_X₂u
        · rw [Walk.support_reverse, List.mem_reverse] at hX2z hX1z
          have hinter : z ∈ V₁ ∩ V₂ := Finset.mem_inter.mpr ⟨hX₁v_sub z hX1z, hX₂u_sub z hX2z⟩
          rw [hV12, Finset.mem_insert, Finset.mem_singleton] at hinter
          rcases hinter with rfl | rfl
          · exact Or.inr rfl
          · exact absurd hX2z hv_not_X₂u
      · simp only [Walk.length_append, Walk.length_reverse]
        omega
    -- Cycle 2: (q.append X₂v) (x → v) + (Y₂.reverse.append X₁u) (v → x)
    have hC2_p1 : (q.append X₂v).IsPath :=
      isPath_append_of_meet_mid q X₂v hq hX₂v_path fun z hz1 hz2 => by
        by_contra hne
        exact hq_av2 z hz1 hne (Finset.mem_sdiff.mpr ⟨hX₂v_sub z hz2, hq_not_S z hz1⟩)
    have hC2_p2 : (Y₂.reverse.append X₁u).IsPath :=
      isPath_append_of_meet_mid Y₂.reverse X₁u hY₂.reverse hX₁u_path fun z hz1 hz2 => by
        rw [Walk.support_reverse, List.mem_reverse] at hz1
        have hinter : z ∈ V₁ ∩ V₂ := Finset.mem_inter.mpr ⟨hX₁u_sub z hz2, hY₂_sub z hz1⟩
        rw [hV12, Finset.mem_insert, Finset.mem_singleton] at hinter
        rcases hinter with rfl | rfl
        · rfl
        · exact absurd hz2 hv_not_X₁u
    have hC2 : ((q.append X₂v).append (Y₂.reverse.append X₁u)).IsCycle := by
      refine isCycle_append_of_internally_disjoint _ _ hC2_p1 hC2_p2 hxv ?_ ?_
      · intro z hz1 hz2
        rcases (Walk.mem_support_append_iff q X₂v).mp hz1 with hqz | hX2z <;>
        rcases (Walk.mem_support_append_iff Y₂.reverse X₁u).mp hz2 with hY2z | hX1z
        · rw [Walk.support_reverse, List.mem_reverse] at hY2z
          have hzy : z = y := by
            by_contra hne
            exact hq_av2 z hqz hne (Finset.mem_sdiff.mpr ⟨hY₂_sub z hY2z, hq_not_S z hqz⟩)
          subst hzy
          rcases hinterXY z hyX₂ hY2z with rfl | rfl
          · exact absurd rfl hyu
          · exact absurd rfl hyv
        · left
          by_contra hne
          exact hq_av1 z hqz hne (Finset.mem_sdiff.mpr ⟨hX₁u_sub z hX1z, hq_not_S z hqz⟩)
        · rw [Walk.support_reverse, List.mem_reverse] at hY2z
          rcases hinterXY z (Walk.support_dropUntil_subset_support X₂ hyX₂ hX2z) hY2z with rfl | rfl
          · exact absurd hX2z hu_not_X₂v
          · exact Or.inr rfl
        · have hinter : z ∈ V₁ ∩ V₂ := Finset.mem_inter.mpr ⟨hX₁u_sub z hX1z, hX₂v_sub z hX2z⟩
          rw [hV12, Finset.mem_insert, Finset.mem_singleton] at hinter
          rcases hinter with rfl | rfl
          · exact absurd hX2z hu_not_X₂v
          · exact Or.inr rfl
      · simp only [Walk.length_append, Walk.length_reverse]
        omega
    have hle1 := hmax x _ hC1
    have hle2 := hmax x _ hC2
    simp only [Walk.length_append, Walk.length_reverse] at hle1 hle2
    omega

end CycleIntersection

/- ### Section 6: Double counting over Aut(G) and main theorem -/

section DoubleCounting

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma double_count_vt (G : SimpleGraph V) [DecidableRel G.Adj]
    (htrans : IsVertexTransitive G) (C : Finset V) (m : ℕ)
    (hinter : ∀ φ : G ≃g G, m ≤ (C ∩ C.image φ).card) :
    m * Fintype.card V ≤ C.card ^ 2 := by
  classical
  let Aut : Finset (Equiv.Perm V) := Finset.univ.filter fun σ =>
    ∀ u v : V, G.Adj (σ u) (σ v) ↔ G.Adj u v
  have h1_mem : (1 : Equiv.Perm V) ∈ Aut := Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ _ => Iff.rfl⟩
  have hmul_mem : ∀ {σ τ : Equiv.Perm V}, σ ∈ Aut → τ ∈ Aut → σ * τ ∈ Aut := by
    intro σ τ hσ hτ
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u v => ?_⟩
    exact ((Finset.mem_filter.mp hσ).2 _ _).trans ((Finset.mem_filter.mp hτ).2 u v)
  have hinv_mem : ∀ {σ : Equiv.Perm V}, σ ∈ Aut → σ⁻¹ ∈ Aut := by
    intro σ hσ
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun u v => ?_⟩
    have h := (Finset.mem_filter.mp hσ).2 (σ⁻¹ u) (σ⁻¹ v)
    simpa using h.symm
  -- Every σ ∈ Aut yields a graph isomorphism G ≃g G
  have hAut_inter : ∀ σ ∈ Aut, m ≤ (C ∩ C.image σ).card := by
    intro σ hσ
    let φ : G ≃g G := { toEquiv := σ, map_rel_iff' := fun {a b} => (Finset.mem_filter.mp hσ).2 a b }
    exact hinter φ
  -- If V is empty, trivial
  by_cases hV : Fintype.card V = 0
  · simp [hV]
  have hV_pos : 0 < Fintype.card V := Nat.pos_of_ne_zero hV
  obtain ⟨v0⟩ : Nonempty V := Fintype.card_pos_iff.mp hV_pos
  -- Stabilizer size is constant across all pairs (u, v)
  let stab := (Aut.filter fun σ => σ v0 = v0).card
  have hstab_pos : 0 < stab :=
    Finset.card_pos.mpr ⟨1, Finset.mem_filter.mpr ⟨h1_mem, rfl⟩⟩
  have hpair_card : ∀ u v : V, (Aut.filter fun σ => σ u = v).card = stab := by
    intro u v
    obtain ⟨φ1, hφ1⟩ := htrans v0 u
    obtain ⟨φ2, hφ2⟩ := htrans v0 v
    have hφ1_mem : φ1.toEquiv ∈ Aut := Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun a b => φ1.map_rel_iff⟩
    have hφ2_mem : φ2.toEquiv ∈ Aut := Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun a b => φ2.map_rel_iff⟩
    apply Finset.card_bij (fun σ _ => φ2.toEquiv⁻¹ * σ * φ1.toEquiv)
    · intro σ hσ
      have ⟨hσA, hσuv⟩ := Finset.mem_filter.mp hσ
      refine Finset.mem_filter.mpr ⟨hmul_mem (hmul_mem (hinv_mem hφ2_mem) hσA) hφ1_mem, ?_⟩
      change φ2.toEquiv.symm (σ (φ1.toEquiv v0)) = v0
      rw [show φ1.toEquiv v0 = u from hφ1, hσuv, ← hφ2]
      exact φ2.symm_apply_apply v0
    · intro σ₁ _ σ₂ _ heq
      have h1 := congrArg (fun τ => φ2.toEquiv * τ * φ1.toEquiv⁻¹) heq
      simpa [mul_assoc] using h1
    · intro τ hτ
      have ⟨hτA, hτ0⟩ := Finset.mem_filter.mp hτ
      refine ⟨φ2.toEquiv * τ * φ1.toEquiv⁻¹, ?_, by simp [mul_assoc]⟩
      refine Finset.mem_filter.mpr ⟨hmul_mem (hmul_mem hφ2_mem hτA) (hinv_mem hφ1_mem), ?_⟩
      change φ2.toEquiv (τ (φ1.toEquiv.symm u)) = v
      rw [← hφ1]
      change φ2.toEquiv (τ (φ1.toEquiv.symm (φ1.toEquiv v0))) = v
      rw [Equiv.symm_apply_apply, hτ0]
      exact hφ2
  -- Aut.card = Fintype.card V * stab
  have hAut_card : Aut.card = Fintype.card V * stab := by
    have hpart : Aut.card = ∑ v : V, (Aut.filter fun σ => σ v0 = v).card := by
      rw [← Finset.card_biUnion]
      · congr 1; ext σ; simp
      · intro v₁ _ v₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro σ h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    rw [hpart]
    simp only [hpair_card v0, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  -- Double count ∑ σ ∈ Aut, (C ∩ C.image σ).card = C.card ^ 2 * stab
  have hsum_eq : ∑ σ ∈ Aut, (C ∩ C.image σ).card = C.card ^ 2 * stab := by
    have hinner : ∀ σ : Equiv.Perm V,
        (C ∩ C.image σ).card = ∑ u ∈ C, ∑ v ∈ C, if σ u = v then 1 else 0 := by
      intro σ
      have h1 : ∀ u ∈ C, (∑ v ∈ C, if σ u = v then 1 else 0) = if σ u ∈ C then 1 else 0 := by
        intro u _
        simp only [Finset.sum_ite_eq]
      rw [Finset.sum_congr rfl h1]
      rw [Finset.sum_boole, Nat.cast_id]
      apply Finset.card_bij (fun x _ => σ⁻¹ x)
      · intro x hx
        have ⟨hxC, hxIm⟩ := Finset.mem_inter.mp hx
        obtain ⟨u, huC, hux⟩ := Finset.mem_image.mp hxIm
        have hinv : σ⁻¹ x = u := by rw [← hux]; exact σ.symm_apply_apply u
        refine Finset.mem_filter.mpr ⟨hinv ▸ huC, ?_⟩
        rw [hinv, hux]; exact hxC
      · intro x₁ _ x₂ _ heq
        exact σ.symm.injective heq
      · intro u hu
        have ⟨huC, hσuC⟩ := Finset.mem_filter.mp hu
        exact ⟨σ u, Finset.mem_inter.mpr ⟨hσuC, Finset.mem_image_of_mem σ huC⟩, σ.symm_apply_apply u⟩
    calc ∑ σ ∈ Aut, (C ∩ C.image σ).card
        = ∑ σ ∈ Aut, ∑ u ∈ C, ∑ v ∈ C, if σ u = v then 1 else 0 :=
          Finset.sum_congr rfl fun σ _ => hinner σ
      _ = ∑ u ∈ C, ∑ σ ∈ Aut, ∑ v ∈ C, if σ u = v then 1 else 0 := Finset.sum_comm
      _ = ∑ u ∈ C, ∑ v ∈ C, ∑ σ ∈ Aut, if σ u = v then 1 else 0 :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ u ∈ C, ∑ v ∈ C, (Aut.filter fun σ => σ u = v).card := by
          refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
          rw [Finset.sum_boole, Nat.cast_id]
      _ = ∑ _u ∈ C, ∑ _v ∈ C, stab := by
          refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => hpair_card u v
      _ = C.card ^ 2 * stab := by
          simp [Finset.sum_const, sq, mul_assoc]
  have hsum_ge : m * Aut.card ≤ ∑ σ ∈ Aut, (C ∩ C.image σ).card := by
    calc m * Aut.card = ∑ _σ ∈ Aut, m := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ σ ∈ Aut, (C ∩ C.image σ).card := Finset.sum_le_sum hAut_inter
  rw [hAut_card, hsum_eq] at hsum_ge
  have hmul : m * Fintype.card V * stab ≤ C.card ^ 2 * stab := by linarith
  exact Nat.le_of_mul_le_mul_right hmul hstab_pos

theorem babai_proof
    {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (htrans : IsVertexTransitive G) (hcard : 3 ≤ Fintype.card V) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
      Real.sqrt (3 * Fintype.card V) ≤ (c.length : ℝ) := by
  classical
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hdeg2 := two_le_degree_of_connected_vt G hconn htrans hcard
  have hreg := degree_eq_of_isVertexTransitive G htrans
  obtain ⟨v0⟩ := ‹Nonempty V›
  by_cases hd2 : G.degree v0 = 2
  · have hall2 : ∀ v : V, G.degree v = 2 := fun v => (hreg v v0).trans hd2
    obtain ⟨v, c, hc⟩ := exists_cycle_of_two_le_degree G hdeg2
    have hlen := card_le_length_of_two_regular G hconn hall2 c hc
    refine ⟨v, c, hc, ?_⟩
    rw [Real.sqrt_le_iff]
    refine ⟨Nat.cast_nonneg _, ?_⟩
    have hnat : 3 * Fintype.card V ≤ c.length ^ 2 := by nlinarith
    exact_mod_cast hnat
  · have hdeg3 : ∀ v : V, 3 ≤ G.degree v := fun v => by
      have := hdeg2 v
      have := hreg v v0
      omega
    have h3c : IsKConnected3 G := three_connected_of_vt G hconn htrans hdeg3
    -- Pick a longest cycle in G
    let S : Finset (Fin (Fintype.card V + 1)) := Finset.univ.filter fun k =>
      ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = k.val
    have hS_ne : S.Nonempty := by
      obtain ⟨v, c, hc⟩ := exists_cycle_of_two_le_degree G hdeg2
      have hlt : c.length < Fintype.card V + 1 := by
        have h1 := cycle_support_card_eq_length c hc
        have h2 := Finset.card_le_univ c.support.toFinset
        omega
      exact ⟨⟨c.length, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, c, hc, rfl⟩⟩
    obtain ⟨kmax, hkmax_mem, hkmax_max⟩ := S.exists_max_image (fun k => k.val) hS_ne
    obtain ⟨_, v, c, hc, hclen⟩ := Finset.mem_filter.mp hkmax_mem
    have hmax : ∀ (w : V) (c' : G.Walk w w), c'.IsCycle → c'.length ≤ kmax.val := by
      intro w c' hc'
      have hlt : c'.length < Fintype.card V + 1 := by
        have h1 := cycle_support_card_eq_length c' hc'
        have h2 := Finset.card_le_univ c'.support.toFinset
        omega
      exact hkmax_max ⟨c'.length, hlt⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, w, c', hc', rfl⟩)
    -- Every automorphism φ maps c to another longest cycle with vertex set C.image φ
    have hinter : ∀ φ : G ≃g G, 3 ≤ (c.support.toFinset ∩ c.support.toFinset.image φ).card := by
      intro φ
      let c' := c.map φ.toHom
      have hc' : c'.IsCycle := by
        rw [Walk.isCycle_def]
        refine ⟨?_, ?_, ?_⟩
        · rw [Walk.isTrail_def, Walk.edges_map]
          exact hc.isTrail.edges_nodup.map (Sym2.map.injective φ.injective)
        · intro hnil
          have := congrArg Walk.length hnil
          rw [Walk.length_map, Walk.length_nil] at this
          have := hc.three_le_length
          omega
        · rw [Walk.support_map]
          have htail : (c.support.map φ.toHom).tail = c.support.tail.map φ.toHom := by
            cases c.support <;> rfl
          rw [htail]
          exact hc.support_nodup.map φ.injective
      have hsup' : c'.support.toFinset = c.support.toFinset.image φ := by
        ext z
        simp only [c', Walk.support_map, List.mem_toFinset, List.mem_map, Finset.mem_image]
        rfl
      rw [← hsup']
      exact longest_cycles_inter_ge_three h3c kmax.val hmax c c' hc hc' hclen (by rw [Walk.length_map, hclen])
    have hsq := double_count_vt G htrans c.support.toFinset 3 hinter
    rw [cycle_support_card_eq_length c hc] at hsq
    refine ⟨v, c, hc, ?_⟩
    rw [Real.sqrt_le_iff]
    refine ⟨Nat.cast_nonneg _, ?_⟩
    exact_mod_cast hsq

end DoubleCounting

end OMABabai

theorem OMA.solution : type_of% @LovaszConjecture.lovasz_conjecture.variants.babai :=
  @OMABabai.babai_proof
