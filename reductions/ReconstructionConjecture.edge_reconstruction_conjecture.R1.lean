import FormalConjectures.Wikipedia.ReconstructionConjecture

/-!
Reduction `ReconstructionConjecture.edge_reconstruction_conjecture.R1` of Harary's edge
reconstruction conjecture into four mathematical pillars, plus an in-file proof of the
regular-graph case.
-/

-- Reduction ReconstructionConjecture.edge_reconstruction_conjecture.R1 of The edge reconstruction conjecture
-- Credit: @green-notes
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_ReconstructionConjecture_edge_reconstruction_conjecture_R1

open SimpleGraph ReconstructionConjecture

-- Pillar 1 (Greenwell-Hemminger 1969, Greenwell 1971, Kelly 1957):
-- Any edge-hypomorphic pair with at least 4 edges either is already isomorphic,
-- or reduces by stripping isolated vertices to a connected, isolate-free,
-- doubly-hypomorphic (EdgeHypomorphic and Hypomorphic) pair.
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] (G H : SimpleGraph V),
    4 ≤ G.edgeSet.ncard → EdgeHypomorphic G H →
    Nonempty (G ≃g H) ∨
      ∃ (W : Type) (_ : Fintype W) (G' H' : SimpleGraph W),
        4 ≤ Fintype.card W ∧ 4 ≤ G'.edgeSet.ncard ∧
        G'.Connected ∧ (∀ w : W, ∃ u : W, G'.Adj w u) ∧
        EdgeHypomorphic G' H' ∧ Hypomorphic G' H' ∧
        (Nonempty (G' ≃g H') → Nonempty (G ≃g H))

-- Pillar 2 (Muller 1977):
-- Superlinear density regime n! < 2^(m - 1) on connected isolate-free doubly-hypomorphic graphs.
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] (G H : SimpleGraph V),
    4 ≤ Fintype.card V → 4 ≤ G.edgeSet.ncard →
    Nat.factorial (Fintype.card V) < 2 ^ (G.edgeSet.ncard - 1) →
    G.Connected → (∀ v : V, ∃ w : V, G.Adj v w) →
    EdgeHypomorphic G H → Hypomorphic G H → Nonempty (G ≃g H)

-- Pillar 3 (Cogentic 2026):
-- Unconditional linear-density regime 1000 * n <= m (with 2^(m - 1) <= n!)
-- on connected, isolate-free, non-regular, doubly-hypomorphic graphs.
def H3 : Prop :=
  ∀ {V : Type} [Fintype V] (G H : SimpleGraph V),
    4 ≤ Fintype.card V → 4 ≤ G.edgeSet.ncard →
    1000 * Fintype.card V ≤ G.edgeSet.ncard →
    2 ^ (G.edgeSet.ncard - 1) ≤ Nat.factorial (Fintype.card V) →
    G.Connected → (∀ v : V, ∃ w : V, G.Adj v w) →
    (∃ u v : V, (G.neighborSet u).ncard ≠ (G.neighborSet v).ncard) →
    EdgeHypomorphic G H → Hypomorphic G H → Nonempty (G ≃g H)

-- Pillar 4 (Open Sparse Non-Regular Frontier):
-- Sparse connected non-regular regime 4 <= m < 1000 * n (with 2^(m - 1) <= n!)
-- on connected, isolate-free, doubly-hypomorphic graphs.
def H4 : Prop :=
  ∀ {V : Type} [Fintype V] (G H : SimpleGraph V),
    4 ≤ Fintype.card V → 4 ≤ G.edgeSet.ncard →
    G.edgeSet.ncard < 1000 * Fintype.card V →
    2 ^ (G.edgeSet.ncard - 1) ≤ Nat.factorial (Fintype.card V) →
    G.Connected → (∀ v : V, ∃ w : V, G.Adj v w) →
    (∃ u v : V, (G.neighborSet u).ncard ≠ (G.neighborSet v).ncard) →
    EdgeHypomorphic G H → Hypomorphic G H → Nonempty (G ≃g H)

section RegularProof

open Classical

private lemma ncard_edgeSet_eq_card_edgeFinset {V : Type} [Fintype V] (G : SimpleGraph V) :
    G.edgeSet.ncard = G.edgeFinset.card := by
  rw [← G.coe_edgeFinset, Set.ncard_coe_finset]

private lemma four_le_card_of_four_le_edgeFinset {V : Type} [Fintype V] (G : SimpleGraph V)
    (hE : 4 ≤ G.edgeFinset.card) : 4 ≤ Fintype.card V := by
  have hle : 4 ≤ (Fintype.card V).choose 2 := hE.trans G.card_edgeFinset_le_card_choose_two
  by_contra hlt
  have hlt' : Fintype.card V < 4 := Nat.lt_of_not_le hlt
  interval_cases h : Fintype.card V <;> simp_all [Nat.choose]

private lemma ncard_neighborSet_eq_degree {V : Type} [Fintype V] (G : SimpleGraph V) (v : V) :
    (G.neighborSet v).ncard = G.degree v := by
  rw [← G.card_neighborSet_eq_degree, Set.ncard_eq_toFinset_card' (G.neighborSet v)]
  simp [Set.toFinset_card]

private lemma neighborFinset_deleteEdges_singleton {V : Type} [Fintype V] (G : SimpleGraph V)
    {u v : V} (x : V) :
    (G.deleteEdges {s(u, v)}).neighborFinset x =
      if x = u then (G.neighborFinset u).erase v
      else if x = v then (G.neighborFinset v).erase u
      else G.neighborFinset x := by
  by_cases hxu : x = u
  · subst hxu
    rw [if_pos rfl]
    ext y
    simp only [mem_neighborFinset, deleteEdges_adj, Set.mem_singleton_iff, Finset.mem_erase,
      ne_eq]
    constructor
    · rintro ⟨hadj, hne⟩
      refine ⟨fun hy => hne (by rw [hy]), hadj⟩
    · rintro ⟨hy, hadj⟩
      refine ⟨hadj, fun h => ?_⟩
      rw [Sym2.eq_iff] at h
      rcases h with ⟨_, hyx⟩ | ⟨_, hyx⟩
      · exact hy hyx
      · exact hadj.ne hyx.symm
  · rw [if_neg hxu]
    by_cases hxv : x = v
    · subst hxv
      rw [if_pos rfl]
      ext y
      simp only [mem_neighborFinset, deleteEdges_adj, Set.mem_singleton_iff, Finset.mem_erase,
        ne_eq]
      constructor
      · rintro ⟨hadj, hne⟩
        refine ⟨fun hy => hne (by rw [hy, Sym2.eq_swap]), hadj⟩
      · rintro ⟨hy, hadj⟩
        refine ⟨hadj, fun h => ?_⟩
        rw [Sym2.eq_iff] at h
        rcases h with ⟨hvu, _⟩ | ⟨_, hyu⟩
        · exact hxu hvu
        · exact hy hyu
    · rw [if_neg hxv]
      ext y
      simp only [mem_neighborFinset, deleteEdges_adj, Set.mem_singleton_iff]
      constructor
      · exact fun h => h.1
      · intro hadj
        refine ⟨hadj, fun h => ?_⟩
        rw [Sym2.eq_iff] at h
        rcases h with ⟨hx, _⟩ | ⟨hx, _⟩
        · exact hxu hx
        · exact hxv hx

private lemma degree_deleteEdges_singleton_of_adj {V : Type} [Fintype V] (G : SimpleGraph V)
    {u v : V} (hadj : G.Adj u v) (x : V) :
    (G.deleteEdges {s(u, v)}).degree x =
      if x = u ∨ x = v then G.degree x - 1 else G.degree x := by
  have hmemu : v ∈ G.neighborFinset u := (G.mem_neighborFinset u v).mpr hadj
  have hmemv : u ∈ G.neighborFinset v := (G.mem_neighborFinset v u).mpr hadj.symm
  rw [degree, neighborFinset_deleteEdges_singleton]
  by_cases hxu : x = u
  · subst hxu
    rw [if_pos rfl, if_pos (Or.inl rfl), Finset.card_erase_of_mem hmemu, card_neighborFinset_eq_degree]
  · rw [if_neg hxu]
    by_cases hxv : x = v
    · subst hxv
      rw [if_pos rfl, if_pos (Or.inr rfl), Finset.card_erase_of_mem hmemv, card_neighborFinset_eq_degree]
    · have hnot : ¬(x = u ∨ x = v) := by tauto
      rw [if_neg hxv, if_neg hnot, card_neighborFinset_eq_degree]

private lemma degree_deleteEdges_singleton_le {V : Type} [Fintype V] (G : SimpleGraph V)
    {e : Sym2 V} (x : V) :
    (G.deleteEdges {e}).degree x ≤ G.degree x :=
  degree_le_of_le (G := G.deleteEdges {e}) (H := G) (deleteEdges_le {e})

private lemma degree_sub_one_le_deleteEdges_singleton {V : Type} [Fintype V] (G : SimpleGraph V)
    {e : Sym2 V} (x : V) :
    G.degree x - 1 ≤ (G.deleteEdges {e}).degree x := by
  obtain ⟨u, v, rfl⟩ : ∃ u v, e = s(u, v) := Sym2.ind (fun u v => ⟨u, v, rfl⟩) e
  by_cases hadj : G.Adj u v
  · rw [degree_deleteEdges_singleton_of_adj G hadj]
    split_ifs <;> omega
  · have hnf : (G.deleteEdges {s(u, v)}).neighborFinset x = G.neighborFinset x := by
      ext y
      simp only [mem_neighborFinset, deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
      constructor
      · exact fun h => h.1
      · intro hxy
        refine ⟨hxy, fun h => ?_⟩
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hadj hxy
        · exact hadj hxy.symm
    simp_rw [degree, hnf]
    omega

private lemma deleteEdges_regular_deg_props {V : Type} [Fintype V] (G : SimpleGraph V)
    {r : ℕ} (hreg : ∀ v : V, G.degree v = r) (e : G.edgeSet) (h4 : 4 ≤ Fintype.card V) :
    (∀ x : V, (G.deleteEdges {e.val}).degree x ≤ r) ∧
      2 ≤ (Finset.univ.filter fun x : V => (G.deleteEdges {e.val}).degree x = r).card := by
  rcases e with ⟨e, he⟩
  obtain ⟨u, v, rfl⟩ : ∃ u v, e = s(u, v) := Sym2.ind (fun u v => ⟨u, v, rfl⟩) e
  have hadj : G.Adj u v := (G.mem_edgeSet).mp he
  have hdeg : ∀ x : V, (G.deleteEdges {s(u, v)}).degree x =
      if x = u ∨ x = v then r - 1 else r := by
    intro x
    rw [degree_deleteEdges_singleton_of_adj G hadj x, hreg x]
  constructor
  · intro x
    rw [hdeg x]
    split_ifs <;> omega
  · have hsub : (Finset.univ \ ({u, v} : Finset V)) ⊆
        Finset.univ.filter fun x : V => (G.deleteEdges {s(u, v)}).degree x = r := by
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
        true_and, not_or] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hdeg x, hx.1, hx.2, or_self,
        ↓reduceIte]
    calc
      2 ≤ Fintype.card V - 2 := by omega
      _ ≤ (Finset.univ \ ({u, v} : Finset V)).card := by
        have hle : ({u, v} : Finset V).card ≤ 2 := Finset.card_le_two
        have hs := Finset.card_sdiff_add_card_inter (Finset.univ : Finset V) {u, v}
        simp only [Finset.univ_inter, Finset.card_univ] at hs
        omega
      _ ≤ (Finset.univ.filter fun x : V => (G.deleteEdges {s(u, v)}).degree x = r).card :=
        Finset.card_le_card hsub

private lemma regular_edge_reconstructible {V : Type} [Fintype V] (G H : SimpleGraph V)
    (hE : 4 ≤ G.edgeSet.ncard) (h : EdgeHypomorphic G H)
    {r : ℕ} (hreg : ∀ v : V, G.degree v = r) : Nonempty (G ≃g H) := by
  obtain ⟨σ, hσ⟩ := h
  have hEG : 4 ≤ G.edgeFinset.card := by rwa [← ncard_edgeSet_eq_card_edgeFinset]
  have hEH_eq : G.edgeFinset.card = H.edgeFinset.card := by
    rw [← G.card_edgeSet, ← H.card_edgeSet]
    exact Fintype.card_congr σ
  have hEH : 4 ≤ H.edgeFinset.card := hEH_eq ▸ hEG
  have h4V : 4 ≤ Fintype.card V := four_le_card_of_four_le_edgeFinset G hEG
  have hGne : G.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨e₀val, he₀mem⟩ := hGne
  let e₀ : G.edgeSet := ⟨e₀val, (G.mem_edgeFinset).mp he₀mem⟩
  have hH_card_le_r : ∀ (e' : H.edgeSet),
      (∀ y : V, (H.deleteEdges {e'.val}).degree y ≤ r) ∧
      2 ≤ (Finset.univ.filter fun y : V => (H.deleteEdges {e'.val}).degree y = r).card := by
    intro e'
    have hsim : Nonempty (G.deleteEdges {(σ.symm e').val} ≃g H.deleteEdges {e'.val}) := by
      simpa only [Equiv.apply_symm_apply] using hσ (σ.symm e')
    obtain ⟨ψ⟩ := hsim
    have hg := deleteEdges_regular_deg_props G hreg (σ.symm e') h4V
    constructor
    · intro y
      have hdeg : (H.deleteEdges {e'.val}).degree y =
          (G.deleteEdges {(σ.symm e').val}).degree (ψ.symm y) := by
        simp [ψ.symm.degree_eq y]
      rw [hdeg]
      exact hg.1 (ψ.symm y)
    · have himg : Finset.image ψ
          (Finset.univ.filter fun x : V => (G.deleteEdges {(σ.symm e').val}).degree x = r) ⊆
          Finset.univ.filter fun y : V => (H.deleteEdges {e'.val}).degree y = r := by
        intro y hy
        rw [Finset.mem_image] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        rw [ψ.degree_eq x]
        exact hx
      have hcard :
          (Finset.univ.filter fun x : V => (G.deleteEdges {(σ.symm e').val}).degree x = r).card =
          (Finset.image ψ (Finset.univ.filter fun x : V =>
            (G.deleteEdges {(σ.symm e').val}).degree x = r)).card :=
        (Finset.card_image_of_injective _ ψ.injective).symm
      calc
        2 ≤ (Finset.univ.filter fun x : V =>
            (G.deleteEdges {(σ.symm e').val}).degree x = r).card := hg.2
        _ = (Finset.image ψ (Finset.univ.filter fun x : V =>
            (G.deleteEdges {(σ.symm e').val}).degree x = r)).card := hcard
        _ ≤ (Finset.univ.filter fun y : V => (H.deleteEdges {e'.val}).degree y = r).card :=
          Finset.card_le_card himg
  have hH_le : ∀ x : V, H.degree x ≤ r := by
    intro x
    by_contra hgt
    have hge : r + 1 ≤ H.degree x := Nat.lt_of_not_le hgt
    by_cases hnon : ∃ e' ∈ H.edgeFinset, x ∉ e'
    · obtain ⟨e'val, he'mem, hxnot⟩ := hnon
      let e' : H.edgeSet := ⟨e'val, (H.mem_edgeFinset).mp he'mem⟩
      obtain ⟨a, b, hab⟩ : ∃ a b, e'val = s(a, b) := Sym2.ind (fun a b => ⟨a, b, rfl⟩) e'val
      have hadj : H.Adj a b := (H.mem_edgeSet).mp (hab ▸ e'.prop)
      have hxne_a : x ≠ a := fun hxa => hxnot (hab ▸ hxa ▸ Sym2.mem_mk_left a b)
      have hxne_b : x ≠ b := fun hxb => hxnot (hab ▸ hxb ▸ Sym2.mem_mk_right a b)
      have hdeg_eq : (H.deleteEdges {e'.val}).degree x = H.degree x := by
        change (H.deleteEdges {e'val}).degree x = H.degree x
        rw [hab, degree_deleteEdges_singleton_of_adj H hadj x]
        simp [hxne_a, hxne_b]
      have hle := (hH_card_le_r e').1 x
      omega
    · push Not at hnon
      have hinc : H.incidenceFinset x = H.edgeFinset := by
        apply Finset.Subset.antisymm (H.incidenceFinset_subset x)
        intro e'val he'mem
        rw [H.incidenceFinset_eq_filter]
        exact Finset.mem_filter.mpr ⟨he'mem, hnon e'val he'mem⟩
      have hdegx : H.degree x = H.edgeFinset.card := by
        rw [← H.card_incidenceFinset_eq_degree, hinc]
      have hother : ∀ y : V, y ≠ x → H.degree y ≤ 1 := by
        intro y hyx
        have hsub : H.neighborFinset y ⊆ {x} := by
          intro z hz
          rw [H.mem_neighborFinset] at hz
          have hemem : s(y, z) ∈ H.edgeFinset := (H.mem_edgeFinset).mpr hz
          have hxmem := hnon s(y, z) hemem
          rw [Sym2.mem_iff] at hxmem
          rcases hxmem with rfl | rfl
          · exact False.elim (hyx rfl)
          · exact Finset.mem_singleton_self _
        calc
          H.degree y = (H.neighborFinset y).card := rfl
          _ ≤ ({x} : Finset V).card := Finset.card_le_card hsub
          _ = 1 := Finset.card_singleton x
      have hHne : H.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨e'val, he'mem⟩ := hHne
      let e' : H.edgeSet := ⟨e'val, (H.mem_edgeFinset).mp he'mem⟩
      have hle_x := (hH_card_le_r e').1 x
      have hsub_x := degree_sub_one_le_deleteEdges_singleton H (e := e'.val) x
      have hr3 : 3 ≤ r := by omega
      have hsub_r : (Finset.univ.filter fun y : V => (H.deleteEdges {e'.val}).degree y = r) ⊆
          {x} := by
        intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        by_contra hyx
        simp only [Finset.mem_singleton] at hyx
        have hy_le : (H.deleteEdges {e'.val}).degree y ≤ 1 :=
          (degree_deleteEdges_singleton_le H y).trans (hother y hyx)
        omega
      have hc2 := (hH_card_le_r e').2
      have hc1 : (Finset.univ.filter fun y : V => (H.deleteEdges {e'.val}).degree y = r).card ≤ 1 :=
        (Finset.card_le_card hsub_r).trans (Finset.card_singleton x).le
      omega
  have hsum : ∑ x : V, H.degree x = ∑ _x : V, r := by
    calc
      ∑ x : V, H.degree x = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
      _ = 2 * G.edgeFinset.card := by rw [hEH_eq]
      _ = ∑ x : V, G.degree x := G.sum_degrees_eq_twice_card_edges.symm
      _ = ∑ _x : V, r := Finset.sum_congr rfl fun x _ => hreg x
  have hH_reg : ∀ x : V, H.degree x = r := by
    have hforall := (Finset.sum_eq_sum_iff_of_le (fun x _ => hH_le x)).mp hsum
    exact fun x => hforall x (Finset.mem_univ x)
  obtain ⟨u₀, v₀, hu₀v₀⟩ : ∃ u₀ v₀, e₀.val = s(u₀, v₀) :=
    Sym2.ind (fun u v => ⟨u, v, rfl⟩) e₀.val
  have hadjG : G.Adj u₀ v₀ := (G.mem_edgeSet).mp (hu₀v₀ ▸ e₀.prop)
  have hr_pos : 1 ≤ r := by
    have := hadjG.degree_pos_left
    rw [hreg u₀] at this
    omega
  let e₁ : H.edgeSet := σ e₀
  obtain ⟨a, b, hab⟩ : ∃ a b, e₁.val = s(a, b) :=
    Sym2.ind (fun a b => ⟨a, b, rfl⟩) e₁.val
  have hadjH : H.Adj a b := (H.mem_edgeSet).mp (hab ▸ e₁.prop)
  obtain ⟨φ⟩ := hσ e₀
  have hmem_pair : ∀ x : V, x = u₀ ∨ x = v₀ ↔ φ x = a ∨ φ x = b := by
    intro x
    have hdegG : (G.deleteEdges {e₀.val}).degree x = if x = u₀ ∨ x = v₀ then r - 1 else r := by
      rw [hu₀v₀, degree_deleteEdges_singleton_of_adj G hadjG x, hreg x]
    have hdegH : (H.deleteEdges {e₁.val}).degree (φ x) =
        if φ x = a ∨ φ x = b then r - 1 else r := by
      have hdegH_gen : ∀ y : V, (H.deleteEdges {e₁.val}).degree y =
          if y = a ∨ y = b then r - 1 else r := by
        intro y
        rw [hab, degree_deleteEdges_singleton_of_adj H hadjH y, hH_reg y]
      exact hdegH_gen (φ x)
    have heq_deg : (H.deleteEdges {e₁.val}).degree (φ x) =
        (G.deleteEdges {e₀.val}).degree x := by
      simp [e₁, φ.degree_eq x]
    rw [hdegH, hdegG] at heq_deg
    constructor
    · intro hx
      simp only [hx, ↓reduceIte] at heq_deg
      by_contra hnot
      simp only [hnot, ↓reduceIte] at heq_deg
      omega
    · intro hφ
      simp only [hφ, ↓reduceIte] at heq_deg
      by_contra hnot
      simp only [hnot, ↓reduceIte] at heq_deg
      omega
  have hmap_edge : Sym2.map φ.toEquiv e₀.val = e₁.val := by
    have hmap_pair : s(φ u₀, φ v₀) = s(a, b) := by
      have h1 := (hmem_pair u₀).mp (Or.inl rfl)
      have h2 := (hmem_pair v₀).mp (Or.inr rfl)
      have hne : φ u₀ ≠ φ v₀ := fun heq => hadjG.ne (φ.injective heq)
      rcases h1 with h1a | h1b <;> rcases h2 with h2a | h2b
      · exact False.elim (hne (h1a.trans h2a.symm))
      · rw [h1a, h2b]
      · rw [h1b, h2a, Sym2.eq_swap]
      · exact False.elim (hne (h1b.trans h2b.symm))
    calc
      Sym2.map φ.toEquiv e₀.val = Sym2.map φ.toEquiv s(u₀, v₀) := congrArg _ hu₀v₀
      _ = s(φ u₀, φ v₀) := Sym2.map_mk _ _ _
      _ = s(a, b) := hmap_pair
      _ = e₁.val := hab.symm
  have hmap_inv : ∀ x y : V, Sym2.map φ.toEquiv s(x, y) = e₁.val → s(x, y) = e₀.val := by
    intro x y hxy
    have hsym := congrArg (Sym2.map φ.symm.toEquiv) hxy
    rw [Sym2.map_map] at hsym
    have hcomp1 : φ.symm.toEquiv ∘ φ.toEquiv = id := by
      ext z
      exact φ.symm_apply_apply z
    rw [hcomp1, Sym2.map_id, id_eq] at hsym
    have hsym0 := congrArg (Sym2.map φ.symm.toEquiv) hmap_edge
    rw [Sym2.map_map, hcomp1, Sym2.map_id, id_eq] at hsym0
    exact hsym.trans hsym0.symm
  refine ⟨⟨φ.toEquiv, ?_⟩⟩
  intro x y
  by_cases hxy : s(x, y) = e₀.val
  · have hφxy : s(φ x, φ y) = e₁.val := by
      calc
        s(φ x, φ y) = Sym2.map φ.toEquiv s(x, y) := (Sym2.map_mk _ _ _).symm
        _ = Sym2.map φ.toEquiv e₀.val := congrArg _ hxy
        _ = e₁.val := hmap_edge
    have hGadj : G.Adj x y := (G.mem_edgeSet).mp (by rw [hxy]; exact e₀.prop)
    have hHadj : H.Adj (φ x) (φ y) := (H.mem_edgeSet).mp (by rw [hφxy]; exact e₁.prop)
    exact iff_of_true hHadj hGadj
  · have hφxy : s(φ x, φ y) ≠ e₁.val := by
      intro heq
      apply hxy
      apply hmap_inv x y
      simpa [Sym2.map_mk] using heq
    have h1 : (G.deleteEdges {e₀.val}).Adj x y ↔ G.Adj x y := by
      simp [deleteEdges_adj, hxy]
    have h2 : (H.deleteEdges {e₁.val}).Adj (φ x) (φ y) ↔ H.Adj (φ x) (φ y) := by
      simp [deleteEdges_adj, hφxy]
    have h3 : (H.deleteEdges {e₁.val}).Adj (φ x) (φ y) ↔ (G.deleteEdges {e₀.val}).Adj x y := by
      simpa [e₁] using (φ.map_rel_iff (a := x) (b := y))
    exact h2.symm.trans (h3.trans h1)

end RegularProof

theorem main : H1 → H2 → H3 → H4 → type_of% @ReconstructionConjecture.edge_reconstruction_conjecture := by
  intro h1 h2 h3 h4 V _ G H hE hEH
  rcases h1 G H hE hEH with hIso | ⟨W, _, G', H', hW, hE', hConn, hNoIso, hEH', hHyp', hLift⟩
  · exact hIso
  · apply hLift
    classical
    by_cases hreg : ∃ r : ℕ, ∀ w : W, G'.degree w = r
    · obtain ⟨r, hr⟩ := hreg
      exact regular_edge_reconstructible G' H' hE' hEH' hr
    · have hnonreg : ∃ u v : W, (G'.neighborSet u).ncard ≠ (G'.neighborSet v).ncard := by
        by_contra hno
        push Not at hno
        have hWpos : Nonempty W := Fintype.card_pos_iff.mp (by omega)
        obtain ⟨u₀⟩ := hWpos
        apply hreg
        refine ⟨G'.degree u₀, fun w => ?_⟩
        rw [← ncard_neighborSet_eq_degree G' w, ← ncard_neighborSet_eq_degree G' u₀]
        exact hno w u₀
      by_cases hmul : Nat.factorial (Fintype.card W) < 2 ^ (G'.edgeSet.ncard - 1)
      · exact h2 G' H' hW hE' hmul hConn hNoIso hEH' hHyp'
      · have hmul_le : 2 ^ (G'.edgeSet.ncard - 1) ≤ Nat.factorial (Fintype.card W) :=
          Nat.le_of_not_lt hmul
        by_cases hlin : 1000 * Fintype.card W ≤ G'.edgeSet.ncard
        · exact h3 G' H' hW hE' hlin hmul_le hConn hNoIso hnonreg hEH' hHyp'
        · have hsparse : G'.edgeSet.ncard < 1000 * Fintype.card W := Nat.lt_of_not_le hlin
          exact h4 G' H' hW hE' hsparse hmul_le hConn hNoIso hnonreg hEH' hHyp'

end OMA.R_ReconstructionConjecture_edge_reconstruction_conjecture_R1
