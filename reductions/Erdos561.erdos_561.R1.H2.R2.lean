import OMAReductions.R_Erdos561_erdos_561_R1

/-!
# Weighted matching bounds for the size Ramsey lower bound

The preceding matching-number reduction uses a Tutte separator to supply
a matching of size s+t−1 under a condition on the smaller arm size.
Here each star of size m in a separator component requires
floor((m+1)/2) pairs of vertices. If one list has at least the opposite
component count minus one in extra pairs, the same matching size is
necessary for a forcing host.

A matching of that size can pay for reducing the positive arms in a
nonempty prefix by one when the diagonal-sum loss is at most s+t−1.
This also handles some lists with a suffix of one-edge stars.
The matching-deletion argument follows Chunlin You (arXiv:2610.25958).
The star forest edge indexing follows the parent reduction by
@marcusbuffett. The unweighted separator argument and the pure matching
case are retained from the earlier reduction of this target.
-/

open Finset SimpleGraph

namespace OMA.R_Erdos561_erdos_561_R1_H2_R2

noncomputable section

private def edges {V : Type} (G : SimpleGraph V) : ℕ := G.edgeSet.ncard

private theorem edges_eq {V : Type} (G : SimpleGraph V) [Fintype G.edgeSet] :
    edges G = G.edgeFinset.card := by
  rw [edges, Set.ncard_eq_toFinset_card']
  rfl

private def Matching {V : Type} (M : SimpleGraph V) : Prop :=
  ∀ ⦃u v w⦄, M.Adj u v → M.Adj u w → v = w

private def extendGraph {V : Type} (G : SimpleGraph V) (d : ℕ) :
    SimpleGraph (V ⊕ Fin d) where
  Adj u v := match u, v with
    | .inl x, .inl y => G.Adj x y
    | _, _ => u ≠ v
  symm := by
    constructor
    intro a b
    cases a <;> cases b <;> simp only
    · exact fun h => h.symm
    all_goals exact Ne.symm
  loopless := by
    constructor
    intro a
    cases a
    · exact G.irrefl
    · exact fun h => h rfl

private theorem extend_inl {V : Type} (G : SimpleGraph V) (d : ℕ) (x y : V) :
    (extendGraph G d).Adj (.inl x) (.inl y) ↔ G.Adj x y := Iff.rfl

private theorem extend_inr {V : Type} (G : SimpleGraph V) (d : ℕ) (x : Fin d)
    (y : V ⊕ Fin d) : (extendGraph G d).Adj (.inr x) y ↔ .inr x ≠ y := by
  cases y <;> rfl

private theorem matching_of_perfect {V : Type} [Fintype V] (G : SimpleGraph V) (d : ℕ)
    (M : (extendGraph G d).Subgraph) (hM : M.IsPerfectMatching) :
    ∃ R ≤ G, Matching R ∧ Fintype.card V ≤ 2 * edges R + d := by
  classical
  let R := M.spanningCoe.comap Sum.inl
  have hR (u v : V) : R.Adj u v ↔ M.Adj (.inl u) (.inl v) := Iff.rfl
  have hmatch : Matching R := by
    intro u v w hu hv
    exact Sum.inl_injective (hM.1.eq_of_adj_left ((hR u v).mp hu) ((hR u w).mp hv))
  refine ⟨R, fun u v h => (extend_inl G d u v).mp (M.adj_sub h), hmatch, ?_⟩
  have hm (u : V ⊕ Fin d) : ∃ w, M.Adj u w := by
    obtain ⟨w, hw, _⟩ := (Subgraph.isPerfectMatching_iff.mp hM) u
    exact ⟨w, hw⟩
  let U := univ.filter (fun u : V => ¬ ∃ v, R.Adj u v)
  have hmate (u : U) : ∃ w : Fin d, M.Adj (.inl (u : V)) (.inr w) := by
    obtain ⟨w, hw⟩ := hm (.inl (u : V))
    cases w with
    | inl v => exact ((mem_filter.mp u.2).2 ⟨v, (hR u v).mpr hw⟩).elim
    | inr v => exact ⟨v, hw⟩
  let f (u : U) := (hmate u).choose
  have hf : Function.Injective f := by
    intro u v he
    have hu := (hmate u).choose_spec
    have hv := (hmate v).choose_spec
    change f u = f v at he
    change M.Adj (.inl (u : V)) (.inr (f u)) at hu
    change M.Adj (.inl (v : V)) (.inr (f v)) at hv
    rw [he] at hu
    apply Subtype.ext
    exact Sum.inl_injective (hM.1.eq_of_adj_right hu hv)
  have hU : U.card ≤ d := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective f hf
  have hdeg (u : V) : R.degree u = if (∃ v, R.Adj u v) then 1 else 0 := by
    by_cases hu : ∃ v, R.Adj u v
    · rw [if_pos hu, degree_eq_one_iff_existsUnique_adj]
      obtain ⟨v, hv⟩ := hu
      exact ⟨v, hv, fun w hw => hmatch hw hv⟩
    · rw [if_neg hu, ← card_neighborFinset_eq_degree, card_eq_zero]
      exact eq_empty_iff_forall_notMem.mpr (fun w hw => hu ⟨w, by simpa using hw⟩)
  have hcard : (univ.filter (fun u : V => ∃ v, R.Adj u v)).card = 2 * edges R := by
    rw [edges_eq, ← R.sum_degrees_eq_twice_card_edges]
    simp_rw [hdeg]
    rw [← sum_filter]
    simp
  have hsum := card_filter_add_card_filter_not (s := (univ : Finset V))
    (p := fun u => ∃ v, R.Adj u v)
  rw [hcard, card_univ] at hsum
  change _ + U.card = _ at hsum
  omega

private theorem component_budget {W : Type} [DecidableEq W] [Fintype W]
    (Q : SimpleGraph W) [DecidableRel Q.Adj] :
    2 * (∑ C : Q.ConnectedComponent, C.supp.ncard / 2) +
      Q.oddComponents.ncard = Fintype.card W := by
  classical
  have hc : (∑ C : Q.ConnectedComponent, C.supp.ncard) = Fintype.card W := by
    have hx := card_eq_sum_card_fiberwise (s := (univ : Finset W))
      (t := (univ : Finset Q.ConnectedComponent))
      (f := Q.connectedComponentMk) (fun _ _ => mem_univ _)
    simpa only [card_univ, ConnectedComponent.supp, Set.toFinset_ofPred,
      Set.ncard_eq_toFinset_card'] using hx.symm
  have ho : Q.oddComponents.ncard =
      ∑ c : Q.ConnectedComponent, (if Odd c.supp.ncard then 1 else 0) := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, ← sum_filter]
    simp
  rw [← hc, ho, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro C _
  by_cases h : Odd C.supp.ncard
  · rw [if_pos h]
    rw [Nat.odd_iff] at h
    omega
  · rw [if_neg h]
    rw [Nat.odd_iff] at h
    omega

private def fibre {V C : Type} {S : Set V} (f : (Sᶜ : Set V) → C) (c : C) :
    Set (Sᶜ : Set V) := {u | f u = c}

-- Add enough universal vertices that a perfect matching would leave at least q
-- edges on the original vertices. A Tutte violator contains all the added vertices.
private theorem matching_or_partition {V : Type} [Fintype V] (G : SimpleGraph V) (q : ℕ) :
    (∃ M ≤ G, Matching M ∧ q ≤ edges M) ∨
      ∃ (S : Set V) (C : Type) (_iC : Fintype C) (f : (Sᶜ : Set V) → C),
        (∀ u v : (Sᶜ : Set V), G.Adj u v → f u = f v) ∧
        S.ncard + (∑ c : C, (fibre f c).ncard / 2) < q := by
  classical
  by_cases hsmall : Fintype.card V < 2 * q
  · right
    refine ⟨∅, Unit, inferInstance, fun _ => (), fun _ _ _ => rfl, ?_⟩
    have hV : (fibre (S := (∅ : Set V)) (fun _ => ()) ()).ncard = Fintype.card V := by
      rw [show fibre (S := (∅ : Set V)) (fun _ => ()) () = Set.univ from by ext; simp [fibre]]
      simp
    simp only [Fintype.sum_unique, Set.ncard_empty, zero_add, hV]
    omega
  let d := Fintype.card V - 2 * q
  have hVd : Fintype.card V = 2 * q + d := by
    dsimp [d]
    omega
  let J := extendGraph G d
  by_cases hm : ∃ M : J.Subgraph, M.IsPerfectMatching
  · left
    obtain ⟨M, hM⟩ := hm
    obtain ⟨R, hR, hsmallR, hcard⟩ := matching_of_perfect G d M hM
    refine ⟨R, hR, hsmallR, ?_⟩
    omega
  · right
    have heven : Even (Nat.card (V ⊕ Fin d)) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin]
      refine ⟨Fintype.card V - q, ?_⟩
      omega
    obtain ⟨U, hU⟩ := exists_isTutteViolator (by simpa only [not_exists] using hm) heven
    let T := (⊤ : J.Subgraph).deleteVerts U
    let Q := T.coe
    have hodd : U.ncard < Q.oddComponents.ncard := hU
    have hT : T.verts = Uᶜ := by simp [T, Set.compl_eq_univ_sdiff]
    have hcardT : Nat.card T.verts + U.ncard = Fintype.card V + d := by
      have h := Set.ncard_add_ncard_compl U
      rw [hT, Nat.card_coe_set_eq]
      simpa only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin, add_comm] using h
    have hall (i : Fin d) : Sum.inr i ∈ U := by
      by_contra hi
      let u : T.verts := ⟨.inr i, by simpa [hT] using hi⟩
      have hreach (v : T.verts) : Q.Reachable u v := by
        by_cases hv : u = v
        · subst v
          exact Reachable.rfl
        · apply Adj.reachable
          change T.Adj u v
          refine Subgraph.deleteVerts_adj.mpr ⟨by simp, hi, by simp, ?_, ?_⟩
          · simpa [hT] using v.2
          · change J.Adj (.inr i) v.val
            exact (extend_inr G d i v.val).mpr (fun h => hv (Subtype.ext h))
      have hconn : Q.Preconnected := fun v w => (hreach v).symm.trans (hreach w)
      let : Subsingleton Q.ConnectedComponent := hconn.subsingleton_connectedComponent
      have ho : Q.oddComponents.ncard ≤ 1 := Set.ncard_le_one_of_subsingleton _
      have hzero : U.ncard = 0 := by omega
      have hpar := (odd_ncard_oddComponents Q).mp (show Odd Q.oddComponents.ncard from by
        have he : Q.oddComponents.ncard = 1 := by omega
        simp [he])
      change Odd (Nat.card T.verts) at hpar
      obtain ⟨z, hz⟩ := hpar
      omega
    let S : Set V := Sum.inl ⁻¹' U
    let e : (Sᶜ : Set V) ≃ T.verts := by
      refine Equiv.ofBijective (fun v => ⟨.inl v.val, ?_⟩) ⟨?_, ?_⟩
      · rw [hT]
        exact v.property
      · intro v w h
        exact Subtype.ext (Sum.inl_injective (congrArg Subtype.val h))
      · intro u
        have hu : u.val ∉ U := by simpa [hT] using u.property
        cases he : u.val with
        | inl x => exact ⟨⟨x, by simpa [S, he] using hu⟩, Subtype.ext he.symm⟩
        | inr i => exact (hu (he ▸ hall i)).elim
    have hcardS : S.ncard + d = U.ncard := by
      have he := Nat.card_congr e
      have hs := Set.ncard_add_ncard_compl S
      rw [Nat.card_coe_set_eq] at he
      rw [Nat.card_eq_fintype_card] at hs
      omega
    let f : (Sᶜ : Set V) → Q.ConnectedComponent := fun v => Q.connectedComponentMk (e v)
    refine ⟨S, Q.ConnectedComponent, inferInstance, f, ?_, ?_⟩
    · intro u v huv
      apply ConnectedComponent.connectedComponentMk_eq_of_adj
      change T.Adj (.inl u.val) (.inl v.val)
      exact Subgraph.deleteVerts_adj.mpr ⟨by simp, u.property, by simp, v.property, huv⟩
    · have he (c : Q.ConnectedComponent) : (fibre f c).ncard = c.supp.ncard :=
        Set.ncard_congr' (e.subtypeEquiv fun _ => Iff.rfl)
      simp only [he]
      have h := component_budget Q
      rw [← Nat.card_eq_fintype_card] at h
      change S.ncard + (∑ c : Q.ConnectedComponent, c.supp.ncard / 2) < q
      omega

private abbrev forest {s : ℕ} (n : Fin s → ℕ) : SimpleGraph (Σ i, Fin (n i + 1)) :=
  fromRel (fun (u v : Σ i, Fin (n i + 1)) =>
    u.1 = v.1 ∧ (u.2.val = 0 ∨ v.2.val = 0))

private theorem spoke_adj {s : ℕ} (n : Fin s → ℕ) (i : Fin s) (a : Fin (n i)) :
    (forest n).Adj ⟨i, 0⟩ ⟨i, a.succ⟩ :=
  (OMA.R_Erdos561_erdos_561_R1.forest_adj n).mpr ⟨i, a, Or.inl ⟨rfl, rfl⟩⟩

private theorem forest_neighbor {s : ℕ} {n : Fin s → ℕ} (hn : ∀ i, 1 ≤ n i)
    (u : Σ i, Fin (n i + 1)) : ∃ v, (forest n).Adj u v := by
  obtain ⟨i, a⟩ := u
  induction a using Fin.cases with
  | zero => exact ⟨_, spoke_adj n i ⟨0, hn i⟩⟩
  | succ a => exact ⟨_, (spoke_adj n i a).symm⟩

private theorem hit_card {V : Type} {s : ℕ} (n : Fin s → ℕ) {I : Finset (Fin s)}
    {B : Finset V} {e : (Σ i, Fin (n i + 1)) → V} (he : Function.Injective e)
    (hits : ∀ i ∈ I, ∃ a : Fin (n i + 1), e ⟨i, a⟩ ∈ B) : I.card ≤ B.card := by
  classical
  let f (i : I) : B := ⟨e ⟨i, (hits i i.2).choose⟩, (hits i i.2).choose_spec⟩
  have hf : Function.Injective f := by
    intro i j h
    exact Subtype.ext (congrArg Sigma.fst (he (congrArg Subtype.val h)))
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

private def avoiding {V : Type} {s t : ℕ} (G : SimpleGraph V)
    (n : Fin s → ℕ) (m : Fin t → ℕ) : Prop :=
  ∃ R ≤ G, ¬ (forest n).IsContained R ∧ ¬ (forest m).IsContained (G \ R)

private theorem distribute {C : Type} (A : Finset C) (cap : C → ℕ) {r : ℕ}
    (hr : r ≤ ∑ c ∈ A, cap c) :
    ∃ b : C → ℕ, (∀ c ∈ A, b c ≤ cap c) ∧ (∑ c ∈ A, b c) = r := by
  classical
  induction A using Finset.induction_on generalizing r with
  | empty =>
    have : r = 0 := by simpa using hr
    exact ⟨fun _ => 0, by simp, by simp [this]⟩
  | @insert a A ha ih =>
    rw [sum_insert ha] at hr
    have h := ih (r := r - min r (cap a)) (by omega)
    obtain ⟨b, hb, hsum⟩ := h
    let f := Function.update b a (min r (cap a))
    have hrest : ∀ c ∈ A, f c = b c := by
      intro c hc
      have hne : c ≠ a := fun he => ha (he ▸ hc)
      simp [f, Function.update_of_ne hne]
    refine ⟨f, ?_, ?_⟩
    · intro c hc
      rcases mem_insert.mp hc with rfl | hc
      · simp [f]
      · rw [hrest c hc]
        exact hb c hc
    · rw [sum_insert ha, sum_congr rfl hrest, hsum]
      simp [f]

private def without {V : Type} (G : SimpleGraph V) (B : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∉ B ∧ v ∉ B
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

private theorem blue_cover {V : Type} {s t : ℕ} (G : SimpleGraph V)
    {n : Fin s → ℕ} (m : Fin t → ℕ) (hm : ∀ j, 1 ≤ m j)
    (B : Finset V) (hB : B.card < t) (h : ¬ (forest n).IsContained (without G B)) :
    avoiding G n m := by
  classical
  refine ⟨without G B, fun _ _ h => h.1, h, ?_⟩
  rintro ⟨e⟩
  have hc : (univ : Finset (Fin t)).card ≤ B.card := by
    apply hit_card m e.injective
    intro i _
    let a : Fin (m i) := ⟨0, hm i⟩
    have ha := e.toHom.map_adj (spoke_adj m i a)
    by_cases hv : e ⟨i, 0⟩ ∈ B
    · exact ⟨0, hv⟩
    · refine ⟨a.succ, Classical.byContradiction fun hw => ?_⟩
      exact ha.2 ⟨ha.1, hv, hw⟩
  simp only [card_univ, Fintype.card_fin] at hc
  omega

private theorem partition_avoids {V C : Type} [Fintype V] [Fintype C] {s t : ℕ}
    (G : SimpleGraph V) (n : Fin s → ℕ) (m : Fin t → ℕ)
    (hs : 1 ≤ s) (ht : 1 ≤ t) (a : ℕ) (ha : 2 ≤ a) (hst : t ≤ (a - 1) * s + 1)
    (hn : ∀ i, a ≤ n i) (hm : ∀ i, 1 ≤ m i)
    (S : Set V) (f : (Sᶜ : Set V) → C)
    (hf : ∀ u v : (Sᶜ : Set V), G.Adj u v → f u = f v)
    (hbudget : S.ncard + (∑ c : C, (fibre f c).ncard / 2) < s + t - 1) :
    avoiding G n m := by
  classical
  let w (c : C) := (fibre f c).ncard / 2
  let W := ∑ c, w c
  -- Use blue hubs on the separator first. Charge the remaining separator
  -- vertices to the red component budget.
  let hub := min S.ncard (t - 1)
  let p := s - 1 - (S.ncard - hub)
  let q := t - 1 - hub
  have hS : S.ncard - hub ≤ s - 1 := by
    change S.ncard + W < s + t - 1 at hbudget
    dsimp [hub]
    omega
  have hW : W ≤ p + q := by
    change S.ncard + W < s + t - 1 at hbudget
    dsimp [p, q, hub]
    omega
  have hWa : W < a * (p + 1) := by
    by_cases h : S.ncard ≤ t - 1
    · have hh : p + 1 = s := by dsimp [p, hub]; omega
      rw [hh]
      rw [Nat.sub_mul, Nat.one_mul] at hst
      have hw : W < s + t - 1 := by
        change S.ncard + W < s + t - 1 at hbudget
        omega
      have hs' := Nat.le_mul_of_pos_left s (by omega : 0 < a)
      omega
    · have hq : q = 0 := by dsimp [q, hub]; omega
      have hp' : W < p + 1 := by omega
      exact hp'.trans_le (Nat.le_mul_of_pos_left _ (by omega))
  -- A component of weight w can spend w - floor(w/a) places on blue hubs.
  -- The unspent places bound the number of remaining disjoint red stars.
  let cap (c : C) := w c - w c / a
  have hab : 0 < a := by omega
  have hd (c : C) : w c / a ≤ w c := Nat.div_le_self _ _
  have hcap : (∑ c : C, w c / a) ≤ p := by
    have hsum : a * (∑ c : C, w c / a) ≤ W := by
      rw [mul_sum]
      exact sum_le_sum fun c _ => Nat.mul_div_le (w c) a
    have hmul : a * (∑ c : C, w c / a) < a * (p + 1) := hsum.trans_lt hWa
    exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_left hmul)
  have hcapsum : (∑ c, cap c) = W - (∑ c : C, w c / a) :=
    sum_tsub_distrib univ (fun c _ => hd c)
  obtain ⟨b, hb, hbsum⟩ := distribute univ cap (r := W - p) (by omega)
  have hbcap (c : C) : b c ≤ cap c := hb c (mem_univ _)
  have hbw (c : C) : b c ≤ w c := (hbcap c).trans (Nat.sub_le _ _)
  have hbn (c : C) : b c ≤ ((fibre f c).toFinset).card := by
    rw [← Set.ncard_eq_toFinset_card']
    have h := hbw c
    dsimp [w] at h
    omega
  choose B hBsub hBcard using fun c => exists_subset_card_eq (hbn c)
  obtain ⟨H, hHsub, hHcard⟩ := exists_subset_card_eq (s := S.toFinset)
    (n := hub) (by rw [← Set.ncard_eq_toFinset_card']; exact min_le_left _ _)
  let Bext := (univ.biUnion B).image (fun u : (Sᶜ : Set V) => u.val)
  let blue := H ∪ Bext
  have hblue : blue.card ≤ t - 1 := by
    have h₁ : Bext.card ≤ ∑ c, (B c).card :=
      card_image_le.trans (card_biUnion_le (s := univ) (t := B))
    simp only [hBcard, hbsum] at h₁
    have h₂ := (card_union_le H Bext).trans (Nat.add_le_add_left h₁ H.card)
    rw [hHcard] at h₂
    change (H ∪ Bext).card ≤ hub + (W - p) at h₂
    change (H ∪ Bext).card ≤ t - 1
    have h₃ : hub ≤ t - 1 := min_le_right _ _
    dsimp [q] at hW
    omega
  let R := without G blue
  refine blue_cover G m hm blue (by omega) ?_
  change ¬ (forest n).IsContained R
  rintro ⟨e⟩
  have hout (i : Fin s) (a : Fin (n i + 1)) : e ⟨i, a⟩ ∉ blue := by
    obtain ⟨v, hv⟩ := forest_neighbor (fun j => (by have := hn j; omega)) ⟨i, a⟩
    exact (e.toHom.map_adj hv).2.1
  let I := univ.filter (fun i : Fin s => ∀ a : Fin (n i + 1), e ⟨i, a⟩ ∉ S)
  have hI {i : Fin s} (hi : i ∈ I) (a : Fin (n i + 1)) : e ⟨i, a⟩ ∉ S :=
    (mem_filter.mp hi).2 a
  have hhits : (univ \ I).card ≤ (S.toFinset \ H).card := by
    apply hit_card n e.injective
    intro i hi
    have h := (mem_sdiff.mp hi).2
    simp only [I, mem_filter, mem_univ, true_and, not_forall, not_not] at h
    obtain ⟨a, ha⟩ := h
    exact ⟨a, mem_sdiff.mpr ⟨Set.mem_toFinset.mpr ha, fun hh =>
      hout i a (mem_union.mpr (Or.inl hh))⟩⟩
  rw [card_sdiff_of_subset hHsub, hHcard, ← Set.ncard_eq_toFinset_card'] at hhits
  let label (i : I) := f ⟨e ⟨i, 0⟩, hI i.2 0⟩
  have hall (i : I) (a : Fin (n i + 1)) :
      f ⟨e ⟨i, a⟩, hI i.2 a⟩ = label i := by
    induction a using Fin.cases with
    | zero => rfl
    | succ a =>
      exact (hf _ _ (e.toHom.map_adj (spoke_adj n i a)).1).symm
  let J (c : C) := univ.filter (fun i : I => label i = c)
  have hJ (c : C) : (a + 1) * (J c).card ≤ (fibre f c).ncard - b c := by
    let f₀ (a : J c × Fin (a + 1)) : Fin (n a.1.val.val + 1) :=
      ⟨a.2.val, by have := hn a.1.val.val; have := a.2.isLt; omega⟩
    let f₁ (a : J c × Fin (a + 1)) : (Sᶜ : Set V) :=
      ⟨e ⟨a.1.val, f₀ a⟩, hI a.1.val.property (f₀ a)⟩
    have hf₁ (a : J c × Fin (a + 1)) : f₁ a ∈ (fibre f c).toFinset \ B c := by
      refine mem_sdiff.mpr ⟨Set.mem_toFinset.mpr ?_, ?_⟩
      · change f (f₁ a) = c
        exact (hall a.1 (f₀ a)).trans (mem_filter.mp a.1.2).2
      · intro ha
        exact hout a.1.val (f₀ a) (mem_union.mpr (Or.inr
          (mem_image.mpr ⟨f₁ a, mem_biUnion.mpr ⟨c, mem_univ _, ha⟩, rfl⟩)))
    let g (a : J c × Fin (a + 1)) : ↥((fibre f c).toFinset \ B c) := ⟨f₁ a, hf₁ a⟩
    have hg : Function.Injective g := by
      intro a a' he
      have he' : (⟨a.1.val.val, f₀ a⟩ : Σ i, Fin (n i + 1)) =
          ⟨a'.1.val.val, f₀ a'⟩ :=
        e.injective (congrArg (fun u => u.val.val) he)
      apply Prod.ext
      · exact Subtype.ext (Subtype.ext (congrArg Sigma.fst he'))
      · exact Fin.ext (congrArg (fun x : Σ i, Fin (n i + 1) => x.2.val) he')
    have hc := Fintype.card_le_of_injective g hg
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, Fintype.card_coe,
      card_sdiff_of_subset (hBsub c), hBcard, ← Set.ncard_eq_toFinset_card'] at hc
    simpa only [Nat.mul_comm] using hc
  have hJ' (c : C) : (J c).card ≤ w c - b c := by
    let k := w c - b c
    have hh : w c / a ≤ k := by
      have h := hbcap c
      dsimp [cap] at h
      have ht := hd c
      dsimp [k]
      omega
    have hw : w c < a * (k + 1) :=
      (Nat.lt_mul_div_succ (w c) hab).trans_le (Nat.mul_le_mul_left a (by omega))
    have h₃ : (fibre f c).ncard ≤ 2 * w c + 1 := by dsimp [w]; omega
    have h₄ := hbw c
    have h₅ : (fibre f c).ncard - b c ≤ w c + (k + 1) := by dsimp [k]; omega
    have h₆ : (a + 1) * (J c).card < (a + 1) * (k + 1) := by
      conv_rhs => rw [Nat.add_mul, Nat.one_mul]
      exact (hJ c).trans_lt (h₅.trans_lt (Nat.add_lt_add_right hw _))
    exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_left h₆)
  have hsumI : I.card = ∑ c, (J c).card := by
    have h := card_eq_sum_card_fiberwise (s := (univ : Finset I))
      (t := (univ : Finset C)) (f := label) (fun _ _ => mem_univ _)
    simpa only [J, card_univ, Fintype.card_coe] using h
  have hsumB : (∑ c, (w c - b c)) + (W - p) = W := by
    rw [← hbsum, ← sum_add_distrib]
    exact sum_congr rfl fun c _ => Nat.sub_add_cancel (hbw c)
  have hIcard : I.card ≤ p := by
    rw [hsumI]
    have h := sum_le_sum (fun c (_ : c ∈ (univ : Finset C)) => hJ' c)
    omega
  have htot := card_sdiff_add_card_eq_card (subset_univ I)
  simp only [card_univ, Fintype.card_fin] at htot
  dsimp [p] at hIcard
  omega

private theorem matching_or_avoiding {V : Type} [Fintype V] {s t : ℕ}
    (G : SimpleGraph V) (n : Fin s → ℕ) (m : Fin t → ℕ)
    (hs : 1 ≤ s) (ht : 1 ≤ t) (a : ℕ) (ha : 2 ≤ a) (hst : t ≤ (a - 1) * s + 1)
    (hn : ∀ i, a ≤ n i) (hm : ∀ i, 1 ≤ m i) :
    (∃ M ≤ G, Matching M ∧ s + t - 1 ≤ edges M) ∨ avoiding G n m := by
  rcases matching_or_partition G (s + t - 1) with h | ⟨S, C, iC, f, hf, hB⟩
  · exact Or.inl h
  · exact Or.inr (partition_avoids G n m hs ht a ha hst hn hm S f hf hB)

private theorem trim_matching {V : Type} {s : ℕ} (n : Fin s → ℕ) (R M : SimpleGraph V)
    (hM : Matching M) (h : (forest n).IsContained (R ⊔ M)) :
    (forest (fun i => n i - 1)).IsContained R := by
  classical
  obtain ⟨e⟩ := h
  let A (i : Fin s) := univ.filter (fun a : Fin (n i) => R.Adj (e ⟨i, 0⟩) (e ⟨i, a.succ⟩))
  have hc (i : Fin s) : n i - 1 ≤ (A i).card := by
    let bad := univ.filter (fun a : Fin (n i) => ¬ R.Adj (e ⟨i, 0⟩) (e ⟨i, a.succ⟩))
    have hb : bad.card ≤ 1 := by
      apply card_le_one.mpr
      intro a ha b hb
      have hm (d : Fin (n i)) (hd : d ∈ bad) : M.Adj (e ⟨i, 0⟩) (e ⟨i, d.succ⟩) :=
        ((sup_adj R M _ _).mp (e.toHom.map_adj (spoke_adj n i d))).resolve_left
          (mem_filter.mp hd).2
      have he := e.injective (hM (hm a ha) (hm b hb))
      exact Fin.ext (by
        have hval := congrArg (fun a : Σ j, Fin (n j + 1) => a.2.val) he
        simpa using hval)
    have he := card_filter_add_card_filter_not (s := (univ : Finset (Fin (n i))))
      (p := fun a => R.Adj (e ⟨i, 0⟩) (e ⟨i, a.succ⟩))
    change (A i).card + bad.card = (univ : Finset (Fin (n i))).card at he
    rw [card_univ, Fintype.card_fin] at he
    omega
  have hi (i : Fin s) : Nonempty (Fin (n i - 1) ↪ A i) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa only [Fintype.card_fin, Fintype.card_coe] using hc i
  let f (i : Fin s) := (hi i).some
  let g (i : Fin s) (a : Fin (n i - 1 + 1)) : Fin (n i + 1) :=
    Fin.cases 0 (fun j => (f i j).val.succ) a
  have hg (i : Fin s) : Function.Injective (g i) := by
    intro u v he
    induction u using Fin.cases <;> induction v using Fin.cases
    · rfl
    · exact (Fin.succ_ne_zero _ he.symm).elim
    · exact (Fin.succ_ne_zero _ he).elim
    · exact congrArg Fin.succ ((f i).injective (Subtype.ext (Fin.succ_injective _ he)))
  let k (u : Σ i, Fin (n i - 1 + 1)) : Σ i, Fin (n i + 1) := ⟨u.1, g u.1 u.2⟩
  refine ⟨⟨⟨e ∘ k, ?_⟩, e.injective.comp ?_⟩⟩
  · intro u v huv
    rcases (OMA.R_Erdos561_erdos_561_R1.forest_adj (fun i => n i - 1)).mp huv with
      ⟨i, a, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact (mem_filter.mp (f i a).property).2
    · exact Adj.symm ((mem_filter.mp (f i a).property).2)
  · rintro ⟨i, a⟩ ⟨j, b⟩ h
    obtain rfl : i = j := congrArg Sigma.fst h
    exact congrArg (Sigma.mk i) (hg i (by simpa [k] using h))

private theorem avoiding_swap {V : Type} {s t : ℕ} {G : SimpleGraph V}
    {n : Fin s → ℕ} {m : Fin t → ℕ} (h : avoiding G m n) : avoiding G n m := by
  obtain ⟨R, hR, hm, hn⟩ := h
  have he : G \ (G \ R) = R := by
    ext u v
    simp only [sdiff_adj]
    constructor
    · rintro ⟨hG, hn'⟩
      exact Classical.byContradiction fun hr => hn' ⟨hG, hr⟩
    · intro hr
      exact ⟨hR hr, fun h => h.2 hr⟩
  refine ⟨G \ R, sdiff_le, hn, ?_⟩
  rwa [he]

-- Count the disjoint pairs of vertices reserved by the stars of a copy
-- off the separator, whether or not those pairs themselves are edges.
private theorem copy_budget {V C : Type} [Fintype V] [Fintype C] {t : ℕ}
    (G : SimpleGraph V) (m : Fin t → ℕ)
    (S : Set V) (f : (Sᶜ : Set V) → C)
    (hf : ∀ u v : (Sᶜ : Set V), G.Adj u v → f u = f v)
    (e : (forest m).Copy G) (I : Finset (Fin t))
    (hI : ∀ i ∈ I, ∀ a : Fin (m i + 1), e ⟨i, a⟩ ∉ S) :
    (∑ i ∈ I, (m i + 1) / 2) ≤ ∑ c, (fibre f c).ncard / 2 := by
  classical
  let label (i : I) := f ⟨e ⟨i, 0⟩, hI i i.2 0⟩
  have hall (i : I) (a : Fin (m i + 1)) :
      f ⟨e ⟨i, a⟩, hI i i.2 a⟩ = label i := by
    induction a using Fin.cases with
    | zero => rfl
    | succ a => exact (hf _ _ (e.toHom.map_adj (spoke_adj m i a))).symm
  let J (c : C) := univ.filter (fun i : I => label i = c)
  have hJ (c : C) : (∑ i ∈ J c, (m i + 1) / 2) ≤ (fibre f c).ncard / 2 := by
    let g (v : Σ i : J c, Fin (m i.val + 1)) : fibre f c :=
      ⟨⟨e ⟨v.1.val, v.2⟩, hI v.1.val v.1.val.2 v.2⟩,
        (hall v.1.val v.2).trans (mem_filter.mp v.1.2).2⟩
    have hg : Function.Injective g := by
      rintro ⟨i, a⟩ ⟨j, b⟩ he
      have h := e.injective (congrArg (fun u => u.val.val) he)
      obtain rfl : i = j := Subtype.ext (Subtype.ext (congrArg Sigma.fst h))
      exact congrArg (Sigma.mk i) (Fin.ext (congrArg
        (fun u : Σ i, Fin (m i + 1) => u.2.val) h))
    have hcard := Fintype.card_le_of_injective g hg
    rw [Fintype.card_sigma] at hcard
    simp only [Fintype.card_fin] at hcard
    rw [Set.ncard_eq_toFinset_card']
    -- Reexpress the vertex bound as a sum on the fibre.
    have hcard' : (∑ i ∈ J c, (m i + 1)) ≤ (fibre f c).toFinset.card := by
      rw [← sum_attach (J c) (fun i => m i + 1)]
      simpa only [attach_eq_univ, ← Set.ncard_eq_toFinset_card',
        ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] using hcard
    have hp : 2 * (∑ i ∈ J c, (m i + 1) / 2) ≤ ∑ i ∈ J c, (m i + 1) := by
      rw [mul_sum]
      exact sum_le_sum fun i _ => by omega
    omega
  have hsum :
      (∑ i ∈ I, (m i + 1) / 2) = ∑ c, ∑ i ∈ J c, (m i + 1) / 2 := by
    rw [← sum_attach I (fun i => (m i + 1) / 2), attach_eq_univ]
    exact (sum_fiberwise_of_maps_to (s := (univ : Finset I))
      (t := (univ : Finset C)) (g := label) (fun _ _ => mem_univ _)
      (fun i => (m i + 1) / 2)).symm
  rw [hsum]
  exact sum_le_sum fun c _ => hJ c

private def pairExcess {t : ℕ} (m : Fin t → ℕ) : ℕ :=
  ∑ i, (m i - 1) / 2

private theorem excess_matching_or_avoiding {V : Type} [Fintype V] {s t : ℕ}
    (G : SimpleGraph V) (n : Fin s → ℕ) (m : Fin t → ℕ)
    (hs : 1 ≤ s) (hn : ∀ i, 1 ≤ n i) (hm : ∀ i, 1 ≤ m i)
    (hlarge : s - 1 ≤ pairExcess m) :
    (∃ M ≤ G, Matching M ∧ s + t - 1 ≤ edges M) ∨ avoiding G n m := by
  classical
  rcases matching_or_partition G (s + t - 1) with h | ⟨S, C, inst, f, hf, hB⟩
  · exact Or.inl h
  right
  apply avoiding_swap
  let b := min S.ncard (s - 1)
  have hb : b ≤ S.toFinset.card := by rw [← Set.ncard_eq_toFinset_card']; exact min_le_left ..
  obtain ⟨B, hBS, hBc⟩ := exists_subset_card_eq hb
  apply blue_cover G n hn B (by rw [hBc]; dsimp [b]; omega)
  rintro ⟨e⟩
  let I := univ.filter (fun i : Fin t => ∀ a : Fin (m i + 1), e ⟨i, a⟩ ∉ S)
  have hI (i : Fin t) (hi : i ∈ I) := (mem_filter.mp hi).2
  let g : (forest m).Copy G :=
    ⟨⟨e, by intro x y h; exact (e.toHom.map_adj h).1⟩, e.injective⟩
  have hbudget := copy_budget G m S f hf g I hI
  have hout (i : Fin t) (a : Fin (m i + 1)) : e ⟨i, a⟩ ∉ B := by
    obtain ⟨v, hv⟩ := forest_neighbor hm ⟨i, a⟩
    exact (e.toHom.map_adj hv).2.1
  have hhit : (univ \ I).card ≤ (S.toFinset \ B).card := by
    apply hit_card m e.injective
    intro i hi
    have h := (mem_sdiff.mp hi).2
    simp only [I, mem_filter, mem_univ, true_and, not_forall, not_not] at h
    obtain ⟨a, ha⟩ := h
    exact ⟨a, mem_sdiff.mpr ⟨Set.mem_toFinset.mpr ha, hout i a⟩⟩
  rw [card_sdiff_of_subset hBS, hBc, ← Set.ncard_eq_toFinset_card'] at hhit
  have htot := card_sdiff_add_card_eq_card (subset_univ I)
  simp only [card_univ, Fintype.card_fin] at htot
  by_cases hS : s - 1 ≤ S.ncard
  · have hcard : I.card ≤ ∑ i ∈ I, (m i + 1) / 2 := by
      calc
        I.card = ∑ _i ∈ I, (1 : ℕ) := by simp
        _ ≤ _ := sum_le_sum fun i _ => by have := hm i; omega
    rw [show b = s - 1 from min_eq_right hS] at hhit
    omega
  · rw [show b = S.ncard from min_eq_left (by omega)] at hhit
    have hIu : I = univ := eq_univ_of_card I (by simpa using (show I.card = t by omega))
    rw [hIu] at hbudget
    have he : (∑ i, (m i + 1) / 2) = t + pairExcess m := by
      calc
        _ = ∑ i, (1 + (m i - 1) / 2) := sum_congr rfl fun i _ => by have := hm i; omega
        _ = _ := by simp [pairExcess, sum_add_distrib]
    rw [he] at hbudget
    omega

private theorem extend_avoiding {V : Type} {s t : ℕ} {G M : SimpleGraph V}
    {n : Fin s → ℕ} {m : Fin t → ℕ} (hle : M ≤ G) (hM : Matching M)
    (h : avoiding (G \ M) (fun i => n i - 1) m) : avoiding G n m := by
  obtain ⟨R, hR, hn, hm⟩ := h
  have he : G \ (R ⊔ M) = (G \ M) \ R := by
    ext u v
    simp only [sdiff_adj, sup_adj]
    tauto
  exact ⟨R ⊔ M, sup_le (hR.trans sdiff_le) hle,
    fun hc => hn (trim_matching n R M hM hc), he.symm ▸ hm⟩

private def diagonalIndices (s t j : ℕ) : Finset (Fin s × Fin t) :=
  univ.filter (fun p => (p.1.val + 1) + (p.2.val + 1) = j)

private def diagonal {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ) (j : ℕ) : ℕ :=
  (diagonalIndices s t j).sup (fun p => n p.1 + m p.2 - 1)

private def total {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ) : ℕ :=
  ∑ j ∈ Icc 2 (s + t), diagonal n m j

private theorem diagonal_nonempty {s t j : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hj : j ∈ Icc 2 (s + t)) : (diagonalIndices s t j).Nonempty := by
  obtain ⟨hj₁, hj₂⟩ := mem_Icc.mp hj
  let a := min (s - 1) (j - 2)
  let b := j - 2 - a
  have ha : a < s := by dsimp [a]; omega
  have hb : b < t := by dsimp [a, b]; omega
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), mem_filter.mpr ⟨mem_univ _, by
    change a + 1 + (b + 1) = j
    dsimp [b, a]
    omega⟩⟩

private theorem total_swap {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ) :
    total n m = total m n := by
  have aux {a b : ℕ} (x : Fin a → ℕ) (y : Fin b → ℕ) (j : ℕ) :
      diagonal x y j ≤ diagonal y x j := by
    apply Finset.sup_le
    intro p hp
    have hq : p.swap ∈ diagonalIndices b a j := by
      have he := (mem_filter.mp hp).2
      exact mem_filter.mpr ⟨mem_univ _, by simpa [Nat.add_comm] using he⟩
    have h := le_sup (f := fun p => y p.1 + x p.2 - 1) hq
    change y p.2 + x p.1 - 1 ≤ diagonal y x j at h
    rwa [Nat.add_comm] at h
  unfold total
  rw [Nat.add_comm s t]
  exact sum_congr rfl fun j _ => (aux n m j).antisymm (aux m n j)

private theorem total_positive {s t : ℕ} {n : Fin s → ℕ} {m : Fin t → ℕ}
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hn : ∀ i, 1 ≤ n i) (hm : ∀ j, 1 ≤ m j) :
    1 ≤ total n m := by
  have h2 : 2 ∈ Icc 2 (s + t) := mem_Icc.mpr ⟨le_rfl, by omega⟩
  obtain ⟨p, hp⟩ := diagonal_nonempty hs ht h2
  have h₁ : 1 ≤ n p.1 + m p.2 - 1 := by have := hn p.1; have := hm p.2; omega
  have h₂ : n p.1 + m p.2 - 1 ≤ diagonal n m 2 :=
    le_sup (f := fun p => n p.1 + m p.2 - 1) hp
  have h₃ : diagonal n m 2 ≤ total n m :=
    single_le_sum (f := diagonal n m) (fun _ _ => Nat.zero_le _) h2
  exact h₁.trans (h₂.trans h₃)

private theorem total_sub_one {s t : ℕ} {n : Fin s → ℕ} {m : Fin t → ℕ}
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hn : ∀ i, 2 ≤ n i) (hm : ∀ i, 1 ≤ m i) :
    total (fun i => n i - 1) m + (s + t - 1) = total n m := by
  have hd (j) (hj : j ∈ Icc 2 (s + t)) :
      diagonal (fun i => n i - 1) m j + 1 = diagonal n m j := by
    obtain ⟨p, hp, he⟩ := exists_mem_eq_sup _ (diagonal_nonempty hs ht hj)
      (fun p => (n p.1 - 1) + m p.2 - 1)
    have hlo : diagonal (fun i => n i - 1) m j + 1 ≤ diagonal n m j := by
      change diagonal (fun i => n i - 1) m j = _ at he
      rw [he]
      have h : n p.1 + m p.2 - 1 ≤ diagonal n m j :=
        le_sup (f := fun p => n p.1 + m p.2 - 1) hp
      have := hn p.1
      have := hm p.2
      omega
    have hhi : diagonal n m j ≤ diagonal (fun i => n i - 1) m j + 1 := by
      apply Finset.sup_le
      intro q hq
      have h : (n q.1 - 1) + m q.2 - 1 ≤ diagonal (fun i => n i - 1) m j :=
        le_sup (f := fun p => (n p.1 - 1) + m p.2 - 1) hq
      have := hn q.1
      have := hm q.2
      omega
    exact hlo.antisymm hhi
  unfold total
  have hcount : (Icc 2 (s + t)).card = s + t - 1 := by
    rw [Nat.card_Icc]
    omega
  have hsum := sum_congr (s₁ := Icc 2 (s+t)) rfl hd
  rw [sum_add_distrib, sum_const, smul_eq_mul, mul_one, hcount] at hsum
  exact hsum

private def armPrefix {s u : ℕ} (n : Fin s → ℕ) (h : u ≤ s) : Fin u → ℕ :=
  fun i => n (Fin.castLE h i)

private theorem prefix_copy {s u : ℕ} (n : Fin s → ℕ) (h : u ≤ s) :
    (forest (armPrefix n h)).IsContained (forest n) := by
  let f (v : Σ i, Fin (armPrefix n h i + 1)) : Σ i, Fin (n i + 1) :=
    ⟨Fin.castLE h v.1, v.2⟩
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro v w hvw
    obtain ⟨i, a, ha | ha⟩ :=
      (OMA.R_Erdos561_erdos_561_R1.forest_adj (armPrefix n h)).mp hvw
    · obtain ⟨rfl, rfl⟩ := ha
      exact spoke_adj n (Fin.castLE h i) a
    · obtain ⟨rfl, rfl⟩ := ha
      exact (spoke_adj n (Fin.castLE h i) a).symm
  · rintro ⟨i, a⟩ ⟨j, b⟩ he
    have hij : i = j := Fin.ext (congrArg (fun v : Σ i, Fin (n i + 1) => v.1.val) he)
    subst j
    exact congrArg (Sigma.mk i) (Fin.ext (congrArg
      (fun v : Σ i, Fin (n i + 1) => v.2.val) he))

private theorem total_prefix_le {s t u : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ)
    (h : u ≤ s) : total (armPrefix n h) m ≤ total n m := by
  unfold total
  refine (sum_le_sum ?_).trans (sum_le_sum_of_subset_of_nonneg ?_ ?_)
  · intro j _
    apply Finset.sup_le
    intro p hp
    let q : Fin s × Fin t := (Fin.castLE h p.1, p.2)
    have hq : q ∈ diagonalIndices s t j := mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hp).2⟩
    exact le_sup (f := fun p => n p.1 + m p.2 - 1) hq
  · intro j hj
    exact mem_Icc.mpr ⟨(mem_Icc.mp hj).1, by have := (mem_Icc.mp hj).2; omega⟩
  · intro j _ _
    exact Nat.zero_le _

private def canTrim {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ) (budget : ℕ) : Prop :=
  ∃ (u : ℕ) (_ : 1 ≤ u) (h : u ≤ s),
    (∀ i, 2 ≤ armPrefix n h i) ∧
    total n m ≤ total (fun i => armPrefix n h i - 1) m + budget

private theorem apply_trim {V : Type} [Fintype V] {s t u budget : ℕ}
    (G : SimpleGraph V) (n : Fin s → ℕ) (m : Fin t → ℕ)
    (h : u ≤ s) (hG : edges G < total n m)
    (hloss : total n m ≤ total (fun i => armPrefix n h i - 1) m + budget)
    (hmatch : (∃ M ≤ G, Matching M ∧ budget ≤ edges M) ∨ avoiding G n m)
    (ih : ∀ H : SimpleGraph V, edges H < total (fun i => armPrefix n h i - 1) m →
      avoiding H (fun i => armPrefix n h i - 1) m) : avoiding G n m := by
  rcases hmatch with ⟨M, hM, hmatch, hcard⟩ | h
  · have hsize : edges (G \ M) = edges G - edges M := by
      rw [edges, edgeSet_sdiff, Set.ncard_sdiff (edgeSet_mono hM)]
      rfl
    have hMsize : edges M ≤ edges G := Set.ncard_mono (edgeSet_mono hM)
    obtain ⟨R, hR, hn, hm⟩ := extend_avoiding hM hmatch (ih _ (by omega))
    exact ⟨R, hR, fun hc => hn ((prefix_copy n h).trans hc), hm⟩
  · exact h

private theorem matching_of_copy {V : Type} [Finite V] {s : ℕ} (G : SimpleGraph V)
    (m : Fin s → ℕ) (hm : ∀ i, 1 ≤ m i) (h : (forest m).IsContained G) :
    ∃ M ≤ G, Matching M ∧ s ≤ edges M := by
  classical
  obtain ⟨e⟩ := h
  let c (i : Fin s) := e ⟨i, 0⟩
  let a (i : Fin s) : Fin (m i) := ⟨0, hm i⟩
  let l (i : Fin s) := e ⟨i, (a i).succ⟩
  have hcl (i j) : c i ≠ l j := by
    intro h
    have hv := congrArg (fun u : Σ i, Fin (m i + 1) => u.2.val) (e.injective h)
    simp [a] at hv
  have hc : Function.Injective c := fun _ _ h => congrArg Sigma.fst (e.injective h)
  have hl : Function.Injective l := fun _ _ h => congrArg Sigma.fst (e.injective h)
  let M : SimpleGraph V :=
    { Adj := fun u v => ∃ i, (u = c i ∧ v = l i) ∨ (u = l i ∧ v = c i)
      symm := ⟨fun _ _ ⟨i, hi⟩ => ⟨i, hi.elim (fun h => Or.inr h.symm) (fun h => Or.inl h.symm)⟩⟩
      loopless := ⟨fun u ⟨i, hi⟩ => hi.elim
        (fun h => hcl i i (h.1.symm.trans h.2))
        (fun h => hcl i i (h.2.symm.trans h.1))⟩ }
  refine ⟨M, ?_, ?_, ?_⟩
  · rintro u v ⟨i, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact e.toHom.map_adj (spoke_adj m i (a i))
    · exact (e.toHom.map_adj (spoke_adj m i (a i))).symm
  · rintro u v w ⟨i, ⟨hi, rfl⟩ | ⟨hi, rfl⟩⟩ ⟨j, ⟨hj, rfl⟩ | ⟨hj, rfl⟩⟩
    · rw [hc (hi.symm.trans hj)]
    · exact (hcl i j (hi.symm.trans hj)).elim
    · exact (hcl j i (hj.symm.trans hi)).elim
    · rw [hl (hi.symm.trans hj)]
  · let key (i : Fin s) : M.edgeSet := ⟨s(c i, l i), i, Or.inl ⟨rfl, rfl⟩⟩
    have hk : Function.Injective key := by
      intro i j h
      rcases Sym2.eq_iff.mp (congrArg Subtype.val h) with hh | hh
      · exact hc hh.1
      · exact (hcl i j hh.1).elim
    have h := Nat.card_le_card_of_injective key hk
    simpa only [Nat.card_eq_fintype_card (α := Fin s), Fintype.card_fin, Nat.card_coe_set_eq, edges]
      using h

private theorem singleton_matching_or_avoiding {V : Type} [Fintype V] {s t : ℕ}
    (G : SimpleGraph V) (n : Fin s → ℕ) (m : Fin t → ℕ) (hs : s = 1)
    (hn : ∀ i, 1 ≤ n i) (hm : ∀ i, 1 ≤ m i) :
    (∃ M ≤ G, Matching M ∧ s + t - 1 ≤ edges M) ∨ avoiding G n m := by
  by_cases h : (forest m).IsContained G
  · subst s
    left
    have hcount : 1 + t - 1 = t := by omega
    rw [hcount]
    exact matching_of_copy G m hm h
  · right
    refine ⟨⊥, bot_le, ?_, by simpa using h⟩
    rintro ⟨e⟩
    let i : Fin s := ⟨0, by omega⟩
    have h := e.toHom.map_adj (spoke_adj n i ⟨0, hn i⟩)
    exact h

-- The edge indexing is the same as in the parent reduction by @marcusbuffett.
private theorem forest_edge_count {s : ℕ} (n : Fin s → ℕ) :
    edges (forest n) = ∑ i, n i := by
  classical
  let key (z : Σ i, Fin (n i)) : Sym2 (Σ i, Fin (n i + 1)) :=
    s((⟨z.1, 0⟩ : Σ i, Fin (n i + 1)), ⟨z.1, z.2.succ⟩)
  have he : (forest n).edgeSet = Set.range key := by
    ext x
    induction x using Sym2.inductionOn with
    | _ a b =>
      rw [mem_edgeSet, OMA.R_Erdos561_erdos_561_R1.forest_adj]
      constructor
      · rintro ⟨i, j, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · exact ⟨⟨i, j⟩, rfl⟩
        · exact ⟨⟨i, j⟩, Sym2.eq_swap⟩
      · rintro ⟨⟨i, j⟩, h⟩
        exact ⟨i, j, (Sym2.eq_iff.mp h.symm).imp id And.symm⟩
  have hi : Function.Injective key := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    rcases Sym2.eq_iff.mp h with ⟨hc, hl⟩ | ⟨hc, hl⟩
    · obtain rfl : i = j := congrArg Sigma.fst hc
      have he : a.succ = b.succ := by simpa using hl
      exact congrArg (Sigma.mk i) (Fin.succ_injective _ he)
    · obtain rfl : i = j := congrArg Sigma.fst hc
      exact ((Fin.succ_ne_zero b).symm (by simpa using hc)).elim
  rw [edges, he, Set.ncard_range_of_injective hi, Nat.card_eq_fintype_card]
  simp

private theorem edges_of_copy {U V : Type} (F : SimpleGraph U) (G : SimpleGraph V)
    [Finite V] (h : F.IsContained G) : edges F ≤ edges G := by
  obtain ⟨e⟩ := h
  rw [edges, edges, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_injective e.mapEdgeSet e.mapEdgeSet.injective

private theorem degree_of_copy {V : Type} [Fintype V] {s : ℕ} (n : Fin s → ℕ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : (forest n).IsContained G) (i : Fin s) :
    ∃ v, n i ≤ G.degree v := by
  obtain ⟨e⟩ := h
  let v := e ⟨i, 0⟩
  let f (a : Fin (n i)) : G.neighborSet v :=
    ⟨e ⟨i, a.succ⟩, e.toHom.map_adj (spoke_adj n i a)⟩
  have hf : Function.Injective f := by
    intro a b he
    have hx := congrArg (fun z : Σ j, Fin (n j + 1) => z.2.val)
      (e.injective (congrArg Subtype.val he))
    exact Fin.ext (by simpa using hx)
  exact ⟨v, by simpa only [Fintype.card_fin, card_neighborSet_eq_degree] using
    Fintype.card_le_of_injective f hf⟩

private theorem constant_one_base {s : ℕ} (n : Fin s → ℕ) :
    total n (fun _ : Fin 1 => 1) = ∑ i, n i := by
  classical
  symm
  unfold total
  refine sum_bij (fun (i : Fin s) _ => i.val + 2) ?_ ?_ ?_ ?_
  · intro i _
    exact mem_Icc.mpr ⟨by omega, by have := i.isLt; omega⟩
  · intro i _ j _ h
    exact Fin.ext (by omega)
  · intro j h
    have hj := mem_Icc.mp h
    exact ⟨⟨j - 2, by omega⟩, mem_univ _, by simp; omega⟩
  · intro i _
    have hp : (i, (0 : Fin 1)) ∈ diagonalIndices s 1 (i.val + 2) := by
      apply mem_filter.mpr
      simp
    have h₁ : n i ≤ diagonal n (fun _ : Fin 1 => 1) (i.val + 2) := by
      have hh : n i + 1 - 1 ≤ diagonal n (fun _ : Fin 1 => 1) (i.val + 2) :=
        le_sup (f := fun p => n p.1 + 1 - 1) hp
      rwa [Nat.add_sub_cancel] at hh
    apply h₁.antisymm
    apply Finset.sup_le
    intro p hp
    have he := (mem_filter.mp hp).2
    have hz : p.2.val = 0 := by have := p.2.isLt; omega
    have hi : p.1 = i := Fin.ext (by omega)
    simp [hi]

private theorem constant_one_succ {s t : ℕ} (ht : 1 ≤ t)
    (n : Fin s → ℕ) (hn : Antitone n) (z : Fin s) (hz : z.val = 0) :
    total n (fun _ : Fin (t + 1) => 1) = n z + total n (fun _ : Fin t => 1) := by
  classical
  let small (j : ℕ) := diagonal n (fun _ : Fin t => 1) j
  let big (j : ℕ) := diagonal n (fun _ : Fin (t + 1) => 1) j
  have hhead : big 2 = n z := by
    apply Nat.le_antisymm
    · apply Finset.sup_le
      intro p hp
      have he := (mem_filter.mp hp).2
      have h : p.1 = z := Fin.ext (by omega)
      simp [h]
    · have hp : (z, (0 : Fin (t + 1))) ∈ diagonalIndices s (t + 1) 2 :=
        mem_filter.mpr ⟨mem_univ _, by simp [hz]⟩
      have hh : n z + 1 - 1 ≤ big 2 := le_sup (f := fun p => n p.1 + 1 - 1) hp
      rwa [Nat.add_sub_cancel] at hh
  have hstep (j : ℕ) (hj : 2 ≤ j) : big (j + 1) = small j := by
    apply Nat.le_antisymm
    · apply Finset.sup_le
      intro p hp
      have he := (mem_filter.mp hp).2
      have hi := p.1.isLt
      have hj' := p.2.isLt
      by_cases h : p.2.val = 0
      · let q : Fin s × Fin t := (⟨p.1.val - 1, by omega⟩, ⟨0, ht⟩)
        have hq : q ∈ diagonalIndices s t j :=
          mem_filter.mpr ⟨mem_univ _, by dsimp [q]; omega⟩
        have hle : n p.1 ≤ n q.1 := hn (show q.1.val ≤ p.1.val by dsimp [q]; omega)
        have hs : n q.1 ≤ small j := by
          have hh : n q.1 + 1 - 1 ≤ small j := le_sup (f := fun p => n p.1 + 1 - 1) hq
          rwa [Nat.add_sub_cancel] at hh
        simpa only [Nat.add_sub_cancel] using hle.trans hs
      · let q : Fin s × Fin t := (p.1, ⟨p.2.val - 1, by omega⟩)
        have hq : q ∈ diagonalIndices s t j :=
          mem_filter.mpr ⟨mem_univ _, by dsimp [q]; omega⟩
        exact le_sup (f := fun p => n p.1 + 1 - 1) hq
    · apply Finset.sup_le
      intro p hp
      have he := (mem_filter.mp hp).2
      have hq : (p.1, p.2.succ) ∈ diagonalIndices s (t + 1) (j + 1) :=
        mem_filter.mpr ⟨mem_univ _, by simp only [Fin.val_succ]; omega⟩
      exact le_sup (f := fun p => n p.1 + 1 - 1) hq
  change ∑ j ∈ Icc 2 (s + (t + 1)), big j = n z + ∑ j ∈ Icc 2 (s + t), small j
  rw [Icc_eq_cons_Ioc (by omega : 2 ≤ s + (t + 1)), sum_cons, hhead]
  congr 1
  symm
  refine sum_bij (fun j _ => j + 1) ?_ ?_ ?_ ?_
  · intro j hj
    have hh := mem_Icc.mp hj
    exact mem_Ioc.mpr ⟨by omega, by omega⟩
  · intro i _ j _ h
    omega
  · intro j hj
    have hh := mem_Ioc.mp hj
    exact ⟨j - 1, mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro j hj
    exact (hstep j (mem_Icc.mp hj).1).symm

-- A pure matching on the blue side is handled by deleting vertices of large degree.
private theorem pure_matching {V : Type} [Fintype V] {s : ℕ}
    (hs : 1 ≤ s) (n : Fin s → ℕ) (hna : Antitone n) :
    ∀ t, 1 ≤ t → ∀ G : SimpleGraph V,
      edges G < total n (fun _ : Fin t => 1) → avoiding G n (fun _ : Fin t => 1) := by
  classical
  suffices ∀ t, 1 ≤ t → ∀ G : SimpleGraph V, edges G < total n (fun _ : Fin t => 1) →
      ∃ B : Finset V, B.card < t ∧ ¬ (forest n).IsContained (without G B) by
    intro t ht G hG
    obtain ⟨B, hB, h⟩ := this t ht G hG
    exact blue_cover G _ (fun _ => le_rfl) B hB h
  intro t
  induction t with
  | zero => omega
  | succ t ih =>
    intro _ G hG
    by_cases h : (forest n).IsContained G
    · by_cases ht : 1 ≤ t
      · let z : Fin s := ⟨0, by omega⟩
        obtain ⟨v, hv⟩ := degree_of_copy n G h z
        let G' := G.deleteIncidenceSet v
        have hsize : edges G' = edges G - G.degree v := by
          simp only [edges_eq, G', card_edgeFinset_deleteIncidenceSet]
        have hdegree : G.degree v ≤ edges G := by
          rw [edges_eq]
          exact G.degree_le_card_edgeFinset v
        have hsum := constant_one_succ ht n hna z rfl
        obtain ⟨B, hB, he⟩ := ih ht G' (by omega)
        refine ⟨insert v B, (card_insert_le _ _).trans_lt (by omega), fun hh => he ?_⟩
        refine hh.trans (IsContained.of_le (fun u w hw => ⟨?_, ?_, ?_⟩))
        · have hu : u ≠ v := fun h => hw.2.1 (h ▸ mem_insert_self _ _)
          have hv : w ≠ v := fun h => hw.2.2 (h ▸ mem_insert_self _ _)
          exact deleteIncidenceSet_adj.mpr ⟨hw.1, hu, hv⟩
        · exact fun hu => hw.2.1 (mem_insert_of_mem hu)
        · exact fun hv => hw.2.2 (mem_insert_of_mem hv)
      · have ht' : t = 0 := by omega
        subst t
        have he := edges_of_copy (forest n) G h
        rw [forest_edge_count] at he
        rw [constant_one_base] at hG
        omega
    · exact ⟨∅, by simp, fun hh => h (hh.trans (IsContained.of_le (fun _ _ h => h.1)))⟩

private def enoughPairs {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ) : Prop :=
  s - 1 ≤ pairExcess m ∨ t - 1 ≤ pairExcess n

private theorem pairs_matching_or_avoiding {V : Type} [Fintype V] {s t : ℕ}
    (G : SimpleGraph V) (n : Fin s → ℕ) (m : Fin t → ℕ)
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hn : ∀ i, 1 ≤ n i) (hm : ∀ i, 1 ≤ m i)
    (h : enoughPairs n m) :
    (∃ M ≤ G, Matching M ∧ s + t - 1 ≤ edges M) ∨ avoiding G n m := by
  rcases h with h | h
  · exact excess_matching_or_avoiding G n m hs hn hm h
  · rcases excess_matching_or_avoiding G m n ht hm hn h with ⟨M, hM, hmatch, hcard⟩ | ha
    · exact Or.inl ⟨M, hM, hmatch, by omega⟩
    · exact Or.inr (avoiding_swap ha)

private def affordableTrim {V : Type} {s t : ℕ} (G : SimpleGraph V)
    (n : Fin s → ℕ) (m : Fin t → ℕ) : Prop :=
  ∃ M ≤ G, Matching M ∧ canTrim n m (edges M)

/-- Mixed lists for which the weighted matching and trimming steps cannot be combined. -/
def H1 : Prop :=
  ∀ {V : Type} [Fintype V] {s t : ℕ}, 1 ≤ s → 1 ≤ t →
    ∀ (n : Fin s → ℕ) (m : Fin t → ℕ), Antitone n → Antitone m →
      (∀ i, 1 ≤ n i) → (∀ j, 1 ≤ m j) →
      (∃ i, n i = 1) → (∃ j, m j = 1) →
      (∃ i, 2 ≤ n i) → (∃ j, 2 ≤ m j) →
      ¬ (enoughPairs n m ∧ (canTrim n m (s + t - 1) ∨ canTrim m n (s + t - 1))) →
      ∀ G : SimpleGraph V, edges G < total n m →
        ¬ affordableTrim G n m → ¬ affordableTrim G m n → avoiding G n m

/-- Only the longer list includes a one-edge star and the component-count inequality
fails even at the minimum arm size of the shorter list. -/
def H2 : Prop :=
  ∀ {V : Type} [Fintype V] {s t : ℕ}, 2 ≤ s → 1 ≤ t →
    ∀ (n : Fin s → ℕ) (m : Fin t → ℕ), Antitone n → Antitone m →
      (∀ i, 2 ≤ n i) → (∀ j, 1 ≤ m j) → (∃ j, m j = 1) → (∃ j, 2 ≤ m j) →
      (∀ a, 2 ≤ a → (∀ i, a ≤ n i) → (a - 1) * s + 1 < t) →
      ¬ enoughPairs n m →
      ∀ G : SimpleGraph V, edges G < total n m →
        (¬ ∃ M ≤ G, Matching M ∧ s + t - 1 ≤ edges M) → avoiding G n m

theorem lower_bound (h1 : H1) (h2 : H2) {V : Type} [Fintype V] :
    ∀ (r : ℕ) {s t : ℕ}, 1 ≤ s → 1 ≤ t →
      ∀ (n : Fin s → ℕ) (m : Fin t → ℕ), Antitone n → Antitone m →
        (∀ i, 1 ≤ n i) → (∀ j, 1 ≤ m j) → total n m = r →
        ∀ G : SimpleGraph V, edges G < total n m → avoiding G n m := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro s t hs ht n m hna hma hn hm hr G hG
    have hswap : total m n = total n m := total_swap m n
    by_cases hnAll : ∀ i, n i = 1
    · have he : n = fun _ => 1 := funext hnAll
      apply avoiding_swap
      rw [he]
      exact pure_matching ht m hma s hs G (by rwa [← he, hswap])
    by_cases hmAll : ∀ j, m j = 1
    · have he : m = fun _ => 1 := funext hmAll
      rw [he]
      exact pure_matching hs n hna t ht G (by rwa [← he])
    have hnBig : ∃ i, 2 ≤ n i := by
      by_contra h
      apply hnAll
      intro i
      have hlt : ¬ 2 ≤ n i := fun he => h ⟨i, he⟩
      have := hn i
      omega
    have hmBig : ∃ j, 2 ≤ m j := by
      by_contra h
      apply hmAll
      intro j
      have hlt : ¬ 2 ≤ m j := fun he => h ⟨j, he⟩
      have := hm j
      omega
    have trim {u v budget : ℕ} (x : Fin u → ℕ) (y : Fin v → ℕ)
        (hv : 1 ≤ v) (hxa : Antitone x) (hya : Antitone y)
        (hy : ∀ j, 1 ≤ y j) (hxy : total x y = r) (hH : edges G < total x y)
        (hmatch : (∃ M ≤ G, Matching M ∧ budget ≤ edges M) ∨ avoiding G x y)
        (htrim : canTrim x y budget) : avoiding G x y := by
      obtain ⟨w, hw, hwle, hpos, hloss⟩ := htrim
      have hle := total_prefix_le x y hwle
      have hadd := total_sub_one hw hv hpos hy
      have hlt : total (fun i => armPrefix x hwle i - 1) y < r := by omega
      apply apply_trim G x y hwle hH hloss hmatch
      intro H hH'
      apply ih _ hlt hw hv _ y ?_ hya ?_ hy rfl H hH'
      · intro i j hij
        exact Nat.sub_le_sub_right (hxa (show Fin.castLE hwle i ≤ Fin.castLE hwle j from hij)) 1
      · intro i
        have := hpos i
        omega
    have canTrimFull {u v budget : ℕ} (x : Fin u → ℕ) (y : Fin v → ℕ)
        (hu : 1 ≤ u) (hv : 1 ≤ v) (hx : ∀ i, 2 ≤ x i) (hy : ∀ j, 1 ≤ y j) :
        u + v - 1 ≤ budget → canTrim x y budget := by
      intro hbudget
      refine ⟨u, hu, le_rfl, hx, ?_⟩
      exact (total_sub_one hu hv hx hy).ge.trans (Nat.add_le_add_left hbudget _)
    by_cases hpt : enoughPairs n m ∧ (canTrim n m (s + t - 1) ∨ canTrim m n (s + t - 1))
    · obtain ⟨hp, htr | htr⟩ := hpt
      · exact trim n m ht hna hma hm hr hG (pairs_matching_or_avoiding G n m hs ht hn hm hp) htr
      · have hp' : enoughPairs m n := hp.symm
        have htr' : canTrim m n (t + s - 1) := by simpa only [Nat.add_comm] using htr
        exact avoiding_swap (trim m n hs hma hna hn (hswap.trans hr) (hswap.symm ▸ hG)
          (pairs_matching_or_avoiding G m n ht hs hm hn hp') htr')
    by_cases hnt : affordableTrim G n m
    · obtain ⟨M, hM, hmatch, ht⟩ := hnt
      exact trim n m ‹1 ≤ t› hna hma hm hr hG (Or.inl ⟨M, hM, hmatch, le_rfl⟩) ht
    by_cases hmt : affordableTrim G m n
    · obtain ⟨M, hM, hmatch, ht⟩ := hmt
      exact avoiding_swap (trim m n hs hma hna hn (hswap.trans hr) (hswap.symm ▸ hG)
        (Or.inl ⟨M, hM, hmatch, le_rfl⟩) ht)
    have step {u v : ℕ} (x : Fin u → ℕ) (y : Fin v → ℕ)
        (hu : 1 ≤ u) (hv : 1 ≤ v) (hxa : Antitone x) (hya : Antitone y)
        (hy : ∀ j, 1 ≤ y j) (hxy : total x y = r) (hH : edges G < total x y)
        (h : ∃ a, 2 ≤ a ∧ (∀ i, a ≤ x i) ∧ (u = 1 ∨ v ≤ (a - 1) * u + 1)) :
        avoiding G x y := by
      obtain ⟨a, ha, hx, huv⟩ := h
      have hx2 (i : Fin u) := ha.trans (hx i)
      have hx1 (i : Fin u) := (by decide : 1 ≤ 2).trans (hx2 i)
      have hmatch := huv.elim (fun hu => singleton_matching_or_avoiding G x y hu hx1 hy)
        (fun huv => matching_or_avoiding G x y hu hv a ha huv hx hy)
      exact trim x y hv hxa hya hy hxy hH hmatch (canTrimFull x y hu hv hx2 hy le_rfl)
    by_cases hnr : ∃ a, 2 ≤ a ∧ (∀ i, a ≤ n i) ∧ (s = 1 ∨ t ≤ (a - 1) * s + 1)
    · exact step n m hs ht hna hma hm hr hG hnr
    by_cases hmr : ∃ a, 2 ≤ a ∧ (∀ j, a ≤ m j) ∧ (t = 1 ∨ s ≤ (a - 1) * t + 1)
    · exact avoiding_swap (step m n ht hs hma hna hn (hswap.trans hr)
        (hswap.symm ▸ hG) hmr)
    by_cases hn1 : ∃ i, n i = 1
    · by_cases hm1 : ∃ j, m j = 1
      · exact h1 hs ht n m hna hma hn hm hn1 hm1 hnBig hmBig hpt G hG hnt hmt
      · have hm2 (j : Fin t) : 2 ≤ m j := by
          have hne : m j ≠ 1 := fun he => hm1 ⟨j, he⟩
          have := hm j
          omega
        have hf a (ha : 2 ≤ a) (hla : ∀ j, a ≤ m j) : (a - 1) * t + 1 < s :=
          lt_of_not_ge fun h => hmr ⟨a, ha, hla, Or.inr h⟩
        have ht2 : 2 ≤ t := by
          have hne : t ≠ 1 := fun he => hmr ⟨2, le_rfl, hm2, Or.inl he⟩
          omega
        have hp : ¬ enoughPairs m n := fun hp =>
          hpt ⟨hp.symm, Or.inr (canTrimFull m n ht hs hm2 hn (by omega))⟩
        have hsmall : ¬ ∃ M ≤ G, Matching M ∧ t + s - 1 ≤ edges M := by
          rintro ⟨M, hM, hmatch, hsize⟩
          exact hmt ⟨M, hM, hmatch, canTrimFull m n ht hs hm2 hn hsize⟩
        exact avoiding_swap
          (h2 ht2 hs m n hma hna hm2 hn hn1 hnBig hf hp G (hswap.symm ▸ hG) hsmall)
    · have hn2 (i : Fin s) : 2 ≤ n i := by
        have hne : n i ≠ 1 := fun he => hn1 ⟨i, he⟩
        have := hn i
        omega
      have hst : s + 1 < t := by
        have hh : (2 - 1) * s + 1 < t := lt_of_not_ge fun h => hnr ⟨2, le_rfl, hn2, Or.inr h⟩
        simpa using hh
      have hm1 : ∃ j, m j = 1 := by
        by_contra h
        have hm2 (j : Fin t) : 2 ≤ m j := by
          have hne : m j ≠ 1 := fun he => h ⟨j, he⟩
          have := hm j
          omega
        apply hmr
        exact ⟨2, le_rfl, hm2, Or.inr (by simp; omega)⟩
      have hf a (ha : 2 ≤ a) (hla : ∀ i, a ≤ n i) : (a - 1) * s + 1 < t :=
        lt_of_not_ge fun h => hnr ⟨a, ha, hla, Or.inr h⟩
      have hs2 : 2 ≤ s := by
        have hne : s ≠ 1 := fun he => hnr ⟨2, le_rfl, hn2, Or.inl he⟩
        omega
      have hp : ¬ enoughPairs n m := fun hp =>
        hpt ⟨hp, Or.inl (canTrimFull n m hs ht hn2 hm le_rfl)⟩
      have hsmall : ¬ ∃ M ≤ G, Matching M ∧ s + t - 1 ≤ edges M := by
        rintro ⟨M, hM, hmatch, hsize⟩
        exact hnt ⟨M, hM, hmatch, canTrimFull n m hs ht hn2 hm hsize⟩
      exact h2 hs2 ht n m hna hma hn2 hm hm1 hmBig hf hp G hG hsmall

theorem main : H1 → H2 → OMA.R_Erdos561_erdos_561_R1.H2 := by
  intro h1 h2 s t hs ht n m hna hma hn hm
  dsimp only
  intro G hG
  change avoiding G n m
  change edges G = total n m - 1 at hG
  have hpos := total_positive hs ht hn hm
  exact lower_bound h1 h2 (total n m) hs ht n m hna hma hn hm rfl G (by omega)

end
end OMA.R_Erdos561_erdos_561_R1_H2_R2
