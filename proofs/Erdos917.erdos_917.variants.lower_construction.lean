import FormalConjectures.ErdosProblems.«917»

/-!
Lower construction for Erdős Problem 917 (Toft 1970 / Stiebitz 1987).
Assembled from reduction R1 and proofs of H1 (odd cycles), H2 (Dirac join),
H3 (Toft 4-critical graph), and H4 (Toft 5-critical graph).
-/

namespace OMA.Erdos917Lower

/-- Odd cycles are `3`-critical: `C_b` has `b` vertices and `b` edges. -/
def H1 : Prop :=
  ∀ b : ℕ, Odd b → 3 ≤ b →
    ∃ G : SimpleGraph (Fin b), Erdos917.IsKCritical G 3 ∧ G.edgeSet.ncard = b

/-- Dirac's join: the join of a `k₁`-critical and a `k₂`-critical graph is `(k₁ + k₂)`-critical. -/
def H2 : Prop :=
  ∀ k₁ k₂ n₁ n₂ e₁ e₂ : ℕ, 3 ≤ k₁ → 3 ≤ k₂ →
    (∃ G : SimpleGraph (Fin n₁), Erdos917.IsKCritical G k₁ ∧ G.edgeSet.ncard = e₁) →
    (∃ G : SimpleGraph (Fin n₂), Erdos917.IsKCritical G k₂ ∧ G.edgeSet.ncard = e₂) →
    ∃ G : SimpleGraph (Fin (n₁ + n₂)),
      Erdos917.IsKCritical G (k₁ + k₂) ∧ G.edgeSet.ncard = e₁ + e₂ + n₁ * n₂

/-- Toft's 4-critical graph `D(A₁, A₂)` from two `3`-critical graphs. -/
def H3 : Prop :=
  ∀ n₁ n₂ e₁ e₂ : ℕ,
    (∃ G : SimpleGraph (Fin n₁), Erdos917.IsKCritical G 3 ∧ G.edgeSet.ncard = e₁) →
    (∃ G : SimpleGraph (Fin n₂), Erdos917.IsKCritical G 3 ∧ G.edgeSet.ncard = e₂) →
    ∃ G : SimpleGraph (Fin (2 * n₁ + 2 * n₂)),
      Erdos917.IsKCritical G 4 ∧ G.edgeSet.ncard = e₁ + e₂ + n₁ + n₂ + n₁ * n₂

/-- Toft's 5-critical graph `T(A, C)` from a `4`-critical graph `A` and a `3`-critical graph `C`. -/
def H4 : Prop :=
  ∀ n₁ n₂ e₁ e₂ : ℕ,
    (∃ G : SimpleGraph (Fin n₁), Erdos917.IsKCritical G 4 ∧ G.edgeSet.ncard = e₁) →
    (∃ G : SimpleGraph (Fin n₂), Erdos917.IsKCritical G 3 ∧ G.edgeSet.ncard = e₂) →
    ∃ G : SimpleGraph (Fin (2 * n₁ + n₂)),
      Erdos917.IsKCritical G 5 ∧ G.edgeSet.ncard = e₁ + e₂ + n₁ + n₁ * n₂

namespace Critical

open Finset SimpleGraph

lemma colorable_of {V : Type*} (H : SimpleGraph V) (K : ℕ) (col : V → ℕ)
    (hb : ∀ x, col x < K) (hp : ∀ x y, H.Adj x y → col x ≠ col y) : H.Colorable K :=
  ⟨Coloring.mk (fun x => ⟨col x, hb x⟩) (fun {x y} h heq => hp x y h (congrArg Fin.val heq))⟩

lemma isKCritical_of_edge_critical {V : Type*} (G : SimpleGraph V) {k : ℕ} (hk : 1 ≤ k)
    (hcol : G.Colorable k) (hnot : ¬ G.Colorable (k - 1))
    (hdeg : ∀ v : V, ∃ w : V, G.Adj v w)
    (hedge : ∀ u w : V, G.Adj u w → (G.deleteEdges {s(u, w)}).Colorable (k - 1)) :
    Erdos917.IsKCritical G k := by
  have hle_chi : (k : ℕ∞) ≤ G.chromaticNumber := by
    rw [le_chromaticNumber_iff_not_colorable (by omega)]
    exact hnot
  have hchi : G.chromaticNumber = (k : ℕ∞) :=
    le_antisymm hcol.chromaticNumber_le hle_chi
  refine ⟨⟨hchi, ?_⟩, ?_⟩
  · intro v
    unfold Subgraph.IsCriticalVertex Subgraph.IsCriticalVerts
    obtain ⟨w, hvw⟩ := hdeg v
    obtain ⟨C⟩ := hedge v w hvw
    have hdel : ((⊤ : G.Subgraph).deleteVerts {v}).coe.Colorable (k - 1) := by
      refine ⟨Coloring.mk (fun a => C a.val) ?_⟩
      intro a b hab
      rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj] at hab
      obtain ⟨_, ha, _, hb, hab⟩ := hab
      rw [Subgraph.top_adj] at hab
      apply C.valid
      rw [deleteEdges_adj]
      refine ⟨hab, ?_⟩
      rw [Set.mem_singleton_iff, Sym2.eq_iff]
      rintro (⟨h1, -⟩ | ⟨-, h2⟩)
      · exact ha (Set.mem_singleton_iff.mpr h1)
      · exact hb (Set.mem_singleton_iff.mpr h2)
    have htop_le : (k : ℕ∞) ≤ (⊤ : G.Subgraph).coe.chromaticNumber := by
      rw [le_chromaticNumber_iff_not_colorable (by omega)]
      rintro ⟨C'⟩
      exact hnot ⟨Coloring.mk (fun x => C' ⟨x, trivial⟩) (fun h => C'.valid (by simpa using h))⟩
    exact lt_of_le_of_lt hdel.chromaticNumber_le
      (lt_of_lt_of_le (by exact_mod_cast (by omega : k - 1 < k)) htop_le)
  · intro e he
    unfold IsCriticalEdge IsCriticalEdges
    revert he
    refine Sym2.ind (fun u w huw => ?_) e
    rw [mem_edgeSet] at huw
    exact lt_of_le_of_lt (hedge u w huw).chromaticNumber_le
      (lt_of_lt_of_le (by exact_mod_cast (by omega : k - 1 < k)) hle_chi)

lemma isKCritical_transport {V W : Type*} (G : SimpleGraph V) (e : V ≃ W) {k : ℕ} (hk : 1 ≤ k)
    (hcol : G.Colorable k) (hnot : ¬ G.Colorable (k - 1))
    (hdeg : ∀ v : V, ∃ w : V, G.Adj v w)
    (hedge : ∀ u w : V, G.Adj u w → (G.deleteEdges {s(u, w)}).Colorable (k - 1)) :
    Erdos917.IsKCritical (G.map e.toEmbedding) k := by
  refine isKCritical_of_edge_critical _ hk ?_ ?_ ?_ ?_
  · obtain ⟨C⟩ := hcol
    refine ⟨Coloring.mk (fun w => C (e.symm w)) ?_⟩
    intro x y hxy
    rw [map_adj] at hxy
    obtain ⟨u, v, huv, rfl, rfl⟩ := hxy
    simpa using C.valid huv
  · rintro ⟨C⟩
    exact hnot ⟨Coloring.mk (fun v => C (e v)) fun {u v} huv =>
      C.valid (by rw [map_adj]; exact ⟨u, v, huv, rfl, rfl⟩)⟩
  · intro w
    obtain ⟨u, hu⟩ := hdeg (e.symm w)
    refine ⟨e u, ?_⟩
    rw [map_adj]
    exact ⟨e.symm w, u, hu, e.apply_symm_apply w, rfl⟩
  · intro x y hxy
    rw [map_adj] at hxy
    obtain ⟨u, v, huv, rfl, rfl⟩ := hxy
    obtain ⟨C⟩ := hedge u v huv
    refine ⟨Coloring.mk (fun w => C (e.symm w)) ?_⟩
    intro a b hab
    rw [deleteEdges_adj, map_adj] at hab
    obtain ⟨⟨u', v', huv', rfl, rfl⟩, hne⟩ := hab
    simp only [Equiv.toEmbedding_apply, Equiv.symm_apply_apply]
    apply C.valid
    rw [deleteEdges_adj]
    refine ⟨huv', ?_⟩
    intro heq
    apply hne
    rw [Set.mem_singleton_iff] at heq ⊢
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Sym2.eq_swap

lemma isKCritical_colorable {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (hG : Erdos917.IsKCritical G k) : G.Colorable k :=
  chromaticNumber_le_iff_colorable.mp hG.1.1.le

lemma isKCritical_not_colorable {V : Type*} {G : SimpleGraph V} {k : ℕ} (hk : 1 ≤ k)
    (hG : Erdos917.IsKCritical G k) : ¬ G.Colorable (k - 1) := by
  intro hc
  have hlt : (k - 1 : ℕ∞) < (k : ℕ∞) := by exact_mod_cast (by omega : k - 1 < k)
  exact not_le_of_gt hlt (hG.1.1.symm.trans_le hc.chromaticNumber_le)

lemma isKCritical_nonempty {V : Type*} {G : SimpleGraph V} {k : ℕ} (hk : 1 ≤ k)
    (hG : Erdos917.IsKCritical G k) : Nonempty V := by
  by_contra hemp
  rw [not_nonempty_iff] at hemp
  exact isKCritical_not_colorable hk hG
    ⟨Coloring.mk (fun v => (IsEmpty.false v).elim) (fun {v} => (IsEmpty.false v).elim)⟩

lemma isKCritical_del_edge_colorable {V : Type*} {G : SimpleGraph V} {k : ℕ} (hk : 1 ≤ k)
    (hG : Erdos917.IsKCritical G k) {u w : V} (huw : G.Adj u w) :
    (G.deleteEdges {s(u, w)}).Colorable (k - 1) := by
  have he : s(u, w) ∈ G.edgeSet := huw
  have hlt := hG.2 _ he
  unfold IsCriticalEdge IsCriticalEdges at hlt
  rw [hG.1.1] at hlt
  by_contra hnc
  exact not_lt_of_ge ((le_chromaticNumber_iff_not_colorable (by omega)).mpr hnc) hlt

lemma isKCritical_del_vert_colorable {V : Type*} {G : SimpleGraph V} {k : ℕ} (hk : 1 ≤ k)
    (hG : Erdos917.IsKCritical G k) (v : V) :
    ∃ col : V → ℕ, (∀ x, x ≠ v → col x < k - 1) ∧
      ∀ x y, x ≠ v → y ≠ v → G.Adj x y → col x ≠ col y := by
  classical
  have hlt := hG.1.2 v
  unfold Subgraph.IsCriticalVertex Subgraph.IsCriticalVerts at hlt
  have htop_le : (⊤ : G.Subgraph).coe.chromaticNumber ≤ G.chromaticNumber := by
    obtain ⟨C⟩ := isKCritical_colorable hG
    rw [hG.1.1]
    exact (Colorable.chromaticNumber_le
      ⟨Coloring.mk (fun x => C x.val) (fun {a b} h => C.valid (by simpa using h))⟩)
  have hlt' : ((⊤ : G.Subgraph).deleteVerts {v}).coe.chromaticNumber < (k : ℕ∞) :=
    lt_of_lt_of_le hlt (htop_le.trans_eq hG.1.1)
  have hcol : ((⊤ : G.Subgraph).deleteVerts {v}).coe.Colorable (k - 1) := by
    by_contra hnc
    exact not_lt_of_ge ((le_chromaticNumber_iff_not_colorable (by omega)).mpr hnc) hlt'
  obtain ⟨C⟩ := hcol
  refine ⟨fun x => if hx : x ≠ v then (C ⟨x, by simp [hx]⟩).val else 0, ?_, ?_⟩
  · intro x hx
    dsimp only
    rw [dif_pos hx]
    exact (C _).isLt
  · intro x y hx hy hadj heq
    dsimp only at heq
    rw [dif_pos hx, dif_pos hy] at heq
    have hadj' : ((⊤ : G.Subgraph).deleteVerts {v}).coe.Adj ⟨x, by simp [hx]⟩ ⟨y, by simp [hy]⟩ := by
      rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj]
      exact ⟨trivial, by simp [hx], trivial, by simp [hy], hadj⟩
    exact C.valid hadj' (Fin.ext heq)

lemma unique_color {X : Type*} {k : ℕ} {G : SimpleGraph X} (hG : Erdos917.IsKCritical G (k + 1)) (v : X) :
    ∃ f : G.Coloring (Fin (k + 1)), ∀ x, f x = Fin.last k ↔ x = v := by
  classical
  obtain ⟨col, hb, hp⟩ := isKCritical_del_vert_colorable (by omega) hG v
  let f (x : X) : Fin (k + 1) := if hx : x = v then Fin.last k else
    ⟨col x, by have := hb x hx; omega⟩
  have hf (x : X) : f x = Fin.last k ↔ x = v := by
    by_cases h : x = v
    · simp [f, h]
    · simp only [f, dif_neg h, h, iff_false]
      intro he
      have := congrArg Fin.val he
      have := hb x h
      simp only [Fin.val_last] at *
      omega
  refine ⟨Coloring.mk f ?_, hf⟩
  intro x y h he
  by_cases hx : x = v
  · exact h.ne (hx.trans ((hf y).mp (he ▸ (hf x).mpr hx)).symm)
  by_cases hy : y = v
  · exact hx ((hf x).mp (he.trans ((hf y).mpr hy)))
  apply hp _ _ hx hy h
  simpa [f, hx, hy] using congrArg Fin.val he

lemma same_deleted_edge {X : Type*} {k : ℕ} {G : SimpleGraph X} {v w x t : X}
    (f : (G.deleteEdges {s(v, w)}).Coloring (Fin k)) (h : G.Adj x t) (he : f x = f t) :
    s(x, t) = s(v, w) := by
  by_contra hn
  exact f.valid (deleteEdges_adj.mpr ⟨h, by simpa using hn⟩) he

lemma degree_sum {X : Type*} [Fintype X] (G : SimpleGraph X) [DecidableRel G.Adj] (v : X) :
    G.degree v = ∑ w : X, if G.Adj v w then 1 else 0 := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, Finset.sum_boole]
  rfl

end Critical

namespace OddCycle

open SimpleGraph Finset

def diracParity {k : ℕ} (r u : Fin (k + 3)) : Fin 2 :=
  ⟨(u - r).val % 2, Nat.mod_lt _ (by decide)⟩

lemma diracCycle_step {k : ℕ} {u v : Fin (k + 3)}
    (hadj : (cycleGraph (k + 3)).Adj u v) : u + 1 = v ∨ v + 1 = u := by
  rcases (cycleGraph_adj (n := k + 1)).mp hadj with h | h
  · right
    calc
      v + 1 = (u - v) + v := by rw [h]; exact add_comm _ _
      _ = u := sub_add_cancel _ _
  · left
    calc
      u + 1 = (v - u) + u := by rw [h]; exact add_comm _ _
      _ = v := sub_add_cancel _ _

lemma diracParity_eq_of_step {k : ℕ} {r u v : Fin (k + 3)}
    (hstep : u + 1 = v) (heq : diracParity r u = diracParity r v) : v = r := by
  let w := u - r
  have hshift : v - r = w + 1 := by
    rw [← hstep]
    dsimp only [w]
    abel
  have hpar : w.val % 2 = (v - r).val % 2 := congrArg Fin.val heq
  have hval : (v - r).val = (w.val + 1) % (k + 3) := by
    rw [hshift, Fin.val_add, Fin.val_one]
  have hwrap : w.val + 1 = k + 3 := by
    by_contra h
    have hlt : w.val + 1 < k + 3 := by have := w.isLt; omega
    rw [Nat.mod_eq_of_lt hlt] at hval
    omega
  have hz : v - r = 0 := by
    apply Fin.ext
    rw [hval, hwrap, Nat.mod_self]
    rfl
  exact sub_eq_zero.mp hz

lemma diracParity_collision {k : ℕ} {r u v : Fin (k + 3)}
    (hadj : (cycleGraph (k + 3)).Adj u v) (h : diracParity r u = diracParity r v) :
    (u + 1 = v ∧ v = r) ∨ (v + 1 = u ∧ u = r) :=
  (diracCycle_step hadj).imp (fun hs => ⟨hs, diracParity_eq_of_step hs h⟩)
    (fun hs => ⟨hs, diracParity_eq_of_step hs h.symm⟩)

lemma diracParity_valid_away {k : ℕ} {r u v : Fin (k + 3)} (hu : u ≠ r) (hv : v ≠ r)
    (hadj : (cycleGraph (k + 3)).Adj u v) : diracParity r u ≠ diracParity r v := by
  intro h
  exact (diracParity_collision hadj h).elim (fun hc => hv hc.2) (fun hc => hu hc.2)

lemma diracParity_valid_without_edge {k : ℕ} {a b u v : Fin (k + 3)} (hab : a + 1 = b)
    (hpair : s(u, v) ≠ s(a, b)) (hadj : (cycleGraph (k + 3)).Adj u v) :
    diracParity b u ≠ diracParity b v := by
  intro h
  rcases diracParity_collision hadj h with ⟨hstep, hv⟩ | ⟨hstep, hu⟩
  · have hu : u = a := add_right_cancel (hstep.trans (hv.trans hab.symm))
    exact hpair (Sym2.eq_iff.mpr (Or.inl ⟨hu, hv⟩))
  · have hv : v = a := add_right_cancel (hstep.trans (hu.trans hab.symm))
    exact hpair (Sym2.eq_iff.mpr (Or.inr ⟨hu, hv⟩))

lemma proof : H1 := by
  intro b hodd hb
  obtain ⟨k, rfl⟩ : ∃ k, b = k + 3 := ⟨b - 3, by omega⟩
  let G := cycleGraph (k + 3)
  have hχ : G.chromaticNumber = 3 := chromaticNumber_cycleGraph_of_odd _ (by omega) hodd
  refine ⟨G, ⟨⟨hχ, ?_⟩, ?_⟩, ?_⟩
  · intro r
    let S := (⊤ : G.Subgraph).deleteVerts ({r} : Set _)
    change S.coe.chromaticNumber < (⊤ : G.Subgraph).coe.chromaticNumber
    rw [chromaticNumber_congr (Subgraph.topIso (G := G)), hχ]
    have hcol : S.coe.Colorable 2 := by
      refine ⟨Coloring.mk (fun x => diracParity r x.val) ?_⟩
      intro x y h
      exact diracParity_valid_away x.property.2 y.property.2 (S.coe_adj_sub _ _ h)
    exact hcol.chromaticNumber_le.trans_lt (by decide)
  · refine Sym2.ind fun a b (hab : G.Adj a b) => ?_
    change (G.deleteEdges {s(a, b)}).chromaticNumber < G.chromaticNumber
    rw [hχ]
    have del (c e : Fin (k + 3)) (hce : c + 1 = e) : (G.deleteEdges {s(c, e)}).Colorable 2 := by
      refine ⟨Coloring.mk (diracParity e) ?_⟩
      intro x y h
      obtain ⟨hxy, hne⟩ := deleteEdges_adj.mp h
      exact diracParity_valid_without_edge hce hne hxy
    rcases diracCycle_step hab with h | h
    · exact (del a b h).chromaticNumber_le.trans_lt (by decide)
    · rw [Sym2.eq_swap]
      exact (del b a h).chromaticNumber_le.trans_lt (by decide)
  · rw [← coe_edgeFinset, Set.ncard_coe_finset]
    have h := sum_degrees_eq_twice_card_edges G
    simp only [G, cycleGraph_degree_three_le, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h
    change (cycleGraph (k + 3)).edgeFinset.card = _
    omega

end OddCycle

namespace DiracJoin

open Finset SimpleGraph Critical

lemma ncard_edgeSet_map {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : V ≃ W)
    [DecidableRel (G.map e.toEmbedding).Adj] :
    (G.map e.toEmbedding).edgeSet.ncard = G.edgeSet.ncard := by
  rw [← coe_edgeFinset, ← coe_edgeFinset, Set.ncard_coe_finset, Set.ncard_coe_finset]
  have hdeg : ∀ v : V, (G.map e.toEmbedding).degree (e v) = G.degree v := by
    intro v
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
      neighborFinset_eq_filter, neighborFinset_eq_filter]
    refine card_bij (fun w _ => e.symm w) ?_ ?_ ?_
    · intro w hw
      rw [mem_filter] at hw ⊢
      refine ⟨mem_univ _, ?_⟩
      have hwadj := hw.2
      rw [map_adj] at hwadj
      obtain ⟨a, b, hab, ha, hb⟩ := hwadj
      have h1 : a = v := e.injective ha
      have h2 : b = e.symm w := by
        apply e.injective
        simpa using hb
      rwa [← h1, ← h2]
    · intro w₁ _ w₂ _ h
      exact e.symm.injective h
    · intro u hu
      rw [mem_filter] at hu
      refine ⟨e u, ?_, e.symm_apply_apply u⟩
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      rw [map_adj]
      exact ⟨v, u, hu.2, rfl, rfl⟩
  have hsum1 := sum_degrees_eq_twice_card_edges (G.map e.toEmbedding)
  have hsum2 := sum_degrees_eq_twice_card_edges G
  have hsum_eq : ∑ w : W, (G.map e.toEmbedding).degree w = ∑ v : V, G.degree v := by
    rw [← e.sum_comp]
    exact sum_congr rfl fun v _ => hdeg v
  omega

def joinSum {V₁ V₂ : Type*} (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂) :
    SimpleGraph (V₁ ⊕ V₂) where
  Adj
    | .inl x, .inl y => G₁.Adj x y
    | .inr x, .inr y => G₂.Adj x y
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
  symm := ⟨fun u v h => by
    cases u <;> cases v <;> simp only at h ⊢
    · exact h.symm
    · exact h.symm⟩
  loopless := ⟨fun u h => by
    cases u <;> simp only at h
    · exact G₁.ne_of_adj h rfl
    · exact G₂.ne_of_adj h rfl⟩

def joinGraph {n₁ n₂ : ℕ} (G₁ : SimpleGraph (Fin n₁)) (G₂ : SimpleGraph (Fin n₂)) :
    SimpleGraph (Fin (n₁ + n₂)) :=
  (joinSum G₁ G₂).map finSumFinEquiv.toEmbedding

lemma joinGraph_critical {n₁ n₂ k₁ k₂ : ℕ} {G₁ : SimpleGraph (Fin n₁)} {G₂ : SimpleGraph (Fin n₂)}
    (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂)
    (h₁ : Erdos917.IsKCritical G₁ k₁) (h₂ : Erdos917.IsKCritical G₂ k₂) :
    Erdos917.IsKCritical (joinGraph G₁ G₂) (k₁ + k₂) := by
  classical
  obtain ⟨v₁₀⟩ := isKCritical_nonempty hk₁ h₁
  obtain ⟨v₂₀⟩ := isKCritical_nonempty hk₂ h₂
  refine isKCritical_transport (joinSum G₁ G₂) finSumFinEquiv (by omega) ?_ ?_ ?_ ?_
  · obtain ⟨C₁⟩ := isKCritical_colorable h₁
    obtain ⟨C₂⟩ := isKCritical_colorable h₂
    refine colorable_of _ (k₁ + k₂)
      (Sum.elim (fun x => (C₁ x).val) (fun y => k₁ + (C₂ y).val))
      (fun u => by
        cases u with
        | inl x => simp only [Sum.elim_inl]; have := (C₁ x).isLt; omega
        | inr y => simp only [Sum.elim_inr]; have := (C₂ y).isLt; omega)
      ?_
    intro u v huv
    rcases u with x | x <;> rcases v with y | y <;>
      simp only [joinSum, Sum.elim_inl, Sum.elim_inr] at huv ⊢
    · intro heq; exact C₁.valid huv (Fin.ext heq)
    · have := (C₁ x).isLt; omega
    · have := (C₁ y).isLt; omega
    · intro heq; exact C₂.valid huv (Fin.ext (by omega))
  · rintro ⟨C⟩
    let S₁ : Finset (Fin (k₁ + k₂ - 1)) := univ.image (fun x : Fin n₁ => C (.inl x))
    let S₂ : Finset (Fin (k₁ + k₂ - 1)) := univ.image (fun y : Fin n₂ => C (.inr y))
    have hdisj : Disjoint S₁ S₂ := by
      rw [Finset.disjoint_left]
      intro c hc₁ hc₂
      obtain ⟨x, _, rfl⟩ := mem_image.mp hc₁
      obtain ⟨y, _, hy⟩ := mem_image.mp hc₂
      exact C.valid (show (joinSum G₁ G₂).Adj (.inl x) (.inr y) from trivial) hy.symm
    have hcard : S₁.card + S₂.card ≤ k₁ + k₂ - 1 := by
      rw [← card_union_of_disjoint hdisj]
      exact (card_le_univ _).trans_eq (Fintype.card_fin _)
    by_cases hle₁ : S₁.card ≤ k₁ - 1
    · apply isKCritical_not_colorable hk₁ h₁
      let eqv := S₁.equivFin
      refine ⟨Coloring.mk (fun x => (eqv ⟨C (.inl x), mem_image_of_mem _ (mem_univ x)⟩).castLE hle₁) ?_⟩
      intro a b hab heq
      have hval := Fin.castLE_injective hle₁ heq
      have hsub := eqv.injective hval
      exact C.valid (show (joinSum G₁ G₂).Adj (.inl a) (.inl b) from hab) (congrArg Subtype.val hsub)
    · have hle₂ : S₂.card ≤ k₂ - 1 := by omega
      apply isKCritical_not_colorable hk₂ h₂
      let eqv := S₂.equivFin
      refine ⟨Coloring.mk (fun y => (eqv ⟨C (.inr y), mem_image_of_mem _ (mem_univ y)⟩).castLE hle₂) ?_⟩
      intro a b hab heq
      have hval := Fin.castLE_injective hle₂ heq
      have hsub := eqv.injective hval
      exact C.valid (show (joinSum G₁ G₂).Adj (.inr a) (.inr b) from hab) (congrArg Subtype.val hsub)
  · intro v
    cases v with
    | inl _ => exact ⟨.inr v₂₀, trivial⟩
    | inr _ => exact ⟨.inl v₁₀, trivial⟩
  · intro u w huw
    cases u <;> cases w <;> simp only [joinSum] at huw
    · rename_i x y
      obtain ⟨C₁⟩ := isKCritical_del_edge_colorable hk₁ h₁ huw
      obtain ⟨C₂⟩ := isKCritical_colorable h₂
      refine colorable_of _ (k₁ + k₂ - 1)
        (Sum.elim (fun a => (C₁ a).val) (fun b => (k₁ - 1) + (C₂ b).val))
        (fun z => by
          cases z with
          | inl a => simp only [Sum.elim_inl]; have := (C₁ a).isLt; omega
          | inr b => simp only [Sum.elim_inr]; have := (C₂ b).isLt; omega)
        ?_
      intro a b hab
      rw [deleteEdges_adj] at hab
      obtain ⟨hadj, hne⟩ := hab
      rcases a with a₁ | a₂ <;> rcases b with b₁ | b₂ <;>
        simp only [joinSum, Sum.elim_inl, Sum.elim_inr] at hadj ⊢
      · intro heq
        have hadj' : (G₁.deleteEdges {s(x, y)}).Adj a₁ b₁ := by
          rw [deleteEdges_adj]
          refine ⟨hadj, ?_⟩
          intro hs
          apply hne
          rw [Set.mem_singleton_iff] at hs ⊢
          rcases Sym2.eq_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · exact Sym2.eq_swap
        exact C₁.valid hadj' (Fin.ext heq)
      · have := (C₁ a₁).isLt; omega
      · have := (C₁ b₁).isLt; omega
      · intro heq; exact C₂.valid hadj (Fin.ext (by omega))
    · rename_i x y
      obtain ⟨c₁, hc₁_lt, hc₁_p⟩ := isKCritical_del_vert_colorable hk₁ h₁ x
      obtain ⟨c₂, hc₂_lt, hc₂_p⟩ := isKCritical_del_vert_colorable hk₂ h₂ y
      refine colorable_of _ (k₁ + k₂ - 1)
        (Sum.elim (fun a => if a = x then k₁ + k₂ - 2 else c₁ a)
          (fun b => if b = y then k₁ + k₂ - 2 else (k₁ - 1) + c₂ b))
        (fun z => by
          cases z with
          | inl a =>
            simp only [Sum.elim_inl]
            by_cases ha : a = x
            · simp [ha]; omega
            · simp [ha]; have := hc₁_lt a ha; omega
          | inr b =>
            simp only [Sum.elim_inr]
            by_cases hb : b = y
            · simp [hb]; omega
            · simp [hb]; have := hc₂_lt b hb; omega)
        ?_
      intro a b hab
      rw [deleteEdges_adj] at hab
      obtain ⟨hadj, hne⟩ := hab
      rcases a with a₁ | a₂ <;> rcases b with b₁ | b₂ <;>
        simp only [joinSum, Sum.elim_inl, Sum.elim_inr] at hadj ⊢
      · by_cases ha : a₁ = x
        · have hb : b₁ ≠ x := by rintro rfl; exact G₁.ne_of_adj hadj ha
          simp only [ha, hb, ↓reduceIte]; have := hc₁_lt b₁ hb; omega
        · by_cases hb : b₁ = x
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt a₁ ha; omega
          · simp only [ha, hb, ↓reduceIte]; exact hc₁_p a₁ b₁ ha hb hadj
      · by_cases ha : a₁ = x
        · by_cases hb : b₂ = y
          · exfalso; exact hne (by subst ha hb; exact Set.mem_singleton _)
          · simp only [ha, hb, ↓reduceIte]; have := hc₂_lt b₂ hb; omega
        · by_cases hb : b₂ = y
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt a₁ ha; omega
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt a₁ ha; omega
      · by_cases ha : a₂ = y
        · by_cases hb : b₁ = x
          · exfalso; exact hne (by subst ha hb; rw [Sym2.eq_swap]; exact Set.mem_singleton _)
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt b₁ hb; omega
        · by_cases hb : b₁ = x
          · simp only [ha, hb, ↓reduceIte]; have := hc₂_lt a₂ ha; omega
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt b₁ hb; omega
      · by_cases ha : a₂ = y
        · have hb : b₂ ≠ y := by rintro rfl; exact G₂.ne_of_adj hadj ha
          simp only [ha, hb, ↓reduceIte]; have := hc₂_lt b₂ hb; omega
        · by_cases hb : b₂ = y
          · simp only [ha, hb, ↓reduceIte]; have := hc₂_lt a₂ ha; omega
          · simp only [ha, hb, ↓reduceIte]; intro heq; exact hc₂_p a₂ b₂ ha hb hadj (by omega)
    · rename_i y x
      rw [Sym2.eq_swap]
      obtain ⟨c₁, hc₁_lt, hc₁_p⟩ := isKCritical_del_vert_colorable hk₁ h₁ x
      obtain ⟨c₂, hc₂_lt, hc₂_p⟩ := isKCritical_del_vert_colorable hk₂ h₂ y
      refine colorable_of _ (k₁ + k₂ - 1)
        (Sum.elim (fun a => if a = x then k₁ + k₂ - 2 else c₁ a)
          (fun b => if b = y then k₁ + k₂ - 2 else (k₁ - 1) + c₂ b))
        (fun z => by
          cases z with
          | inl a =>
            simp only [Sum.elim_inl]
            by_cases ha : a = x
            · simp [ha]; omega
            · simp [ha]; have := hc₁_lt a ha; omega
          | inr b =>
            simp only [Sum.elim_inr]
            by_cases hb : b = y
            · simp [hb]; omega
            · simp [hb]; have := hc₂_lt b hb; omega)
        ?_
      intro a b hab
      rw [deleteEdges_adj] at hab
      obtain ⟨hadj, hne⟩ := hab
      rcases a with a₁ | a₂ <;> rcases b with b₁ | b₂ <;>
        simp only [joinSum, Sum.elim_inl, Sum.elim_inr] at hadj ⊢
      · by_cases ha : a₁ = x
        · have hb : b₁ ≠ x := by rintro rfl; exact G₁.ne_of_adj hadj ha
          simp only [ha, hb, ↓reduceIte]; have := hc₁_lt b₁ hb; omega
        · by_cases hb : b₁ = x
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt a₁ ha; omega
          · simp only [ha, hb, ↓reduceIte]; exact hc₁_p a₁ b₁ ha hb hadj
      · by_cases ha : a₁ = x
        · by_cases hb : b₂ = y
          · exfalso; exact hne (by subst ha hb; exact Set.mem_singleton _)
          · simp only [ha, hb, ↓reduceIte]; have := hc₂_lt b₂ hb; omega
        · by_cases hb : b₂ = y
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt a₁ ha; omega
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt a₁ ha; omega
      · by_cases ha : a₂ = y
        · by_cases hb : b₁ = x
          · exfalso; exact hne (by subst ha hb; rw [Sym2.eq_swap]; exact Set.mem_singleton _)
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt b₁ hb; omega
        · by_cases hb : b₁ = x
          · simp only [ha, hb, ↓reduceIte]; have := hc₂_lt a₂ ha; omega
          · simp only [ha, hb, ↓reduceIte]; have := hc₁_lt b₁ hb; omega
      · by_cases ha : a₂ = y
        · have hb : b₂ ≠ y := by rintro rfl; exact G₂.ne_of_adj hadj ha
          simp only [ha, hb, ↓reduceIte]; have := hc₂_lt b₂ hb; omega
        · by_cases hb : b₂ = y
          · simp only [ha, hb, ↓reduceIte]; have := hc₂_lt a₂ ha; omega
          · simp only [ha, hb, ↓reduceIte]; intro heq; exact hc₂_p a₂ b₂ ha hb hadj (by omega)
    · rename_i x y
      obtain ⟨C₁⟩ := isKCritical_colorable h₁
      obtain ⟨C₂⟩ := isKCritical_del_edge_colorable hk₂ h₂ huw
      refine colorable_of _ (k₁ + k₂ - 1)
        (Sum.elim (fun a => (C₁ a).val) (fun b => k₁ + (C₂ b).val))
        (fun z => by
          cases z with
          | inl a => simp only [Sum.elim_inl]; have := (C₁ a).isLt; omega
          | inr b => simp only [Sum.elim_inr]; have := (C₂ b).isLt; omega)
        ?_
      intro a b hab
      rw [deleteEdges_adj] at hab
      obtain ⟨hadj, hne⟩ := hab
      rcases a with a₁ | a₂ <;> rcases b with b₁ | b₂ <;>
        simp only [joinSum, Sum.elim_inl, Sum.elim_inr] at hadj ⊢
      · intro heq; exact C₁.valid hadj (Fin.ext heq)
      · have := (C₁ a₁).isLt; omega
      · have := (C₁ b₁).isLt; omega
      · intro heq
        have hadj' : (G₂.deleteEdges {s(x, y)}).Adj a₂ b₂ := by
          rw [deleteEdges_adj]
          refine ⟨hadj, ?_⟩
          intro hs
          apply hne
          rw [Set.mem_singleton_iff] at hs ⊢
          rcases Sym2.eq_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · exact Sym2.eq_swap
        exact C₂.valid hadj' (Fin.ext (by omega))

lemma joinGraph_ncard_edges {n₁ n₂ : ℕ} (G₁ : SimpleGraph (Fin n₁)) (G₂ : SimpleGraph (Fin n₂)) :
    (joinGraph G₁ G₂).edgeSet.ncard = G₁.edgeSet.ncard + G₂.edgeSet.ncard + n₁ * n₂ := by
  classical
  unfold joinGraph
  rw [ncard_edgeSet_map, ← coe_edgeFinset, ← coe_edgeFinset, ← coe_edgeFinset,
    Set.ncard_coe_finset, Set.ncard_coe_finset, Set.ncard_coe_finset]
  have hdeg_inl : ∀ x : Fin n₁, (joinSum G₁ G₂).degree (.inl x) = G₁.degree x + n₂ := by
    intro x
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
      neighborFinset_eq_filter, neighborFinset_eq_filter]
    have hset : univ.filter (fun z : Fin n₁ ⊕ Fin n₂ => (joinSum G₁ G₂).Adj (.inl x) z) =
        ((univ.filter (fun y : Fin n₁ => G₁.Adj x y)).image Sum.inl) ∪ (univ.image Sum.inr) := by
      ext z
      simp only [mem_union, mem_filter, mem_univ, true_and, mem_image]
      cases z <;> simp [joinSum]
    rw [hset, card_union_of_disjoint, card_image_of_injective _ Sum.inl_injective,
      card_image_of_injective _ Sum.inr_injective, card_univ, Fintype.card_fin]
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    obtain ⟨_, _, rfl⟩ := mem_image.mp hz₁
    obtain ⟨_, _, h⟩ := mem_image.mp hz₂
    cases h
  have hdeg_inr : ∀ y : Fin n₂, (joinSum G₁ G₂).degree (.inr y) = n₁ + G₂.degree y := by
    intro y
    rw [← card_neighborFinset_eq_degree, ← card_neighborFinset_eq_degree,
      neighborFinset_eq_filter, neighborFinset_eq_filter]
    have hset : univ.filter (fun z : Fin n₁ ⊕ Fin n₂ => (joinSum G₁ G₂).Adj (.inr y) z) =
        (univ.image Sum.inl) ∪ ((univ.filter (fun w : Fin n₂ => G₂.Adj y w)).image Sum.inr) := by
      ext z
      simp only [mem_union, mem_filter, mem_univ, true_and, mem_image]
      cases z <;> simp [joinSum]
    rw [hset, card_union_of_disjoint, card_image_of_injective _ Sum.inl_injective,
      card_image_of_injective _ Sum.inr_injective, card_univ, Fintype.card_fin]
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    obtain ⟨_, _, rfl⟩ := mem_image.mp hz₁
    obtain ⟨_, _, h⟩ := mem_image.mp hz₂
    cases h
  have h1 := sum_degrees_eq_twice_card_edges (joinSum G₁ G₂)
  have h2 := sum_degrees_eq_twice_card_edges G₁
  have h3 := sum_degrees_eq_twice_card_edges G₂
  have hsum : ∑ z : Fin n₁ ⊕ Fin n₂, (joinSum G₁ G₂).degree z =
      (∑ x : Fin n₁, (G₁.degree x + n₂)) + (∑ y : Fin n₂, (n₁ + G₂.degree y)) := by
    rw [Fintype.sum_sum_type]
    congr 1
    · exact sum_congr rfl fun x _ => hdeg_inl x
    · exact sum_congr rfl fun y _ => hdeg_inr y
  rw [sum_add_distrib, sum_add_distrib] at hsum
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  have hcomm : n₂ * n₁ = n₁ * n₂ := Nat.mul_comm n₂ n₁
  omega

lemma proof : H2 := by
  rintro k₁ k₂ n₁ n₂ e₁ e₂ hk₁ hk₂ ⟨G, hG, rfl⟩ ⟨H, hH, rfl⟩
  exact ⟨joinGraph G H, joinGraph_critical (by omega) (by omega) hG hH,
    joinGraph_ncard_edges G H⟩

end DiracJoin

namespace ToftFour

open Finset SimpleGraph Critical

abbrev V (X Y : Type*) := X ⊕ (X ⊕ (Y ⊕ Y))
abbrev a {X Y : Type*} (x : X) : V X Y := .inl x
abbrev b {X Y : Type*} (x : X) : V X Y := .inr (.inl x)
abbrev c {X Y : Type*} (y : Y) : V X Y := .inr (.inr (.inl y))
abbrev d {X Y : Type*} (y : Y) : V X Y := .inr (.inr (.inr y))

section Graph

variable {X Y : Type*} (G : SimpleGraph X) (H : SimpleGraph Y)

def rel : V X Y → V X Y → Prop
  | .inl x, .inl t => G.Adj x t
  | .inl x, .inr (.inl t) => x = t
  | .inr (.inl t), .inl x => x = t
  | .inr (.inl _), .inr (.inr (.inl _)) => True
  | .inr (.inr (.inl _)), .inr (.inl _) => True
  | .inr (.inr (.inl y)), .inr (.inr (.inr t)) => y = t
  | .inr (.inr (.inr t)), .inr (.inr (.inl y)) => y = t
  | .inr (.inr (.inr y)), .inr (.inr (.inr t)) => H.Adj y t
  | _, _ => False

def graph : SimpleGraph (V X Y) where
  Adj := rel G H
  symm := ⟨by
    rintro (x|x|y|y) (t|t|s|s) h <;> simp only [rel] at * <;> first | assumption | exact h.symm⟩
  loopless := ⟨by rintro (x|x|y|y) <;> simp [rel]⟩

lemma coloring {k : ℕ} (D : Set (Sym2 (V X Y))) (f g : X → Fin k) (h i : Y → Fin k)
    (ha : ∀ x t, G.Adj x t → f x = f t → s(a x, a t) ∈ D)
    (hd : ∀ y t, H.Adj y t → i y = i t → s(d y, d t) ∈ D)
    (hm : ∀ x, f x = g x → s(a x, b x) ∈ D)
    (hn : ∀ y, i y = h y → s(c y, d y) ∈ D)
    (hb : ∀ x y, g x = h y → s(b x, c y) ∈ D) :
    ((graph G H).deleteEdges D).Colorable k := by
  refine ⟨Coloring.mk (Sum.elim f (Sum.elim g (Sum.elim h i))) ?_⟩
  intro v w had he
  rw [deleteEdges_adj] at had
  obtain ⟨hadj, hne⟩ := had
  apply hne
  rcases v with x|x|y|y <;> rcases w with t|t|u|u <;>
    simp only [graph, rel] at hadj <;> simp only [Sum.elim_inl, Sum.elim_inr] at he
  · exact ha _ _ hadj he
  · subst t; exact hm _ he
  · subst t; rw [Sym2.eq_swap]; exact hm _ he.symm
  · exact hb _ _ he
  · rw [Sym2.eq_swap]; exact hb _ _ he.symm
  · subst u; exact hn _ he.symm
  · subst u; rw [Sym2.eq_swap]; exact hn _ he
  · exact hd _ _ hadj he

lemma full (hG : Erdos917.IsKCritical G 3) (hH : Erdos917.IsKCritical H 3) :
    (graph G H).Colorable 4 := by
  obtain ⟨f⟩ := isKCritical_colorable hG
  obtain ⟨i⟩ := isKCritical_colorable hH
  have hcol := coloring G H (∅ : Set _) (fun x => (f x).castSucc) (fun _ => (3 : Fin 4))
    (fun y => if i y = 0 then 1 else 0) (fun y => (i y).castSucc)
    (by intro x t hx he; exact (f.valid hx (Fin.castSucc_injective _ he)).elim)
    (by intro y t hy he; exact (i.valid hy (Fin.castSucc_injective _ he)).elim)
    (by intro x he; have := congrArg Fin.val he; simp at this; omega)
    (by intro y he; split at he <;> have := congrArg Fin.val he <;> simp at this <;> omega)
    (by intro x y he; split at he <;> contradiction)
  simpa using hcol

lemma shadow_pair {G : SimpleGraph X} (hG : Erdos917.IsKCritical G 3) (f : G.Coloring (Fin 3))
    (g : X → Fin 3) (hg : ∀ x, f x ≠ g x) : ∃ x t, g x ≠ g t := by
  obtain ⟨v⟩ := isKCritical_nonempty (by decide) hG
  obtain ⟨x, hx⟩ := (chromaticNumber_eq_iff_forall_surjective (isKCritical_colorable hG)).mp
    hG.1.1 f (g v)
  exact ⟨x, v, fun h => hg x (hx.trans h.symm)⟩

lemma not_three (hG : Erdos917.IsKCritical G 3) (hH : Erdos917.IsKCritical H 3) :
    ¬(graph G H).Colorable 3 := by
  rintro ⟨F⟩
  let f : G.Coloring (Fin 3) := Coloring.mk (fun x => F (a x))
    (fun {x t} hp => F.valid (show (graph G H).Adj (a x) (a t) from hp))
  let i : H.Coloring (Fin 3) := Coloring.mk (fun y => F (d y))
    (fun {y t} hp => F.valid (show (graph G H).Adj (d y) (d t) from hp))
  obtain ⟨x, t, hx⟩ := shadow_pair hG f (fun x => F (b x))
    (fun x => F.valid (show (graph G H).Adj (a x) (b x) from rfl))
  obtain ⟨y, u, hy⟩ := shadow_pair hH i (fun y => F (c y))
    (fun y => F.valid (show (graph G H).Adj (d y) (c y) from rfl))
  have cross (x : X) (y : Y) : F (b x) ≠ F (c y) := F.valid (show (graph G H).Adj _ _ from trivial)
  have pigeon : ∀ i j k l : Fin 3, i ≠ j → k ≠ l → i ≠ k → i ≠ l → j ≠ k → j ≠ l → False := by
    intro i j k l
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> decide
  exact pigeon _ _ _ _ hx hy (cross x y) (cross x u) (cross t y) (cross t u)

lemma del_l_edge (hG : Erdos917.IsKCritical G 3) (hH : Erdos917.IsKCritical H 3)
    {v w : X} (hvw : G.Adj v w) : ((graph G H).deleteEdges {s(a v, a w)}).Colorable 3 := by
  obtain ⟨f⟩ := isKCritical_del_edge_colorable (by decide) hG hvw
  obtain ⟨i⟩ := isKCritical_colorable hH
  apply coloring G H _ (fun x => (f x).castSucc) (fun _ => (2 : Fin 3)) (fun t => if i t = 0 then 1 else 0) i
  · intro x t hx he
    exact congrArg (Sym2.map a) (same_deleted_edge f hx (Fin.castSucc_injective _ he))
  · intro y t hy he; exact (i.valid hy he).elim
  · intro x he; have := congrArg Fin.val he; simp at this; omega
  · intro y he; exact (show ∀ z : Fin 3, z ≠ (if z = 0 then 1 else 0) by decide) (i y) he |>.elim
  · intro x y he; split at he <;> contradiction

lemma del_l_match (hG : Erdos917.IsKCritical G 3) (hH : Erdos917.IsKCritical H 3)
    (v : X) : ((graph G H).deleteEdges {s(a v, b v)}).Colorable 3 := by
  obtain ⟨f, hf⟩ := unique_color (k := 2) hG v
  obtain ⟨i⟩ := isKCritical_colorable hH
  apply coloring G H _ f (fun _ => (2 : Fin 3)) (fun t => if i t = 0 then 1 else 0) i
  · intro x t hx he; exact (f.valid hx he).elim
  · intro y t hy he; exact (i.valid hy he).elim
  · intro x he; rw [(hf x).mp he]; rfl
  · intro y he; exact (show ∀ z : Fin 3, z ≠ (if z = 0 then 1 else 0) by decide) (i y) he |>.elim
  · intro x y he; split at he <;> contradiction

lemma del_r_edge (hG : Erdos917.IsKCritical G 3) (hH : Erdos917.IsKCritical H 3)
    {v w : Y} (hvw : H.Adj v w) : ((graph G H).deleteEdges {s(d v, d w)}).Colorable 3 := by
  obtain ⟨f⟩ := isKCritical_del_edge_colorable (by decide) hH hvw
  obtain ⟨i⟩ := isKCritical_colorable hG
  apply coloring G H _ i (fun t => if i t = 0 then 1 else 0) (fun _ => (2 : Fin 3)) (fun x => (f x).castSucc)
  · intro y t hy he; exact (i.valid hy he).elim
  · intro x t hx he
    exact congrArg (Sym2.map d) (same_deleted_edge f hx (Fin.castSucc_injective _ he))
  · intro y he; exact (show ∀ z : Fin 3, z ≠ (if z = 0 then 1 else 0) by decide) (i y) he |>.elim
  · intro x he; have := congrArg Fin.val he; simp at this; omega
  · intro x y he; split at he <;> contradiction

lemma del_r_match (hG : Erdos917.IsKCritical G 3) (hH : Erdos917.IsKCritical H 3)
    (v : Y) : ((graph G H).deleteEdges {s(c v, d v)}).Colorable 3 := by
  obtain ⟨f, hf⟩ := unique_color (k := 2) hH v
  obtain ⟨i⟩ := isKCritical_colorable hG
  apply coloring G H _ i (fun t => if i t = 0 then 1 else 0) (fun _ => (2 : Fin 3)) f
  · intro y t hy he; exact (i.valid hy he).elim
  · intro x t hx he; exact (f.valid hx he).elim
  · intro y he; exact (show ∀ z : Fin 3, z ≠ (if z = 0 then 1 else 0) by decide) (i y) he |>.elim
  · intro x he; rw [(hf x).mp he]; rfl
  · intro x y he; split at he <;> contradiction

lemma named_color {G : SimpleGraph X} (hG : Erdos917.IsKCritical G 3) (v : X) (k : Fin 3) :
    ∃ f : G.Coloring (Fin 3), ∀ x, f x = k ↔ x = v := by
  classical
  obtain ⟨f, hf⟩ := unique_color (k := 2) hG v
  let e := Equiv.swap (Fin.last 2) k
  have he : e (Fin.last 2) = k := Equiv.swap_apply_left _ _
  refine ⟨Coloring.mk (fun x => e (f x)) (fun {x t} h hh => f.valid h (e.injective hh)), ?_⟩
  intro x
  change e (f x) = k ↔ x = v
  rw [← he, e.injective.eq_iff, hf]

lemma del_cross [DecidableEq X] [DecidableEq Y] (hG : Erdos917.IsKCritical G 3) (hH : Erdos917.IsKCritical H 3)
    (v : X) (w : Y) : ((graph G H).deleteEdges {s(b v, c w)}).Colorable 3 := by
  obtain ⟨f, hf⟩ := named_color hG v 0
  obtain ⟨i, hi⟩ := named_color hH w 1
  apply coloring G H _ f (fun x => if x = v then 2 else 0) (fun y => if y = w then 2 else 1) i
  · intro x t hx he; exact (f.valid hx he).elim
  · intro y t hy he; exact (i.valid hy he).elim
  · intro x he; split at he
    · rename_i hx; have hh := (hf x).mpr hx; omega
    · rename_i hx; exact (hx ((hf x).mp he)).elim
  · intro y he; split at he
    · rename_i hy; have hh := (hi y).mpr hy; omega
    · rename_i hy; exact (hy ((hi y).mp he)).elim
  · intro x y he
    by_cases hx : x = v <;> by_cases hy : y = w <;> simp_all

lemma del [DecidableEq X] [DecidableEq Y] (hG : Erdos917.IsKCritical G 3) (hH : Erdos917.IsKCritical H 3) :
    ∀ v w, (graph G H).Adj v w → ((graph G H).deleteEdges {s(v, w)}).Colorable 3 := by
  rintro (x|x|y|y) (t|t|s|s) hadj <;> simp only [graph, rel] at hadj
  · exact del_l_edge G H hG hH hadj
  · subst t; exact del_l_match G H hG hH x
  · subst t; rw [Sym2.eq_swap]; exact del_l_match G H hG hH x
  · exact del_cross G H hG hH x s
  · rw [Sym2.eq_swap]; exact del_cross G H hG hH t y
  · subst s; exact del_r_match G H hG hH y
  · subst s; rw [Sym2.eq_swap]; exact del_r_match G H hG hH y
  · exact del_r_edge G H hG hH hadj

end Graph

lemma edge_count {n m : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m)) :
    (graph G H).edgeSet.ncard = G.edgeSet.ncard + H.edgeSet.ncard + n + m + n * m := by
  classical
  let T := graph G H
  have da (x : Fin n) : T.degree (a x) = G.degree x + 1 := by
    rw [degree_sum, degree_sum, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [T, graph, rel, a]
  have db (x : Fin n) : T.degree (b x) = 1 + m := by
    rw [degree_sum, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [T, graph, rel, b]
  have dc (y : Fin m) : T.degree (c y) = n + 1 := by
    rw [degree_sum, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [T, graph, rel, c]
  have dd (y : Fin m) : T.degree (d y) = H.degree y + 1 := by
    rw [degree_sum, degree_sum, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [T, graph, rel, d, add_comm]
  have hs := sum_degrees_eq_twice_card_edges T
  change (∑ v : Fin n ⊕ (Fin n ⊕ (Fin m ⊕ Fin m)), T.degree v) = _ at hs
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at hs
  change (∑ x, T.degree (a x)) + ((∑ x, T.degree (b x)) + ((∑ y, T.degree (c y)) + ∑ y, T.degree (d y))) = _ at hs
  simp only [da, db, dc, dd, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hs
  have hg := sum_degrees_eq_twice_card_edges G
  have hh := sum_degrees_eq_twice_card_edges H
  change T.edgeSet.ncard = _
  rw [← coe_edgeFinset, ← coe_edgeFinset, ← coe_edgeFinset]
  simp only [Set.ncard_coe_finset]
  nlinarith

lemma proof : H3 := by
  classical
  rintro n m _ _ ⟨G, hG, rfl⟩ ⟨H, hH, rfl⟩
  let e : V (Fin n) (Fin m) ≃ Fin (2 * n + 2 * m) := Fintype.equivOfCardEq (by simp [V]; omega)
  refine ⟨(graph G H).map e.toEmbedding, ?_, ?_⟩
  · apply isKCritical_transport _ e (by decide : 1 ≤ 4) (full G H hG hH) (not_three G H hG hH)
    · rintro (x|x|y|y)
      · exact ⟨b x, rfl⟩
      · exact ⟨a x, rfl⟩
      · exact ⟨d y, rfl⟩
      · exact ⟨c y, rfl⟩
    · exact del G H hG hH
  · rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset, SimpleGraph.card_edgeFinset_map]
    simpa only [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset] using edge_count G H

end ToftFour

namespace ToftFive

open Finset SimpleGraph Critical

abbrev V (X Y : Type*) := X ⊕ (X ⊕ Y)
abbrev a {X Y : Type*} (x : X) : V X Y := .inl x
abbrev b {X Y : Type*} (x : X) : V X Y := .inr (.inl x)
abbrev c {X Y : Type*} (y : Y) : V X Y := .inr (.inr y)

section Graph

variable {X Y : Type*} (G : SimpleGraph X) (H : SimpleGraph Y)

def rel : V X Y → V X Y → Prop
  | .inl x, .inl t => G.Adj x t
  | .inl x, .inr (.inl t) => x = t
  | .inr (.inl t), .inl x => x = t
  | .inr (.inl _), .inr (.inr _) => True
  | .inr (.inr _), .inr (.inl _) => True
  | .inr (.inr y), .inr (.inr t) => H.Adj y t
  | _, _ => False

def graph : SimpleGraph (V X Y) where
  Adj := rel G H
  symm := ⟨by
    rintro (x|x|y) (t|t|s) h <;> simp only [rel] at * <;> first | assumption | exact h.symm⟩
  loopless := ⟨by rintro (x|x|y) <;> simp [rel]⟩

lemma coloring {k : ℕ} (D : Set (Sym2 (V X Y))) (f g : X → Fin k) (h : Y → Fin k)
    (ha : ∀ x t, G.Adj x t → f x = f t → s(a x, a t) ∈ D)
    (hc : ∀ y t, H.Adj y t → h y = h t → s(c y, c t) ∈ D)
    (hm : ∀ x, f x = g x → s(a x, b x) ∈ D)
    (hb : ∀ x y, g x = h y → s(b x, c y) ∈ D) :
    ((graph G H).deleteEdges D).Colorable k := by
  refine ⟨Coloring.mk (Sum.elim f (Sum.elim g h)) ?_⟩
  intro v w had he
  rw [deleteEdges_adj] at had
  obtain ⟨hadj, hne⟩ := had
  apply hne
  rcases v with x|x|y <;> rcases w with t|t|u <;>
    simp only [graph, rel] at hadj <;> simp only [Sum.elim_inl, Sum.elim_inr] at he
  · exact ha _ _ hadj he
  · subst t; exact hm _ he
  · subst t; rw [Sym2.eq_swap]; exact hm _ he.symm
  · exact hb _ _ he
  · rw [Sym2.eq_swap]; exact hb _ _ he.symm
  · exact hc _ _ hadj he

lemma full (hG : Erdos917.IsKCritical G 4) (hH : Erdos917.IsKCritical H 3) :
    (graph G H).Colorable 5 := by
  obtain ⟨f⟩ := isKCritical_colorable hG
  obtain ⟨h⟩ := isKCritical_colorable hH
  have hcol := coloring G H (∅ : Set _) (fun x => (f x).castSucc) (fun _ => (4 : Fin 5))
    (fun y => (h y).castLE (by decide : 3 ≤ 5))
    (by intro x t hx he; exact (f.valid hx (Fin.castSucc_injective _ he)).elim)
    (by intro y t hy he; exact (h.valid hy (Fin.castLE_injective _ he)).elim)
    (by intro x he; have := congrArg Fin.val he; simp at this; omega)
    (by intro x y he; have := congrArg Fin.val he; simp at this; omega)
  simpa using hcol

lemma not_four [Fintype Y] (hG : Erdos917.IsKCritical G 4) (hH : Erdos917.IsKCritical H 3) :
    ¬(graph G H).Colorable 4 := by
  classical
  rintro ⟨F⟩
  let S : Finset (Fin 4) := univ.image (fun y : Y => F (c y))
  have hS : 3 ≤ S.card := by
    by_contra! he
    apply isKCritical_not_colorable (by decide : 1 ≤ 3) hH
    refine ⟨Coloring.mk (fun y => (S.equivFin ⟨F (c y), mem_image_of_mem _ (mem_univ y)⟩).castLE
      (by omega : S.card ≤ 3 - 1)) ?_⟩
    intro y t hy heq
    exact F.valid (show (graph G H).Adj (c y) (c t) from hy)
      (congrArg Subtype.val (S.equivFin.injective (Fin.castLE_injective _ heq)))
  have hb (x : X) : F (b x) ∉ S := by
    rintro he
    obtain ⟨y, _, hh⟩ := mem_image.mp he
    exact F.valid (show (graph G H).Adj (b x) (c y) from trivial) hh.symm
  obtain ⟨v⟩ := isKCritical_nonempty (by decide : 1 ≤ 4) hG
  have same (x : X) : F (b x) = F (b v) := by
    by_contra h
    have hbound := card_le_univ (insert (F (b x)) (insert (F (b v)) S))
    rw [Fintype.card_fin, card_insert_of_notMem (by simp [h, hb]), card_insert_of_notMem (hb v)] at hbound
    omega
  let col : G.Coloring (Fin 4) := Coloring.mk (fun x => F (a x))
    (fun {x t} hp => F.valid (show (graph G H).Adj (a x) (a t) from hp))
  obtain ⟨x, hx⟩ := (chromaticNumber_eq_iff_forall_surjective (isKCritical_colorable hG)).mp
    hG.1.1 col (F (b v))
  exact F.valid (show (graph G H).Adj (a x) (b x) from rfl) (hx.trans (same x).symm)

lemma del_a (hG : Erdos917.IsKCritical G 4) (hH : Erdos917.IsKCritical H 3)
    {v w : X} (hvw : G.Adj v w) : ((graph G H).deleteEdges {s(a v, a w)}).Colorable 4 := by
  obtain ⟨f⟩ := isKCritical_del_edge_colorable (by decide) hG hvw
  obtain ⟨h⟩ := isKCritical_colorable hH
  apply coloring G H _ (fun x => (f x).castSucc) (fun _ => 3) (fun y => (h y).castSucc)
  · intro x t hx he
    exact congrArg (Sym2.map a) (same_deleted_edge f hx (Fin.castSucc_injective _ he))
  · intro x t hx he; exact (h.valid hx (Fin.castSucc_injective _ he)).elim
  · intro x he; have := congrArg Fin.val he; simp at this; omega
  · intro x y he; have := congrArg Fin.val he; simp at this; omega

lemma del_c (hG : Erdos917.IsKCritical G 4) (hH : Erdos917.IsKCritical H 3)
    {v w : Y} (hvw : H.Adj v w) : ((graph G H).deleteEdges {s(c v, c w)}).Colorable 4 := by
  obtain ⟨f⟩ := isKCritical_colorable hG
  obtain ⟨h⟩ := isKCritical_del_edge_colorable (by decide) hH hvw
  apply coloring G H _ f (fun x => if f x = 2 then 3 else 2)
    (fun y => (h y).castLE (by decide : 3 - 1 ≤ 4))
  · intro x t hx he; exact (f.valid hx he).elim
  · intro x t hx he
    exact congrArg (Sym2.map c) (same_deleted_edge h hx (Fin.castLE_injective _ he))
  · intro x he; split at he <;> omega
  · intro x y he
    split at he <;> have hh := congrArg Fin.val he <;> simp at hh <;> omega

lemma del_match [DecidableEq X] (hG : Erdos917.IsKCritical G 4) (hH : Erdos917.IsKCritical H 3)
    (v : X) : ((graph G H).deleteEdges {s(a v, b v)}).Colorable 4 := by
  obtain ⟨f, hf⟩ := unique_color (k := 3) hG v
  obtain ⟨h⟩ := isKCritical_colorable hH
  apply coloring G H _ f (fun _ => 3) (fun y => (h y).castSucc)
  · intro x t hx he; exact (f.valid hx he).elim
  · intro x t hx he; exact (h.valid hx (Fin.castSucc_injective _ he)).elim
  · intro x he; rw [(hf x).mp he]; rfl
  · intro x y he; have := congrArg Fin.val he; simp at this; omega

lemma del_cross [DecidableEq X] (hG : Erdos917.IsKCritical G 4) (hH : Erdos917.IsKCritical H 3)
    (v : X) (w : Y) : ((graph G H).deleteEdges {s(b v, c w)}).Colorable 4 := by
  obtain ⟨f, hf⟩ := unique_color (k := 3) hG v
  obtain ⟨h, hh⟩ := unique_color (k := 2) hH w
  apply coloring G H _ f (fun x => if x = v then 2 else 3) (fun y => (h y).castSucc)
  · intro x t hx he; exact (f.valid hx he).elim
  · intro x t hx he; exact (h.valid hx (Fin.castSucc_injective _ he)).elim
  · intro x he; split at he
    · rename_i h; have h3 : f x = 3 := (hf x).mpr h; rw [h3] at he; contradiction
    · rename_i hn; exact (hn ((hf x).mp he)).elim
  · intro x y he; split at he
    · rename_i h'
      have hy : h y = Fin.last 2 := Fin.castSucc_injective _ (show (h y).castSucc = (Fin.last 2).castSucc from he.symm)
      rw [h', (hh y).mp hy]; rfl
    · have := congrArg Fin.val he; simp at this; omega

lemma del [DecidableEq X] (hG : Erdos917.IsKCritical G 4) (hH : Erdos917.IsKCritical H 3) :
    ∀ v w, (graph G H).Adj v w → ((graph G H).deleteEdges {s(v, w)}).Colorable 4 := by
  rintro (x|x|y) (t|t|s) hadj <;> simp only [graph, rel] at hadj
  · exact del_a G H hG hH hadj
  · subst t; exact del_match G H hG hH x
  · subst t; rw [Sym2.eq_swap]; exact del_match G H hG hH x
  · exact del_cross G H hG hH x s
  · rw [Sym2.eq_swap]; exact del_cross G H hG hH t y
  · exact del_c G H hG hH hadj

end Graph

lemma edge_count {n m : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin m)) :
    (graph G H).edgeSet.ncard = G.edgeSet.ncard + H.edgeSet.ncard + n + n * m := by
  classical
  let T := graph G H
  have da (x : Fin n) : T.degree (a x) = G.degree x + 1 := by
    rw [degree_sum, degree_sum]
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [T, graph, rel, a]
  have db (x : Fin n) : T.degree (b x) = 1 + m := by
    rw [degree_sum]
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [T, graph, rel, b]
  have dc (y : Fin m) : T.degree (c y) = n + H.degree y := by
    rw [degree_sum, degree_sum]
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [T, graph, rel, c]
  have hs := sum_degrees_eq_twice_card_edges T
  change (∑ v : Fin n ⊕ (Fin n ⊕ Fin m), T.degree v) = _ at hs
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at hs
  change (∑ x, T.degree (a x)) + ((∑ x, T.degree (b x)) + ∑ y, T.degree (c y)) = _ at hs
  simp only [da, db, dc, sum_add_distrib, sum_const,
    card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hs
  have hg := sum_degrees_eq_twice_card_edges G
  have hh := sum_degrees_eq_twice_card_edges H
  change T.edgeSet.ncard = _
  rw [← coe_edgeFinset, ← coe_edgeFinset, ← coe_edgeFinset]
  simp only [Set.ncard_coe_finset]
  nlinarith

lemma proof : H4 := by
  classical
  rintro n m _ _ ⟨G, hG, rfl⟩ ⟨H, hH, rfl⟩
  let e : V (Fin n) (Fin m) ≃ Fin (2 * n + m) := Fintype.equivOfCardEq (by simp [V]; omega)
  refine ⟨(graph G H).map e.toEmbedding, ?_, ?_⟩
  · apply isKCritical_transport _ e (by decide : 1 ≤ 5) (full G H hG hH) (not_four G H hG hH)
    · obtain ⟨x₀⟩ := isKCritical_nonempty (by decide : 1 ≤ 4) hG
      rintro (x|x|y)
      · exact ⟨b x, rfl⟩
      · exact ⟨a x, rfl⟩
      · exact ⟨b x₀, trivial⟩
    · exact del G H hG hH
  · rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset, SimpleGraph.card_edgeFinset_map]
    simpa only [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset] using edge_count G H

end ToftFive

namespace Reduction

open Filter

/-- Joining `r` further odd cycles `C_b` to a `k₀`-critical graph. -/
lemma iter (h1 : H1) (h2 : H2) {b : ℕ} (hb : Odd b) (hb3 : 3 ≤ b) {k₀ a e : ℕ} (hk₀ : 3 ≤ k₀)
    (h : ∃ G : SimpleGraph (Fin a), Erdos917.IsKCritical G k₀ ∧ G.edgeSet.ncard = e) :
    ∀ r : ℕ, ∃ E : ℕ,
      (∃ G : SimpleGraph (Fin (a + r * b)), Erdos917.IsKCritical G (k₀ + 3 * r) ∧ G.edgeSet.ncard = E) ∧
      2 * E + r * b ^ 2 = 2 * e + 2 * r * b + 2 * a * r * b + r ^ 2 * b ^ 2 := by
  intro r
  induction r with
  | zero =>
    refine ⟨e, ?_, by ring⟩
    have h' : a + 0 * b = a := by simp
    have h2 : k₀ + 3 * 0 = k₀ := by simp
    rw [h', h2]
    exact h
  | succ r ih =>
    obtain ⟨E, hE, hE2⟩ := ih
    have hj := h2 (k₀ + 3 * r) 3 (a + r * b) b E b (by omega) le_rfl hE (h1 b hb hb3)
    refine ⟨E + b + (a + r * b) * b, ?_, ?_⟩
    · have e1 : k₀ + 3 * (r + 1) = k₀ + 3 * r + 3 := by ring
      have e2 : a + (r + 1) * b = a + r * b + b := by ring
      rw [e1, e2]
      exact hj
    · nlinarith [hE2]

/-- From a critical graph with enough edges to the target inequality. -/
lemma finish {k n E : ℕ} (D : ℝ) (hD : 0 < D)
    (hD' : (((k / 3 : ℕ) : ℝ) + Erdos917.delta k) = D)
    (hP : ∃ G : SimpleGraph (Fin n), Erdos917.IsKCritical G k ∧ G.edgeSet.ncard = E)
    (hineq : (D - 1) * (n : ℝ) ^ 2 ≤ D * (2 * (E : ℝ))) :
    1 / 2 * (1 - 1 / (((k / 3 : ℕ) : ℝ) + Erdos917.delta k)) * (n : ℝ) ^ 2 ≤
      (Erdos917.f k n : ℝ) := by
  obtain ⟨G, hG, hGE⟩ := hP
  have hle : (E : ℝ) ≤ (Erdos917.f k n : ℝ) := by
    have := Erdos917.edgeSet_ncard_le_f hG
    rw [hGE] at this
    exact_mod_cast this
  refine le_trans ?_ hle
  rw [hD']
  have hD0 : D ≠ 0 := hD.ne'
  have e : 1 / 2 * (1 - 1 / D) * (n : ℝ) ^ 2 - E =
      ((D - 1) * (n : ℝ) ^ 2 - D * (2 * (E : ℝ))) / (2 * D) := by
    field_simp
  have h0 : 1 / 2 * (1 - 1 / D) * (n : ℝ) ^ 2 - E ≤ 0 := by
    rw [e]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  linarith

lemma main (h1 : H1) (h2 : H2) (h3 : H3) (h4 : H4) :
    type_of% @Erdos917.erdos_917.variants.lower_construction := by
  intro k hk
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨r, hr⟩ : ∃ r : ℕ, k / 3 = r + 1 := ⟨k / 3 - 1, by omega⟩
  have hrR : (((k / 3 : ℕ) : ℝ)) = (r : ℝ) + 1 := by rw [hr, Nat.cast_add, Nat.cast_one]
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  set j : ℕ := N + 1 with hj
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hmod with hm | hm | hm
  · have hb : Odd (2 * j + 1) := ⟨j, rfl⟩
    have hb3 : 3 ≤ 2 * j + 1 := by omega
    obtain ⟨E, hE, hE2⟩ := iter h1 h2 hb hb3 le_rfl (h1 _ hb hb3) r
    have hk3 : 3 + 3 * r = k := by omega
    rw [hk3] at hE
    have hE2R : (2 : ℝ) * E + r * (2 * j + 1) ^ 2 =
        2 * (2 * j + 1) + 2 * r * (2 * j + 1) + 2 * (2 * j + 1) * r * (2 * j + 1) +
          r ^ 2 * (2 * j + 1) ^ 2 := by exact_mod_cast hE2
    refine ⟨2 * j + 1 + r * (2 * j + 1), by omega, ?_⟩
    have hdelta : Erdos917.delta k = 0 := by simp [Erdos917.delta, hm]
    refine finish ((r : ℝ) + 1) (by positivity) (by rw [hrR, hdelta, add_zero]) hE ?_
    have h2E : (2 : ℝ) * E = 2 * (r + 1) * (2 * j + 1) + r * (r + 1) * (2 * j + 1) ^ 2 := by
      linarith [hE2R]
    rw [h2E]
    push_cast
    have : ((r : ℝ) + 1) * (2 * (r + 1) * (2 * j + 1) + r * (r + 1) * (2 * j + 1) ^ 2) -
        ((r : ℝ) + 1 - 1) * (2 * j + 1 + r * (2 * j + 1)) ^ 2 =
          2 * ((r : ℝ) + 1) ^ 2 * (2 * j + 1) := by ring
    have hpos : (0 : ℝ) ≤ 2 * ((r : ℝ) + 1) ^ 2 * (2 * j + 1) := by positivity
    linarith
  · have hq : Odd (4 * j + 1) := ⟨2 * j, by ring⟩
    have hq3 : 3 ≤ 4 * j + 1 := by omega
    have hb : Odd (14 * j + 3) := ⟨7 * j + 1, by ring⟩
    have hb3 : 3 ≤ 14 * j + 3 := by omega
    have hC := h1 _ hq hq3
    have hT := h3 _ _ _ _ hC hC
    obtain ⟨E, hE, hE2⟩ := iter h1 h2 hb hb3 (by norm_num : 3 ≤ 4) hT r
    have hk3 : 4 + 3 * r = k := by omega
    rw [hk3] at hE
    have hE2R : (2 : ℝ) * E + r * (14 * j + 3) ^ 2 =
        2 * ((4 * j + 1) + (4 * j + 1) + (4 * j + 1) + (4 * j + 1) + (4 * j + 1) * (4 * j + 1)) +
          2 * r * (14 * j + 3) +
          2 * (2 * (4 * j + 1) + 2 * (4 * j + 1)) * r * (14 * j + 3) +
          r ^ 2 * (14 * j + 3) ^ 2 := by exact_mod_cast hE2
    refine ⟨2 * (4 * j + 1) + 2 * (4 * j + 1) + r * (14 * j + 3), by omega, ?_⟩
    have hdelta : Erdos917.delta k = 1 / 7 := by simp [Erdos917.delta, hm]
    refine finish ((r : ℝ) + 1 + 1 / 7) (by positivity) (by rw [hrR, hdelta]) hE ?_
    have h2E : (2 : ℝ) * E =
        2 * ((4 * j + 1) + (4 * j + 1) + (4 * j + 1) + (4 * j + 1) + (4 * j + 1) * (4 * j + 1)) +
          2 * r * (14 * j + 3) +
          2 * (2 * (4 * j + 1) + 2 * (4 * j + 1)) * r * (14 * j + 3) +
          r ^ 2 * (14 * j + 3) ^ 2 - r * (14 * j + 3) ^ 2 := by linarith [hE2R]
    rw [h2E]
    push_cast
    have : ((r : ℝ) + 1 + 1 / 7) *
          (2 * ((4 * j + 1) + (4 * j + 1) + (4 * j + 1) + (4 * j + 1) + (4 * j + 1) * (4 * j + 1)) +
            2 * r * (14 * j + 3) +
            2 * (2 * (4 * j + 1) + 2 * (4 * j + 1)) * r * (14 * j + 3) +
            r ^ 2 * (14 * j + 3) ^ 2 - r * (14 * j + 3) ^ 2) -
        ((r : ℝ) + 1 + 1 / 7 - 1) *
          (2 * (4 * j + 1) + 2 * (4 * j + 1) + r * (14 * j + 3)) ^ 2 =
        (2 * (7 * (r + 1) + 1) * (2 * (4 * j + 1) + 2 * (4 * j + 1) + r * (14 * j + 3)) - 2 * r) /
          7 := by ring
    have hpos : (0 : ℝ) ≤
        (2 * (7 * ((r : ℝ) + 1) + 1) * (2 * (4 * j + 1) + 2 * (4 * j + 1) + r * (14 * j + 3)) -
          2 * r) / 7 := by
      refine div_nonneg ?_ (by norm_num)
      nlinarith [mul_nonneg hr0 hj0, mul_nonneg hr0 hr0, mul_nonneg (mul_nonneg hr0 hr0) hj0]
    linarith
  · have hq : Odd (4 * j + 1) := ⟨2 * j, by ring⟩
    have hq3 : 3 ≤ 4 * j + 1 := by omega
    have hg : Odd (30 * j + 7) := ⟨15 * j + 3, by ring⟩
    have hg3 : 3 ≤ 30 * j + 7 := by omega
    have hb : Odd (46 * j + 11) := ⟨23 * j + 5, by ring⟩
    have hb3 : 3 ≤ 46 * j + 11 := by omega
    have hC := h1 _ hq hq3
    have hT := h3 _ _ _ _ hC hC
    have hF := h4 _ _ _ _ hT (h1 _ hg hg3)
    obtain ⟨E, hE, hE2⟩ := iter h1 h2 hb hb3 (by norm_num : 3 ≤ 5) hF r
    have hk3 : 5 + 3 * r = k := by omega
    rw [hk3] at hE
    have hE2R : (2 : ℝ) * E + r * (46 * j + 11) ^ 2 =
        2 * (((4 * j + 1) + (4 * j + 1) + (4 * j + 1) + (4 * j + 1) + (4 * j + 1) * (4 * j + 1)) +
            (30 * j + 7) + (2 * (4 * j + 1) + 2 * (4 * j + 1)) +
            (2 * (4 * j + 1) + 2 * (4 * j + 1)) * (30 * j + 7)) +
          2 * r * (46 * j + 11) +
          2 * (2 * (2 * (4 * j + 1) + 2 * (4 * j + 1)) + (30 * j + 7)) * r * (46 * j + 11) +
          r ^ 2 * (46 * j + 11) ^ 2 := by exact_mod_cast hE2
    refine ⟨2 * (2 * (4 * j + 1) + 2 * (4 * j + 1)) + (30 * j + 7) + r * (46 * j + 11),
      by omega, ?_⟩
    have hdelta : Erdos917.delta k = 24 / 69 := by simp [Erdos917.delta, hm]
    refine finish ((r : ℝ) + 1 + 24 / 69) (by positivity) (by rw [hrR, hdelta]) hE ?_
    have h2E : (2 : ℝ) * E =
        2 * (((4 * j + 1) + (4 * j + 1) + (4 * j + 1) + (4 * j + 1) + (4 * j + 1) * (4 * j + 1)) +
            (30 * j + 7) + (2 * (4 * j + 1) + 2 * (4 * j + 1)) +
            (2 * (4 * j + 1) + 2 * (4 * j + 1)) * (30 * j + 7)) +
          2 * r * (46 * j + 11) +
          2 * (2 * (2 * (4 * j + 1) + 2 * (4 * j + 1)) + (30 * j + 7)) * r * (46 * j + 11) +
          r ^ 2 * (46 * j + 11) ^ 2 - r * (46 * j + 11) ^ 2 := by linarith [hE2R]
    rw [h2E]
    push_cast
    have : ((r : ℝ) + 1 + 24 / 69) *
          (2 * (((4 * j + 1) + (4 * j + 1) + (4 * j + 1) + (4 * j + 1) +
                (4 * j + 1) * (4 * j + 1)) +
              (30 * j + 7) + (2 * (4 * j + 1) + 2 * (4 * j + 1)) +
              (2 * (4 * j + 1) + 2 * (4 * j + 1)) * (30 * j + 7)) +
            2 * r * (46 * j + 11) +
            2 * (2 * (2 * (4 * j + 1) + 2 * (4 * j + 1)) + (30 * j + 7)) * r * (46 * j + 11) +
            r ^ 2 * (46 * j + 11) ^ 2 - r * (46 * j + 11) ^ 2) -
        ((r : ℝ) + 1 + 24 / 69 - 1) *
          (2 * (2 * (4 * j + 1) + 2 * (4 * j + 1)) + (30 * j + 7) + r * (46 * j + 11)) ^ 2 =
        (2 * (23 * (r + 1) + 8) *
            (2 * (2 * (4 * j + 1) + 2 * (4 * j + 1)) + (30 * j + 7) + r * (46 * j + 11)) -
          2 * (r + 1)) / 23 := by ring
    have hpos : (0 : ℝ) ≤
        (2 * (23 * ((r : ℝ) + 1) + 8) *
            (2 * (2 * (4 * j + 1) + 2 * (4 * j + 1)) + (30 * j + 7) + r * (46 * j + 11)) -
          2 * (r + 1)) / 23 := by
      refine div_nonneg ?_ (by norm_num)
      nlinarith [mul_nonneg hr0 hj0, mul_nonneg hr0 hr0, mul_nonneg (mul_nonneg hr0 hr0) hj0]
    linarith

end Reduction

end OMA.Erdos917Lower

theorem OMA.solution : type_of% @Erdos917.erdos_917.variants.lower_construction :=
  OMA.Erdos917Lower.Reduction.main
    OMA.Erdos917Lower.OddCycle.proof
    OMA.Erdos917Lower.DiracJoin.proof
    OMA.Erdos917Lower.ToftFour.proof
    OMA.Erdos917Lower.ToftFive.proof
