import OMAStatements.S_oeis_a054727
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Tactic

/-!
# Recurrence for noncrossing forests

Split each nonempty forest at the component containing its first vertex. The other
components lie in the gaps between successive vertices of that component. A
nontrivial tree splits in turn at the greatest neighbor of the first vertex,
producing an ordered triple of smaller trees. These bijections give the two
generating-function identities from which we extract the recurrence.

The decompositions are described by Flajolet and Sedgewick, Analytic Combinatorics,
p. 487 (non-crossing configurations).
-/

section

namespace OMA.A054727ForestGaps

open OMA.S_oeis_a054727

/-- An edge disjoint from the first component cannot surround one of its vertices. -/
theorem first_component_outside_edge {n : ℕ} {G : SimpleGraph (Fin (n + 1))}
    (hnc : NonCrossing G) {l r v : Fin (n + 1)} (hlr : l < r) (he : G.Adj l r)
    (hl : ¬ G.Reachable 0 l) (hv : G.Reachable 0 v) : v < l ∨ r < v := by
  have hr : ¬ G.Reachable 0 r := fun h => hl (h.trans he.symm.reachable)
  rw [SimpleGraph.reachable_iff_reflTransGen] at hv
  induction hv with
  | refl =>
    left
    exact lt_of_le_of_ne (Fin.zero_le _) (fun h => hl (h ▸ SimpleGraph.Reachable.rfl))
  | @tail a b path ab ih =>
    have hb : G.Reachable 0 b := ((G.reachable_iff_reflTransGen _ _).mpr path).trans ab.reachable
    have hbl : b ≠ l := fun h => hl (h ▸ hb)
    have hbr : b ≠ r := fun h => hr (h ▸ hb)
    by_contra! h
    obtain ⟨hlb, hbr'⟩ := h
    have h₁ : l < b := lt_of_le_of_ne hlb hbl.symm
    have h₂ : b < r := lt_of_le_of_ne hbr' hbr
    rcases ih with ha | ha
    · exact hnc a b l r (ha.trans h₁) hlr ab he (Or.inl ⟨ha, h₁, h₂⟩)
    · exact hnc b a l r (h₂.trans ha) hlr ab.symm he (Or.inr ⟨h₁, h₂, ha⟩)

/-- All vertices of the first component lie on the same side of both endpoints of
an edge in another component. Thus the endpoints occupy the same gap. -/
theorem outside_edge_same_gap {n : ℕ} {G : SimpleGraph (Fin (n + 1))}
    (hnc : NonCrossing G) {u v : Fin (n + 1)} (he : G.Adj u v) (hu : ¬ G.Reachable 0 u) :
    ∀ w, G.Reachable 0 w → (w ≤ u ↔ w ≤ v) := by
  intro w hw
  rcases lt_trichotomy u v with huv | rfl | hvu
  · rcases first_component_outside_edge hnc huv he hu hw with h | h <;> omega
  · rfl
  · have hv : ¬ G.Reachable 0 v := fun h => hu (h.trans he.symm.reachable)
    rcases first_component_outside_edge hnc hvu he.symm hv hw with h | h <;> omega

/-- Equal cuts locate vertices in the same interval after deleting the first component. -/
def SameCut {n : ℕ} (S : Set (Fin n)) (u v : Fin n) : Prop :=
  ∀ w ∈ S, (w ≤ u ↔ w ≤ v)

theorem first_component_edge_partition {n : ℕ} {G : SimpleGraph (Fin (n + 1))}
    (hnc : NonCrossing G) {u v : Fin (n + 1)} (he : G.Adj u v) :
    (G.Reachable 0 u ∧ G.Reachable 0 v) ∨
    (¬ G.Reachable 0 u ∧ ¬ G.Reachable 0 v ∧ SameCut {w | G.Reachable 0 w} u v) := by
  by_cases hu : G.Reachable 0 u
  · exact Or.inl ⟨hu,hu.trans he.reachable⟩
  · exact Or.inr ⟨hu, fun hv => hu (hv.trans he.symm.reachable), outside_edge_same_gap hnc he hu⟩

theorem first_component_reachable_same_gap {n : ℕ} {G : SimpleGraph (Fin (n + 1))}
    (hnc : NonCrossing G) {u v : Fin (n + 1)} (hu : ¬ G.Reachable 0 u)
    (huv : G.Reachable u v) : SameCut {w | G.Reachable 0 w} u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at huv
  induction huv with
  | refl => exact fun _ _ => Iff.rfl
  | @tail a b path ab ih =>
    have hua := (G.reachable_iff_reflTransGen u a).mpr path
    have ha : ¬ G.Reachable 0 a := fun h => hu (h.trans hua.symm)
    exact fun w hw => (ih w hw).trans (outside_edge_same_gap hnc ab ha w hw)

theorem sameCut_of_between {n : ℕ} {S : Set (Fin n)} {a b c : Fin n}
    (h : SameCut S a b) (hac : a ≤ c) (hcb : c ≤ b) : SameCut S a c := by
  intro w hw
  exact ⟨fun ha => ha.trans hac, fun hc => (h w hw).mpr (hc.trans hcb)⟩

/-- Label a gap by the last backbone vertex that precedes it. The label is
defined for every vertex, including those after the last backbone vertex. -/
def gapLabel {n : ℕ} (S : Finset (Fin (n + 1))) (h0 : 0 ∈ S) (u : Fin (n + 1)) : S :=
  let B := S.filter (· ≤ u)
  have hB : B.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨h0, Fin.zero_le _⟩⟩
  ⟨B.max' hB, (Finset.mem_filter.mp (B.max'_mem hB)).1⟩

theorem gapLabel_le {n : ℕ} (S : Finset (Fin (n + 1))) (h0 : 0 ∈ S) (u : Fin (n + 1)) :
    (gapLabel S h0 u : Fin (n+1)) ≤ u :=
  (Finset.mem_filter.mp (Finset.max'_mem (S.filter (· ≤ u))
    ⟨0, Finset.mem_filter.mpr ⟨h0, Fin.zero_le _⟩⟩)).2

theorem le_gapLabel_iff {n : ℕ} (S : Finset (Fin (n + 1))) (h0 : 0 ∈ S)
    (u : Fin (n + 1)) (w : S) : (w ≤ gapLabel S h0 u) ↔ ((w : Fin (n+1)) ≤ u) := by
  refine ⟨fun h => le_trans h (gapLabel_le S h0 u), ?_⟩
  intro h
  exact (S.filter (· ≤ u)).le_max' w (Finset.mem_filter.mpr ⟨w.property,h⟩)

theorem sameCut_iff_gapLabel_eq {n : ℕ} (S : Finset (Fin (n + 1))) (h0 : 0 ∈ S)
    (u v : Fin (n + 1)) : SameCut (↑S) u v ↔ gapLabel S h0 u = gapLabel S h0 v := by
  constructor
  · intro h
    apply le_antisymm
    · apply (le_gapLabel_iff S h0 v _).mpr
      exact (h _ (gapLabel S h0 u).property).mp (gapLabel_le S h0 u)
    · apply (le_gapLabel_iff S h0 u _).mpr
      exact (h _ (gapLabel S h0 v).property).mpr (gapLabel_le S h0 v)
  · intro h w hw
    let w' : S := ⟨w,hw⟩
    calc w ≤ u ↔ w' ≤ gapLabel S h0 u := (le_gapLabel_iff S h0 u w').symm
         _ ↔ w' ≤ gapLabel S h0 v := by rw [h]
         _ ↔ w ≤ v := le_gapLabel_iff S h0 v w'

/-- To glue non-crossing graphs, it suffices to check pairs of edges on the
backbone and pairs of edges whose endpoints occupy a common gap. -/
theorem nonCrossing_of_pieces {n : ℕ} {G : SimpleGraph (Fin n)} (S : Set (Fin n))
    (parts : ∀ {u v}, G.Adj u v → (u ∈ S ∧ v ∈ S) ∨ (u ∉ S ∧ v ∉ S ∧ SameCut S u v))
    (backbone : ∀ {a b c d}, a ∈ S → b ∈ S → c ∈ S → d ∈ S → a < c → c < b → b < d →
      G.Adj a b → G.Adj c d → False)
    (gaps : ∀ {a b c d}, a ∉ S → b ∉ S → c ∉ S → d ∉ S → SameCut S a c →
      a < c → c < b → b < d → G.Adj a b → G.Adj c d → False) : NonCrossing G := by
  have sep {a b c d : Fin n} (hac : a < c) (hcb : c < b) (hbd : b < d)
      (ab : G.Adj a b) (cd : G.Adj c d) : False := by
    rcases parts ab with ⟨ha,hb⟩ | ⟨ha,hb,hab⟩ <;>
      rcases parts cd with ⟨hc,hd⟩ | ⟨hc,hd,hcd⟩
    · exact backbone ha hb hc hd hac hcb hbd ab cd
    · exact hcb.not_ge ((hcd b hb).mpr hbd.le)
    · exact hac.not_ge ((hab c hc).mpr hcb.le)
    · exact gaps ha hb hc hd (sameCut_of_between hab hac.le hcb.le) hac hcb hbd ab cd
  rintro a b c d _ _ ab cd (⟨hac,hcb,hbd⟩ | ⟨hca,had,hdb⟩)
  · exact sep hac hcb hbd ab cd
  · exact sep hca had hdb cd ab

end OMA.A054727ForestGaps


namespace A054727
open SimpleGraph
variable {V I : Type*} (label : V → I)

/-- Glue graphs on the fibers of a vertex labeling, with all edges inside one fiber. -/
def glueFibers (H : ∀ i, SimpleGraph {v // label v = i}) : SimpleGraph V where
  Adj u v := ∃ i, ∃ hu : label u = i, ∃ hv : label v = i, (H i).Adj ⟨u, hu⟩ ⟨v, hv⟩
  symm := ⟨by
    rintro _ _ ⟨i, hu, hv, h⟩
    exact ⟨i, hv, hu, h.symm⟩⟩
  loopless := ⟨by
    rintro _ ⟨i, hu, hv, h⟩
    exact (H i).loopless.irrefl _ h⟩

lemma induce_glueFibers (H : ∀ i, SimpleGraph {v // label v = i}) (i : I) :
    (glueFibers label H).induce {v | label v = i} = H i := by
  ext ⟨u, hu⟩ ⟨v, hv⟩
  constructor
  · rintro ⟨j, hj, _, ha⟩
    obtain rfl : i = j := hu.symm.trans hj
    exact ha
  · exact fun ha => ⟨i, hu, hv, ha⟩

def fiberGraphsEquiv :
    {G : SimpleGraph V // ∀ ⦃u v⦄, G.Adj u v → label u = label v} ≃
      (∀ i, SimpleGraph {v // label v = i}) where
  toFun G i := G.val.induce {v | label v = i}
  invFun H := ⟨glueFibers label H, by rintro _ _ ⟨i, hu, hv, _⟩; exact hu.trans hv.symm⟩
  left_inv G := by
    apply Subtype.ext
    ext u v
    constructor
    · rintro ⟨_, _, _, ha⟩
      exact ha
    · intro ha
      exact ⟨label u, rfl, (G.property ha).symm, ha⟩
  right_inv H := funext (induce_glueFibers label H)

lemma walk_label {G : SimpleGraph V} (h : ∀ ⦃u v⦄, G.Adj u v → label u = label v)
    {u v} (p : G.Walk u v) : label u = label v := by
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (h hadj).trans ih

lemma acyclic_iff_fibers {G : SimpleGraph V}
    (h : ∀ ⦃u v⦄, G.Adj u v → label u = label v) :
    G.IsAcyclic ↔ ∀ i, (G.induce {v | label v = i}).IsAcyclic := by
  classical
  refine ⟨fun ha i => ha.induce _, ?_⟩
  intro hacyc u p hp
  let s := {v | label v = label u}
  have hs (v) (hv : v ∈ p.support) : v ∈ s :=
    (walk_label label h (p.takeUntil v hv)).symm
  have hc : ((p.induce s hs).map (Embedding.induce s).toHom).IsCycle := by simpa using hp
  exact hacyc (label u) (p.induce s hs) hc.of_map

-- This equivalence counts all choices of independent forests on the prescribed fibers.
def fiberForestsEquiv :
    {G : SimpleGraph V // G.IsAcyclic ∧ (∀ ⦃u v⦄, G.Adj u v → label u = label v)} ≃
      (∀ i, {G : SimpleGraph {v // label v = i} // G.IsAcyclic}) where
  toFun G i := ⟨G.val.induce {v | label v = i}, G.property.1.induce _⟩
  invFun H := by
    let g := (fiberGraphsEquiv label).symm (fun i => (H i).val)
    refine ⟨g.val, (acyclic_iff_fibers label g.property).mpr ?_, g.property⟩
    intro i
    change ((glueFibers label (fun i => (H i).val)).induce _).IsAcyclic
    rw [induce_glueFibers]
    exact (H i).property
  left_inv G := by
    apply Subtype.ext
    let g : {A : SimpleGraph V // ∀ ⦃u v⦄, A.Adj u v → label u = label v} := ⟨G.val, G.property.2⟩
    exact congrArg (fun K : {A : SimpleGraph V // ∀ ⦃u v⦄, A.Adj u v → label u = label v} =>
      K.val) ((fiberGraphsEquiv label).left_inv g)
  right_inv H := funext fun i => Subtype.ext (induce_glueFibers label _ i)

end A054727

end

section

open Finset OMA.A054727ForestGaps

namespace OMA.H1Blocks
variable {N : ℕ}

def start (c : Composition N) (i : Fin c.length) : Fin N :=
  c.embedding i ⟨0, c.one_le_blocksFun i⟩

@[simp] lemma start_val (c : Composition N) (i : Fin c.length) :
    (start c i).val = c.sizeUpTo i := by simp [start]

@[simp] lemma index_start (c : Composition N) (i : Fin c.length) : c.index (start c i) = i :=
  c.index_embedding _ _

def roots (c : Composition N) : Finset (Fin N) := univ.image (start c)

lemma start_inj (c : Composition N) : Function.Injective (start c) :=
  fun _ _ h => by simpa only [index_start] using congrArg c.index h

lemma roots_card (c : Composition N) : (roots c).card = c.length := by
  simp [roots, card_image_of_injective _ (start_inj c)]

def startEquiv (c : Composition N) : Fin c.length ≃ ↥(roots c) where
  toFun i := ⟨start c i, mem_image_of_mem _ (mem_univ _)⟩
  invFun u := c.index u.val
  left_inv _ := index_start ..
  right_inv := by
    rintro ⟨u,hu⟩
    obtain ⟨i,_,rfl⟩ := mem_image.mp hu
    exact Subtype.ext (congrArg (start c) (index_start c i))

lemma start_le_iff (c : Composition N) (i : Fin c.length) (v : Fin N) :
    start c i ≤ v ↔ i ≤ c.index v := by
  change (start c i).val ≤ v.val ↔ i.val ≤ (c.index v).val
  rw [start_val]
  constructor
  · intro h
    by_contra! hh
    have hm := c.monotone_sizeUpTo (Nat.succ_le_of_lt hh)
    have hv := c.lt_sizeUpTo_index_succ v
    change v.val < c.sizeUpTo ((c.index v).val + 1) at hv
    exact (not_lt_of_ge (hm.trans h)) hv
  · exact fun h => (c.monotone_sizeUpTo h).trans (c.sizeUpTo_index_le v)

lemma roots_zero {n : ℕ} (c : Composition (n+1)) : 0 ∈ roots c := by
  have hl : 0 < c.length := c.length_pos_iff.mpr (by omega)
  apply mem_image.mpr
  exact ⟨⟨0, hl⟩, mem_univ _, Fin.ext (by simp)⟩

lemma gapLabel_eq {n : ℕ} (c : Composition (n+1)) (v : Fin (n+1)) :
    gapLabel (roots c) (roots_zero c) v = startEquiv c (c.index v) := by
  apply le_antisymm
  · let g := gapLabel (roots c) (roots_zero c) v
    obtain ⟨j,hj⟩ := (startEquiv c).surjective g
    have hle := gapLabel_le (roots c) (roots_zero c) v
    change (g : Fin (n+1)) ≤ v at hle
    rw [← hj] at hle
    change start c j ≤ v at hle
    change g ≤ _
    rw [← hj]
    change start c j ≤ start c (c.index v)
    rw [start_le_iff, index_start]
    exact (start_le_iff c j v).mp hle
  · apply (le_gapLabel_iff _ _ v _).mpr
    exact (start_le_iff c _ v).mpr le_rfl

lemma embedding_mem_roots (c : Composition N) (i : Fin c.length) (j : Fin (c.blocksFun i)) :
    c.embedding i j ∈ roots c ↔ j.val = 0 := by
  constructor
  · rintro h
    obtain ⟨k,_,hk⟩ := mem_image.mp h
    obtain rfl : k = i := by simpa only [index_start, Composition.index_embedding] using congrArg c.index hk
    simpa [start] using (congrArg Fin.val ((c.embedding k).injective hk)).symm
  · intro h
    have : j = ⟨0, c.one_le_blocksFun i⟩ := Fin.ext h
    subst j
    exact (startEquiv c i).property

lemma gap_card {n : ℕ} (c : Composition (n+1)) (i : Fin c.length) :
    (univ.filter (fun v : Fin (n+1) =>
      v ∉ roots c ∧ gapLabel (roots c) (roots_zero c) v = startEquiv c i)).card =
        c.blocksFun i - 1 := by
  classical
  let pos := (univ : Finset (Fin (c.blocksFun i))).filter (fun j => j.val ≠ 0)
  have hem : univ.filter (fun v : Fin (n+1) =>
      v ∉ roots c ∧ gapLabel (roots c) (roots_zero c) v = startEquiv c i) =
      pos.image (c.embedding i) := by
    ext v
    simp only [mem_filter, mem_univ, true_and, mem_image, gapLabel_eq, Equiv.apply_eq_iff_eq]
    constructor
    · rintro ⟨hn, hi⟩
      subst i
      refine ⟨c.invEmbedding v, ?_, c.embedding_comp_inv v⟩
      apply mem_filter.mpr
      refine ⟨mem_univ _, fun he => hn ?_⟩
      rw [← c.embedding_comp_inv v]
      exact (embedding_mem_roots c _ _).mpr he
    · rintro ⟨j,hj,rfl⟩
      exact ⟨fun h => (mem_filter.mp hj).2 ((embedding_mem_roots c i j).mp h), c.index_embedding i j⟩
  rw [hem, card_image_of_injective _ (c.embedding i).injective]
  let z : Fin (c.blocksFun i) := ⟨0,c.one_le_blocksFun i⟩
  have hz : pos = univ.erase z := by
    ext j
    simp [pos, z, Fin.ext_iff]
  simp [hz]

lemma mem_roots_iff {n : ℕ} (c : Composition n) (v : Fin n) :
    v ∈ roots c ↔ v.castSucc ∈ c.boundaries := by
  constructor
  · intro h
    obtain ⟨i, _, rfl⟩ := mem_image.mp h
    apply mem_map.mpr
    exact ⟨i.castSucc, mem_univ _, Fin.ext (by simp [Composition.boundary])⟩
  · intro h
    obtain ⟨j,_,hj⟩ := mem_map.mp h
    obtain ⟨i, rfl⟩ : ∃ i : Fin c.length, i.castSucc = j := by
      apply Fin.exists_castSucc_eq.mpr
      rintro rfl
      change c.boundary (Fin.last c.length) = v.castSucc at hj
      rw [c.boundary_last] at hj
      exact v.castSucc_ne_last hj.symm
    apply mem_image.mpr
    exact ⟨i, mem_univ _, Fin.ext (by simpa [Composition.boundary] using congrArg Fin.val hj)⟩

def rootSetsEquiv (n : ℕ) : Composition (n+1) ≃ {S : Finset (Fin (n+1)) // 0 ∈ S} where
  toFun c := ⟨roots c, roots_zero c⟩
  invFun S := (⟨insert (Fin.last (n+1)) (S.val.map Fin.castSuccEmb),
    by exact mem_insert_of_mem (mem_map.mpr ⟨0, S.property, rfl⟩), mem_insert_self ..⟩ :
    CompositionAsSet (n+1)).toComposition
  left_inv c := by
    apply (compositionEquiv _).injective
    ext j
    change j ∈ (CompositionAsSet.toComposition _).boundaries ↔ j ∈ c.boundaries
    rw [CompositionAsSet.toComposition_boundaries]
    refine Fin.lastCases ?_ (fun v => ?_) j
    · simp
      exact c.toCompositionAsSet.getLast_mem
    · change v.castSucc ∈ insert _ ((roots c).map Fin.castSuccEmb) ↔ v.castSucc ∈ c.boundaries
      rw [← mem_roots_iff]
      simp
  right_inv S := by
    apply Subtype.ext
    ext v
    rw [mem_roots_iff, CompositionAsSet.toComposition_boundaries]
    simp

end OMA.H1Blocks

end

section

open Finset PowerSeries
namespace OMA.H1Enumeration

def profileComp {k n : ℕ} (p : Fin k →₀ ℕ) (hs : ∑ i, p i = n) (hp : ∀ i, 0 < p i) :
    Composition n where
  blocks := List.ofFn fun i => p i
  blocks_sum := by simpa only [Fin.sum_ofFn] using hs
  blocks_pos := by simpa using hp

lemma coeff_pow_comps (U : PowerSeries ℚ) (hU : coeff 0 U = 0) (k n : ℕ) :
    coeff n (U ^ k) = ∑ c ∈ univ.filter (fun c : Composition n => c.length = k),
      (c.blocks.map (fun d => coeff d U)).prod := by
  classical
  have hp := coeff_prod (fun _ : Fin k => U) n univ
  simp only [prod_const, card_univ, Fintype.card_fin] at hp
  rw [hp]
  let s := finsuppAntidiag (univ : Finset (Fin k)) n
  change ∑ p ∈ s, _ = _
  have hs (p) (h : p ∈ s) : ∑ i, p i = n := (mem_finsuppAntidiag.mp h).1
  have hre : (∑ p ∈ s.filter (fun p => ∀ i, 0 < p i), ∏ i, coeff (p i) U) =
      ∑ p ∈ s, ∏ i, coeff (p i) U := by
    apply sum_subset (filter_subset ..)
    intro p hmem hnot
    simp only [mem_filter, hmem, true_and, not_forall, not_lt, Nat.le_zero] at hnot
    obtain ⟨i, hi⟩ := hnot
    exact prod_eq_zero (mem_univ i) (hi ▸ hU)
  rw [← hre]
  let f (p : Fin k →₀ ℕ) (h : p ∈ s.filter (fun p => ∀ i, 0 < p i)) :=
    profileComp p (hs p (mem_filter.mp h).1) (mem_filter.mp h).2
  apply sum_bij f
  · intro p h
    simp [f, profileComp, Composition.length]
  · intro p hp' q hq' he
    have h := congrArg Composition.blocks he
    have hz : List.ofFn (fun i => p i) = List.ofFn (fun i => q i) := h
    exact DFunLike.ext' (List.ofFn_inj.mp hz)
  · intro c hc
    obtain rfl : c.length = k := (mem_filter.mp hc).2
    let p := Finsupp.equivFunOnFinite.symm c.blocksFun
    have he (i) : p i = c.blocksFun i := rfl
    have hm : p ∈ s := mem_finsuppAntidiag.mpr ⟨by simpa only [he] using c.sum_blocksFun,
      subset_univ _⟩
    have hp' : ∀ i, 0 < p i := c.one_le_blocksFun
    refine ⟨p, mem_filter.mpr ⟨hm,hp'⟩, ?_⟩
    apply Composition.ext
    exact c.ofFn_blocksFun
  · intro p h
    simp [f, profileComp, List.map_ofFn, Fin.prod_ofFn, Function.comp_def]

lemma coeff_subst_comps (T U : PowerSeries ℚ) (hU : coeff 0 U = 0) (n : ℕ) :
    coeff n (T.subst U) = ∑ c : Composition n, coeff c.length T *
      (c.blocks.map (fun d => coeff d U)).prod := by
  classical
  have hsubst : HasSubst U := HasSubst.of_constantCoeff_zero' (by simpa using hU)
  rw [coeff_subst' hsubst]
  simp_rw [smul_eq_mul, coeff_pow_comps U hU, mul_sum]
  have hr (k : ℕ) : (∑ c ∈ univ.filter (fun c : Composition n => c.length = k),
      coeff k T * (c.blocks.map (fun d => coeff d U)).prod) =
      ∑ c ∈ univ.filter (fun c : Composition n => c.length = k),
      coeff c.length T * (c.blocks.map (fun d => coeff d U)).prod := by
    apply sum_congr rfl
    intro c hc
    rw [(mem_filter.mp hc).2]
  simp_rw [hr]
  rw [finsum_eq_sum_of_support_subset _ (s := range (n+1))]
  · apply sum_fiberwise_of_maps_to
    intro c _
    exact mem_range.mpr (Nat.lt_succ_of_le c.length_le)
  · intro k hk
    contrapose! hk
    rw [Function.notMem_support]
    apply sum_eq_zero
    intro c hc
    have := (mem_filter.mp hc).2
    have := c.length_le
    have hk' : ¬ k < n + 1 := fun h => hk (mem_range.mpr h)
    omega

end OMA.H1Enumeration

end

section

namespace OMA.H1Fixed

open SimpleGraph OMA.S_oeis_a054727 OMA.A054727ForestGaps
open _root_.A054727

variable {n : ℕ} (S : Finset (Fin (n+1))) (h0 : 0 ∈ S)

def region (v : Fin (n+1)) : Option S :=
  if v ∈ S then none else some (gapLabel S h0 v)

def gapSet (s : S) : Finset (Fin (n+1)) :=
  Finset.univ.filter (fun v => v ∉ S ∧ gapLabel S h0 v = s)

@[simp] lemma region_none {v} : region S h0 v = none ↔ v ∈ S := by
  by_cases h : v ∈ S <;> simp [region, h]

@[simp] lemma region_some {v} {s : S} : region S h0 v = some s ↔ v ∈ gapSet S h0 s := by
  by_cases h : v ∈ S <;> simp [region, gapSet, h]

def NC {V : Type*} [LT V] (G : SimpleGraph V) : Prop :=
  ∀ ⦃a b c d : V⦄, a < c → c < b → b < d → G.Adj a b → G.Adj c d → False

lemma nc_iff {m : ℕ} (G : SimpleGraph (Fin m)) : NC G ↔ NonCrossing G := by
  constructor
  · rintro h a b c d _ _ ab cd (⟨hac,hcb,hbd⟩ | ⟨hca,had,hdb⟩)
    · exact h hac hcb hbd ab cd
    · exact h hca had hdb cd ab
  · intro h a b c d hac hcb hbd ab cd
    exact h a b c d (hac.trans hcb) (hcb.trans hbd) ab cd (Or.inl ⟨hac,hcb,hbd⟩)

lemma edges_in_regions {G : SimpleGraph (Fin (n+1))} (hn : NonCrossing G)
    (hs : ∀ v, G.Reachable 0 v ↔ v ∈ S) :
    ∀ ⦃u v⦄, G.Adj u v → region S h0 u = region S h0 v := by
  intro u v he
  rcases first_component_edge_partition hn he with ⟨hu,hv⟩ | ⟨hu,hv,h⟩
  · simp [region, (hs _).mp hu, (hs _).mp hv]
  · have hcut : SameCut (↑S) u v := fun x hx => h x ((hs _).mpr hx)
    simp [region, mt (hs _).mpr hu, mt (hs _).mpr hv,
      (sameCut_iff_gapLabel_eq S h0 u v).mp hcut]

variable {S h0}

abbrev Fiber (S : Finset (Fin (n+1))) (h0 : 0 ∈ S) (i : Option S) :=
  {v // region S h0 v = i}

def Good (i : Option S) (G : SimpleGraph (Fiber S h0 i)) : Prop :=
  G.IsAcyclic ∧ NC G ∧ (i = none → G.Connected)

lemma local_connected {G : SimpleGraph (Fin (n+1))}
    (hs : ∀ v, G.Reachable 0 v ↔ v ∈ S) :
    (G.induce {v | region S h0 v = none}).Connected := by
  classical
  apply (connected_iff_exists_forall_reachable _).mpr
  refine ⟨⟨0, (region_none S h0).mpr h0⟩, ?_⟩
  rintro ⟨v,hv⟩
  obtain ⟨w⟩ := (hs v).mpr ((region_none S h0).mp hv)
  exact ⟨w.induce _ (fun x hx => (region_none S h0).mpr ((hs x).mp (w.takeUntil x hx).reachable))⟩

lemma local_good {G : SimpleGraph (Fin (n+1))} (ha : G.IsAcyclic) (hn : NonCrossing G)
    (hs : ∀ v, G.Reachable 0 v ↔ v ∈ S) (i : Option S) :
    Good i (G.induce {v | region S h0 v = i}) := by
  refine ⟨ha.induce _, fun a b c d x y z ab cd => (nc_iff G).mpr hn x y z ab cd, ?_⟩
  rintro rfl
  exact local_connected hs

lemma nonCrossing_fibers {G : SimpleGraph (Fin (n+1))}
    (e : ∀ ⦃u v⦄, G.Adj u v → region S h0 u = region S h0 v)
    (hh : ∀ i, Good i (G.induce {v | region S h0 v = i})) : NonCrossing G := by
  apply nonCrossing_of_pieces (↑S)
  · intro u v huv
    have hh' := e huv
    by_cases hu : u ∈ S
    · exact Or.inl ⟨hu,(region_none S h0).mp (hh'.symm.trans ((region_none S h0).mpr hu))⟩
    · have hv : v ∉ S := fun h => hu ((region_none S h0).mp (hh'.trans ((region_none S h0).mpr h)))
      exact Or.inr ⟨hu,hv,(sameCut_iff_gapLabel_eq S h0 u v).mpr (by simpa [region,hu,hv] using hh')⟩
  · intro a b c d ha hb hc hd hac hcb hbd ab cd
    have hnc : NC (G.induce {v | region S h0 v = none}) := (hh none).2.1
    apply hnc (a := ⟨a,(region_none S h0).mpr ha⟩)
      (b := ⟨b,(region_none S h0).mpr hb⟩) (c := ⟨c,(region_none S h0).mpr hc⟩)
      (d := ⟨d,(region_none S h0).mpr hd⟩) hac hcb hbd ab cd
  · intro a b c d ha _ hc _ cut hac hcb hbd ab cd
    let i := region S h0 a
    change a ∉ S at ha
    change c ∉ S at hc
    have hc' : region S h0 c = i := by
      simp [i, region, ha, hc, (sameCut_iff_gapLabel_eq S h0 a c).mp cut]
    have hnc : NC (G.induce {v | region S h0 v = i}) := (hh i).2.1
    exact hnc (a := ⟨a,rfl⟩) (b := ⟨b,(e ab).symm⟩)
      (c := ⟨c,hc'⟩) (d := ⟨d,(e cd).symm.trans hc'⟩) hac hcb hbd ab cd

lemma reachable_fibers {G : SimpleGraph (Fin (n+1))}
    (e : ∀ ⦃u v⦄, G.Adj u v → region S h0 u = region S h0 v)
    (hc : (G.induce {v | region S h0 v = none}).Connected) (v : Fin (n+1)) :
    G.Reachable 0 v ↔ v ∈ S := by
  have hz := (region_none S h0).mpr h0
  constructor
  · rintro ⟨p⟩
    exact (region_none S h0).mp ((walk_label _ e p).symm.trans hz)
  · intro hv
    exact (hc ⟨0,hz⟩ ⟨v,(region_none S h0).mpr hv⟩).map (Embedding.induce _).toHom

variable (S h0)

def fixedEquiv :
    {G : SimpleGraph (Fin (n+1)) // G.IsAcyclic ∧ NonCrossing G ∧ ∀ v, G.Reachable 0 v ↔ v ∈ S} ≃
    (∀ i : Option S, {H : SimpleGraph (Fiber S h0 i) // Good i H}) where
  toFun G i := ⟨G.val.induce _, local_good G.property.1 G.property.2.1 G.property.2.2 i⟩
  invFun H := by
    let K := (fiberGraphsEquiv (region S h0)).symm (fun i => (H i).val)
    have hK (i) : Good i (K.val.induce {v | region S h0 v = i}) := by
      exact (induce_glueFibers (region S h0) (fun i => (H i).val) i) ▸ (H i).property
    exact ⟨K.val,(acyclic_iff_fibers _ K.property).mpr (fun i => (hK i).1),
      nonCrossing_fibers K.property hK, reachable_fibers K.property ((hK none).2.2 rfl)⟩
  left_inv G := by
    apply Subtype.ext
    let K : {A : SimpleGraph (Fin (n+1)) // ∀ ⦃u v⦄, A.Adj u v → region S h0 u = region S h0 v} :=
      ⟨G.val,edges_in_regions S h0 G.property.2.1 G.property.2.2⟩
    exact congrArg (fun A : {A : SimpleGraph (Fin (n+1)) //
      ∀ ⦃u v⦄, A.Adj u v → region S h0 u = region S h0 v} => A.val)
      ((fiberGraphsEquiv (region S h0)).left_inv K)
  right_inv H := funext fun i => Subtype.ext (induce_glueFibers _ _ i)

end OMA.H1Fixed

end

section

namespace OMA.H1Fixed

open SimpleGraph OMA.S_oeis_a054727

def relabel {V W : Type*} (e : V ≃ W) : SimpleGraph W ≃ SimpleGraph V where
  toFun G := G.comap e
  invFun G := G.comap e.symm
  left_inv G := by ext; simp
  right_inv G := by ext; simp

theorem nc_comap {V W : Type*} [LinearOrder V] [LinearOrder W] (e : V ≃o W) (G : SimpleGraph W) :
    NC (G.comap e) ↔ NC G := by
  constructor
  · intro h a b c d hac hcb hbd ab cd
    apply h (a := e.symm a) (b := e.symm b) (c := e.symm c) (d := e.symm d)
      (e.symm.strictMono hac) (e.symm.strictMono hcb) (e.symm.strictMono hbd)
    · simpa using ab
    · simpa using cd
  · intro h a b c d hac hcb hbd ab cd
    exact h (e.strictMono hac) (e.strictMono hcb) (e.strictMono hbd) ab cd

variable {n : ℕ} (S : Finset (Fin (n+1))) (h0 : 0 ∈ S)

def rootOrder : Fin S.card ≃o Fiber S h0 none :=
  (S.orderIsoOfFin rfl).trans (OrderIso.setCongr _ _ (by ext v; exact (region_none S h0).symm))

def gapOrder (s : S) : Fin (gapSet S h0 s).card ≃o Fiber S h0 (some s) :=
  ((gapSet S h0 s).orderIsoOfFin rfl).trans (OrderIso.setCongr _ _ (by ext v; exact (region_some S h0).symm))

def rootEquiv :
    {G : SimpleGraph (Fiber S h0 none) // Good none G} ≃
    {G : SimpleGraph (Fin S.card) // G.IsTree ∧ NonCrossing G} := by
  let e := rootOrder S h0
  refine Equiv.subtypeEquiv (relabel e.toEquiv) ?_
  intro G
  change (G.IsAcyclic ∧ NC G ∧ (none = (none : Option S) → G.Connected)) ↔
    (G.comap e).IsTree ∧ NonCrossing (G.comap e)
  rw [← nc_iff, nc_comap]
  have hi := (Iso.comap e.toEquiv G).isTree_iff
  change (G.comap e).IsTree ↔ G.IsTree at hi
  rw [hi]
  exact ⟨fun ⟨ha,hn,hc⟩ => ⟨⟨hc rfl,ha⟩,hn⟩,
    fun ⟨ht,hn⟩ => ⟨ht.isAcyclic,hn,fun _ => ht.connected⟩⟩

def gapEquiv (s : S) :
    {G : SimpleGraph (Fiber S h0 (some s)) // Good (some s) G} ≃
    {G : SimpleGraph (Fin (gapSet S h0 s).card) // G.IsAcyclic ∧ NonCrossing G} := by
  let e := gapOrder S h0 s
  refine Equiv.subtypeEquiv (relabel e.toEquiv) ?_
  intro G
  change (G.IsAcyclic ∧ NC G ∧ (some s = none → G.Connected)) ↔
    (G.comap e).IsAcyclic ∧ NonCrossing (G.comap e)
  rw [← nc_iff, nc_comap]
  have hi := (Iso.comap e.toEquiv G).isAcyclic_iff
  change (G.comap e).IsAcyclic ↔ G.IsAcyclic at hi
  simp [hi]

/-- The fixed-backbone decomposition, with all pieces relabelled in circular order. -/
def fixedNumberedEquiv :
    {G : SimpleGraph (Fin (n+1)) // G.IsAcyclic ∧ NonCrossing G ∧ ∀ v, G.Reachable 0 v ↔ v ∈ S} ≃
    {T : SimpleGraph (Fin S.card) // T.IsTree ∧ NonCrossing T} ×
      (∀ s : S, {G : SimpleGraph (Fin (gapSet S h0 s).card) // G.IsAcyclic ∧ NonCrossing G}) :=
  ((fixedEquiv S h0).trans Equiv.piOptionEquivProd).trans
    (Equiv.prodCongr (rootEquiv S h0) (Equiv.piCongrRight (gapEquiv S h0)))

end OMA.H1Fixed

end

section

namespace OMA.H1Fixed

open SimpleGraph OMA.S_oeis_a054727

abbrev Forest (n : ℕ) := {G : SimpleGraph (Fin n) // G.IsAcyclic ∧ NonCrossing G}
abbrev Tree (n : ℕ) := {G : SimpleGraph (Fin n) // G.IsTree ∧ NonCrossing G}
abbrev RootSet (n : ℕ) := {S : Finset (Fin (n+1)) // 0 ∈ S}
abbrev FixedForest {n : ℕ} (S : RootSet n) :=
  {G : SimpleGraph (Fin (n+1)) // G.IsAcyclic ∧ NonCrossing G ∧ ∀ v, G.Reachable 0 v ↔ v ∈ S.val}

noncomputable def rootSetOf {n : ℕ} (G : SimpleGraph (Fin (n+1))) : RootSet n := by
  classical
  exact ⟨Finset.univ.filter (G.Reachable 0), Finset.mem_filter.mpr ⟨Finset.mem_univ _, .rfl⟩⟩

@[simp] lemma mem_rootSetOf {n : ℕ} (G : SimpleGraph (Fin (n+1))) (v : Fin (n+1)) :
    v ∈ (rootSetOf G).val ↔ G.Reachable 0 v := by classical simp [rootSetOf]

noncomputable def splitRoot (n : ℕ) : Forest (n+1) ≃ (Σ S : RootSet n, FixedForest S) where
  toFun G := ⟨rootSetOf G.val, G.val,G.property.1,G.property.2,fun v => (mem_rootSetOf G.val v).symm⟩
  invFun p := ⟨p.2.val, p.2.property.1, p.2.property.2.1⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨S, G, ha, hn, hs⟩
    have hS : rootSetOf G = S := by
      apply Subtype.ext
      ext v
      exact (mem_rootSetOf G v).trans (hs v)
    cases hS
    rfl

theorem forest_sum_sets (n : ℕ) :
    Nat.card (Forest (n+1)) = ∑ S : RootSet n, Nat.card (Tree S.val.card) *
      ∏ s : S.val, Nat.card (Forest (gapSet S.val S.property s).card) := by
  classical
  rw [Nat.card_congr (splitRoot n), Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro S _
  rw [Nat.card_congr (fixedNumberedEquiv S.val S.property), Nat.card_prod, Nat.card_pi]

end OMA.H1Fixed

end

section

namespace OMA.H1Series
open PowerSeries Finset OMA.S_oeis_a054727 H1Fixed H1Blocks

noncomputable def F : PowerSeries ℚ := 1 + X * PowerSeries.mk (fun n => (a (n+1) : ℚ))
noncomputable def T : PowerSeries ℚ := X * PowerSeries.mk (fun n => (Nat.card (H1Fixed.Tree (n+1)) : ℚ))

lemma forest_zero : Nat.card (Forest 0) = 1 := by
  classical
  have : Nonempty (Forest 0) := ⟨⟨⊥, SimpleGraph.isAcyclic_bot, fun a => Fin.elim0 a⟩⟩
  exact Nat.card_unique

lemma coeff_F (m : ℕ) : coeff m F = (Nat.card (Forest m) : ℚ) := by
  cases m with
  | zero => simp [F, forest_zero]
  | succ m =>
    simp only [F, map_add, coeff_one, Nat.succ_ne_zero, if_false, zero_add,
      coeff_succ_X_mul, coeff_mk]
    change ((Nat.card (Forest (m+1)) : ℤ) : ℚ) = _
    norm_cast

lemma coeff_T (m : ℕ) (hm : 0 < m) : coeff m T = (Nat.card (H1Fixed.Tree m) : ℚ) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  simp [T, coeff_succ_X_mul]

lemma coeff_XF (m : ℕ) (hm : 0 < m) : coeff m (X * F) = (Nat.card (Forest (m-1)) : ℚ) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  simp [coeff_succ_X_mul, coeff_F]

lemma forest_comps (n : ℕ) : Nat.card (Forest (n+1)) =
    ∑ c : Composition (n+1), Nat.card (H1Fixed.Tree c.length) *
      ∏ i, Nat.card (Forest (c.blocksFun i - 1)) := by
  classical
  rw [forest_sum_sets, ← (rootSetsEquiv n).sum_comp]
  apply sum_congr rfl
  intro c _
  change Nat.card (H1Fixed.Tree (roots c).card) *
    (∏ s : roots c, Nat.card (Forest (gapSet (roots c) (roots_zero c) s).card)) = _
  rw [roots_card, ← (startEquiv c).prod_comp]
  simp only [gapSet, gap_card]

theorem forest_series : F = 1 + T.subst (X * F) := by
  classical
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    have h : HasSubst (X * F) := HasSubst.of_constantCoeff_zero' (by simp)
    rw [show T = X * PowerSeries.mk (fun n => (Nat.card (H1Fixed.Tree (n+1)) : ℚ)) from rfl,
      subst_mul h, subst_X h]
    simp [F]
  | succ n =>
    rw [coeff_F, map_add, coeff_one, if_neg (Nat.succ_ne_zero n), zero_add,
      H1Enumeration.coeff_subst_comps _ _ (by simp), forest_comps]
    push_cast
    apply sum_congr rfl
    intro c _
    rw [coeff_T c.length (c.length_pos_iff.mpr (Nat.succ_pos n))]
    congr 1
    rw [← c.ofFn_blocksFun, List.map_ofFn, Fin.prod_ofFn]
    exact prod_congr rfl (fun i _ => (coeff_XF _ (c.one_le_blocksFun i)).symm)

end OMA.H1Series

end

section

namespace A054727H2
open SimpleGraph OMA.S_oeis_a054727

abbrev Tree (n : ℕ) := {G : SimpleGraph (Fin (n+1)) // G.IsTree ∧ NonCrossing G}

variable {n a b c : ℕ}

def shift {m N : ℕ} (s : ℕ) (hs : s+m ≤ N) : Fin m ↪ Fin N where
  toFun v := ⟨s + v.val, by omega⟩
  inj' := by intro u v h; apply Fin.ext; exact Nat.add_left_cancel (congrArg Fin.val h)

def left (hs : a+b+c=n) : Fin (a+1) ↪ Fin (n+2) := shift 0 (by omega)
def middle (hs : a+b+c=n) : Fin (b+1) ↪ Fin (n+2) := shift (a+1) (by omega)
def right (hs : a+b+c=n) : Fin (c+1) ↪ Fin (n+2) := shift (a+b+1) (by omega)
def pivot (hs : a+b+c=n) : Fin (n+2) := ⟨a+b+1,by omega⟩

def glue (hs : a+b+c=n) (A : SimpleGraph (Fin (a+1))) (B : SimpleGraph (Fin (b+1)))
    (C : SimpleGraph (Fin (c+1))) : SimpleGraph (Fin (n+2)) :=
  A.map (left hs) ⊔ B.map (middle hs) ⊔ C.map (right hs) ⊔ edge 0 (pivot hs)

end A054727H2

end

section

namespace A054727H2
open SimpleGraph OMA.S_oeis_a054727 OMA.A054727ForestGaps

lemma root_component_prefix {n : ℕ} (G R : SimpleGraph (Fin (n+2))) (k : Fin (n+2))
    (hnc : NonCrossing G) (hRG : R ≤ G) (hk : G.Adj 0 k)
    (greatest : ∀ v, G.Adj 0 v → v ≤ k) (apart : ¬ R.Reachable 0 k)
    (cover : ∀ v, R.Reachable 0 v ∨ R.Reachable k v) :
    ∃ a : ℕ, a < k.val ∧ ∀ v, R.Reachable 0 v ↔ v.val ≤ a := by
  classical
  have hk0 : (0 : Fin (n+2)) < k := lt_of_le_of_ne (Fin.zero_le _) hk.ne
  have ltK {v : Fin (n+2)} (h : R.Reachable 0 v) : v < k := by
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact hk0
    | @tail p q path pq ih =>
      have hrp := (R.reachable_iff_reflTransGen _ _).mpr path
      have hqk : q ≠ k := fun e => apart (e ▸ hrp.trans pq.reachable)
      by_cases h0 : p = 0
      · subst p
        exact lt_of_le_of_ne (greatest q (hRG pq)) hqk
      · by_contra! h
        have hkq := lt_of_le_of_ne h hqk.symm
        exact hnc 0 k p q hk0 (ih.trans hkq) hk (hRG pq)
          (Or.inl ⟨lt_of_le_of_ne (Fin.zero_le _) (Ne.symm h0), ih, hkq⟩)
  let S := Finset.univ.filter (R.Reachable 0)
  have mem (v : Fin (n+2)) : v ∈ S ↔ R.Reachable 0 v := by simp [S]
  have hn : S.Nonempty := ⟨0,(mem _).mpr .rfl⟩
  let m := S.max' hn
  have hm : R.Reachable 0 m := (mem m).mp (S.max'_mem hn)
  have hRnc : NonCrossing R := fun a b c d h₁ h₂ e₁ e₂ => hnc a b c d h₁ h₂ (hRG e₁) (hRG e₂)
  refine ⟨m.val, ltK hm, fun v => ⟨fun h => S.le_max' v ((mem v).mpr h), ?_⟩⟩
  intro hvm
  obtain hv | hv := cover v
  · exact hv
  · have sc := first_component_reachable_same_gap hRnc apart hv
    have hmv : m ≤ v := (sc m hm).mp (ltK hm).le
    exact (le_antisymm hmv (show v ≤ m from hvm)) ▸ hm

end A054727H2

end

section

namespace A054727H2
open SimpleGraph OMA.S_oeis_a054727

lemma classified_after_erase {n a b c : ℕ} (G : SimpleGraph (Fin (n+2)))
    (hs : a+b+c=n) (hnc : NonCrossing G) (hp : G.Adj 0 (pivot hs))
    (seg : ∀ w, (G.deleteEdges {s(0,pivot hs)}).Reachable 0 w ↔ w.val ≤ a)
    {u v : Fin (n+2)} (huv : u<v) (he : G.Adj u v) :
    v.val ≤ a ∨ (a+1 ≤ u.val ∧ v.val ≤ a+b+1) ∨
      a+b+1 ≤ u.val ∨ (u=0 ∧ v=pivot hs) := by
  classical
  by_cases hb : s(u,v) = s(0,pivot hs)
  · rcases Sym2.eq_iff.mp hb with h|⟨_,hv⟩
    · exact .inr (.inr (.inr h))
    · exact (Fin.not_lt_zero _ (hv ▸ huv)).elim
  have hadj : (G.deleteEdges {s(0,pivot hs)}).Adj u v :=
    deleteEdges_adj.mpr ⟨he, fun h => hb (Set.mem_singleton_iff.mp h)⟩
  by_cases hu : u.val ≤ a
  · exact .inl ((seg v).mp (((seg u).mpr hu).trans hadj.reachable))
  by_cases hv : v.val ≤ a+b+1
  · exact .inr (.inl ⟨by omega, hv⟩)
  by_cases hu' : a+b+1 ≤ u.val
  · exact .inr (.inr (.inl hu'))
  have h0p : (0 : Fin (n+2)) < pivot hs := Fin.pos_iff_ne_zero.mpr hp.ne.symm
  have h0u : (0 : Fin (n+2)) < u := by change 0 < u.val; omega
  exact (hnc _ _ _ _ h0p huv hp he (.inl ⟨h0u, by change u.val < a+b+1; omega,
    by change a+b+1 < v.val; omega⟩)).elim

lemma sizes_of_prefix {n : ℕ} (G : Tree (n+1)) (k : Fin (n+2)) (hk : G.1.Adj 0 k)
    (a : ℕ) (hak : a < k.val)
    (hseg : ∀ w, (G.1.deleteEdges {s(0,k)}).Reachable 0 w ↔ w.val ≤ a) :
    ∃ (a b c : ℕ) (hs : a+b+c=n), G.1.Adj 0 (pivot hs) ∧
      ∀ {u v : Fin (n+2)}, u<v → G.1.Adj u v →
        v.val ≤ a ∨ (a+1 ≤ u.val ∧ v.val ≤ a+b+1) ∨
          a+b+1 ≤ u.val ∨ (u=0 ∧ v=pivot hs) := by
  let b := k.val-(a+1)
  let c := n+1-k.val
  have hs : a+b+c=n := by dsimp [b,c]; omega
  have he : pivot hs = k := Fin.ext (by change a+b+1=k.val; dsimp [b]; omega)
  have h' : G.1.Adj 0 (pivot hs) := he.symm ▸ hk
  exact ⟨a,b,c,hs,h',classified_after_erase G.1 hs G.2.2 h' (by simpa only [he] using hseg)⟩

end A054727H2

end

section

namespace A054727H2
open SimpleGraph OMA.S_oeis_a054727
variable {n a b c : ℕ}

lemma shift_adj {m N d : ℕ} (h : d+m ≤ N) (G : SimpleGraph (Fin m)) (x y : Fin N) :
    (G.map (shift d h)).Adj x y ↔
      ∃ u v, x.val = d+u.val ∧ y.val = d+v.val ∧ G.Adj u v := by
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨u,v,hg,rfl,rfl⟩; exact ⟨u,v,rfl,rfl,hg⟩
  · rintro ⟨u,v,hx,hy,hg⟩; exact ⟨u,v,hg,Fin.ext hx.symm,Fin.ext hy.symm⟩

lemma glue_cases (hs : a+b+c=n) (A : Tree a) (B : Tree b) (C : Tree c)
    {x y : Fin (n+2)} (hxy : x < y) (h : (glue hs A.1 B.1 C.1).Adj x y) :
    (∃ u v, x.val = u.val ∧ y.val = v.val ∧ A.1.Adj u v) ∨
    (∃ u v, x.val = a+1+u.val ∧ y.val = a+1+v.val ∧ B.1.Adj u v) ∨
    (∃ u v, x.val = a+b+1+u.val ∧ y.val = a+b+1+v.val ∧ C.1.Adj u v) ∨
    (x.val = 0 ∧ y.val = a+b+1) := by
  simp only [glue, sup_adj, left, middle, right, shift_adj, Nat.zero_add, edge_adj] at h
  rcases h with ((h|h)|h)|⟨h|h,_⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr ⟨congrArg Fin.val h.1,congrArg Fin.val h.2⟩))
  · obtain ⟨_,rfl⟩ := h
    exact (Fin.not_lt_zero _ hxy).elim

lemma glue_nonCrossing (hs : a+b+c=n) (A : Tree a) (B : Tree b) (C : Tree c) :
    NonCrossing (glue hs A.1 B.1 C.1) := by
  have apart {x y z w : Fin (n+2)} (hxy : x<y) (hyz : y<z) (hzw : z<w)
      (hxz : (glue hs A.1 B.1 C.1).Adj x z) (hyw : (glue hs A.1 B.1 C.1).Adj y w) : False := by
    rcases glue_cases hs A B C (hxy.trans hyz) hxz with
      ⟨u,v,hu,hv,h₁⟩ | ⟨u,v,hu,hv,h₁⟩ | ⟨u,v,hu,hv,h₁⟩ | ⟨hu,hv⟩ <;>
      rcases glue_cases hs A B C (hyz.trans hzw) hyw with
        ⟨r,s,hr,hs',h₂⟩ | ⟨r,s,hr,hs',h₂⟩ | ⟨r,s,hr,hs',h₂⟩ | ⟨hr,hs'⟩
    all_goals first
      | omega
      | exact A.2.2 u v r s (by omega) (by omega) h₁ h₂ (.inl ⟨by omega,by omega,by omega⟩)
      | exact B.2.2 u v r s (by omega) (by omega) h₁ h₂ (.inl ⟨by omega,by omega,by omega⟩)
      | exact C.2.2 u v r s (by omega) (by omega) h₁ h₂ (.inl ⟨by omega,by omega,by omega⟩)
  rintro x z y w _ _ h₁ h₂ (⟨h,i,j⟩|⟨h,i,j⟩)
  · exact apart h i j h₁ h₂
  · exact apart h i j h₂ h₁

lemma in_map_reachable {U V : Type*} {G : SimpleGraph U} {F : SimpleGraph V}
    (e : U ↪ V) (h : G.map e ≤ F) (hc : G.Connected) (u v : U) : F.Reachable (e u) (e v) := by
  let f : G →g F := ⟨e, fun hh => h (map_adj_apply.mpr hh)⟩
  exact (hc u v).map f

lemma glue_connected (hs : a+b+c=n) (A : Tree a) (B : Tree b) (C : Tree c) :
    (glue hs A.1 B.1 C.1).Connected := by
  let G := glue hs A.1 B.1 C.1
  have la : A.1.map (left hs) ≤ G := by dsimp [G,glue]; exact le_sup_left.trans (le_sup_left.trans le_sup_left)
  have lb : B.1.map (middle hs) ≤ G := by dsimp [G,glue]; exact le_sup_right.trans (le_sup_left.trans le_sup_left)
  have lc : C.1.map (right hs) ≤ G := by dsimp [G,glue]; exact le_sup_right.trans le_sup_left
  have br : G.Reachable 0 (pivot hs) := by
    apply Adj.reachable
    exact Or.inr ((edge_adj ..).2 ⟨.inl ⟨rfl,rfl⟩, by intro he; have he' := congrArg Fin.val he; simp [pivot] at he'⟩)
  apply (connected_iff_exists_forall_reachable _).2
  refine ⟨0, fun v => ?_⟩
  by_cases hv : v.val ≤ a
  · let u : Fin (a+1) := ⟨v.val,by omega⟩
    have huv : left hs u = v := Fin.ext (Nat.zero_add _)
    rw [←huv]
    exact in_map_reachable (left hs) la A.2.1.connected 0 u
  by_cases hv' : v.val ≤ a+b+1
  · let u : Fin (b+1) := ⟨v.val-(a+1),by omega⟩
    have huv : middle hs u = v := Fin.ext (by change a+1+(v.val-(a+1))=v.val; omega)
    have hroot : middle hs (Fin.last b) = pivot hs := Fin.ext (by change a+1+b=a+b+1; omega)
    rw [←huv]
    apply br.trans
    rw [←hroot]
    exact in_map_reachable _ lb B.2.1.connected _ _
  · let u : Fin (c+1) := ⟨v.val-(a+b+1),by omega⟩
    have huv : right hs u = v := Fin.ext (by change a+b+1+(v.val-(a+b+1))=v.val; omega)
    rw [←huv]
    apply br.trans
    exact in_map_reachable _ lc C.2.1.connected 0 u


end A054727H2

end

section

namespace A054727H2
open SimpleGraph OMA.S_oeis_a054727
variable {n a b c : ℕ}
lemma edge_count_map_le {U V : Type*} [Finite U] [Finite V] (e : U ↪ V) (G : SimpleGraph U) :
    (G.map e).edgeSet.ncard = G.edgeSet.ncard := by
  rw [edgeSet_map,Set.ncard_image_of_injective _ e.sym2Map.injective]

set_option maxHeartbeats 3000000 in
lemma glue_tree (hs : a+b+c=n) (A : Tree a) (B : Tree b) (C : Tree c) :
    (glue hs A.1 B.1 C.1).IsTree := by
  have hc := glue_connected hs A B C
  refine isTree_iff_connected_and_card.2 ⟨hc, le_antisymm ?_ hc.card_vert_le_card_edgeSet_add_one⟩
  have count {j : ℕ} (D : Tree j) : D.1.edgeSet.ncard = j := by
    have h := (isTree_iff_connected_and_card.1 D.2.1).2
    simp only [Nat.card_coe_set_eq,Nat.card_fin] at h
    omega
  have union (P Q : SimpleGraph (Fin (n+2))) : (P ⊔ Q).edgeSet.ncard ≤ P.edgeSet.ncard + Q.edgeSet.ncard := by
    rw [edgeSet_sup]; exact Set.ncard_union_le _ _
  simp only [Nat.card_coe_set_eq, Nat.card_fin, glue]
  have he : (edge (0 : Fin (n+2)) (pivot hs)).edgeSet.ncard ≤ 1 :=
    (Set.ncard_le_ncard edgeSet_edge_subset).trans_eq (Set.ncard_singleton _)
  let L := A.1.map (left hs)
  let M := B.1.map (middle hs)
  let R := C.1.map (right hs)
  let E := edge (0 : Fin (n+2)) (pivot hs)
  have hl : L.edgeSet.ncard = a := (edge_count_map_le _ _).trans (count A)
  have hm : M.edgeSet.ncard = b := (edge_count_map_le _ _).trans (count B)
  have hr : R.edgeSet.ncard = c := (edge_count_map_le _ _).trans (count C)
  change E.edgeSet.ncard ≤ 1 at he
  change (L ⊔ M ⊔ R ⊔ E).edgeSet.ncard + 1 ≤ n+2
  have h1 := union L M
  have h2 := union (L ⊔ M) R
  have h3 := union (L ⊔ M ⊔ R) E
  omega

end A054727H2

end

section

namespace A054727H2
open SimpleGraph OMA.S_oeis_a054727
variable {n a b c : ℕ}

lemma pivot_adj (hs : a+b+c=n) (A : Tree a) (B : Tree b) (C : Tree c) :
    (glue hs A.1 B.1 C.1).Adj 0 (pivot hs) :=
  Or.inr ((edge_adj ..).2 ⟨.inl ⟨rfl,rfl⟩, by intro h; have := congrArg Fin.val h; simp [pivot] at this⟩)

lemma pivot_greatest (hs : a+b+c=n) (A : Tree a) (B : Tree b) (C : Tree c)
    {w : Fin (n+2)} (hw : (glue hs A.1 B.1 C.1).Adj 0 w) : w ≤ pivot hs := by
  have h0 : (0 : Fin (n+2)) < w := lt_of_le_of_ne (Fin.zero_le _) hw.ne
  rcases glue_cases hs A B C h0 hw with ⟨u,v,hu,hv,_⟩|⟨u,v,hu,hv,_⟩|⟨u,v,hu,hv,_⟩|⟨_,hv⟩ <;>
    change w.val ≤ a+b+1 <;> simp only [Fin.val_zero] at * <;> omega

def eraseBridge {m : ℕ} (G : SimpleGraph (Fin (m+2))) (k : Fin (m+2)) :=
  G.deleteEdges {s(0,k)}

lemma eraseBridge_root_side (hs : a+b+c=n) (A : Tree a) (B : Tree b) (C : Tree c)
    (w : Fin (n+2)) : (eraseBridge (glue hs A.1 B.1 C.1) (pivot hs)).Reachable 0 w ↔ w.val ≤ a := by
  let G := eraseBridge (glue hs A.1 B.1 C.1) (pivot hs)
  have closed {u v : Fin (n+2)} (ha : G.Adj u v) (hu : u.val ≤ a) : v.val ≤ a := by
    by_contra! hv
    obtain ⟨he, hn⟩ := deleteEdges_adj.mp ha
    have huv : u < v := by omega
    rcases glue_cases hs A B C huv he with ⟨r,s,hr,hs',_⟩|⟨r,s,hr,hs',_⟩|⟨r,s,hr,hs',_⟩|⟨h₁,h₂⟩
    · omega
    · omega
    · omega
    · obtain rfl : u = 0 := Fin.ext h₁
      obtain rfl : v = pivot hs := Fin.ext h₂
      exact hn (Set.mem_singleton _)
  constructor
  · rintro ⟨p⟩
    have walk_closed {x y : Fin (n+2)} (q : G.Walk x y) (hx : x.val ≤ a) : y.val ≤ a := by
      induction q with
      | nil => exact hx
      | cons h _ ih => exact ih (closed h hx)
    exact walk_closed p (Nat.zero_le a)
  · intro hw
    let v : Fin (a+1) := ⟨w.val,by omega⟩
    have hw' : left hs v = w := Fin.ext (Nat.zero_add _)
    rw [←hw']
    apply in_map_reachable (left hs) (G := A.1) (u := 0) (v := v) _ A.2.1.connected
    intro x y h
    refine deleteEdges_adj.mpr ⟨Or.inl (Or.inl (Or.inl h)),?_⟩
    obtain ⟨u,v,_,rfl,rfl⟩ := (map_adj ..).1 h
    simp only [Set.mem_singleton_iff, Sym2.eq_iff, not_or]
    change ¬ (_ = 0 ∧ _ = pivot hs) ∧ ¬ (_ = pivot hs ∧ _ = 0)
    have neq (r : Fin (a+1)) : left hs r ≠ pivot hs := by
      intro h; have he := congrArg Fin.val h; change 0+r.val=a+b+1 at he; omega
    exact ⟨fun he => neq _ he.2,fun he => neq _ he.1⟩

lemma sizes_eq {a' b' c' : ℕ} (hs : a+b+c=n) (ht : a'+b'+c'=n)
    (A : Tree a) (B : Tree b) (C : Tree c) (D : Tree a') (E : Tree b') (F : Tree c')
    (h : glue hs A.1 B.1 C.1 = glue ht D.1 E.1 F.1) : a=a' ∧ b=b' ∧ c=c' := by
  have hp : pivot hs = pivot ht := le_antisymm
    (pivot_greatest ht D E F (h ▸ pivot_adj hs A B C))
    (pivot_greatest hs A B C (h.symm ▸ pivot_adj ht D E F))
  have he (v : Fin (n+2)) : v.val ≤ a ↔ v.val ≤ a' := by
    rw [← eraseBridge_root_side hs A B C, h, hp, eraseBridge_root_side ht D E F]
  have ha : a=a' := le_antisymm ((he ⟨a,by omega⟩).mp (le_refl a)) ((he ⟨a',by omega⟩).mpr (le_refl a'))
  have := congrArg Fin.val hp
  change a+b+1=a'+b'+1 at this
  omega

end A054727H2

end

section

namespace A054727H2
open SimpleGraph OMA.S_oeis_a054727
variable {n a b c : ℕ}

lemma eq_of_adj_lt {N : ℕ} {G H : SimpleGraph (Fin N)}
    (f : ∀ u v, u<v → (G.Adj u v ↔ H.Adj u v)) : G=H := by
  ext u v
  rcases lt_trichotomy u v with huv|rfl|hvu
  · exact f u v huv
  · simp
  · simpa only [G.adj_comm v u, H.adj_comm v u] using f v u hvu

lemma left_val (hs : a+b+c=n) (v : Fin (a+1)) : (left hs v).val = v.val := Nat.zero_add _
lemma middle_val (hs : a+b+c=n) (v : Fin (b+1)) : (middle hs v).val = a+1+v.val := rfl
lemma right_val (hs : a+b+c=n) (v : Fin (c+1)) : (right hs v).val = a+b+1+v.val := rfl

lemma comap_left (hs : a+b+c=n) (A : Tree a) (B : Tree b) (C : Tree c) :
    (glue hs A.1 B.1 C.1).comap (left hs) = A.1 := by
  apply eq_of_adj_lt
  intro x y hxy
  rw [comap_adj]
  constructor
  · intro h
    have hxy' : left hs x < left hs y := by change 0+x.val < 0+y.val; omega
    rcases glue_cases hs A B C hxy' h with ⟨u,v,hu,hv,he⟩|⟨u,v,hu,hv,_⟩|⟨u,v,hu,hv,_⟩|⟨hu,hv⟩ <;>
      simp only [left_val] at hu hv
    · have hxu : x=u := Fin.ext (by omega)
      have hyv : y=v := Fin.ext (by omega)
      simpa [hxu,hyv] using he
    all_goals omega
  · exact fun h => Or.inl (Or.inl (Or.inl (map_adj_apply.mpr h)))

lemma comap_middle (hs : a+b+c=n) (A : Tree a) (B : Tree b) (C : Tree c) :
    (glue hs A.1 B.1 C.1).comap (middle hs) = B.1 := by
  apply eq_of_adj_lt
  intro x y hxy
  rw [comap_adj]
  constructor
  · intro h
    have hxy' : middle hs x < middle hs y := by change a+1+x.val < a+1+y.val; omega
    rcases glue_cases hs A B C hxy' h with ⟨u,v,hu,hv,_⟩|⟨u,v,hu,hv,he⟩|⟨u,v,hu,hv,_⟩|⟨hu,hv⟩ <;>
      simp only [middle_val] at hu hv
    · omega
    · have hxu : x=u := Fin.ext (by omega)
      have hyv : y=v := Fin.ext (by omega)
      simpa [hxu,hyv] using he
    all_goals omega
  · exact fun h => Or.inl (Or.inl (Or.inr (map_adj_apply.mpr h)))

lemma comap_right (hs : a+b+c=n) (A : Tree a) (B : Tree b) (C : Tree c) :
    (glue hs A.1 B.1 C.1).comap (right hs) = C.1 := by
  apply eq_of_adj_lt
  intro x y hxy
  rw [comap_adj]
  constructor
  · intro h
    have hxy' : right hs x < right hs y := by change a+b+1+x.val < a+b+1+y.val; omega
    rcases glue_cases hs A B C hxy' h with ⟨u,v,hu,hv,_⟩|⟨u,v,hu,hv,_⟩|⟨u,v,hu,hv,he⟩|⟨hu,hv⟩ <;>
      simp only [right_val] at hu hv
    · omega
    · omega
    · have hxu : x=u := Fin.ext (by omega)
      have hyv : y=v := Fin.ext (by omega)
      simpa [hxu,hyv] using he
    · omega
  · exact fun h => Or.inl (Or.inr (map_adj_apply.mpr h))

end A054727H2

end

section

namespace A054727H2
open SimpleGraph OMA.S_oeis_a054727

abbrev Branches (n : ℕ) := (p : ↥(Finset.HasAntidiagonal.antidiagonal n)) ×
  (q : ↥(Finset.HasAntidiagonal.antidiagonal p.val.1)) × Tree q.val.1 × Tree q.val.2 × Tree p.val.2

def pack {n a b c : ℕ} (hs : a+b+c=n) (A : Tree a) (B : Tree b) (C : Tree c) : Branches n :=
  ⟨⟨(a+b,c),Finset.HasAntidiagonal.mem_antidiagonal.mpr hs⟩,⟨(a,b),Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl⟩,A,B,C⟩

lemma pack_all {n : ℕ} (x : Branches n) : ∃ (a b c : ℕ) (hs : a+b+c=n) (A : Tree a) (B : Tree b) (C : Tree c),
    x = pack hs A B C := by
  rcases x with ⟨⟨⟨ab,c⟩,hp⟩,⟨⟨a,b⟩,hq⟩,A,B,C⟩
  obtain rfl : a+b=ab := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
  exact ⟨a,b,c,Finset.HasAntidiagonal.mem_antidiagonal.mp hp,A,B,C,rfl⟩

def assemble {n : ℕ} (x : Branches n) : Tree (n+1) := by
  rcases x with ⟨⟨⟨ab,c⟩,hp⟩,⟨⟨a,b⟩,hq⟩,A,B,C⟩
  have hab : a+b=ab := Finset.HasAntidiagonal.mem_antidiagonal.mp hq
  have hn : ab+c=n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hs : a+b+c=n := by omega
  exact ⟨glue hs A.1 B.1 C.1,glue_tree hs A B C,glue_nonCrossing hs A B C⟩

lemma assemble_injective (n : ℕ) : Function.Injective (@assemble n) := by
  intro x y hxy
  obtain ⟨a,b,c,hs,A,B,C,rfl⟩ := pack_all x
  obtain ⟨a',b',c',ht,D,E,F,rfl⟩ := pack_all y
  have hg : glue hs A.1 B.1 C.1 = glue ht D.1 E.1 F.1 := congrArg Subtype.val hxy
  obtain ⟨rfl,rfl,rfl⟩ := sizes_eq hs ht A B C D E F hg
  have ha : A=D := Subtype.ext (by simpa only [comap_left] using congrArg (·.comap (left hs)) hg)
  have hb : B=E := Subtype.ext (by simpa only [comap_middle] using congrArg (·.comap (middle hs)) hg)
  have hc : C=F := Subtype.ext (by simpa only [comap_right] using congrArg (·.comap (right hs)) hg)
  subst D; subst E; subst F; rfl

noncomputable def splitEquiv (cut : ∀ (n : ℕ) (G : Tree (n+1)),
    ∃ (a b c : ℕ) (hs : a+b+c=n) (A : Tree a) (B : Tree b) (C : Tree c), G.1 = glue hs A.1 B.1 C.1)
    (n : ℕ) : Tree (n+1) ≃ Branches n := by
  apply Equiv.symm
  apply Equiv.ofBijective assemble
  refine ⟨assemble_injective _, fun G => ?_⟩
  obtain ⟨a,b,c,hs,A,B,C,hg⟩ := cut n G
  exact ⟨pack hs A B C, Subtype.ext hg.symm⟩

end A054727H2

end

section

namespace A054727H2
open SimpleGraph OMA.S_oeis_a054727
variable {n a b c : ℕ}

def projL (hs : a+b+c=n) (v : Fin (n+2)) : Fin (a+1) :=
  if h : v.val ≤ a then ⟨v.val,by omega⟩ else 0
def projM (hs : a+b+c=n) (v : Fin (n+2)) : Fin (b+1) :=
  if h : a+1 ≤ v.val ∧ v.val ≤ a+b+1 then ⟨v.val-(a+1),by omega⟩ else Fin.last b
def projR (hs : a+b+c=n) (v : Fin (n+2)) : Fin (c+1) :=
  ⟨v.val-(a+b+1),by omega⟩

lemma projL_l (hs : a+b+c=n) (u : Fin (a+1)) : projL hs (left hs u) = u := by
  apply Fin.ext; simp [projL,left,shift,show u.val ≤ a by omega]
lemma projL_m (hs : a+b+c=n) (u : Fin (b+1)) : projL hs (middle hs u) = 0 := by
  unfold projL
  rw [dif_neg (by change ¬a+1+u.val≤a; omega)]
lemma projL_r (hs : a+b+c=n) (u : Fin (c+1)) : projL hs (right hs u) = 0 := by
  unfold projL
  rw [dif_neg (by change ¬a+b+1+u.val≤a; omega)]
lemma projM_l (hs : a+b+c=n) (u : Fin (a+1)) : projM hs (left hs u) = Fin.last b := by
  simp [projM,left,shift,show ¬a+1≤u.val by omega]
lemma projM_m (hs : a+b+c=n) (u : Fin (b+1)) : projM hs (middle hs u) = u := by
  unfold projM
  rw [dif_pos (by change a+1≤a+1+u.val ∧ a+1+u.val≤a+b+1; omega)]
  apply Fin.ext; change a+1+u.val-(a+1)=u.val; omega
lemma projM_r (hs : a+b+c=n) (u : Fin (c+1)) : projM hs (right hs u) = Fin.last b := by
  unfold projM
  by_cases h : a+1≤(right hs u).val ∧ (right hs u).val≤a+b+1
  · rw [dif_pos h]
    apply Fin.ext
    change a+b+1+u.val-(a+1)=b
    change a+1≤a+b+1+u.val ∧ a+b+1+u.val≤a+b+1 at h
    omega
  · rw [dif_neg h]
lemma projR_l (hs : a+b+c=n) (u : Fin (a+1)) : projR hs (left hs u) = 0 := by
  apply Fin.ext; change 0+u.val-(a+b+1)=0; omega
lemma projR_m (hs : a+b+c=n) (u : Fin (b+1)) : projR hs (middle hs u) = 0 := by
  apply Fin.ext; change a+1+u.val-(a+b+1)=0; omega
lemma projR_r (hs : a+b+c=n) (u : Fin (c+1)) : projR hs (right hs u) = u := by
  apply Fin.ext; change a+b+1+u.val-(a+b+1)=u.val; omega

lemma connected_of_retract {U V : Type*} {G : SimpleGraph U} {H : SimpleGraph V}
    (hc : G.Connected) (f : U → V) (g : V → U) (hg : ∀ v, f (g v) = v)
    (weak : ∀ {u v}, G.Adj u v → f u = f v ∨ H.Adj (f u) (f v)) : H.Connected := by
  have down {u v} (p : G.Walk u v) : H.Reachable (f u) (f v) := by
    induction p with
    | nil => exact .rfl
    | cons e _ ih =>
      obtain he|he := weak e
      · simpa only [he] using ih
      · exact he.reachable.trans ih
  haveI := hc.nonempty.map f
  refine ⟨fun u v => ?_⟩
  obtain ⟨p⟩ := hc (g u) (g v)
  simpa only [hg] using down p

lemma retract_glue_conn (hs : a+b+c=n) (A : SimpleGraph (Fin (a+1))) (B : SimpleGraph (Fin (b+1)))
    (C : SimpleGraph (Fin (c+1))) (hc : (glue hs A B C).Connected) :
    A.Connected ∧ B.Connected ∧ C.Connected := by
  have hp : right hs 0 = pivot hs := Fin.ext (by change a+b+1+0=a+b+1; omega)
  have hz : left hs 0 = 0 := Fin.ext (by simp [left,shift])
  refine ⟨connected_of_retract hc (projL hs) (left hs) (projL_l hs) ?_,
    connected_of_retract hc (projM hs) (middle hs) (projM_m hs) ?_,
    connected_of_retract hc (projR hs) (right hs) (projR_r hs) ?_⟩ <;>
    rintro u v he <;>
    simp only [glue,sup_adj,map_adj,edge_adj] at he <;>
    rcases he with ((⟨u',v',h,rfl,rfl⟩|⟨u',v',h,rfl,rfl⟩)|⟨u',v',h,rfl,rfl⟩)|⟨(⟨rfl,rfl⟩|⟨rfl,rfl⟩),_⟩
  all_goals first
    | simpa only [projL_l,projL_m,projL_r,projM_l,projM_m,projM_r,projR_l,projR_m,projR_r,true_or] using Or.inr h
    | simp only [projL_l,projL_m,projL_r,projM_l,projM_m,projM_r,projR_l,projR_m,projR_r,true_or]
    | rw [←hp,←hz]; simp [projL_l,projL_r,projM_l,projM_r,projR_l,projR_r]

end A054727H2

end

section

namespace A054727H2
open SimpleGraph OMA.S_oeis_a054727
variable {n a b c : ℕ}

lemma nonCrossing_comap {N m : ℕ} {G : SimpleGraph (Fin N)}
    (hnc : NonCrossing G) (e : Fin m ↪ Fin N) (hs : StrictMono e) : NonCrossing (G.comap e) := by
  rintro u v p q huv hpq a₁ a₂ (⟨h,i,j⟩|⟨h,i,j⟩)
  · exact hnc _ _ _ _ (hs huv) (hs hpq) a₁ a₂ (.inl ⟨hs h,hs i,hs j⟩)
  · exact hnc _ _ _ _ (hs huv) (hs hpq) a₁ a₂ (.inr ⟨hs h,hs i,hs j⟩)

lemma shift_mono {m N s : ℕ} (h : s+m≤N) : StrictMono (shift s h) := by
  intro x y hx; change s+x.val<s+y.val; omega

lemma cut_trees (G : Tree (n+1)) (hs : a+b+c=n)
    (he : G.1 = glue hs (G.1.comap (left hs)) (G.1.comap (middle hs)) (G.1.comap (right hs))) :
    ∃ (A : Tree a) (B : Tree b) (C : Tree c), G.1 = glue hs A.1 B.1 C.1 := by
  have hc := retract_glue_conn hs _ _ _ (he ▸ G.2.1.connected)
  let mkTree {m s : ℕ} (h : s+(m+1)≤n+2) (hc : (G.1.comap (shift s h)).Connected) : Tree m :=
    ⟨G.1.comap (shift s h), ⟨hc,G.2.1.isAcyclic.of_comap _⟩,
      nonCrossing_comap G.2.2 _ (shift_mono h)⟩
  exact ⟨mkTree (s:=0) (by omega) hc.1,mkTree (s:=a+1) (by omega) hc.2.1,
    mkTree (s:=a+b+1) (by omega) hc.2.2,he⟩

/-- Glue the three restrictions once each original edge is located in a block or is the bridge. -/
lemma rawCut_of_edges (G : SimpleGraph (Fin (n+2))) (hs : a+b+c=n)
    (hp : G.Adj 0 (pivot hs))
    (he : ∀ {u v}, u<v → G.Adj u v →
      v.val ≤ a ∨ (a+1 ≤ u.val ∧ v.val ≤ a+b+1) ∨ a+b+1 ≤ u.val ∨ (u=0 ∧ v=pivot hs)) :
    G = glue hs (G.comap (left hs)) (G.comap (middle hs)) (G.comap (right hs)) := by
  let F := glue hs (G.comap (left hs)) (G.comap (middle hs)) (G.comap (right hs))
  have ordered {u v} (huv : u<v) (h : G.Adj u v) : F.Adj u v := by
    rcases he huv h with hL|⟨hM,hM'⟩|hR|⟨rfl,rfl⟩
    · let x : Fin (a+1) := ⟨u.val,by omega⟩
      let y : Fin (a+1) := ⟨v.val,by omega⟩
      have hx : left hs x = u := Fin.ext (Nat.zero_add _)
      have hy : left hs y = v := Fin.ext (Nat.zero_add _)
      exact Or.inl (Or.inl (Or.inl ((map_adj ..).2 ⟨x,y,comap_adj.mpr (by simpa only [hx,hy] using h),hx,hy⟩)))
    · let x : Fin (b+1) := ⟨u.val-(a+1),by omega⟩
      let y : Fin (b+1) := ⟨v.val-(a+1),by omega⟩
      have hx : middle hs x = u := Fin.ext (by change a+1+(u.val-(a+1))=u.val; omega)
      have hy : middle hs y = v := Fin.ext (by change a+1+(v.val-(a+1))=v.val; omega)
      exact Or.inl (Or.inl (Or.inr ((map_adj ..).2 ⟨x,y,comap_adj.mpr (by simpa only [hx,hy] using h),hx,hy⟩)))
    · let x : Fin (c+1) := ⟨u.val-(a+b+1),by omega⟩
      let y : Fin (c+1) := ⟨v.val-(a+b+1),by omega⟩
      have hx : right hs x = u := Fin.ext (by change a+b+1+(u.val-(a+b+1))=u.val; omega)
      have hy : right hs y = v := Fin.ext (by change a+b+1+(v.val-(a+b+1))=v.val; omega)
      exact Or.inl (Or.inr ((map_adj ..).2 ⟨x,y,comap_adj.mpr (by simpa only [hx,hy] using h),hx,hy⟩))
    · exact Or.inr ((edge_adj ..).2 ⟨Or.inl ⟨rfl,rfl⟩,hp.ne⟩)
  ext u v
  constructor
  · intro h
    obtain huv|hvu := lt_or_gt_of_ne h.ne
    · exact ordered huv h
    · exact (ordered hvu h.symm).symm
  · intro h
    simp only [glue,sup_adj,map_adj,comap_adj,edge_adj] at h
    rcases h with ((⟨x,y,he,rfl,rfl⟩|⟨x,y,he,rfl,rfl⟩)|⟨x,y,he,rfl,rfl⟩)|⟨(⟨rfl,rfl⟩|⟨rfl,rfl⟩),_⟩
    all_goals first | exact he | exact hp | exact hp.symm

end A054727H2

end

section

open PowerSeries OMA.S_oeis_a054727

namespace A054727TreeBijection

/-- The size parameter is the number of edges, so a singleton has size zero. -/
abbrev Tree (n : ℕ) := {G : SimpleGraph (Fin (n+1)) // G.IsTree ∧ NonCrossing G}

/-- Triples indexed by the sizes of the left, middle, and right trees. -/
abbrev Branches (n : ℕ) := (p : ↥(Finset.HasAntidiagonal.antidiagonal n)) ×
  (q : ↥(Finset.HasAntidiagonal.antidiagonal p.val.1)) × Tree q.val.1 × Tree q.val.2 × Tree p.val.2

lemma singleton_count : Nat.card (Tree 0) = 1 := by
  letI : Subsingleton (Fin (0+1)) := inferInstanceAs (Subsingleton (Fin 1))
  letI : Nonempty (Tree 0) := ⟨⟨⊥, SimpleGraph.IsTree.of_subsingleton,
    by intro a b c d hab; exact (hab.ne (Subsingleton.elim a b)).elim⟩⟩
  exact Nat.card_unique

lemma tree_series_of_split
    (split : ∀ n, Tree (n+1) ≃ Branches n) :
    let T : PowerSeries ℚ := X * mk (fun n =>
      ({G : SimpleGraph (Fin (n+1)) | G.IsTree ∧ NonCrossing G}.ncard : ℚ))
    T ^ 3 - X * T + X ^ 2 = 0 := by
  classical
  letI (n : ℕ) : Fintype (Tree n) := Fintype.ofFinite _
  let B : PowerSeries ℚ := mk fun n => (Nat.card (Tree n) : ℚ)
  have hc : B = 1 + X * B ^ 3 := by
    ext n
    cases n with
    | zero => simpa [B, coeff_zero_eq_constantCoeff_apply] using singleton_count
    | succ n =>
      rw [map_add, coeff_one, if_neg (Nat.succ_ne_zero n), zero_add, coeff_succ_X_mul,
        pow_succ, coeff_mul]
      simp_rw [sq, coeff_mul, B, coeff_mk]
      have h := Fintype.card_congr (split n)
      simp only [Branches, Fintype.card_sigma, Fintype.card_prod] at h
      let t := fun m => Fintype.card (Tree m)
      let diag := Finset.HasAntidiagonal.antidiagonal (A := ℕ)
      have inner (p : ℕ × ℕ) := Finset.sum_coe_sort (diag p.1)
        (fun q : ℕ × ℕ => t q.1 * (t q.2 * t p.2))
      have outer := Finset.sum_coe_sort (diag n)
        (fun p : ℕ × ℕ => ∑ q ∈ diag p.1, t q.1 * (t q.2 * t p.2))
      change t (n+1) = ∑ p : ↥(diag n), ∑ q : ↥(diag p.val.1),
        t q.val.1 * (t q.val.2 * t p.val.2) at h
      simp_rw [inner] at h
      rw [outer] at h
      simp only [← mul_assoc] at h
      simp_rw [Finset.sum_mul, Nat.card_eq_fintype_card]
      exact_mod_cast h
  change (X * B)^3 - X*(X*B) + X^2 = 0
  linear_combination -(X ^ 2) * hc

end A054727TreeBijection

end

section

namespace A054727H2
open SimpleGraph PowerSeries OMA.S_oeis_a054727

theorem tree_series_of_cut_edges (cuts : ∀ (n : ℕ) (G : Tree (n+1)),
    ∃ (a b c : ℕ) (hs : a+b+c=n), G.1.Adj 0 (pivot hs) ∧
      ∀ {u v}, u<v → G.1.Adj u v →
        v.val≤a ∨ (a+1≤u.val ∧ v.val≤a+b+1) ∨ a+b+1≤u.val ∨ (u=0 ∧ v=pivot hs)) :
    let T : PowerSeries ℚ := X * mk (fun n =>
      ({G : SimpleGraph (Fin (n+1)) | G.IsTree ∧ NonCrossing G}.ncard : ℚ))
    T^3-X*T+X^2=0 := by
  apply A054727TreeBijection.tree_series_of_split
  intro size
  apply splitEquiv _ size
  intro n G
  obtain ⟨a,b,c,hs,hp,he⟩ := cuts n G
  obtain ⟨A,B,C,hG⟩ := cut_trees G hs (rawCut_of_edges G.1 hs hp he)
  exact ⟨a,b,c,hs,A,B,C,hG⟩

end A054727H2

end

section

namespace A054727H2
open SimpleGraph OMA.S_oeis_a054727

lemma bridge_data (n : ℕ) (G : Tree (n+1)) : ∃ k : Fin (n+2), G.val.Adj 0 k ∧
    (∀ w, G.val.Adj 0 w → w ≤ k) ∧
    ¬ (G.val.deleteEdges {s(0,k)}).Reachable 0 k ∧
    ∀ w, (G.val.deleteEdges {s(0,k)}).Reachable 0 w ∨
      (G.val.deleteEdges {s(0,k)}).Reachable k w := by
  classical
  let S := Finset.univ.filter (G.val.Adj 0)
  have mem (w : Fin (n+2)) : w ∈ S ↔ G.val.Adj 0 w := by simp [S]
  obtain ⟨w,hw⟩ := G.property.1.connected.preconnected.exists_adj_of_nontrivial 0
  have hn : S.Nonempty := ⟨w,(mem w).mpr hw⟩
  let k := S.max' hn
  have hk : G.val.Adj 0 k := (mem k).mp (S.max'_mem hn)
  refine ⟨k,hk,fun v h => S.le_max' v ((mem v).mpr h),
    (isAcyclic_iff_forall_adj_isBridge.mp G.property.1.isAcyclic hk),?_⟩
  let R := G.val.deleteEdges {s(0,k)}
  intro v
  obtain h := (G.val.reachable_iff_reflTransGen 0 v).mp (G.property.1.connected.preconnected 0 v)
  change R.Reachable 0 v ∨ R.Reachable k v
  induction h with
  | refl => exact .inl .rfl
  | @tail p q path pq ih =>
    by_cases he : s(p,q) = s(0,k)
    · rcases Sym2.eq_iff.mp he with ⟨_,rfl⟩ | ⟨_,rfl⟩
      · exact .inr .rfl
      · exact .inl .rfl
    · have hR : R.Adj p q := deleteEdges_adj.mpr ⟨pq,fun h => he (Set.mem_singleton_iff.mp h)⟩
      exact ih.imp (fun h => h.trans hR.reachable) (fun h => h.trans hR.reachable)

end A054727H2

end

section

namespace A054727H2
open PowerSeries OMA.S_oeis_a054727

theorem tree_series :
    let T : PowerSeries ℚ := X * mk (fun n =>
      ({G : SimpleGraph (Fin (n+1)) | G.IsTree ∧ NonCrossing G}.ncard : ℚ))
    T^3-X*T+X^2=0 := by
  apply tree_series_of_cut_edges
  intro n G
  obtain ⟨k,hk,hm,ha,hcov⟩ := bridge_data n G
  obtain ⟨a,hak,hseg⟩ := root_component_prefix G.val _ k G.property.2
    (SimpleGraph.deleteEdges_le _) hk hm ha hcov
  exact sizes_of_prefix G k hk a hak hseg

end A054727H2

end

namespace OMA.A054727Recurrence

lemma jet_identity {R : Type*} [CommRing R]
    (p b c d e f g h y u v w r0 r1 r2 r3 k : R)
    (h1 : p * u + b = 0)
    (h2 : p * v + c * u ^ 2 + 2 * d * u + e = 0)
    (h3 : p * w + 3 * (c * u + d) * v + f * u ^ 3 + 3 * g * u ^ 2 + 3 * h * u = 0) :
    p ^ 5 * (r0 * y + r1 * u + r2 * v + r3 * w + k) =
      (r0 * y + k) * p ^ 5 - r1 * b * p ^ 4 -
      r2 * p ^ 2 * (c * b ^ 2 - 2 * d * b * p + e * p ^ 2) +
      r3 * (3 * (d * p - c * b) * (c * b ^ 2 - 2 * d * b * p + e * p ^ 2) +
        f * b ^ 3 * p - 3 * g * b ^ 2 * p ^ 2 + 3 * h * b * p ^ 3) := by
  let B := c * b ^ 2 - 2 * d * b * p + e * p ^ 2
  have hv : p ^ 3 * v + B = 0 := by
    dsimp [B]
    linear_combination p ^ 2 * h2 - (c * (p * u - b) + 2 * d * p) * h1
  have hw : p ^ 5 * w -
      (3 * (d * p - c * b) * B + f * b ^ 3 * p - 3 * g * b ^ 2 * p ^ 2 +
        3 * h * b * p ^ 3) = 0 := by
    linear_combination p ^ 4 * h3 - 3 * p * (c * u + d) * hv -
      (f * p * (p ^ 2 * u ^ 2 - p * u * b + b ^ 2) +
        3 * g * p ^ 2 * (p * u - b) + 3 * h * p ^ 3 - 3 * c * B) * h1
  change p ^ 5 * _ = (r0 * y + k) * p ^ 5 - r1 * b * p ^ 4 - r2 * p ^ 2 * B +
    r3 * (3 * (d * p - c * b) * B + f * b ^ 3 * p - 3 * g * b ^ 2 * p ^ 2 +
      3 * h * b * p ^ 3)
  linear_combination r1 * p ^ 4 * h1 + r2 * p ^ 2 * hv + r3 * hw

open PowerSeries

set_option maxHeartbeats 2000000 in
lemma cubic_ode (Y : PowerSeries ℚ)
    (h0 : X * Y ^ 3 + (X ^ 2 - X) * Y ^ 2 + (2 * X - 1) * Y + 1 = 0) :
    (1050 * X ^ 2 - 140 * X - 126) * Y +
      (-1050 * X ^ 3 + 1190 * X ^ 2 + 2026 * X + 36) * derivative ℚ Y +
      (-1265 * X ^ 4 + 1580 * X ^ 3 + 4544 * X ^ 2 - 346 * X) *
        derivative ℚ (derivative ℚ Y) +
      (-37 * X ^ 2 * (5 * X ^ 3 - 8 * X ^ 2 - 32 * X + 4)) *
        derivative ℚ (derivative ℚ (derivative ℚ Y)) + 54 + 680 * X = 0 := by
  let p := 3 * X * Y ^ 2 + 2 * (X ^ 2 - X) * Y + 2 * X - 1
  let b := Y ^ 3 + (2 * X - 1) * Y ^ 2 + 2 * Y
  let c := 6 * X * Y + 2 * (X ^ 2 - X)
  let d := 3 * Y ^ 2 + 2 * (2 * X - 1) * Y + 2
  let e := 2 * Y ^ 2
  let f : PowerSeries ℚ := 6 * X
  let g := 6 * Y + 2 * (2 * X - 1)
  let h := 4 * Y
  have hd2 : derivative ℚ (2 : PowerSeries ℚ) = 0 := Derivation.map_natCast _ 2
  have hd3 : derivative ℚ (3 : PowerSeries ℚ) = 0 := Derivation.map_natCast _ 3
  have hd6 : derivative ℚ (6 : PowerSeries ℚ) = 0 := Derivation.map_natCast _ 6
  have h1 : p * derivative ℚ Y + b = 0 := by
    have hh := congrArg (derivative ℚ) h0
    simp only [map_add, map_sub, map_zero, Derivation.leibniz, derivative_pow,
      derivative_X, Derivation.map_one_eq_zero, hd2, smul_eq_mul] at hh
    dsimp [p, b]
    convert hh using 1; ring
  have h2 : p * derivative ℚ (derivative ℚ Y) + c * (derivative ℚ Y) ^ 2 +
      2 * d * derivative ℚ Y + e = 0 := by
    have hh := congrArg (derivative ℚ) h1
    dsimp [p, b] at hh
    simp only [map_add, map_sub, map_zero, Derivation.leibniz, derivative_pow,
      derivative_X, Derivation.map_one_eq_zero, hd2, hd3, smul_eq_mul] at hh
    dsimp [p, c, d, e]
    convert hh using 1; ring
  have h3 : p * derivative ℚ (derivative ℚ (derivative ℚ Y)) +
      3 * (c * derivative ℚ Y + d) * derivative ℚ (derivative ℚ Y) +
      f * (derivative ℚ Y) ^ 3 + 3 * g * (derivative ℚ Y) ^ 2 + 3 * h * derivative ℚ Y = 0 := by
    have hh := congrArg (derivative ℚ) h2
    dsimp [p, c, d, e] at hh
    simp only [map_add, map_sub, map_zero, Derivation.leibniz, derivative_pow,
      derivative_X, Derivation.map_one_eq_zero, hd2, hd3, hd6, smul_eq_mul] at hh
    dsimp [p, c, d, f, g, h]
    convert hh using 1; ring
  have hp : p ≠ 0 := by
    intro hz
    have hz' := congrArg constantCoeff hz
    norm_num [p] at hz'
  apply (mul_eq_zero.mp (show p ^ 5 * _ = 0 from ?_)).resolve_left (pow_ne_zero _ hp)
  rw [add_assoc _ (54 : PowerSeries ℚ) (680 * X)]
  rw [jet_identity p b c d e f g h Y _ _ _ _ _ _ _ _ h1 h2 h3]
  dsimp [p, b, c, d, e, f, g, h]
  linear_combination (2 * (10880 * X ^ 10 * Y ^ 4 + 75200 * X ^ 9 * Y ^ 5 - 48096 * X ^ 9 * Y ^ 4 +
    43520 * X ^ 9 * Y ^ 3 + 272880 * X ^ 8 * Y ^ 6 - 270032 * X ^ 8 * Y ^ 5 + 310672 * X ^ 8 * Y ^ 4
    - 170624 * X ^ 8 * Y ^ 3 + 65280 * X ^ 8 * Y ^ 2 + 333600 * X ^ 7 * Y ^ 7 - 613476 * X ^ 7 * Y ^
    6 + 1028800 * X ^ 7 * Y ^ 5 - 798130 * X ^ 7 * Y ^ 4 + 481536 * X ^ 7 * Y ^ 3 - 223296 * X ^ 7 *
    Y ^ 2 + 43520 * X ^ 7 * Y + 125100 * X ^ 6 * Y ^ 8 - 379416 * X ^ 6 * Y ^ 7 + 842190 * X ^ 6 * Y
    ^ 6 - 1322950 * X ^ 6 * Y ^ 5 + 1365194 * X ^ 6 * Y ^ 4 - 855304 * X ^ 6 * Y ^ 3 + 356896 * X ^
    6 * Y ^ 2 - 127104 * X ^ 6 * Y + 10880 * X ^ 6 - 17181 * X ^ 5 * Y ^ 8 + 42696 * X ^ 5 * Y ^ 7 -
    299772 * X ^ 5 * Y ^ 6 + 602480 * X ^ 5 * Y ^ 5 - 920719 * X ^ 5 * Y ^ 4 + 828228 * X ^ 5 * Y ^
    3 - 421226 * X ^ 5 * Y ^ 2 + 135872 * X ^ 5 * Y - 26336 * X ^ 5 - 1170 * X ^ 4 * Y ^ 8 - 864 * X
    ^ 4 * Y ^ 7 + 20823 * X ^ 4 * Y ^ 6 - 53587 * X ^ 4 * Y ^ 5 + 190603 * X ^ 4 * Y ^ 4 - 269032 *
    X ^ 4 * Y ^ 3 + 254147 * X ^ 4 * Y ^ 2 - 105460 * X ^ 4 * Y + 25040 * X ^ 4 - 1494 * X ^ 3 * Y ^
    8 + 3984 * X ^ 3 * Y ^ 7 - 5673 * X ^ 3 * Y ^ 6 + 10136 * X ^ 3 * Y ^ 5 - 18105 * X ^ 3 * Y ^ 4
    + 20420 * X ^ 3 * Y ^ 3 - 58417 * X ^ 3 * Y ^ 2 + 48708 * X ^ 3 * Y - 11440 * X ^ 3 + 2712 * X ^
    2 * Y ^ 6 - 4428 * X ^ 2 * Y ^ 5 + 5555 * X ^ 2 * Y ^ 4 - 7418 * X ^ 2 * Y ^ 3 + 4659 * X ^ 2 *
    Y ^ 2 - 5989 * X ^ 2 * Y + 2320 * X ^ 2 - 1236 * X * Y ^ 4 + 836 * X * Y ^ 3 - 1377 * X * Y ^ 2
    - 1200 * X * Y - 70 * X + 18 * Y ^ 2 - 27)) * h0

lemma coeff_euler (Y : PowerSeries ℚ) (n : ℕ) :
    coeff n (X * derivative ℚ Y) = n * coeff n Y := by
  cases n with
  | zero => simp
  | succ n => rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

set_option maxHeartbeats 2000000 in
lemma cubic_euler (Y : PowerSeries ℚ)
    (h0 : X * Y ^ 3 + (X ^ 2 - X) * Y ^ 2 + (2 * X - 1) * Y + 1 = 0) :
    let F := 1 + X * Y;
    let E := fun Z : PowerSeries ℚ => X * derivative ℚ Z
    (-148 * E (E (E F)) + 542 * E (E F) - 554 * E F + 160 * F) +
    X ^ 1 * (1184 * E (E (E F)) - 2560 * E (E F) + 1418 * E F - 168 * F) +
    X ^ 2 * (296 * E (E (E F)) - 196 * E (E F) - 294 * E F + 54 * F) +
    X ^ 3 * (-185 * E (E (E F)) - 155 * E (E F) + 710 * E F + 680 * F) =
      160 - 168 * X := by
  have hh := cubic_ode Y h0
  dsimp
  simp only [map_add, Derivation.leibniz, derivative_X,
    Derivation.map_one_eq_zero, smul_eq_mul, map_zero]
  linear_combination X ^ 2 * hh

lemma coeff_num_mul (k : ℕ) [k.AtLeastTwo] (Y : PowerSeries ℚ) (n : ℕ) :
    coeff n ((ofNat(k) : PowerSeries ℚ) * Y) = ofNat(k) * coeff n Y :=
  coeff_C_mul n Y (ofNat(k) : ℚ)

lemma coeff_num (k n : ℕ) [k.AtLeastTwo] :
    coeff n (ofNat(k) : PowerSeries ℚ) = if n = 0 then ofNat(k) else 0 :=
  coeff_C n (ofNat(k) : ℚ)

set_option maxHeartbeats 2000000 in
lemma cubic_recurrence (Y : PowerSeries ℚ)
    (h0 : X * Y ^ 3 + (X ^ 2 - X) * Y ^ 2 + (2 * X - 1) * Y + 1 = 0)
    (n : ℕ) (hn : 4 ≤ n) :
    let F := 1 + X * Y;
    -2 * (37 * (n : ℚ) - 80) * ((n : ℚ) - 1) * (2 * (n : ℚ) - 1) * coeff n F +
    2 * (592 * (n : ℚ) ^ 3 - 3056 * (n : ℚ) ^ 2 + 5045 * (n : ℚ) - 2665) * coeff (n - 1) F +
    2 * (148 * (n : ℚ) ^ 3 - 986 * (n : ℚ) ^ 2 + 2021 * (n : ℚ) - 1255) * coeff (n - 2) F -
    5 * ((n : ℚ) - 5) * ((n : ℚ) - 2) * (37 * (n : ℚ) - 43) * coeff (n - 3) F = 0 := by
  have hh := congrArg (coeff n) (cubic_euler Y h0)
  dsimp only at hh ⊢
  generalize (1 + X * Y) = F at hh ⊢
  simp only [map_add, map_sub, neg_mul, map_neg, coeff_X_pow_mul', coeff_num_mul] at hh
  simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, if_true] at hh
  simp only [coeff_euler, coeff_num, coeff_X, show n ≠ 0 by omega, show n ≠ 1 by omega,
    if_false, mul_zero, sub_zero] at hh
  simp only [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega),
    Nat.cast_sub (show 3 ≤ n by omega)] at hh
  linear_combination hh

lemma forest_cubic (Y T : PowerSeries ℚ)
    (hT : T ^ 3 - X * T + X ^ 2 = 0)
    (hF : 1 + X * Y = 1 + T.subst (X * (1 + X * Y))) :
    X * Y ^ 3 + (X ^ 2 - X) * Y ^ 2 + (2 * X - 1) * Y + 1 = 0 := by
  have hs : HasSubst (X * (1 + X * Y)) :=
    HasSubst.of_constantCoeff_zero' (by simp)
  have ht := congrArg (fun Z : PowerSeries ℚ => Z.subst (X * (1 + X * Y))) hT
  have he : T.subst (X * (1 + X * Y)) = X * Y := by linear_combination -hF
  simp only [subst_add hs, subst_sub hs, subst_mul hs, subst_pow hs, subst_X hs,
    ← coe_substAlgHom hs, map_zero] at ht
  rw [coe_substAlgHom] at ht
  rw [he] at ht
  apply X_pow_mul_cancel (k := 2)
  linear_combination ht

open OMA.S_oeis_a054727

-- Decomposition by the component of the first vertex.
def H1 : Prop :=
  let F : PowerSeries ℚ := 1 + X * mk (fun n => (a (n + 1) : ℚ))
  let T : PowerSeries ℚ := X * mk (fun n =>
    ({G : SimpleGraph (Fin (n + 1)) | G.IsTree ∧ NonCrossing G}.ncard : ℚ))
  F = 1 + T.subst (X * F)

-- Butterfly decomposition of a non-crossing tree rooted at the first vertex.
def H2 : Prop :=
  let T : PowerSeries ℚ := X * mk (fun n =>
    ({G : SimpleGraph (Fin (n + 1)) | G.IsTree ∧ NonCrossing G}.ncard : ℚ))
  T ^ 3 - X * T + X ^ 2 = 0

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a054727.main := by
  intro h1 h2 n hn
  let Y : PowerSeries ℚ := mk (fun n => (a (n + 1) : ℚ))
  let T : PowerSeries ℚ := X * mk (fun n =>
    ({G : SimpleGraph (Fin (n + 1)) | G.IsTree ∧ NonCrossing G}.ncard : ℚ))
  have hc := forest_cubic Y T h2 h1
  have hr := cubic_recurrence Y hc n hn
  have hcoeff (m : ℕ) (hm : 0 < m) : coeff m (1 + X * Y) = (a m : ℚ) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    simp [Y, coeff_succ_X_mul]
  dsimp only at hr
  rw [hcoeff n (by omega), hcoeff (n - 1) (by omega), hcoeff (n - 2) (by omega),
    hcoeff (n - 3) (by omega)] at hr
  exact_mod_cast hr

end OMA.A054727Recurrence

theorem OMA.solution : type_of% @OMA.S_oeis_a054727.main :=
  OMA.A054727Recurrence.main OMA.H1Series.forest_series
    A054727H2.tree_series
