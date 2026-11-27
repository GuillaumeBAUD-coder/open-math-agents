import FormalConjectures.ErdosProblems.«593»
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Compactness
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.PowersetCard
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Order.TransfiniteIteration
import Mathlib.Order.WellFounded
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-
Samuil Petkov, Obligatory Triple Systems: An Alternative Proof and Lean Verification.
Source: https://github.com/SamPetkov/Erdos593/tree/70675e5ce5646718df4e6fd4f93c509ef3447a77
Copyright Samuil Petkov; original Lean licensed CC BY 4.0:
https://creativecommons.org/licenses/by/4.0/
Eric Li gave the first complete proof (https://arxiv.org/abs/2606.24882); the
classification and proof architecture are shared. Petkov credits GPT-5.6 Pro
and Aristotle for contributions to proof development, checking and formalisation.
Adapted to the pinned Mathlib, renamed the namespace, removed unused declarations,
inlined the required code and bridged it to formal-conjectures for Left to Solve.
Some port-local identifiers were shortened to fit the 512 KiB cap. The definitions behind OMA.answer and the bridge keep their original names.
-/
-- ARISTOTLE_TARGET B1
section
namespace P593
universe u v
structure TripleSystem (V : Type u) (E : Type v) where
  Inc : V → E → Prop
  edge_ncard : ∀ e, Set.ncard {x | Inc x e} = 3
  simple : Function.Injective (fun e => {x | Inc x e})
namespace TripleSystem
variable {V : Type u} {E : Type v} (F : TripleSystem V E)
def IsIsolated (x : V) : Prop :=
  ∀ e, ¬F.Inc x e
def Linear : Prop :=
  ∀ ⦃e f : E⦄ ⦃x y : V⦄, e ≠ f →
    F.Inc x e → F.Inc x f → F.Inc y e → F.Inc y f → x = y
def edgeSet (e : E) : Set V :=
  {x | F.Inc x e}
@[simp]
theorem Zb8 {x : V} {e : E} : x ∈ F.edgeSet e ↔ F.Inc x e :=
  Iff.rfl
theorem Zaa (e : E) : (F.edgeSet e).ncard = 3 :=
  F.edge_ncard e
theorem Z8n : Function.Injective F.edgeSet :=
  F.simple
theorem Z2u :
    F.Linear ↔ ∀ ⦃e f : E⦄, e ≠ f →
      (F.edgeSet e ∩ F.edgeSet f).Subsingleton := by
  constructor
  · intro h e f hef x hx y hy
    exact h hef hx.1 hx.2 hy.1 hy.2
  · intro h e f x y hef hxe hxf hye hyf
    exact h hef ⟨hxe, hxf⟩ ⟨hye, hyf⟩
end TripleSystem
end P593
end
section
namespace P593
universe u
namespace TripleSystem
namespace TriangleHost
abbrev Pair (κ : Type u) := Set.powersetCard κ 2
abbrev ZbI (κ : Type u) := Set.powersetCard κ 3
private def faces {κ : Type u} [DecidableEq κ] (t : ZbI κ) : Finset (Pair κ) :=
  (t.1.powersetCard 2).attach.map
    { toFun := fun s =>
        ⟨s.1, (Finset.mem_powersetCard.mp s.2).2⟩
      inj' := by
        intro a b hab
        apply Subtype.ext
        simpa using congrArg (fun p : Pair κ => p.1) hab }
private theorem Zat {κ : Type u} [DecidableEq κ]
    (t : ZbI κ) (p : Pair κ) :
    p ∈ faces t ↔ p.1 ⊆ t.1 := by
  constructor
  · intro hp
    rcases Finset.mem_map.mp hp with ⟨s, hs, hsp⟩
    rw [← hsp]
    exact (Finset.mem_powersetCard.mp s.2).1
  · intro hp
    let s : {s : Finset κ // s ∈ t.1.powersetCard 2} :=
      ⟨p.1, Finset.mem_powersetCard.mpr ⟨hp, p.2⟩⟩
    have hs : s ∈ (t.1.powersetCard 2).attach := Finset.mem_attach _ _
    apply Finset.mem_map.mpr
    refine ⟨s, hs, ?_⟩
    apply Subtype.ext
    rfl
private theorem Zbk {κ : Type u} [DecidableEq κ]
    (t : ZbI κ) : (faces t).card = 3 := by
  simp [faces, Finset.card_powersetCard]
private theorem Z6o {κ : Type u} [DecidableEq κ]
    (t : ZbI κ) {v : κ} (hv : v ∈ t.1) :
    ∃ p : Pair κ, v ∈ p.1 ∧ p.1 ⊆ t.1 := by
  rcases Finset.card_eq_three.mp t.2 with ⟨a, b, c, hab, hac, hbc, ht⟩
  rw [ht] at hv ⊢
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · refine ⟨⟨{v, b}, by simp [hab]⟩, ?_, ?_⟩ <;> simp
  · refine ⟨⟨{a, v}, by simp [hab]⟩, ?_, ?_⟩ <;> simp
  · refine ⟨⟨{a, v}, by simp [hac]⟩, ?_, ?_⟩ <;> simp
def system (κ : Type u) [DecidableEq κ] : TripleSystem (Pair κ) (ZbI κ) where
  Inc p t := p.1 ⊆ t.1
  edge_ncard := by
    intro t
    change Set.ncard {p : Pair κ | p.1 ⊆ t.1} = 3
    rw [show {p : Pair κ | p.1 ⊆ t.1} = (faces t : Set (Pair κ)) by
      ext p
      exact (Zat t p).symm]
    simpa using Zbk t
  simple := by
    intro t u htu
    apply Subtype.ext
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      obtain ⟨p, hvp, hpt⟩ := Z6o t hv
      have hpu : p.1 ⊆ u.1 := (Set.ext_iff.mp htu p).mp hpt
      exact hpu hvp
    · have ht : t.1.card = 3 := t.2
      have hu : u.1.card = 3 := u.2
      omega
theorem linear (κ : Type u) [DecidableEq κ] : (system κ).Linear := by
  intro e f x y hef hxe hxf hye hyf
  change x.1 ⊆ e.1 at hxe
  change x.1 ⊆ f.1 at hxf
  change y.1 ⊆ e.1 at hye
  change y.1 ⊆ f.1 at hyf
  by_contra hxy
  apply hef
  apply Subtype.ext
  let z := x.1 ∪ y.1
  have hze : z ⊆ e.1 := Finset.union_subset hxe hye
  have hzf : z ⊆ f.1 := Finset.union_subset hxf hyf
  have hx : x.1.card = 2 := x.2
  have hy : y.1.card = 2 := y.2
  have he : e.1.card = 3 := e.2
  have hf : f.1.card = 3 := f.2
  have hzle : z.card ≤ 3 := by
    calc
      z.card ≤ e.1.card := Finset.card_le_card hze
      _ = 3 := he
  have hxle : 2 ≤ z.card := by
    calc
      2 = x.1.card := hx.symm
      _ ≤ z.card := Finset.card_le_card Finset.subset_union_left
  have hz : z.card = 3 := by
    by_contra hne
    have hzle_two : z.card ≤ 2 := by omega
    have hzx : z.card ≤ x.1.card := by omega
    have hzy : z.card ≤ y.1.card := by omega
    have hxz : x.1 = z := Finset.eq_of_subset_of_card_le Finset.subset_union_left hzx
    have hyz : y.1 = z := Finset.eq_of_subset_of_card_le Finset.subset_union_right hzy
    apply hxy
    apply Subtype.ext
    exact hxz.trans hyz.symm
  have hzeq : z = e.1 := by
    apply Finset.eq_of_subset_of_card_le hze
    omega
  have hzfq : z = f.1 := by
    apply Finset.eq_of_subset_of_card_le hzf
    omega
  exact hzeq.symm.trans hzfq
end TriangleHost
end TripleSystem
end P593
end
section
namespace P593
universe u v w x y z
namespace TripleSystem
structure Embedding {V : Type u} {E : Type v} {W : Type w} {D : Type x}
    (F : TripleSystem V E) (H : TripleSystem W D) where
  vertex : V ↪ W
  edge : E → D
  map_edge : ∀ e, vertex '' F.edgeSet e = H.edgeSet (edge e)
namespace Embedding
variable {V : Type u} {E : Type v} {W : Type w} {D : Type x}
variable {X : Type y} {A : Type z}
variable {F : TripleSystem V E} {H : TripleSystem W D} {K : TripleSystem X A}
def trans (f : F.Embedding H) (g : H.Embedding K) : F.Embedding K where
  vertex := f.vertex.trans g.vertex
  edge := g.edge ∘ f.edge
  map_edge := by
    intro e
    change (fun x => g.vertex (f.vertex x)) '' F.edgeSet e =
      K.edgeSet (g.edge (f.edge e))
    rw [← Set.image_image, f.map_edge, g.map_edge]
theorem Z9P (f : F.Embedding H) : Function.Injective f.edge := by
  intro e e' h
  apply F.Z8n
  apply Set.image_injective.mpr f.vertex.injective
  rw [f.map_edge, f.map_edge, h]
end Embedding
end TripleSystem
end P593
end
section
namespace P593
open scoped Cardinal
universe u v w
namespace TripleSystem
variable {V : Type u} {E : Type v} (F : TripleSystem V E)
def IsProperColoring {C : Type w} (c : V → C) : Prop :=
  ∀ e : E, ∃ x : V, F.Inc x e ∧ ∃ y : V, F.Inc y e ∧ c x ≠ c y
noncomputable def chromaticCardinal : Cardinal.{u} :=
  sInf {k : Cardinal.{u} | ∃ C : Type u, #C = k ∧
    ∃ c : V → C, F.IsProperColoring c}
def Appears {W : Type u} {D : Type v}
    (F : TripleSystem V E) (H : TripleSystem W D) : Prop :=
  Nonempty (F.Embedding H)
def IsTwoColorable : Prop :=
  ∃ c : V → Fin 2, F.IsProperColoring c
def IsObligatory : Prop :=
  ∀ (W : Type u) (D : Type v) [DecidableEq W]
    (H : TripleSystem W D), ℵ₀ < H.chromaticCardinal → F.Appears H
theorem Appears.trans {W : Type u} {D : Type v} {X : Type u} {A : Type v}
    {H : TripleSystem W D} {K : TripleSystem X A}
    (hFH : F.Appears H) (hHK : H.Appears K) : F.Appears K := by
  rcases hFH with ⟨f⟩
  rcases hHK with ⟨g⟩
  exact ⟨f.trans g⟩
end TripleSystem
end P593
end
section
namespace P593
universe u
namespace TripleSystem
namespace TriangleHost
def Z7S (κ : Type u) [DecidableEq κ] : Prop :=
  ∀ c : Pair κ → ℕ, ∃ t : ZbI κ,
    ∀ p q : Pair κ, p.1 ⊆ t.1 → q.1 ⊆ t.1 → c p = c q
theorem Z1d
    (κ : Type u) [DecidableEq κ]
    (hRamsey : Z7S κ) (c : Pair κ → ℕ) :
    ¬ (system κ).IsProperColoring c := by
  intro hc
  obtain ⟨t, ht⟩ := hRamsey c
  rcases hc t with ⟨p, hp, q, hq, hpq⟩
  exact hpq (ht p q hp hq)
end TriangleHost
end TripleSystem
end P593
end
section
namespace P593
universe u v
namespace TripleSystem
namespace TriangleHost
def Z9a {kappa : Type u} (c : Pair kappa → ℕ) (H : Set kappa) : Prop :=
  ∀ p q : Pair kappa, (p.1 : Set kappa) ⊆ H → (q.1 : Set kappa) ⊆ H → c p = c q
theorem Z12
    {kappa : Type u} [DecidableEq kappa]
    (h : ∀ c : Pair kappa → ℕ, ∃ H : Set kappa, H.Infinite ∧ Z9a c H) :
    Z7S kappa := by
  intro c
  obtain ⟨H, hHinf, hHmono⟩ := h c
  obtain ⟨t, htH, htcard⟩ := hHinf.exists_subset_card_eq 3
  refine ⟨⟨t, htcard⟩, ?_⟩
  intro p q hp hq
  have hp' : (p.1 : Set kappa) ⊆ t := Finset.coe_subset.2 hp
  have hq' : (q.1 : Set kappa) ⊆ t := Finset.coe_subset.2 hq
  exact hHmono p q (hp'.trans htH) (hq'.trans htH)
end TriangleHost
end TripleSystem
end P593
end
section
namespace P593
namespace TripleSystem
namespace TriangleHost
noncomputable abbrev ErdosRadoCarrier : Type :=
  (Order.succ (Cardinal.continuum : Cardinal)).out
noncomputable instance erdosRadoCarrierDecidableEq : DecidableEq ErdosRadoCarrier :=
  Classical.decEq _
theorem Z7x :
    Cardinal.mk ErdosRadoCarrier = Order.succ (Cardinal.continuum : Cardinal) :=
  Cardinal.mk_out _
def Z4E : Prop :=
  ∀ c : Pair ErdosRadoCarrier → ℕ, ∃ H : Set ErdosRadoCarrier,
    H.Infinite ∧ Z9a c H
def Z2m : Prop :=
  ∀ c : Pair ErdosRadoCarrier → ℕ, ∃ H : Set ErdosRadoCarrier,
    Cardinal.aleph0 < Cardinal.mk H ∧ Z9a c H
theorem Z1T
    (h : Z2m) :
    Z4E := by
  intro c
  obtain ⟨H, hH, hhomogeneous⟩ := h c
  refine ⟨H, ?_, hhomogeneous⟩
  exact Set.infinite_coe_iff.mp (Cardinal.aleph0_le_mk_iff.mp hH.le)
theorem Z2s
    (h : Z4E) :
    Z7S ErdosRadoCarrier :=
  Z12 h
theorem ZQ
    (h : Z2m) :
    Z7S ErdosRadoCarrier :=
  Z2s
    (Z1T h)
end TriangleHost
end TripleSystem
end P593
end
section
namespace P593
namespace TripleSystem
namespace TriangleHost
namespace ErdosRado
noncomputable abbrev TraceCarrier : Type :=
  (Order.succ (Cardinal.continuum : Cardinal)).ord.ToType
theorem Z9q :
    Cardinal.mk TraceCarrier = Order.succ (Cardinal.continuum : Cardinal) := by
  exact Cardinal.mk_ord_toType _
noncomputable def erdosRadoCarrierEquivTraceCarrier :
    Equiv ErdosRadoCarrier TraceCarrier :=
  Classical.choice <|
    Cardinal.eq.mp (Z7x.trans Z9q.symm)
noncomputable abbrev TraceHeight : Ordinal :=
  (Order.succ (Cardinal.aleph0 : Cardinal)).ord
theorem Z9V :
    Cardinal.mk TraceHeight.ToType = Order.succ (Cardinal.aleph0 : Cardinal) := by
  exact Cardinal.mk_ord_toType _
noncomputable instance traceCarrierDecidableEq : DecidableEq TraceCarrier :=
  Classical.decEq _
noncomputable def tracePair (x y : TraceCarrier) (hxy : x ≠ y) :
    Pair TraceCarrier :=
  ⟨{x, y}, by simp [hxy]⟩
abbrev Za5 := Pair TraceCarrier → ℕ
structure TracePrefix (α : TraceCarrier) where
  length : Ordinal
  length_le : length ≤ TraceHeight
  node : length.ToType → TraceCarrier
  node_lt_anchor : ∀ ξ, node ξ < α
  strictMono_node : StrictMono node
namespace TracePrefix
theorem Za2 {α : TraceCarrier} (p : TracePrefix α)
    (ξ : p.length.ToType) : p.node ξ ≠ α :=
  ne_of_lt (p.node_lt_anchor ξ)
theorem Za1 {α : TraceCarrier} (p : TracePrefix α) :
    Function.Injective p.node :=
  p.strictMono_node.injective
theorem ZaC {α : TraceCarrier} (p : TracePrefix α)
    {ξ ζ : p.length.ToType} (h : ξ < ζ) : p.node ξ < p.node ζ :=
  p.strictMono_node h
noncomputable def lowerBound {α : TraceCarrier} (p : TracePrefix α) : Ordinal :=
  ⨆ ξ : p.length.ToType, (p.node ξ).toOrd + 1
theorem Z8r {α : TraceCarrier} (p : TracePrefix α)
    (x : TraceCarrier) :
    p.lowerBound ≤ x.toOrd ↔ ∀ ξ, p.node ξ < x := by
  constructor
  · intro h ξ
    apply ((Ordinal.ToType.mk
      (o := (Order.succ (Cardinal.continuum : Cardinal)).ord)).symm.lt_iff_lt).mp
    exact (Ordinal.lt_iSup_add_one
      (fun ξ : p.length.ToType => (p.node ξ).toOrd) ξ).trans_le h
  · intro h
    apply Ordinal.iSup_add_one_le
    intro ξ
    exact ((Ordinal.ToType.mk
      (o := (Order.succ (Cardinal.continuum : Cardinal)).ord)).symm.lt_iff_lt).mpr
        (h ξ)
def EndhomogeneousTo {α : TraceCarrier} (p : TracePrefix α)
    (c : Za5) : Prop :=
  ∀ ⦃ξ ζ : p.length.ToType⦄ (h : ξ < ζ),
    c (tracePair (p.node ξ) (p.node ζ)
      (ne_of_lt (p.ZaC h))) =
      c (tracePair (p.node ξ) α (ne_of_lt (p.node_lt_anchor ξ)))
end TracePrefix
structure TraceCandidate (c : Za5) {α : TraceCarrier}
    (p : TracePrefix α) where
  live : p.length < TraceHeight
  value : TraceCarrier
  lt_anchor : value < α
  above_prefix : ∀ ξ, p.node ξ < value
  agrees : ∀ ξ,
    c (tracePair (p.node ξ) value (ne_of_lt (above_prefix ξ))) =
      c (tracePair (p.node ξ) α (ne_of_lt (p.node_lt_anchor ξ)))
namespace TraceCandidate
theorem Z7I {c : Za5} {α : TraceCarrier}
    {p : TracePrefix α} (q : TraceCandidate c p) :
    p.lowerBound ≤ q.value.toOrd :=
  (p.Z8r q.value).mpr q.above_prefix
structure Eligible (c : Za5) {α : TraceCarrier}
    (p : TracePrefix α) (β : TraceCarrier) : Prop where
  lt_anchor : β < α
  lowerBound_le : p.lowerBound ≤ β.toOrd
  agrees : ∀ ξ,
    c (tracePair (p.node ξ) β
      (ne_of_lt ((p.Z8r β).mp lowerBound_le ξ))) =
      c (tracePair (p.node ξ) α (ne_of_lt (p.node_lt_anchor ξ)))
def Zbj {c : Za5} {α : TraceCarrier}
    {p : TracePrefix α} {β : TraceCarrier}
    (hlive : p.length < TraceHeight) (h : Eligible c p β) :
    TraceCandidate c p where
  live := hlive
  value := β
  lt_anchor := h.lt_anchor
  above_prefix := (p.Z8r β).mp h.lowerBound_le
  agrees := by
    intro ξ
    simpa only using h.agrees ξ
theorem Z6v {c : Za5} {α : TraceCarrier}
    {p : TracePrefix α} (q : TraceCandidate c p) : Eligible c p q.value where
  lt_anchor := q.lt_anchor
  lowerBound_le := q.Z7I
  agrees := by
    intro ξ
    simpa only using q.agrees ξ
def ZbN (c : Za5) {α : TraceCarrier} (p : TracePrefix α) :
    Set TraceCarrier :=
  {x | ∃ q : TraceCandidate c p, q.value = x}
theorem Z8v {c : Za5} {α : TraceCarrier}
    {p : TracePrefix α} (h : Nonempty (TraceCandidate c p)) :
    (ZbN c p).Nonempty := by
  rcases h with ⟨q⟩
  exact ⟨q.value, q, rfl⟩
noncomputable def leastValue {c : Za5} {α : TraceCarrier}
    {p : TracePrefix α} (h : Nonempty (TraceCandidate c p)) : TraceCarrier :=
  WellFounded.min wellFounded_lt (ZbN c p) (Z8v h)
theorem Z9R {c : Za5} {α : TraceCarrier}
    {p : TracePrefix α} (h : Nonempty (TraceCandidate c p)) :
    leastValue h ∈ ZbN c p := by
  exact WellFounded.min_mem wellFounded_lt (ZbN c p) (Z8v h)
noncomputable def least {c : Za5} {α : TraceCarrier}
    {p : TracePrefix α} (h : Nonempty (TraceCandidate c p)) : TraceCandidate c p :=
  Classical.choose (Z9R h)
theorem Zb3 {c : Za5} {α : TraceCarrier}
    {p : TracePrefix α} (h : Nonempty (TraceCandidate c p)) :
    (least h).value = leastValue h :=
  Classical.choose_spec (Z9R h)
theorem Z8c {c : Za5} {α : TraceCarrier}
    {p : TracePrefix α} (h : Nonempty (TraceCandidate c p))
    (q : TraceCandidate c p) : ¬ q.value < (least h).value := by
  rw [Zb3]
  exact WellFounded.not_lt_min wellFounded_lt (ZbN c p) ⟨q, rfl⟩
theorem Za0 {c : Za5} {α : TraceCarrier}
    {p : TracePrefix α} (h : Nonempty (TraceCandidate c p))
    (q : TraceCandidate c p) : (least h).value ≤ q.value := by
  exact le_of_not_gt (Z8c h q)
theorem Z2B
    {c : Za5} {α : TraceCarrier} (p : TracePrefix α)
    (hp : p.length = TraceHeight) : ¬ Nonempty (TraceCandidate c p) := by
  rintro ⟨q⟩
  have h := q.live
  rw [hp] at h
  exact lt_irrefl _ h
end TraceCandidate
end ErdosRado
end TriangleHost
end TripleSystem
end P593
end
section
namespace P593
namespace TripleSystem
namespace TriangleHost
namespace ErdosRado
open scoped Cardinal Ordinal
local instance : IsEmpty (0 : Ordinal).ToType :=
  Ordinal.isEmpty_toType_iff.mpr rfl
namespace TracePrefix
noncomputable def empty (a : TraceCarrier) : TracePrefix a where
  length := 0
  length_le := bot_le
  node := fun i => isEmptyElim i
  node_lt_anchor := fun i => isEmptyElim i
  strictMono_node := by
    intro i
    exact isEmptyElim i
noncomputable def reanchor {a : TraceCarrier} (p : TracePrefix a)
    (b : TraceCarrier) (h : ∀ ξ, p.node ξ < b) : TracePrefix b where
  length := p.length
  length_le := p.length_le
  node := p.node
  node_lt_anchor := h
  strictMono_node := p.strictMono_node
@[simp]
theorem Zax {a : TraceCarrier} (p : TracePrefix a)
    (b : TraceCarrier) (h : ∀ ξ, p.node ξ < b) (ξ : p.length.ToType) :
    (p.reanchor b h).node ξ = p.node ξ :=
  rfl
@[simp]
theorem Z9y {a : TraceCarrier} (p : TracePrefix a)
    (b : TraceCarrier) (h : ∀ ξ, p.node ξ < b) :
    (p.reanchor b h).length = p.length :=
  rfl
@[simp]
theorem Z7O {a : TraceCarrier} (p : TracePrefix a)
    (b : TraceCarrier) (h : ∀ ξ, p.node ξ < b) :
    (p.reanchor b h).lowerBound = p.lowerBound :=
  rfl
noncomputable def atCandidate {c : Za5} {a : TraceCarrier}
    (p : TracePrefix a) (q : TraceCandidate c p) : TracePrefix q.value :=
  p.reanchor q.value q.above_prefix
@[simp]
theorem Z8d {c : Za5} {a : TraceCarrier}
    (p : TracePrefix a) (q : TraceCandidate c p) :
    (p.atCandidate q).length = p.length :=
  rfl
@[simp]
theorem Z91 {c : Za5} {a : TraceCarrier}
    (p : TracePrefix a) (q : TraceCandidate c p) (ξ : p.length.ToType) :
    (p.atCandidate q).node ξ = p.node ξ :=
  rfl
@[simp]
theorem Z6b {c : Za5} {a : TraceCarrier}
    (p : TracePrefix a) (q : TraceCandidate c p) :
    (p.atCandidate q).lowerBound = p.lowerBound :=
  rfl
noncomputable def restrictIndex {α : TraceCarrier} (p : TracePrefix α)
    {η : Ordinal} (hη : η ≤ p.length) (ξ : η.ToType) : p.length.ToType :=
  Ordinal.ToType.mk ⟨(ξ.toOrd : Ordinal), by
    exact Set.mem_Iio.mpr <| lt_of_lt_of_le
      (Set.mem_Iio.mp ((Ordinal.ToType.mk (o := η)).symm ξ).property) hη⟩
noncomputable def restrict {α : TraceCarrier} (p : TracePrefix α)
    (η : Ordinal) (hη : η ≤ p.length) : TracePrefix α where
  length := η
  length_le := hη.trans p.length_le
  node ξ := p.node (p.restrictIndex hη ξ)
  node_lt_anchor ξ := p.node_lt_anchor (p.restrictIndex hη ξ)
  strictMono_node := by
    intro ξ ζ hξζ
    apply p.strictMono_node
    apply (Ordinal.ToType.mk (o := p.length)).lt_iff_lt.mpr
    exact (Ordinal.ToType.mk (o := η)).symm.lt_iff_lt.mpr hξζ
@[simp]
theorem Z7e {α : TraceCarrier} (p : TracePrefix α)
    {η : Ordinal} (hη : η ≤ p.length) (ξ : η.ToType) :
    ((p.restrictIndex hη ξ).toOrd : Ordinal) = ξ.toOrd :=
  by
    unfold restrictIndex
    exact congrArg Subtype.val ((Ordinal.ToType.mk (o := p.length)).left_inv _)
theorem Zar {α : TraceCarrier} (p : TracePrefix α)
    {η : Ordinal} (hη : η ≤ p.length) (ξ : η.ToType) :
    (p.restrict η hη).node ξ = p.node (p.restrictIndex hη ξ) :=
  rfl
theorem Z8e {α : TraceCarrier} (p : TracePrefix α)
    {η θ : Ordinal} (hη : η ≤ p.length) (hθ : θ ≤ η)
    (ξ : θ.ToType) :
    p.restrictIndex hη ((p.restrict η hη).restrictIndex hθ ξ) =
      p.restrictIndex (hθ.trans hη) ξ := by
  apply (Ordinal.ToType.mk (o := p.length)).symm.injective
  apply Subtype.ext
  exact (p.Z7e hη _).trans
    (((p.restrict η hη).Z7e hθ ξ).trans
      (p.Z7e (hθ.trans hη) ξ).symm)
theorem Z92 {α : TraceCarrier} (p : TracePrefix α)
    {η : Ordinal} (hη : η ≤ p.length) {ξ ζ : η.ToType} (hξζ : ξ < ζ) :
    p.restrictIndex hη ξ < p.restrictIndex hη ζ := by
  apply (Ordinal.ToType.mk (o := p.length)).lt_iff_lt.mpr
  exact (Ordinal.ToType.mk (o := η)).symm.lt_iff_lt.mpr hξζ
theorem EndhomogeneousTo.ZbT {c : Za5} {α : TraceCarrier}
    {p : TracePrefix α} (hp : p.EndhomogeneousTo c)
    {η : Ordinal} (hη : η ≤ p.length) :
    (p.restrict η hη).EndhomogeneousTo c := by
  intro ξ ζ hξζ
  exact hp (p.Z92 hη hξζ)
end TracePrefix
namespace TraceCandidate
theorem Z5t {c : Za5} {a : TraceCarrier}
    (p : TracePrefix a) (q : TraceCandidate c p) (β : TraceCarrier) :
    Eligible c (p.atCandidate q) β ↔ Eligible c p β ∧ β < q.value := by
  constructor
  · intro h
    refine ⟨?_, h.lt_anchor⟩
    refine {
      lt_anchor := h.lt_anchor.trans q.lt_anchor
      lowerBound_le := by
        simpa only [TracePrefix.Z6b] using h.lowerBound_le
      agrees := by
        intro ξ
        simpa only [TracePrefix.Z91] using
          (h.agrees ξ).trans (q.agrees ξ)
    }
  · rintro ⟨h, hβq⟩
    refine {
      lt_anchor := hβq
      lowerBound_le := by
        simpa only [TracePrefix.Z6b] using h.lowerBound_le
      agrees := by
        intro ξ
        exact (h.agrees ξ).trans (q.agrees ξ).symm
    }
noncomputable def atCandidateOfLt {c : Za5} {a : TraceCarrier}
    (p : TracePrefix a) (q r : TraceCandidate c p)
    (hrq : r.value < q.value) : TraceCandidate c (p.atCandidate q) :=
  Zbj
    (p := p.atCandidate q)
    (by simpa only [TracePrefix.Z8d] using q.live)
    ((Z5t p q r.value).2
      ⟨Z6v r, hrq⟩)
@[simp]
theorem Z6B {c : Za5} {a : TraceCarrier}
    (p : TracePrefix a) (q r : TraceCandidate c p)
    (hrq : r.value < q.value) :
    (atCandidateOfLt p q r hrq).value = r.value :=
  rfl
noncomputable def ofAtCandidate {c : Za5} {a : TraceCarrier}
    (p : TracePrefix a) (q : TraceCandidate c p)
    (r : TraceCandidate c (p.atCandidate q)) : TraceCandidate c p :=
  Zbj (p := p) q.live <|
    ((Z5t p q r.value).1
      (Z6v r)).1
@[simp]
theorem Z7v {c : Za5} {a : TraceCarrier}
    (p : TracePrefix a) (q : TraceCandidate c p)
    (r : TraceCandidate c (p.atCandidate q)) :
    (ofAtCandidate p q r).value = r.value :=
  rfl
theorem Z3a {c : Za5}
    {a : TraceCarrier} (p : TracePrefix a) (q : TraceCandidate c p) :
    Nonempty (TraceCandidate c (p.atCandidate q)) ↔
      ∃ r : TraceCandidate c p, r.value < q.value := by
  constructor
  · rintro ⟨r⟩
    refine ⟨ofAtCandidate p q r, ?_⟩
    simpa only [Z7v] using
      ((Z5t p q r.value).1
        (Z6v r)).2
  · rintro ⟨r, hr⟩
    exact ⟨atCandidateOfLt p q r hr⟩
def IsLeast {c : Za5} {a : TraceCarrier} {p : TracePrefix a}
    (q : TraceCandidate c p) : Prop :=
  ∀ r : TraceCandidate c p, q.value ≤ r.value
theorem Zah {c : Za5} {a : TraceCarrier}
    {p : TracePrefix a} (hp : Nonempty (TraceCandidate c p)) :
    (least hp).IsLeast := by
  intro r
  exact Za0 hp r
theorem IsLeast.ZbQ {c : Za5} {a : TraceCarrier}
    {p : TracePrefix a} {q r : TraceCandidate c p}
    (hq : q.IsLeast) (hr : r.IsLeast) : q.value = r.value := by
  exact le_antisymm (hq r) (hr q)
theorem Z5W {c : Za5}
    {a : TraceCarrier} {p : TracePrefix a} {q : TraceCandidate c p}
    (hq : q.IsLeast) :
    ¬ Nonempty (TraceCandidate c (p.atCandidate q)) := by
  intro hat
  rcases (Z3a p q).1 hat with ⟨r, hr⟩
  exact (not_lt_of_ge (hq r)) hr
theorem IsLeast.Z9x {c : Za5} {a : TraceCarrier}
    {p : TracePrefix a} {q r : TraceCandidate c p}
    (hr : r.IsLeast) (hrq : r.value < q.value) :
    (atCandidateOfLt p q r hrq).IsLeast := by
  intro s
  simpa only [Z6B, Z7v] using
    hr (ofAtCandidate p q s)
noncomputable def restrict {c : Za5} {α : TraceCarrier}
    {p : TracePrefix α} (q : TraceCandidate c p)
    {η : Ordinal} (hη : η ≤ p.length) :
    TraceCandidate c (p.restrict η hη) where
  live := hη.trans_lt q.live
  value := q.value
  lt_anchor := q.lt_anchor
  above_prefix ξ := q.above_prefix (p.restrictIndex hη ξ)
  agrees ξ := q.agrees (p.restrictIndex hη ξ)
@[simp]
theorem Z9S {c : Za5} {α : TraceCarrier}
    {p : TracePrefix α} (q : TraceCandidate c p)
    {η : Ordinal} (hη : η ≤ p.length) :
    (q.restrict hη).value = q.value :=
  rfl
end TraceCandidate
namespace TracePrefix
noncomputable def snocNode {c : Za5} {α : TraceCarrier}
    (p : TracePrefix α) (q : TraceCandidate c p) :
    (Order.succ p.length).ToType → TraceCarrier := fun ξ ↦
  if hξ : (ξ.toOrd : Ordinal) < p.length then
    p.node (Ordinal.ToType.mk ⟨(ξ.toOrd : Ordinal), hξ⟩)
  else
    q.value
noncomputable def snoc {c : Za5} {α : TraceCarrier}
    (p : TracePrefix α) (q : TraceCandidate c p) : TracePrefix α where
  length := Order.succ p.length
  length_le := Order.succ_le_iff.mpr q.live
  node := p.snocNode q
  node_lt_anchor := by
    intro ξ
    by_cases hξ : (ξ.toOrd : Ordinal) < p.length
    · simpa [TracePrefix.snocNode, hξ] using
        p.node_lt_anchor (Ordinal.ToType.mk ⟨(ξ.toOrd : Ordinal), hξ⟩)
    · simpa [TracePrefix.snocNode, hξ] using q.lt_anchor
  strictMono_node := by
    intro ξ ζ hξζ
    have hOrd : (ξ.toOrd : Ordinal) < (ζ.toOrd : Ordinal) :=
      ((Ordinal.ToType.mk (o := Order.succ p.length)).symm.lt_iff_lt).mpr hξζ
    by_cases hx : (ξ.toOrd : Ordinal) < p.length
    · by_cases hy : (ζ.toOrd : Ordinal) < p.length
      · have hOld :
          (Ordinal.ToType.mk ⟨(ξ.toOrd : Ordinal), hx⟩ : p.length.ToType) <
            Ordinal.ToType.mk ⟨(ζ.toOrd : Ordinal), hy⟩ :=
          (Ordinal.ToType.mk (o := p.length)).lt_iff_lt.mpr hOrd
        simpa [TracePrefix.snocNode, hx, hy] using p.strictMono_node hOld
      · simpa [TracePrefix.snocNode, hx, hy] using
          q.above_prefix (Ordinal.ToType.mk ⟨(ξ.toOrd : Ordinal), hx⟩)
    · have hxle : (ξ.toOrd : Ordinal) ≤ p.length :=
        Order.lt_succ_iff.mp ξ.toOrd.2
      have hxEq : (ξ.toOrd : Ordinal) = p.length :=
        le_antisymm hxle (le_of_not_gt hx)
      have hyle : (ζ.toOrd : Ordinal) ≤ p.length :=
        Order.lt_succ_iff.mp ζ.toOrd.2
      have hcontra : p.length < (ζ.toOrd : Ordinal) := by
        simpa [hxEq] using hOrd
      exact (not_lt_of_ge hyle hcontra).elim
theorem Z9m {c : Za5} {α : TraceCarrier}
    (p : TracePrefix α) (q : TraceCandidate c p)
    (ξ : (Order.succ p.length).ToType)
    (hξ : (ξ.toOrd : Ordinal) < p.length) :
    (p.snoc q).node ξ =
      p.node (Ordinal.ToType.mk ⟨(ξ.toOrd : Ordinal), hξ⟩) := by
  simp [TracePrefix.snoc, TracePrefix.snocNode, hξ]
theorem Z7w {c : Za5} {α : TraceCarrier}
    (p : TracePrefix α) (q : TraceCandidate c p)
    (ξ : (Order.succ p.length).ToType)
    (hξ : ¬ (ξ.toOrd : Ordinal) < p.length) :
    (p.snoc q).node ξ = q.value := by
  simp [TracePrefix.snoc, TracePrefix.snocNode, hξ]
noncomputable def snocLast {α : TraceCarrier} (p : TracePrefix α) :
    (Order.succ p.length).ToType :=
  Ordinal.ToType.mk ⟨p.length,
    Set.mem_Iio.mpr (Order.lt_succ_iff.mpr (le_refl _))⟩
theorem Z9I {α : TraceCarrier} (p : TracePrefix α) :
    ((p.snocLast).toOrd : Ordinal) = p.length := by
  simp [TracePrefix.snocLast]
theorem Z9U {c : Za5} {α : TraceCarrier}
    (p : TracePrefix α) (q : TraceCandidate c p) :
    (p.snoc q).node p.snocLast = q.value := by
  apply TracePrefix.Z7w
  simp [TracePrefix.Z9I]
noncomputable def snocLift {α : TraceCarrier} (p : TracePrefix α)
    (ξ : p.length.ToType) : (Order.succ p.length).ToType :=
  Ordinal.ToType.mk ⟨(ξ.toOrd : Ordinal), Set.mem_Iio.mpr
    (Order.lt_succ_iff.mpr (le_of_lt (Set.mem_Iio.mp ξ.toOrd.2)))⟩
theorem Z9M {α : TraceCarrier} (p : TracePrefix α)
    (ξ : p.length.ToType) : ((p.snocLift ξ).toOrd : Ordinal) = ξ.toOrd := by
  simp [TracePrefix.snocLift]
theorem Za3 {c : Za5} {α : TraceCarrier}
    (p : TracePrefix α) (q : TraceCandidate c p) (ξ : p.length.ToType) :
    (p.snoc q).node (p.snocLift ξ) = p.node ξ := by
  have hlt : ((p.snocLift ξ).toOrd : Ordinal) < p.length := by
    rw [TracePrefix.Z9M]
    exact Set.mem_Iio.mp ξ.toOrd.2
  rw [TracePrefix.Z9m p q (p.snocLift ξ) hlt]
  apply congrArg p.node
  calc
    Ordinal.ToType.mk ⟨((p.snocLift ξ).toOrd : Ordinal), Set.mem_Iio.mpr hlt⟩ =
        Ordinal.ToType.mk ξ.toOrd := by
      congr 1
      apply Subtype.ext
      simpa using p.Z9M ξ
    _ = ξ := (Ordinal.ToType.mk (o := p.length)).apply_symm_apply ξ
theorem Z5H {α : TraceCarrier} (p : TracePrefix α)
    (ξ : (Order.succ p.length).ToType) :
    (ξ.toOrd : Ordinal) < p.length ∨ ξ = p.snocLast := by
  by_cases h : (ξ.toOrd : Ordinal) < p.length
  · exact Or.inl h
  · right
    have hle : (ξ.toOrd : Ordinal) ≤ p.length :=
      Order.lt_succ_iff.mp (Set.mem_Iio.mp ξ.toOrd.2)
    have heq : (ξ.toOrd : Ordinal) = p.length := le_antisymm hle (le_of_not_gt h)
    apply (Ordinal.ToType.mk (o := Order.succ p.length)).symm.injective
    apply Subtype.ext
    simpa only [TracePrefix.Z9I] using heq
end TracePrefix
namespace TracePrefix
end TracePrefix
namespace TraceCandidate
end TraceCandidate
end ErdosRado
end TriangleHost
end TripleSystem
end P593
end
section
namespace P593.TripleSystem.TriangleHost.ErdosRado
structure CoherentTraceSystem (c : Za5) where
  height : TraceCarrier → Ordinal
  height_le : ∀ a, height a ≤ TraceHeight
  node : ∀ (a : TraceCarrier) {eta : Ordinal}, eta < height a → TraceCarrier
  node_lt_anchor : ∀ (a : TraceCarrier) {eta : Ordinal} (heta : eta < height a),
    node a heta < a
  node_strict : ∀ (a : TraceCarrier) {eta zeta : Ordinal}
    (heta : eta < height a) (hzeta : zeta < height a), eta < zeta →
    node a heta < node a hzeta
  coherent_height : ∀ (a : TraceCarrier) {eta : Ordinal} (heta : eta < height a),
    height (node a heta) = eta
  coherent_prefix : ∀ (a : TraceCarrier) {eta zeta : Ordinal}
    (heta : eta < height a) (hzetaChild : zeta < height (node a heta))
    (hzetaParent : zeta < height a),
    node (node a heta) hzetaChild = node a hzetaParent
namespace CoherentTraceSystem
variable {c : Za5} (T : CoherentTraceSystem c)
noncomputable def tracePrefix (a : TraceCarrier) : TracePrefix a where
  length := T.height a
  length_le := T.height_le a
  node eta := T.node a (Set.mem_Iio.mp eta.toOrd.2)
  node_lt_anchor eta := T.node_lt_anchor a (Set.mem_Iio.mp eta.toOrd.2)
  strictMono_node := by
    intro eta theta heta
    apply T.node_strict a (Set.mem_Iio.mp eta.toOrd.2)
      (Set.mem_Iio.mp theta.toOrd.2)
    exact (Ordinal.ToType.mk (o := T.height a)).symm.lt_iff_lt.mpr heta
@[simp]
theorem Z8i (a : TraceCarrier) :
    (T.tracePrefix a).length = T.height a :=
  rfl
@[simp]
theorem Z95 (a : TraceCarrier) (eta : (T.height a).ToType) :
    (T.tracePrefix a).node eta = T.node a (Set.mem_Iio.mp eta.toOrd.2) :=
  rfl
def Z8K : Prop :=
  ∀ (a : TraceCarrier) {eta zeta : Ordinal}
      (heta : eta < T.height a) (hzeta : zeta < T.height a) (h : eta < zeta),
      c (tracePair (T.node a heta) (T.node a hzeta)
        (ne_of_lt (T.node_strict a heta hzeta h))) =
        c (tracePair (T.node a heta) a
          (ne_of_lt (T.node_lt_anchor a heta)))
def level (rho : Ordinal) : Set TraceCarrier := {a | T.height a = rho}
end CoherentTraceSystem
end P593.TripleSystem.TriangleHost.ErdosRado
end
section
namespace P593.TripleSystem.TriangleHost.ErdosRado
namespace CoherentTraceSystem
variable {c : Za5} (T : CoherentTraceSystem c)
private theorem Z9r {x y x' y' : TraceCarrier}
    (hx : x = x') (hy : y = y') (hxy : x ≠ y) (hx'y' : x' ≠ y') :
    tracePair x y hxy = tracePair x' y' hx'y' := by
  subst x
  subst y
  rfl
noncomputable def liftLevelIndex {delta rho : Ordinal} (h : delta < rho)
    (xi : delta.ToType) : rho.ToType :=
  Ordinal.ToType.mk ⟨(xi.toOrd : Ordinal),
    (Set.mem_Iio.mp xi.toOrd.2).trans h⟩
@[simp]
theorem Z79 {delta rho : Ordinal} (h : delta < rho)
    (xi : delta.ToType) :
    ((liftLevelIndex h xi).toOrd : Ordinal) = xi.toOrd := by
  simp [liftLevelIndex]
noncomputable def levelIndex (rho : Ordinal) (zeta : rho.ToType) : Ordinal :=
  zeta.toOrd.1
theorem Zab (rho : Ordinal) (zeta : rho.ToType) :
    levelIndex rho zeta < rho :=
  zeta.toOrd.2
theorem Z6R (rho : Ordinal) (a : T.level rho)
    (zeta : rho.ToType) :
    levelIndex rho zeta < T.height a.1 := by
  rw [a.2]
  exact Zab rho zeta
noncomputable def levelNode (rho : Ordinal) (a : T.level rho)
    (zeta : rho.ToType) : TraceCarrier :=
  T.node a.1 (T.Z6R rho a zeta)
theorem Z7H (rho : Ordinal) (a : T.level rho)
    (zeta : rho.ToType) (xi : (levelIndex rho zeta).ToType) :
    T.levelNode (levelIndex rho zeta)
        ⟨T.levelNode rho a zeta, by
          exact T.coherent_height a.1 (T.Z6R rho a zeta)⟩ xi =
      T.levelNode rho a
        (liftLevelIndex (Zab rho zeta) xi) := by
  have hparent : levelIndex (levelIndex rho zeta) xi < T.height a.1 := by
    rw [a.2]
    exact (Zab (levelIndex rho zeta) xi).trans
      (Zab rho zeta)
  have hcoherent := T.coherent_prefix a.1
    (T.Z6R rho a zeta)
    (T.Z6R (levelIndex rho zeta)
      ⟨T.levelNode rho a zeta, by
        exact T.coherent_height a.1 (T.Z6R rho a zeta)⟩ xi)
    hparent
  have hord :
      levelIndex rho (liftLevelIndex (Zab rho zeta) xi) =
        levelIndex (levelIndex rho zeta) xi := by
    simp [levelIndex, liftLevelIndex]
  simpa only [levelNode, hord] using hcoherent
theorem Z7p (rho : Ordinal) (a : T.level rho)
    (zeta : rho.ToType) :
    T.levelNode rho a zeta < a.1 :=
  T.node_lt_anchor a.1 (T.Z6R rho a zeta)
noncomputable def levelTracePrefix (rho : Ordinal) (a : T.level rho) :
    TracePrefix a.1 where
  length := rho
  length_le := by
    rw [← a.2]
    exact T.height_le a.1
  node := T.levelNode rho a
  node_lt_anchor := T.Z7p rho a
  strictMono_node := by
    intro xi zeta hxizeta
    apply T.node_strict a.1 (T.Z6R rho a xi)
      (T.Z6R rho a zeta)
    exact (Ordinal.ToType.mk (o := rho)).symm.lt_iff_lt.mpr hxizeta
@[simp]
theorem Z6I (rho : Ordinal) (a : T.level rho)
    (xi : rho.ToType) :
    (T.levelTracePrefix rho a).node xi = T.levelNode rho a xi :=
  rfl
theorem Z3Q (hend : T.Z8K)
    (rho : Ordinal) (a : T.level rho) :
    (T.levelTracePrefix rho a).EndhomogeneousTo c := by
  intro xi zeta hxizeta
  have hord : levelIndex rho xi < levelIndex rho zeta :=
    (Ordinal.ToType.mk (o := rho)).symm.lt_iff_lt.mpr hxizeta
  exact
    hend a.1 (T.Z6R rho a xi)
      (T.Z6R rho a zeta) hord
noncomputable def levelCode (rho : Ordinal) (a : T.level rho) :
    rho.ToType -> Nat :=
  fun zeta =>
    c (tracePair (T.levelNode rho a zeta) a.1
      (ne_of_lt (T.Z7p rho a zeta)))
theorem Z7u (hend : T.Z8K)
    (rho : Ordinal) (a : T.level rho) (zeta : rho.ToType) :
    T.levelCode (levelIndex rho zeta)
        ⟨T.levelNode rho a zeta, by
          exact T.coherent_height a.1 (T.Z6R rho a zeta)⟩ =
      fun xi => T.levelCode rho a
        (liftLevelIndex (Zab rho zeta) xi) := by
  funext xi
  let xi' := liftLevelIndex (Zab rho zeta) xi
  have hxizeta : levelIndex rho xi' < levelIndex rho zeta := by
    simpa [xi', levelIndex, liftLevelIndex] using
      (Zab (levelIndex rho zeta) xi)
  have hxi : levelIndex rho xi' < T.height a.1 :=
    T.Z6R rho a xi'
  have hzeta : levelIndex rho zeta < T.height a.1 :=
    T.Z6R rho a zeta
  have hcolor := hend a.1 hxi hzeta hxizeta
  have hnode_lt : T.levelNode rho a xi' < T.levelNode rho a zeta := by
    exact T.node_strict a.1 hxi hzeta hxizeta
  have hnode_ne : T.levelNode rho a xi' ≠ T.levelNode rho a zeta :=
    ne_of_lt hnode_lt
  unfold levelCode
  calc
    c (tracePair
        (T.levelNode (levelIndex rho zeta)
          ⟨T.levelNode rho a zeta, by
            exact T.coherent_height a.1 (T.Z6R rho a zeta)⟩ xi)
        (T.levelNode rho a zeta) _) =
        c (tracePair (T.levelNode rho a xi') (T.levelNode rho a zeta) _) := by
          apply congrArg c
          exact Z9r (T.Z7H rho a zeta xi) rfl _ hnode_ne
    _ = c (tracePair (T.levelNode rho a xi') a.1 _) := by
      simpa only [levelNode] using hcolor
def Z7U (rho : Ordinal) : Prop :=
  Function.Injective (T.levelCode rho)
theorem Z2I
    (rho : Ordinal) (a b : T.level rho) (hrho : rho < TraceHeight)
    (hab : a.1 < b.1)
    (hnodes : ∀ zeta : rho.ToType,
      T.levelNode rho a zeta = T.levelNode rho b zeta)
    (hcode : T.levelCode rho a = T.levelCode rho b) :
    Nonempty (TraceCandidate c (T.levelTracePrefix rho b)) := by
  refine ⟨{
    live := hrho
    value := a.1
    lt_anchor := hab
    above_prefix := ?_
    agrees := ?_
  }⟩
  · intro zeta
    change T.levelNode rho b zeta < a.1
    rw [← hnodes zeta]
    exact T.Z7p rho a zeta
  · intro zeta
    have hnode := hnodes zeta
    calc
      c (tracePair ((T.levelTracePrefix rho b).node zeta) a.1 _) =
          c (tracePair (T.levelNode rho a zeta) a.1 _) := by
            apply congrArg c
            exact Z9r
              ((T.Z6I rho b zeta).trans hnode.symm) rfl _ _
      _ = c (tracePair (T.levelNode rho b zeta) b.1 _) :=
        congrFun hcode zeta
theorem Z4h
    (hend : T.Z8K)
    (hstop : ∀ (rho : Ordinal) (a : T.level rho), rho < TraceHeight →
      ¬ Nonempty (TraceCandidate c (T.levelTracePrefix rho a)))
    (rho : Ordinal) (hrho : rho < TraceHeight) :
    T.Z7U rho := by
  refine (wellFounded_lt : WellFounded (fun x y : Ordinal => x < y)).induction
    (C := fun theta => theta < TraceHeight -> T.Z7U theta)
    rho ?_ hrho
  intro theta ih htheta a b hcode
  have hnodes : ∀ zeta : theta.ToType,
      T.levelNode theta a zeta = T.levelNode theta b zeta := by
    intro zeta
    have hchild :
        (⟨T.levelNode theta a zeta, by
          exact T.coherent_height a.1 (T.Z6R theta a zeta)⟩ :
            T.level (levelIndex theta zeta)) =
        ⟨T.levelNode theta b zeta, by
          exact T.coherent_height b.1 (T.Z6R theta b zeta)⟩ := by
      apply ih (levelIndex theta zeta) (Zab theta zeta)
        ((Zab theta zeta).trans htheta)
      rw [T.Z7u hend theta a zeta,
        T.Z7u hend theta b zeta]
      funext xi
      exact congrFun hcode (liftLevelIndex (Zab theta zeta) xi)
    exact congrArg Subtype.val hchild
  apply Subtype.ext
  by_contra hab
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · exact hstop theta b htheta <|
      T.Z2I theta a b htheta hablt hnodes hcode
  · exact hstop theta a htheta <|
      T.Z2I theta b a htheta hbalt
        (fun zeta ↦ (hnodes zeta).symm) hcode.symm
end CoherentTraceSystem
end P593.TripleSystem.TriangleHost.ErdosRado
end
section
namespace P593
namespace TripleSystem
namespace TriangleHost
namespace ErdosRado
open scoped Cardinal Ordinal
namespace TracePrefix
noncomputable def liftIndex {α : TraceCarrier} {p q : TracePrefix α}
    (h : p.length ≤ q.length) (ξ : p.length.ToType) : q.length.ToType :=
  q.restrictIndex h ξ
theorem Z9e {α : TraceCarrier} {p q : TracePrefix α}
    (h : p.length ≤ q.length) (ξ : p.length.ToType) :
    ((liftIndex h ξ).toOrd : Ordinal) = ξ.toOrd := by
  simp [liftIndex, TracePrefix.restrictIndex]
def Z8M {α : TraceCarrier} (p q : TracePrefix α) : Prop :=
  ∃ h : p.length ≤ q.length,
    ∀ ξ : p.length.ToType, q.node (liftIndex h ξ) = p.node ξ
structure LimitChain (α : TraceCarrier) (o : Ordinal) where
  stage : o.ToType → TracePrefix α
  length_eq : ∀ η, (stage η).length = η.toOrd
  coherent : ∀ {η θ : o.ToType}, η ≤ θ →
    Z8M (stage η) (stage θ)
namespace LimitChain
noncomputable def ofPrefix {α : TraceCarrier} (p : TracePrefix α)
    (o : Ordinal) (ho : o ≤ p.length) : LimitChain α o where
  stage η := p.restrict η.toOrd <| by
    exact (le_of_lt (Set.mem_Iio.mp η.toOrd.2)).trans ho
  length_eq η := rfl
  coherent := by
    intro η θ hηθ
    have hord : (η.toOrd : Ordinal) ≤ θ.toOrd := by
      exact (Ordinal.ToType.mk (o := o)).symm.monotone hηθ
    let hη : (η.toOrd : Ordinal) ≤ p.length :=
      (le_of_lt (Set.mem_Iio.mp η.toOrd.2)).trans ho
    let hθ : (θ.toOrd : Ordinal) ≤ p.length :=
      (le_of_lt (Set.mem_Iio.mp θ.toOrd.2)).trans ho
    let hlen : (p.restrict η.toOrd hη).length ≤
        (p.restrict θ.toOrd hθ).length := hord
    refine ⟨hlen, ?_⟩
    intro ξ
    exact congrArg p.node (p.Z8e hθ hlen ξ)
noncomputable def nextStage {α : TraceCarrier} {o : Ordinal}
    (_F : LimitChain α o) (ho : Order.IsSuccLimit o)
    (ξ : o.ToType) : o.ToType :=
  Ordinal.ToType.mk ⟨Order.succ (ξ.toOrd : Ordinal),
    Set.mem_Iio.mpr (ho.succ_lt (Set.mem_Iio.mp ξ.toOrd.2))⟩
theorem Z9f {α : TraceCarrier} {o : Ordinal}
    (F : LimitChain α o) (ho : Order.IsSuccLimit o)
    (ξ : o.ToType) :
    ((F.nextStage ho ξ).toOrd : Ordinal) =
      Order.succ (ξ.toOrd : Ordinal) := by
  simp [nextStage]
noncomputable def diagonalIndex {α : TraceCarrier} {o : Ordinal}
    (F : LimitChain α o) (ho : Order.IsSuccLimit o)
    (ξ : o.ToType) : (F.stage (F.nextStage ho ξ)).length.ToType :=
  Ordinal.ToType.mk ⟨(ξ.toOrd : Ordinal), Set.mem_Iio.mpr (by
    rw [F.length_eq, F.Z9f]
    exact Order.lt_succ (ξ.toOrd : Ordinal))⟩
theorem Z7q {α : TraceCarrier} {o : Ordinal}
    (F : LimitChain α o) (ho : Order.IsSuccLimit o)
    (ξ : o.ToType) :
    ((F.diagonalIndex ho ξ).toOrd : Ordinal) = ξ.toOrd := by
  simp [diagonalIndex]
noncomputable def limitNode {α : TraceCarrier} {o : Ordinal}
    (F : LimitChain α o) (ho : Order.IsSuccLimit o) :
    o.ToType → TraceCarrier := fun ξ =>
  (F.stage (F.nextStage ho ξ)).node (F.diagonalIndex ho ξ)
noncomputable def indexAt {α : TraceCarrier} {o : Ordinal}
    (F : LimitChain α o) {η : o.ToType} (ξ : o.ToType)
    (hξη : (ξ.toOrd : Ordinal) < η.toOrd) :
    (F.stage η).length.ToType :=
  Ordinal.ToType.mk ⟨(ξ.toOrd : Ordinal), Set.mem_Iio.mpr (by
    rw [F.length_eq]
    exact hξη)⟩
theorem Zaf {α : TraceCarrier} {o : Ordinal}
    (F : LimitChain α o) {η : o.ToType} (ξ : o.ToType)
    (hξη : (ξ.toOrd : Ordinal) < η.toOrd) :
    ((F.indexAt ξ hξη).toOrd : Ordinal) = ξ.toOrd := by
  simp [indexAt]
theorem Z7T {α : TraceCarrier} {o : Ordinal}
    (F : LimitChain α o) (ho : Order.IsSuccLimit o)
    {η : o.ToType} (ξ : o.ToType)
    (hξη : (ξ.toOrd : Ordinal) < η.toOrd) :
    F.limitNode ho ξ = (F.stage η).node (F.indexAt ξ hξη) := by
  have hnext : F.nextStage ho ξ ≤ η := by
    apply (Ordinal.ToType.mk (o := o)).symm.le_iff_le.mp
    change ((F.nextStage ho ξ).toOrd : Ordinal) ≤ η.toOrd
    rw [F.Z9f]
    exact Order.succ_le_iff.mpr hξη
  rcases F.coherent hnext with ⟨hlen, hnode⟩
  calc
    F.limitNode ho ξ =
        (F.stage (F.nextStage ho ξ)).node (F.diagonalIndex ho ξ) := rfl
    _ = (F.stage η).node (liftIndex hlen (F.diagonalIndex ho ξ)) :=
      (hnode (F.diagonalIndex ho ξ)).symm
    _ = (F.stage η).node (F.indexAt ξ hξη) := by
      apply congrArg (F.stage η).node
      apply (Ordinal.ToType.mk (o := (F.stage η).length)).symm.injective
      apply Subtype.ext
      simp [Z9e, Z7q, Zaf]
noncomputable def limitPrefix {α : TraceCarrier} {o : Ordinal}
    (F : LimitChain α o) (ho : Order.IsSuccLimit o)
    (hheight : o ≤ TraceHeight) : TracePrefix α where
  length := o
  length_le := hheight
  node := F.limitNode ho
  node_lt_anchor := by
    intro ξ
    exact (F.stage (F.nextStage ho ξ)).node_lt_anchor
      (F.diagonalIndex ho ξ)
  strictMono_node := by
    intro ξ ζ hξζ
    have hOrd : (ξ.toOrd : Ordinal) < ζ.toOrd :=
      ((Ordinal.ToType.mk (o := o)).symm.lt_iff_lt).mpr hξζ
    let η := F.nextStage ho ζ
    have hζη : (ζ.toOrd : Ordinal) < η.toOrd := by
      dsimp [η]
      rw [F.Z9f]
      exact Order.lt_succ (ζ.toOrd : Ordinal)
    have hξη : (ξ.toOrd : Ordinal) < η.toOrd := hOrd.trans hζη
    rw [F.Z7T ho ξ hξη,
      F.Z7T ho ζ hζη]
    apply (F.stage η).strictMono_node
    apply (Ordinal.ToType.mk (o := (F.stage η).length)).lt_iff_lt.mpr
    simpa [F.Zaf] using hOrd
theorem Z33 {α : TraceCarrier} {o : Ordinal}
    (F : LimitChain α o) (ho : Order.IsSuccLimit o)
    (hheight : o ≤ TraceHeight) (η : o.ToType) :
    Z8M (F.stage η) (F.limitPrefix ho hheight) := by
  let hlen : (F.stage η).length ≤ (F.limitPrefix ho hheight).length := by
    change (F.stage η).length ≤ o
    rw [F.length_eq]
    exact le_of_lt (Set.mem_Iio.mp η.toOrd.2)
  refine ⟨hlen, ?_⟩
  intro ξ
  have hξη : ((liftIndex hlen ξ).toOrd : Ordinal) < η.toOrd := by
    rw [Z9e, ← F.length_eq]
    exact Set.mem_Iio.mp ξ.toOrd.2
  change F.limitNode ho (liftIndex hlen ξ) = (F.stage η).node ξ
  rw [F.Z7T ho (liftIndex hlen ξ) hξη]
  apply congrArg (F.stage η).node
  calc
    F.indexAt (liftIndex hlen ξ) hξη =
        Ordinal.ToType.mk ξ.toOrd := by
      change (Ordinal.ToType.mk (o := (F.stage η).length)) ⟨_, _⟩ = _
      apply congrArg (Ordinal.ToType.mk (o := (F.stage η).length))
      apply Subtype.ext
      exact Z9e hlen ξ
    _ = ξ :=
      (Ordinal.ToType.mk (o := (F.stage η).length)).apply_symm_apply ξ
theorem Z55 {α : TraceCarrier} {o : Ordinal}
    (F : LimitChain α o) (ho : Order.IsSuccLimit o)
    (hheight : o ≤ TraceHeight) (c : Za5)
    (hend : ∀ η, (F.stage η).EndhomogeneousTo c) :
    (F.limitPrefix ho hheight).EndhomogeneousTo c := by
  change ∀ ⦃ξ ζ : o.ToType⦄ (h : ξ < ζ),
    c (tracePair (F.limitNode ho ξ) (F.limitNode ho ζ) _) =
      c (tracePair (F.limitNode ho ξ) α _)
  intro ξ ζ hξζ
  have hOrd : (ξ.toOrd : Ordinal) < ζ.toOrd :=
    ((Ordinal.ToType.mk (o := o)).symm.lt_iff_lt).mpr hξζ
  let η := F.nextStage ho ζ
  have hζη : (ζ.toOrd : Ordinal) < η.toOrd := by
    dsimp [η]
    rw [F.Z9f]
    exact Order.lt_succ (ζ.toOrd : Ordinal)
  have hξη : (ξ.toOrd : Ordinal) < η.toOrd := hOrd.trans hζη
  have hstage : F.indexAt ξ hξη < F.indexAt ζ hζη := by
    apply (Ordinal.ToType.mk (o := (F.stage η).length)).lt_iff_lt.mpr
    simpa [F.Zaf] using hOrd
  have hx := F.Z7T ho ξ hξη
  have hz := F.Z7T ho ζ hζη
  simpa only [hx, hz] using hend η hstage
end LimitChain
end TracePrefix
end ErdosRado
end TriangleHost
end TripleSystem
end P593
end
section
namespace P593
namespace TripleSystem
namespace TriangleHost
namespace ErdosRado
namespace TraceIteration
abbrev Zbf : Type 1 := Ordinal × TraceCarrier
abbrev Za9 : Type 1 := Set Zbf
variable (step : Za9 → Za9)
noncomputable def run (eta : Ordinal) : Za9 :=
  transfiniteIterate step eta ∅
@[simp]
theorem ZbS : run step 0 = ∅ := by
  change transfiniteIterate step (0 : Ordinal) (∅ : Za9) = ∅
  rw [← Ordinal.bot_eq_zero]
  exact transfiniteIterate_bot step (∅ : Za9)
theorem ZbR (eta : Ordinal) (h_eta : ¬ IsMax eta) :
    run step (Order.succ eta) = step (run step eta) := by
  simpa [run] using
    (transfiniteIterate_succ step (∅ : Za9) eta h_eta)
theorem Z8Z (eta : Ordinal) :
    run step (Order.succ eta) = step (run step eta) := by
  exact ZbR step eta (not_isMax eta)
theorem ZbD (eta : Ordinal) (h_eta : Order.IsSuccLimit eta) :
    run step eta = ⨆ xi : Set.Iio eta, run step xi.1 := by
  simpa [run] using
    (transfiniteIterate_limit step (∅ : Za9) eta h_eta)
theorem ZaN (hinfl : ∀ s : Za9, s ⊆ step s) :
    Monotone (run step) := by
  exact monotone_transfiniteIterate step ∅ hinfl
end TraceIteration
end ErdosRado
end TriangleHost
end TripleSystem
end P593
end
section
namespace P593
namespace TripleSystem
namespace TriangleHost
namespace ErdosRado
open scoped Cardinal Ordinal
namespace TracePrefix
def graph {a : TraceCarrier} (p : TracePrefix a) :
    TraceIteration.Za9 :=
  {z | ∃ ξ : p.length.ToType,
    z = ((ξ.toOrd : Ordinal), p.node ξ)}
@[simp]
theorem Zb5 (a : TraceCarrier) :
    (empty a).graph = ∅ := by
  ext z
  constructor
  · rintro ⟨ξ, _⟩
    have hξ : (ξ.toOrd : Ordinal) < 0 := Set.mem_Iio.mp ξ.toOrd.2
    exact (not_lt_of_ge bot_le hξ).elim
  · intro hz
    exact hz.elim
theorem Z9B {a : TraceCarrier} (p : TracePrefix a)
    {η : Ordinal} (hη : η ≤ p.length) :
    (p.restrict η hη).graph = p.graph ∩ {z | z.1 < η} := by
  ext z
  constructor
  · rintro ⟨ξ, rfl⟩
    refine ⟨?_, Set.mem_setOf.mpr (Set.mem_Iio.mp ξ.toOrd.2)⟩
    refine ⟨p.restrictIndex hη ξ, ?_⟩
    apply Prod.ext
    · exact (p.Z7e hη ξ).symm
    · rfl
  · rintro ⟨⟨ξ, rfl⟩, hξη⟩
    let ζ : η.ToType := Ordinal.ToType.mk ⟨ξ.toOrd, hξη⟩
    have hζOrd : (ζ.toOrd : Ordinal) = ξ.toOrd := by
      simp [ζ, Ordinal.ToType.toOrd]
    have hindex : p.restrictIndex hη ζ = ξ := by
      apply (Ordinal.ToType.mk (o := p.length)).symm.injective
      apply Subtype.ext
      rw [p.Z7e hη]
      exact hζOrd
    refine ⟨ζ, ?_⟩
    apply Prod.ext
    · exact hζOrd.symm
    · simp only [Zar, hindex]
theorem Z7L {a : TraceCarrier} (p : TracePrefix a)
    {eta : Ordinal} (heta : Order.succ eta ≤ p.length) :
    (p.restrict (Order.succ eta) heta).graph =
      (p.restrict eta ((Order.le_succ eta).trans heta)).graph ∪
        {((eta : Ordinal), p.node (Ordinal.ToType.mk
          ⟨eta, (Order.lt_succ eta).trans_le heta⟩))} := by
  rw [Z9B, Z9B]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_union,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨hz, hzsucc⟩
    rcases lt_or_eq_of_le (Order.lt_succ_iff.mp hzsucc) with hlt | heq
    · exact Or.inl ⟨hz, hlt⟩
    · right
      rcases hz with ⟨xi, rfl⟩
      let i : p.length.ToType := Ordinal.ToType.mk
        ⟨eta, (Order.lt_succ eta).trans_le heta⟩
      have hiord : (i.toOrd : Ordinal) = eta := by
        exact congrArg Subtype.val
          ((Ordinal.ToType.mk (o := p.length)).symm_apply_apply
            ⟨eta, (Order.lt_succ eta).trans_le heta⟩)
      have hxiord : (xi.toOrd : Ordinal) = eta := heq
      have hxi : xi = i := by
        apply (Ordinal.ToType.mk (o := p.length)).symm.injective
        apply Subtype.ext
        exact hxiord.trans hiord.symm
      subst xi
      apply Prod.ext
      · exact hiord
      · rfl
  · rintro (⟨hz, hlt⟩ | rfl)
    · exact ⟨hz, hlt.trans (Order.lt_succ eta)⟩
    · let i : p.length.ToType := Ordinal.ToType.mk
        ⟨eta, (Order.lt_succ eta).trans_le heta⟩
      have hiord : (i.toOrd : Ordinal) = eta := by
        exact congrArg Subtype.val
          ((Ordinal.ToType.mk (o := p.length)).symm_apply_apply
            ⟨eta, (Order.lt_succ eta).trans_le heta⟩)
      refine ⟨⟨i, ?_⟩, Order.lt_succ eta⟩
      apply Prod.ext
      · exact hiord.symm
      · rfl
theorem Zbg {c : Za5} {a : TraceCarrier}
    (p : TracePrefix a) (q : TraceCandidate c p) :
    (p.snoc q).graph = p.graph ∪ {((p.length : Ordinal), q.value)} := by
  ext z
  constructor
  · rintro ⟨ξ, rfl⟩
    by_cases hξ : (ξ.toOrd : Ordinal) < p.length
    · left
      refine ⟨Ordinal.ToType.mk ⟨ξ.toOrd, hξ⟩, ?_⟩
      apply Prod.ext
      · simp [Ordinal.ToType.toOrd]
      · exact p.Z9m q ξ hξ
    · right
      have hle : (ξ.toOrd : Ordinal) ≤ p.length :=
        Order.lt_succ_iff.mp ξ.toOrd.2
      have heq : (ξ.toOrd : Ordinal) = p.length :=
        le_antisymm hle (le_of_not_gt hξ)
      simp only [Set.mem_singleton_iff]
      apply Prod.ext
      · exact heq
      · exact p.Z7w q ξ hξ
  · rintro (hz | hz)
    · rcases hz with ⟨ξ, rfl⟩
      refine ⟨p.snocLift ξ, ?_⟩
      apply Prod.ext
      · exact (p.Z9M ξ).symm
      · exact (p.Za3 q ξ).symm
    · rw [Set.mem_singleton_iff] at hz
      subst z
      refine ⟨p.snocLast, ?_⟩
      apply Prod.ext
      · exact (p.Z9I).symm
      · exact (p.Z9U q).symm
theorem LimitChain.Z8D {a : TraceCarrier} {o : Ordinal}
    (F : LimitChain a o) (ho : Order.IsSuccLimit o)
    (hheight : o ≤ TraceHeight) :
    (F.limitPrefix ho hheight).graph =
      ⋃ η : o.ToType, (F.stage η).graph := by
  ext z
  constructor
  · rintro ⟨ξ, rfl⟩
    rw [Set.mem_iUnion]
    refine ⟨F.nextStage ho ξ, ?_⟩
    refine ⟨F.diagonalIndex ho ξ, ?_⟩
    apply Prod.ext
    · exact (F.Z7q ho ξ).symm
    · rfl
  · rw [Set.mem_iUnion]
    rintro ⟨η, ξ, rfl⟩
    rcases F.Z33 ho hheight η with
      ⟨hlen, hnode⟩
    refine ⟨liftIndex hlen ξ, ?_⟩
    apply Prod.ext
    · exact (Z9e hlen ξ).symm
    · exact (hnode ξ).symm
end TracePrefix
namespace TraceIteration
noncomputable def historyLength (s : Za9) : Ordinal :=
  sSup ((fun z : Zbf => z.1 + 1) '' s)
@[simp]
theorem Z7N {a : TraceCarrier} (p : TracePrefix a) :
    historyLength p.graph = p.length := by
  apply le_antisymm
  · apply csSup_le'
    rintro _ ⟨z, ⟨ξ, rfl⟩, rfl⟩
    exact Order.succ_le_iff.mpr (Set.mem_Iio.mp ξ.toOrd.2)
  · refine le_of_forall_lt fun β hβ => ?_
    let ξ : p.length.ToType := Ordinal.ToType.mk ⟨β, hβ⟩
    have hb : BddAbove ((fun z : Zbf => z.1 + 1) '' p.graph) := by
      refine ⟨p.length, ?_⟩
      rintro _ ⟨z, ⟨ζ, rfl⟩, rfl⟩
      exact Order.succ_le_iff.mpr (Set.mem_Iio.mp ζ.toOrd.2)
    let z : Zbf := (β, p.node ξ)
    have hz : z ∈ p.graph := by
      refine ⟨ξ, ?_⟩
      simp [z, ξ, Ordinal.ToType.toOrd]
    exact (lt_add_one β).trans_le (le_csSup hb ⟨z, hz, rfl⟩)
end TraceIteration
namespace TracePrefix
theorem Z99 {a : TraceCarrier} :
    Function.Injective (@graph a) := by
  intro p q hgraph
  have hlength : p.length = q.length := by
    have h := congrArg TraceIteration.historyLength hgraph
    simpa using h
  cases p with
  | mk plen ple pnode panchor pmono =>
    cases q with
    | mk qlen qle qnode qanchor qmono =>
      dsimp at hlength
      subst qlen
      congr 1
      apply funext
      intro xi
      have hz : (@graph a (TracePrefix.mk plen ple pnode panchor pmono))
          ((xi.toOrd : Ordinal), pnode xi) := Exists.intro xi rfl
      rw [hgraph] at hz
      cases hz with
      | intro zeta hzeta =>
        have hxizeta : xi = zeta := by
          apply (Ordinal.ToType.mk (o := plen)).symm.injective
          apply Subtype.ext
          exact congrArg Prod.fst hzeta
        subst zeta
        exact congrArg Prod.snd hzeta
theorem Z3D {a : TraceCarrier}
    {p q : TracePrefix a} (hgraph : p.graph ⊆ q.graph) :
    p.Z8M q := by
  have hlength : p.length ≤ q.length := by
    refine le_of_forall_lt fun β hβ ↦ ?_
    let ξ : p.length.ToType := Ordinal.ToType.mk ⟨β, hβ⟩
    have hz : ((β : Ordinal), p.node ξ) ∈ p.graph := by
      refine ⟨ξ, ?_⟩
      apply Prod.ext
      · simp [ξ, Ordinal.ToType.toOrd]
      · rfl
    rcases hgraph hz with ⟨ζ, hζ⟩
    have hβζ : β = (ζ.toOrd : Ordinal) := congrArg Prod.fst hζ
    rw [hβζ]
    exact Set.mem_Iio.mp ζ.toOrd.2
  refine ⟨hlength, fun ξ ↦ ?_⟩
  have hz : ((ξ.toOrd : Ordinal), p.node ξ) ∈ p.graph := ⟨ξ, rfl⟩
  rcases hgraph hz with ⟨ζ, hζ⟩
  have hindex : liftIndex hlength ξ = ζ := by
    apply (Ordinal.ToType.mk (o := q.length)).symm.injective
    apply Subtype.ext
    rw [Z9e]
    exact congrArg Prod.fst hζ
  rw [hindex]
  exact (congrArg Prod.snd hζ).symm
end TracePrefix
end ErdosRado
end TriangleHost
end TripleSystem
end P593
end
section
namespace P593
namespace TripleSystem
namespace TriangleHost
namespace ErdosRado
open scoped Cardinal Ordinal
namespace TraceIteration
def Zaz (a : TraceCarrier) (s : Za9) : Prop :=
  ∃ p : TracePrefix a, p.graph = s
theorem Z81 {a : TraceCarrier} (p : TracePrefix a) :
    Zaz a p.graph :=
  ⟨p, rfl⟩
noncomputable def decodedPrefix {a : TraceCarrier} {s : Za9}
    (hs : Zaz a s) : TracePrefix a :=
  Classical.choose hs
@[simp]
theorem Z7J {a : TraceCarrier} {s : Za9}
    (hs : Zaz a s) : (decodedPrefix hs).graph = s := by
  exact Classical.choose_spec hs
@[simp]
theorem Z8Q {a : TraceCarrier} (p : TracePrefix a)
    (hs : Zaz a p.graph) : decodedPrefix hs = p := by
  exact TracePrefix.Z99 (Z7J hs)
private theorem Z4S {c : Za5}
    {a : TraceCarrier} {p q : TracePrefix a} (hpq : p = q)
    (hp : Nonempty (TraceCandidate c p))
    (hq : Nonempty (TraceCandidate c q)) :
    (TraceCandidate.least hp).value = (TraceCandidate.least hq).value := by
  subst q
  rfl
noncomputable def sourceStep (c : Za5) (a : TraceCarrier)
    (s : Za9) : Za9 := by
  classical
  exact
    if hs : Zaz a s then
      if hp : Nonempty (TraceCandidate c (decodedPrefix hs)) then
        s ∪ {(((decodedPrefix hs).length : Ordinal),
          (TraceCandidate.least hp).value)}
      else
        s
    else
      s
theorem Z6J (c : Za5) (a : TraceCarrier)
    (s : Za9) (hs : ¬ Zaz a s) :
    sourceStep c a s = s := by
  simp [sourceStep, hs]
theorem Z6C (c : Za5) (a : TraceCarrier)
    {s : Za9} (hs : Zaz a s)
    (hp : ¬ Nonempty (TraceCandidate c (decodedPrefix hs))) :
    sourceStep c a s = s := by
  simp [sourceStep, hs, hp]
theorem Z5x (c : Za5) (a : TraceCarrier)
    {s : Za9} (hs : Zaz a s)
    (hp : Nonempty (TraceCandidate c (decodedPrefix hs))) :
    sourceStep c a s =
      s ∪ {(((decodedPrefix hs).length : Ordinal),
        (TraceCandidate.least hp).value)} := by
  simp [sourceStep, hs, hp]
theorem Z41 (c : Za5)
    {a : TraceCarrier} (p : TracePrefix a)
    (hp : Nonempty (TraceCandidate c p)) :
    sourceStep c a p.graph =
      (p.snoc (TraceCandidate.least hp)).graph := by
  let hs : Zaz a p.graph := Z81 p
  have hdecode : decodedPrefix hs = p := Z8Q p hs
  have hp' : Nonempty (TraceCandidate c (decodedPrefix hs)) := by
    simpa only [hdecode] using hp
  have hvalue : (TraceCandidate.least hp').value =
      (TraceCandidate.least hp).value :=
    Z4S hdecode hp' hp
  rw [TracePrefix.Zbg,
    Z5x c a hs hp']
  rw [congrArg TracePrefix.length hdecode, hvalue]
theorem Z4N (c : Za5)
    {a : TraceCarrier} (p : TracePrefix a)
    (hp : ¬ Nonempty (TraceCandidate c p)) :
    sourceStep c a p.graph = p.graph := by
  let hs : Zaz a p.graph := Z81 p
  have hdecode : decodedPrefix hs = p := Z8Q p hs
  apply Z6C c a hs
  simpa only [hdecode] using hp
theorem Z5Y (c : Za5) (a : TraceCarrier) :
    ∀ s : Za9, s ⊆ sourceStep c a s := by
  intro s
  by_cases hs : Zaz a s
  · by_cases hp : Nonempty (TraceCandidate c (decodedPrefix hs))
    · rw [Z5x c a hs hp]
      exact Set.subset_union_left
    · rw [Z6C c a hs hp]
  · rw [Z6J c a s hs]
noncomputable def sourceRun (c : Za5) (a : TraceCarrier)
    (η : Ordinal) : Za9 :=
  run (sourceStep c a) η
@[simp]
theorem Z9T (c : Za5) (a : TraceCarrier) :
    sourceRun c a 0 = ∅ := by
  exact ZbS (sourceStep c a)
theorem Z9L (c : Za5) (a : TraceCarrier) (η : Ordinal) :
    sourceRun c a (Order.succ η) = sourceStep c a (sourceRun c a η) := by
  exact Z8Z (sourceStep c a) η
theorem Z9l (c : Za5) (a : TraceCarrier) (η : Ordinal)
    (hη : Order.IsSuccLimit η) :
    sourceRun c a η = ⋃ ξ : Set.Iio η, sourceRun c a ξ.1 := by
  exact ZbD (sourceStep c a) η hη
theorem Z80 (c : Za5) (a : TraceCarrier) :
    Monotone (sourceRun c a) := by
  exact ZaN (sourceStep c a) (Z5Y c a)
theorem Z4d (c : Za5)
    {a : TraceCarrier} (p : TracePrefix a)
    (hp : ¬ Nonempty (TraceCandidate c p))
    {η : Ordinal} (hη : sourceRun c a η = p.graph) :
    ∀ {θ : Ordinal}, η ≤ θ → sourceRun c a θ = p.graph := by
  intro θ hηθ
  induction θ using Ordinal.limitRecOn with
  | zero =>
      have hηzero : η = 0 :=
        le_antisymm hηθ (bot_le : (0 : Ordinal) ≤ η)
      simpa [hηzero] using hη
  | add_one θ ih =>
      by_cases hηθ' : η ≤ θ
      · rw [← Order.succ_eq_add_one, Z9L, ih hηθ',
          Z4N c p hp]
      · have hθη : θ < η := lt_of_not_ge hηθ'
        have hsuccη : θ + 1 ≤ η := by
          rw [← Order.succ_eq_add_one]
          exact Order.succ_le_of_lt hθη
        have : η = θ + 1 := le_antisymm hηθ hsuccη
        simpa [this] using hη
  | limit θ hθ ih =>
      by_cases heq : η = θ
      · simpa [heq] using hη
      · have hlt : η < θ := hηθ.lt_of_ne heq
        rw [Z9l c a θ hθ]
        apply le_antisymm
        · refine iSup_le fun ξ ↦ ?_
          by_cases hηξ : η ≤ ξ.1
          · exact le_of_eq (ih ξ.1 ξ.2 hηξ)
          · rw [← hη]
            exact Z80 c a (le_of_not_ge hηξ)
        · rw [← hη]
          exact le_iSup (fun ξ : Set.Iio θ ↦ sourceRun c a ξ.1)
            ⟨η, hlt⟩
end TraceIteration
end ErdosRado
end TriangleHost
end TripleSystem
end P593
end
section
namespace P593
namespace TripleSystem
namespace TriangleHost
namespace ErdosRado
open scoped Cardinal Ordinal
namespace TracePrefix
noncomputable def before {a : TraceCarrier} (p : TracePrefix a)
    (ξ : p.length.ToType) : TracePrefix a :=
  p.restrict ξ.toOrd (le_of_lt (Set.mem_Iio.mp ξ.toOrd.2))
@[simp]
theorem Zaw {a : TraceCarrier} (p : TracePrefix a)
    (ξ : p.length.ToType) : (p.before ξ).length = ξ.toOrd :=
  rfl
def IsSourceCanonicalFor {a : TraceCarrier} (p : TracePrefix a)
    (c : Za5) : Prop :=
  ∀ ξ : p.length.ToType,
    ∃ q : TraceCandidate c (p.before ξ),
      q.IsLeast ∧ q.value = p.node ξ
theorem Z56 (c : Za5) (a : TraceCarrier) :
    (empty a).IsSourceCanonicalFor c := by
  intro ξ
  have hξ : (ξ.toOrd : Ordinal) < 0 := Set.mem_Iio.mp ξ.toOrd.2
  exact (not_lt_of_ge bot_le hξ).elim
private theorem Z8h {a : TraceCarrier} (p : TracePrefix a)
    {η : Ordinal} (hη : η ≤ p.length) (ξ : η.ToType) :
    (p.restrict η hη).before ξ = p.before (p.restrictIndex hη ξ) := by
  apply Z99
  unfold before
  rw [Z9B, Z9B, Z9B]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  have hord : ((p.restrictIndex hη ξ).toOrd : Ordinal) =
      (ξ.toOrd : Ordinal) := p.Z7e hη ξ
  constructor
  · rintro ⟨⟨hz, hzη⟩, hzξ⟩
    rw [hord]
    exact ⟨hz, hzξ⟩
  · rintro ⟨hz, hzξ⟩
    have hξη : (ξ.toOrd : Ordinal) < η := Set.mem_Iio.mp ξ.toOrd.2
    rw [hord] at hzξ
    have hzη : z.1 < η := hzξ.trans hξη
    exact ⟨⟨hz, hzη⟩, hzξ⟩
theorem IsSourceCanonicalFor.ZbU {c : Za5}
    {a : TraceCarrier} {p : TracePrefix a}
    (hp : p.IsSourceCanonicalFor c) {η : Ordinal} (hη : η ≤ p.length) :
    (p.restrict η hη).IsSourceCanonicalFor c := by
  intro ξ
  rcases hp (p.restrictIndex hη ξ) with ⟨q, hq, hvalue⟩
  rw [Z8h p hη ξ]
  exact ⟨q, hq, hvalue⟩
theorem Z3R {a : TraceCarrier}
    (p q : TracePrefix a) (hseg : p.Z8M q) :
    q.restrict p.length hseg.choose = p := by
  apply Z99
  rw [Z9B]
  ext z
  constructor
  · rintro ⟨⟨ζ, rfl⟩, hζ⟩
    let ξ : p.length.ToType :=
      Ordinal.ToType.mk ⟨(ζ.toOrd : Ordinal), hζ⟩
    refine ⟨ξ, ?_⟩
    apply Prod.ext
    · simp [ξ, Ordinal.ToType.toOrd]
    · have hnode := hseg.choose_spec ξ
      simpa [ξ, liftIndex, TracePrefix.restrictIndex] using hnode
  · rintro ⟨ξ, rfl⟩
    refine ⟨?_, Set.mem_setOf.mpr (Set.mem_Iio.mp ξ.toOrd.2)⟩
    refine ⟨liftIndex hseg.choose ξ, ?_⟩
    apply Prod.ext
    · exact (Z9e hseg.choose ξ).symm
    · exact (hseg.choose_spec ξ).symm
private theorem Z78 {c : Za5}
    {a : TraceCarrier} (p : TracePrefix a) (q : TraceCandidate c p)
    (ζ : (p.snoc q).length.ToType) (hζ : (ζ.toOrd : Ordinal) < p.length) :
    (p.snoc q).before ζ =
      p.before (Ordinal.ToType.mk ⟨(ζ.toOrd : Ordinal), hζ⟩) := by
  apply Z99
  unfold before
  rw [Z9B, Z9B, Zbg]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hz | rfl, hzζ⟩
    · refine ⟨hz, ?_⟩
      simpa [Ordinal.ToType.toOrd] using hzζ
    · exact (not_lt_of_ge (le_of_lt hζ) hzζ).elim
  · rintro ⟨hz, hzζ⟩
    refine ⟨Or.inl hz, ?_⟩
    simpa [Ordinal.ToType.toOrd] using hzζ
private theorem Z5I {c : Za5}
    {a : TraceCarrier} (p : TracePrefix a) (q : TraceCandidate c p)
    (ζ : (p.snoc q).length.ToType)
    (hζ : ¬ (ζ.toOrd : Ordinal) < p.length) :
    (p.snoc q).before ζ = p := by
  have hbound : (ζ.toOrd : Ordinal) < Order.succ p.length := by
    have h := Set.mem_Iio.mp ζ.toOrd.2
    change (ζ.toOrd : Ordinal) < Order.succ p.length at h
    exact h
  have heq : (ζ.toOrd : Ordinal) = p.length :=
    le_antisymm (Order.lt_succ_iff.mp hbound) (le_of_not_gt hζ)
  apply Z99
  unfold before
  rw [Z9B, Zbg]
  rw [heq]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hz | rfl, hzlt⟩
    · exact hz
    · exact (lt_irrefl p.length hzlt).elim
  · intro hz
    refine ⟨Or.inl hz, ?_⟩
    rcases hz with ⟨ξ, rfl⟩
    exact Set.mem_Iio.mp ξ.toOrd.2
theorem IsSourceCanonicalFor.snoc {c : Za5}
    {a : TraceCarrier} {p : TracePrefix a}
    (hp : p.IsSourceCanonicalFor c) (q : TraceCandidate c p)
    (hq : q.IsLeast) : (p.snoc q).IsSourceCanonicalFor c := by
  intro ζ
  rcases p.Z5H ζ with hζ | rfl
  · let ξ : p.length.ToType :=
      Ordinal.ToType.mk ⟨(ζ.toOrd : Ordinal), hζ⟩
    rcases hp ξ with ⟨r, hr, hvalue⟩
    rw [Z78 p q ζ hζ]
    refine ⟨r, hr, ?_⟩
    rw [p.Z9m q ζ hζ]
    exact hvalue
  · have hnot : ¬
        (((p.snocLast : (p.snoc q).length.ToType).toOrd : Ordinal)) <
          p.length := by
      intro h
      have h' : ((p.snocLast).toOrd : Ordinal) < p.length := h
      rw [p.Z9I] at h'
      exact (lt_irrefl p.length h').elim
    rw [Z5I p q p.snocLast hnot]
    exact ⟨q, hq, (p.Z9U q).symm⟩
theorem IsSourceCanonicalFor.Zb4 {c : Za5}
    {a : TraceCarrier} {o : Ordinal} (F : LimitChain a o)
    (ho : Order.IsSuccLimit o) (hheight : o ≤ TraceHeight)
    (hcanonical : ∀ η, (F.stage η).IsSourceCanonicalFor c) :
    (F.limitPrefix ho hheight).IsSourceCanonicalFor c := by
  intro ξ
  let η := F.nextStage ho ξ
  let ζ := F.diagonalIndex ho ξ
  rcases hcanonical η ζ with ⟨q, hq, hvalue⟩
  have hseg := F.Z33 ho hheight η
  have hstage :
      (F.limitPrefix ho hheight).restrict (F.stage η).length hseg.choose =
        F.stage η :=
    Z3R (F.stage η)
      (F.limitPrefix ho hheight) hseg
  have hstagegraph := congrArg TracePrefix.graph hstage
  rw [Z9B] at hstagegraph
  have hbefore : (F.stage η).before ζ =
      (F.limitPrefix ho hheight).before ξ := by
    apply Z99
    unfold before
    rw [Z9B, Z9B, ← hstagegraph]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    have hord : (ζ.toOrd : Ordinal) = ξ.toOrd :=
      F.Z7q ho ξ
    constructor
    · rintro ⟨⟨hz, hzη⟩, hzζ⟩
      exact ⟨hz, by simpa [hord] using hzζ⟩
    · rintro ⟨hz, hzξ⟩
      refine ⟨⟨hz, ?_⟩, ?_⟩
      · rw [F.length_eq]
        change z.1 < ((F.nextStage ho (show o.ToType from ξ)).toOrd : Ordinal)
        rw [F.Z9f]
        exact hzξ.trans (Order.lt_succ _)
      · simpa [hord] using hzξ
  rw [← hbefore]
  refine ⟨q, hq, ?_⟩
  change q.value = F.limitNode ho ξ
  simpa [η, ζ, LimitChain.limitNode] using hvalue
end TracePrefix
end ErdosRado
end TriangleHost
end TripleSystem
end P593
end
section
namespace P593
namespace TripleSystem
namespace TriangleHost
namespace ErdosRado
open scoped Cardinal Ordinal
namespace TraceIteration
def Z9d (c : Za5) (a : TraceCarrier)
    (η : Ordinal) : Prop :=
  ∃ p : TracePrefix a,
    sourceRun c a η = p.graph ∧
    p.IsSourceCanonicalFor c ∧
    p.length ≤ η ∧
    (p.length = η ∨
      (p.length < η ∧ ¬ Nonempty (TraceCandidate c p)))
theorem Z3v (c : Za5)
    {a : TraceCarrier} {p : TracePrefix a}
    (hcanonical : p.IsSourceCanonicalFor c)
    (hp : ¬ Nonempty (TraceCandidate c p))
    {η θ : Ordinal} (hrun : sourceRun c a η = p.graph)
    (hηθ : η ≤ θ) (hlength : p.length < θ) :
    Z9d c a θ := by
  refine ⟨p, Z4d c p hp hrun hηθ,
    hcanonical, le_of_lt hlength, Or.inr ⟨hlength, hp⟩⟩
theorem Z73 (c : Za5) (a : TraceCarrier)
    {η : Ordinal} (hη : Z9d c a η) :
    Z9d c a (Order.succ η) := by
  rcases hη with ⟨p, hrun, hcanonical, hlength, hstatus⟩
  by_cases hp : Nonempty (TraceCandidate c p)
  · rcases hstatus with heq | ⟨hlt, hstopped⟩
    · let q : TraceCandidate c p := TraceCandidate.least hp
      refine ⟨p.snoc q, ?_, ?_, ?_, Or.inl ?_⟩
      · rw [Z9L, hrun,
          Z41 c p hp]
      · exact hcanonical.snoc q (TraceCandidate.Zah hp)
      · change Order.succ p.length ≤ Order.succ η
        exact Order.succ_le_succ hlength
      · change Order.succ p.length = Order.succ η
        exact congrArg Order.succ heq
    · exact (hstopped hp).elim
  · exact Z3v c hcanonical hp hrun
      (Order.le_succ η) (hlength.trans_lt (Order.lt_succ η))
theorem Z47
    (c : Za5) (a : TraceCarrier) (η : Ordinal)
    (hηlim : Order.IsSuccLimit η) (hηheight : η ≤ TraceHeight)
    (hspec : ∀ ξ : Set.Iio η, Z9d c a ξ.1) :
    Z9d c a η := by
  classical
  by_cases hstop : ∃ ξ : Set.Iio η, ∃ p : TracePrefix a,
      sourceRun c a ξ.1 = p.graph ∧
      p.IsSourceCanonicalFor c ∧ p.length < ξ.1 ∧
      ¬ Nonempty (TraceCandidate c p)
  · rcases hstop with ⟨ξ, p, hrun, hcanonical, hlength, hterminal⟩
    exact Z3v c hcanonical hterminal hrun
      (le_of_lt ξ.2) (hlength.trans ξ.2)
  · let stage : η.ToType → TracePrefix a := fun ξ ↦ Classical.choose (hspec ξ)
    have stage_spec (ξ : η.ToType) :
        sourceRun c a ξ.toOrd = (stage ξ).graph ∧
        (stage ξ).IsSourceCanonicalFor c ∧
        (stage ξ).length ≤ ξ.toOrd ∧
        ((stage ξ).length = ξ.toOrd ∨
          ((stage ξ).length < ξ.toOrd ∧
            ¬ Nonempty (TraceCandidate c (stage ξ)))) :=
      Classical.choose_spec (hspec ξ)
    have stage_run (ξ : η.ToType) :
        sourceRun c a ξ.toOrd = (stage ξ).graph :=
      (stage_spec ξ).1
    have stage_canonical (ξ : η.ToType) :
        (stage ξ).IsSourceCanonicalFor c :=
      (stage_spec ξ).2.1
    have stage_status (ξ : η.ToType) :
        (stage ξ).length = ξ.toOrd ∨
          ((stage ξ).length < ξ.toOrd ∧
            ¬ Nonempty (TraceCandidate c (stage ξ))) :=
      (stage_spec ξ).2.2.2
    have stage_length (ξ : η.ToType) : (stage ξ).length = ξ.toOrd := by
      rcases stage_status ξ with heq | hshort
      · exact heq
      · exfalso
        apply hstop
        exact ⟨ξ, stage ξ, stage_run ξ, stage_canonical ξ,
          hshort.1, hshort.2⟩
    let F : TracePrefix.LimitChain a η :=
      { stage := stage
        length_eq := stage_length
        coherent := by
          intro ξ θ hξθ
          apply TracePrefix.Z3D
          rw [← stage_run ξ, ← stage_run θ]
          apply Z80 c a
          exact (Ordinal.ToType.mk (o := η)).symm.monotone hξθ }
    let p := F.limitPrefix hηlim hηheight
    refine ⟨p, ?_, ?_, le_rfl, Or.inl rfl⟩
    · calc
        sourceRun c a η = ⋃ ξ : Set.Iio η, sourceRun c a ξ.1 :=
          Z9l c a η hηlim
        _ = ⋃ ξ : η.ToType, (F.stage ξ).graph := by
          ext z
          simp only [Set.mem_iUnion]
          constructor
          · rintro ⟨ξ, hz⟩
            let j : η.ToType := Ordinal.ToType.mk ξ
            refine ⟨j, ?_⟩
            rw [← stage_run j]
            simpa [j, Ordinal.ToType.toOrd] using hz
          · rintro ⟨ξ, hz⟩
            refine ⟨ξ.toOrd, ?_⟩
            rw [stage_run ξ]
            exact hz
        _ = p.graph := (F.Z8D hηlim hηheight).symm
    · apply TracePrefix.IsSourceCanonicalFor.Zb4
      intro ξ
      exact stage_canonical ξ
theorem Z9H (c : Za5) (a : TraceCarrier)
    (η : Ordinal) (hη : η ≤ TraceHeight) :
    Z9d c a η := by
  revert hη
  induction η using Ordinal.limitRecOn with
  | zero =>
      intro _
      refine ⟨TracePrefix.empty a, ?_,
        TracePrefix.Z56 c a, bot_le, Or.inl rfl⟩
      rw [Z9T, TracePrefix.Zb5]
  | add_one η ih =>
      intro hheight
      apply Z73 c a
      apply ih
      exact (Order.le_succ η).trans hheight
  | limit η hlim ih =>
      intro hheight
      apply Z47 c a η hlim hheight
      intro ξ
      apply ih ξ.1 ξ.2
      exact (le_of_lt ξ.2).trans hheight
end TraceIteration
end ErdosRado
end TriangleHost
end TripleSystem
end P593
end
section
namespace P593
namespace TripleSystem
namespace TriangleHost
namespace ErdosRado
open scoped Cardinal Ordinal
namespace TraceIteration
theorem Z6h
    {c : Za5} {a : TraceCarrier} {p : TracePrefix a}
    (hcanonical : p.IsSourceCanonicalFor c)
    (q : TraceCandidate c p) {eta : Ordinal} (heta : eta ≤ p.length) :
    sourceRun c q.value eta = (p.restrict eta heta).graph := by
  classical
  induction eta using Ordinal.limitRecOn with
  | zero =>
      rw [Z9T, TracePrefix.Z9B]
      ext z
      simp
  | add_one eta ih =>
      have hbase : eta ≤ p.length :=
        (Order.le_succ eta).trans heta
      have hi : eta < p.length :=
        (Order.lt_succ eta).trans_le heta
      let i : p.length.ToType := Ordinal.ToType.mk ⟨eta, hi⟩
      have hiord : (i.toOrd : Ordinal) = eta := by
        exact congrArg Subtype.val
          ((Ordinal.ToType.mk (o := p.length)).symm_apply_apply ⟨eta, hi⟩)
      have hbefore : p.before i = p.restrict eta hbase := by
        apply TracePrefix.Z99
        unfold TracePrefix.before
        rw [TracePrefix.Z9B, TracePrefix.Z9B]
        ext z
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
        rw [hiord]
      have hcanonicalAt :
          ∃ r : TraceCandidate c (p.restrict eta hbase),
            r.IsLeast ∧ r.value = p.node i := by
        exact hbefore ▸ hcanonical i
      rcases hcanonicalAt with ⟨r, hrleast, hrvalue⟩
      let qeta : TraceCandidate c (p.restrict eta hbase) := q.restrict hbase
      have hrq : r.value < qeta.value := by
        rw [TraceCandidate.Z9S, hrvalue]
        exact q.above_prefix i
      let rstep : TraceCandidate c
          ((p.restrict eta hbase).atCandidate qeta) :=
        TraceCandidate.atCandidateOfLt (p.restrict eta hbase) qeta r hrq
      have hrstepLeast : rstep.IsLeast :=
        hrleast.Z9x hrq
      have hrstepValue : rstep.value = p.node i := by
        rw [TraceCandidate.Z6B, hrvalue]
      have hextendable : Nonempty (TraceCandidate c
          ((p.restrict eta hbase).atCandidate qeta)) := ⟨rstep⟩
      have hleastValue :
          (TraceCandidate.least hextendable).value = p.node i := by
        rw [← hrstepValue]
        exact (TraceCandidate.Zah hextendable).ZbQ hrstepLeast
      calc
        sourceRun c q.value (eta + 1) =
            sourceRun c q.value (Order.succ eta) := by
          rw [Order.succ_eq_add_one]
        _ = sourceStep c q.value (sourceRun c q.value eta) :=
          Z9L c q.value eta
        _ = (p.restrict (eta + 1) heta).graph := by
          rw [ih hbase]
          rw [← TraceCandidate.Z9S q hbase]
          change sourceStep c qeta.value
              ((p.restrict eta hbase).atCandidate qeta).graph = _
          rw [Z41 c
            ((p.restrict eta hbase).atCandidate qeta) hextendable]
          rw [TracePrefix.Zbg, hleastValue]
          change (p.restrict eta hbase).graph ∪
              {((eta : Ordinal), p.node i)} = _
          have hsucc : Order.succ eta ≤ p.length := by
            simpa only [Order.succ_eq_add_one] using heta
          simpa only [Order.succ_eq_add_one] using
            (TracePrefix.Z7L p hsucc).symm
  | limit eta hlimit ih =>
      rw [Z9l c q.value eta hlimit]
      rw [TracePrefix.Z9B]
      ext z
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨beta, hz⟩
        rw [ih beta.1 beta.2 ((le_of_lt beta.2).trans heta)] at hz
        rw [TracePrefix.Z9B] at hz
        exact ⟨hz.1, hz.2.trans beta.2⟩
      · rintro ⟨hz, hzeta⟩
        let beta : Set.Iio eta :=
          ⟨Order.succ z.1, hlimit.succ_lt hzeta⟩
        refine ⟨beta, ?_⟩
        rw [ih beta.1 beta.2 ((le_of_lt beta.2).trans heta)]
        rw [TracePrefix.Z9B]
        exact ⟨hz, Order.lt_succ z.1⟩
theorem Z5X
    {c : Za5} {a : TraceCarrier} {p : TracePrefix a}
    (hcanonical : p.IsSourceCanonicalFor c)
    (xi : p.length.ToType)
    {theta : Ordinal} (htheta : theta ≤ xi.toOrd) :
    sourceRun c (p.node xi) theta =
      (p.restrict theta
        (htheta.trans (le_of_lt xi.toOrd.2))).graph := by
  rcases hcanonical xi with ⟨qxi, _, hqxiValue⟩
  rw [← hqxiValue]
  have hbeforeCanonical : (p.before xi).IsSourceCanonicalFor c := by
    exact hcanonical.ZbU (le_of_lt xi.toOrd.2)
  have hrun := Z6h hbeforeCanonical qxi htheta
  rw [hrun]
  refine ((p.before xi).Z9B htheta).trans ?_
  delta TracePrefix.before
  rw [TracePrefix.Z9B p, TracePrefix.Z9B p]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hz, _⟩, hztheta⟩
    exact ⟨hz, hztheta⟩
  · rintro ⟨hz, hztheta⟩
    exact ⟨⟨hz, hztheta.trans_le htheta⟩, hztheta⟩
end TraceIteration
end ErdosRado
end TriangleHost
end TripleSystem
end P593
end
section
namespace P593
namespace TripleSystem
namespace TriangleHost
namespace ErdosRado
open scoped Cardinal Ordinal
namespace TracePrefix
noncomputable def beforeAtNode {a : TraceCarrier} (p : TracePrefix a)
    (xi : p.length.ToType) : TracePrefix (p.node xi) :=
  (p.before xi).reanchor (p.node xi) (by
    intro eta
    change (xi.toOrd : Ordinal).ToType at eta
    apply p.ZaC
    have hetaXi : (eta.toOrd : Ordinal) < xi.toOrd :=
      Set.mem_Iio.mp eta.toOrd.2
    apply ((Ordinal.ToType.mk (o := p.length)).symm.lt_iff_lt).mp
    change ((p.restrictIndex
      (le_of_lt (Set.mem_Iio.mp xi.toOrd.2)) eta).toOrd : Ordinal) < xi.toOrd
    rw [p.Z7e]
    exact hetaXi)
@[simp]
theorem Z7K {a : TraceCarrier} (p : TracePrefix a)
    (xi : p.length.ToType) : (p.beforeAtNode xi).length = xi.toOrd :=
  rfl
@[simp]
theorem Z82 {a : TraceCarrier} (p : TracePrefix a)
    (xi : p.length.ToType) :
    (p.beforeAtNode xi).graph = (p.before xi).graph :=
  rfl
end TracePrefix
namespace TraceIteration
noncomputable def terminalPrefix (c : Za5) (a : TraceCarrier) :
    TracePrefix a :=
  Classical.choose (Z9H c a TraceHeight le_rfl)
@[simp]
theorem Z74 (c : Za5) (a : TraceCarrier) :
    sourceRun.{0} c a TraceHeight = (terminalPrefix c a).graph :=
  (Classical.choose_spec (Z9H c a TraceHeight le_rfl)).1
theorem Z5y (c : Za5) (a : TraceCarrier) :
    (terminalPrefix c a).IsSourceCanonicalFor c :=
  (Classical.choose_spec (Z9H c a TraceHeight le_rfl)).2.1
theorem Z6K (c : Za5) (a : TraceCarrier) :
    (terminalPrefix c a).length = TraceHeight ∨
      ((terminalPrefix c a).length < TraceHeight ∧
        ¬ Nonempty (TraceCandidate c (terminalPrefix c a))) :=
  (Classical.choose_spec (Z9H c a TraceHeight le_rfl)).2.2.2
theorem Z6i (c : Za5) (a : TraceCarrier) :
    ¬ Nonempty (TraceCandidate c (terminalPrefix c a)) := by
  rcases Z6K c a with hfull | ⟨_, hstop⟩
  · exact TraceCandidate.Z2B
      (terminalPrefix c a) hfull
  · exact hstop
theorem Z4i
    {c : Za5} {a : TraceCarrier} {p : TracePrefix a}
    (hp : p.IsSourceCanonicalFor c) (xi : p.length.ToType) :
    sourceRun.{0} c (p.node xi) TraceHeight = (p.beforeAtNode xi).graph := by
  rcases hp xi with ⟨q, hqleast, hqvalue⟩
  let q' : TraceCandidate c (p.before xi) := {
    live := q.live
    value := p.node xi
    lt_anchor := by simpa only [← hqvalue] using q.lt_anchor
    above_prefix := by
      intro eta
      simpa only [← hqvalue] using q.above_prefix eta
    agrees := by
      intro eta
      simpa only [← hqvalue] using q.agrees eta
  }
  have hq'least : q'.IsLeast := by
    intro r
    change p.node xi ≤ r.value
    rw [← hqvalue]
    exact hqleast r
  have hstopped :
      ¬ Nonempty (TraceCandidate c (p.beforeAtNode xi)) := by
    have hreanchor : p.beforeAtNode xi = (p.before xi).atCandidate q' := by
      apply TracePrefix.Z99
      rfl
    rw [hreanchor]
    exact TraceCandidate.Z5W hq'least
  have hstage :
      sourceRun.{0} c (p.node xi) xi.toOrd = (p.beforeAtNode xi).graph := by
    rw [TracePrefix.Z82]
    exact Z5X hp xi (le_refl xi.toOrd)
  exact Z4d c (p.beforeAtNode xi) hstopped hstage
    (θ := TraceHeight)
    ((le_of_lt (Set.mem_Iio.mp xi.toOrd.2)).trans p.length_le)
@[simp]
theorem Z6a (c : Za5) (a : TraceCarrier)
    (xi : (terminalPrefix c a).length.ToType) :
    terminalPrefix c ((terminalPrefix c a).node xi) =
      (terminalPrefix c a).beforeAtNode xi := by
  apply TracePrefix.Z99
  rw [← Z74]
  exact Z4i (Z5y c a) xi
end TraceIteration
end ErdosRado
end TriangleHost
end TripleSystem
end P593
end
section
namespace P593
namespace TripleSystem
namespace TriangleHost
namespace ErdosRado
open scoped Cardinal Ordinal
namespace TracePrefix
private theorem Z9s {x y x' y' : TraceCarrier}
    (hx : x = x') (hy : y = y') (hxy : x ≠ y) (hx'y' : x' ≠ y') :
    tracePair x y hxy = tracePair x' y' hx'y' := by
  subst x'
  subst y'
  rfl
theorem IsSourceCanonicalFor.Z90
    {c : Za5} {a : TraceCarrier} {p : TracePrefix a}
    (hp : p.IsSourceCanonicalFor c) : p.EndhomogeneousTo c := by
  intro xi zeta hxiz
  rcases hp zeta with ⟨q, _hq, hqvalue⟩
  have hord : (xi.toOrd : Ordinal) < (zeta.toOrd : Ordinal) :=
    ((Ordinal.ToType.mk (o := p.length)).symm.lt_iff_lt).mpr hxiz
  let xi' : (zeta.toOrd : Ordinal).ToType :=
    Ordinal.ToType.mk ⟨(xi.toOrd : Ordinal), Set.mem_Iio.mpr hord⟩
  have hindex : p.restrictIndex
      (le_of_lt (Set.mem_Iio.mp zeta.toOrd.2)) xi' = xi := by
    apply (Ordinal.ToType.mk (o := p.length)).symm.injective
    apply Subtype.ext
    rw [p.Z7e]
    unfold xi'
    exact congrArg Subtype.val
      ((Ordinal.ToType.mk (o := (zeta.toOrd : Ordinal))).symm_apply_apply
        ⟨(xi.toOrd : Ordinal), Set.mem_Iio.mpr hord⟩)
  have hnode : (p.before zeta).node xi' = p.node xi := by
    change p.node (p.restrictIndex
      (le_of_lt (Set.mem_Iio.mp zeta.toOrd.2)) xi') = p.node xi
    rw [hindex]
  calc
    c (tracePair (p.node xi) (p.node zeta)
        (ne_of_lt (p.ZaC hxiz))) =
        c (tracePair ((p.before zeta).node xi') q.value
          (ne_of_lt (q.above_prefix xi'))) := by
            apply congrArg c
            exact Z9s hnode.symm hqvalue.symm _ _
    _ = c (tracePair ((p.before zeta).node xi') a
          (ne_of_lt ((p.before zeta).node_lt_anchor xi'))) := q.agrees xi'
    _ = c (tracePair (p.node xi) a
          (ne_of_lt (p.node_lt_anchor xi))) := by
            apply congrArg c
            exact Z9s hnode rfl _ _
end TracePrefix
namespace TraceIteration
theorem Z4j (c : Za5) (a : TraceCarrier) :
    (terminalPrefix c a).EndhomogeneousTo c :=
  (Z5y c a).Z90
end TraceIteration
end ErdosRado
end TriangleHost
end TripleSystem
end P593
end
section
namespace P593
namespace TripleSystem
namespace TriangleHost
namespace ErdosRado
open scoped Cardinal Ordinal
namespace TraceIteration
noncomputable def terminalIndex (c : Za5) (a : TraceCarrier)
    {eta : Ordinal} (heta : eta < (terminalPrefix c a).length) :
    (terminalPrefix c a).length.ToType :=
  Ordinal.ToType.mk ⟨eta, Set.mem_Iio.mpr heta⟩
@[simp]
theorem Z7k (c : Za5) (a : TraceCarrier)
    {eta : Ordinal} (heta : eta < (terminalPrefix c a).length) :
    ((terminalIndex c a heta).toOrd : Ordinal) = eta := by
  simp [terminalIndex]
noncomputable def sourceCoherentTraceSystem (c : Za5) :
    CoherentTraceSystem c where
  height a := (terminalPrefix c a).length
  height_le a := (terminalPrefix c a).length_le
  node a eta heta := (terminalPrefix c a).node (terminalIndex c a heta)
  node_lt_anchor a eta heta :=
    (terminalPrefix c a).node_lt_anchor (terminalIndex c a heta)
  node_strict a eta zeta heta hzeta hetazeta := by
    apply (terminalPrefix c a).ZaC
    simpa [terminalIndex] using hetazeta
  coherent_height a eta heta := by
    have hprefix := Z6a c a (terminalIndex c a heta)
    have hlength := congrArg TracePrefix.length hprefix
    simpa only [TracePrefix.Z7K, Z7k] using hlength
  coherent_prefix a eta zeta heta hzetaChild hzetaParent := by
    let xi := terminalIndex c a heta
    have hprefix := Z6a c a xi
    let child := terminalPrefix c ((terminalPrefix c a).node xi)
    let childIndex := terminalIndex c ((terminalPrefix c a).node xi) hzetaChild
    have hmem : ((zeta : Ordinal), child.node childIndex) ∈ child.graph := by
      refine ⟨childIndex, ?_⟩
      apply Prod.ext
      · exact (Z7k c ((terminalPrefix c a).node xi)
          hzetaChild).symm
      · rfl
    have hgraph : child.graph = ((terminalPrefix c a).before xi).graph := by
      rw [show child = terminalPrefix c ((terminalPrefix c a).node xi) from rfl,
        hprefix, TracePrefix.Z82]
    rw [hgraph] at hmem
    rcases hmem with ⟨k, hk⟩
    have hkord : (k.toOrd : Ordinal) = zeta :=
      (congrArg Prod.fst hk).symm
    change child.node childIndex =
      (terminalPrefix c a).node (terminalIndex c a hzetaParent)
    calc
      child.node childIndex = ((terminalPrefix c a).before xi).node k :=
        congrArg Prod.snd hk
      _ = (terminalPrefix c a).node (terminalIndex c a hzetaParent) := by
        change (terminalPrefix c a).node
            ((terminalPrefix c a).restrictIndex (le_of_lt xi.toOrd.2) k) = _
        apply congrArg (terminalPrefix c a).node
        apply (Ordinal.ToType.mk
          (o := (terminalPrefix c a).length)).symm.injective
        apply Subtype.ext
        rw [(terminalPrefix c a).Z7e,
          Z7k]
        exact hkord
@[simp]
theorem Z3K (c : Za5) (a : TraceCarrier) :
    (sourceCoherentTraceSystem c).height a = (terminalPrefix c a).length :=
  rfl
theorem Z1R (c : Za5) :
    (sourceCoherentTraceSystem c).Z8K := by
  intro a eta zeta heta hzeta hetazeta
  let xi := terminalIndex c a heta
  let kappa := terminalIndex c a hzeta
  have hxikappa : xi < kappa := by
    simpa [xi, kappa, terminalIndex] using hetazeta
  have hend := Z4j c a hxikappa
  simpa only [sourceCoherentTraceSystem, xi, kappa] using hend
@[simp]
theorem Z1S
    (c : Za5) (rho : Ordinal)
    (a : (sourceCoherentTraceSystem c).level rho) :
    (sourceCoherentTraceSystem c).levelTracePrefix rho a =
      terminalPrefix c a.1 := by
  have hrho : (terminalPrefix c a.1).length = rho := a.2
  apply TracePrefix.Z99
  ext z
  constructor
  · rintro ⟨xi, rfl⟩
    let xi' : (terminalPrefix c a.1).length.ToType :=
      Ordinal.ToType.mk ⟨(xi.toOrd : Ordinal), by
        rw [hrho]
        exact Set.mem_Iio.mp xi.toOrd.2⟩
    have hxi' : (xi'.toOrd : Ordinal) = xi.toOrd := by
      exact congrArg Subtype.val
        ((Ordinal.ToType.mk
          (o := (terminalPrefix c a.1).length)).symm_apply_apply _)
    refine ⟨xi', ?_⟩
    apply Prod.ext
    · exact hxi'.symm
    · apply congrArg (terminalPrefix c a.1).node
      apply (Ordinal.ToType.mk
        (o := (terminalPrefix c a.1).length)).symm.injective
      apply Subtype.ext
      exact (Z7k c a.1
        ((sourceCoherentTraceSystem c).Z6R rho a (show rho.ToType from xi))).trans hxi'.symm
  · rintro ⟨xi, rfl⟩
    let xi' : rho.ToType := Ordinal.ToType.mk
      ⟨(xi.toOrd : Ordinal), by
        exact (Set.mem_Iio.mp xi.toOrd.2).trans_le (le_of_eq hrho)⟩
    have hxi' : (xi'.toOrd : Ordinal) = xi.toOrd := by
      exact congrArg Subtype.val
        ((Ordinal.ToType.mk (o := rho)).symm_apply_apply _)
    refine ⟨xi', ?_⟩
    apply Prod.ext
    · exact hxi'.symm
    · apply congrArg (terminalPrefix c a.1).node
      apply (Ordinal.ToType.mk
        (o := (terminalPrefix c a.1).length)).symm.injective
      apply Subtype.ext
      exact hxi'.symm.trans ((Z7k c a.1
        ((sourceCoherentTraceSystem c).Z6R rho a xi')).symm)
theorem Z3g
    (c : Za5) (rho : Ordinal)
    (a : (sourceCoherentTraceSystem c).level rho) :
    ¬ Nonempty
      (TraceCandidate c
        ((sourceCoherentTraceSystem c).levelTracePrefix rho a)) := by
  rw [Z1S]
  exact Z6i c a.1
theorem Z1F :
    ∀ c : Za5,
      ∃ T : CoherentTraceSystem c, T.Z8K ∧
        ∀ (rho : Ordinal) (a : T.level rho), rho < TraceHeight →
          ¬ Nonempty
            (TraceCandidate c (T.levelTracePrefix rho a)) := by
  intro c
  refine ⟨sourceCoherentTraceSystem c,
    Z1R c, ?_⟩
  intro rho a _hrho
  exact Z3g c rho a
end TraceIteration
end ErdosRado
end TriangleHost
end TripleSystem
end P593
end
section
namespace P593
namespace TripleSystem
namespace TriangleHost
universe u
def Zbs {α β : Type u} (e : α ≃ β) : Pair α ≃ Pair β :=
  e.finsetCongr.subtypeEquiv (by
    intro s
    simp [Equiv.finsetCongr_apply])
@[simp] theorem Zai {α β : Type u} (e : α ≃ β) (p : Pair α) :
    ((Zbs e p).1 : Set β) = e '' (p.1 : Set α) := by
  change ((Set.powersetCard.map 2 e.toEmbedding p).1 : Set β) = _
  exact Set.powersetCard.coe_map 2 e.toEmbedding p
def Z8L {α β : Type u} (e : α ≃ β) (c : Pair α → ℕ) : Pair β → ℕ :=
  fun q => c ((Zbs e).symm q)
theorem Z57 {α β : Type u} (e : α ≃ β) (c : Pair α → ℕ)
    (H : Set β) (h : Z9a (Z8L e c) H) :
    Z9a c (e.symm '' H) := by
  intro p q hp hq
  have hp' : ((Zbs e p).1 : Set β) ⊆ H := by
    rw [Zai]
    rintro z ⟨x, hxp, rfl⟩
    rcases hp hxp with ⟨y, hyH, hyx⟩
    have hexy : e x = y := by
      calc
        e x = e (e.symm y) := congrArg e hyx.symm
        _ = y := e.apply_symm_apply y
    simpa [hexy] using hyH
  have hq' : ((Zbs e q).1 : Set β) ⊆ H := by
    rw [Zai]
    rintro z ⟨x, hxq, rfl⟩
    rcases hq hxq with ⟨y, hyH, hyx⟩
    have hexy : e x = y := by
      calc
        e x = e (e.symm y) := congrArg e hyx.symm
        _ = y := e.apply_symm_apply y
    simpa [hexy] using hyH
  have htransported := h (Zbs e p) (Zbs e q) hp' hq'
  change c ((Zbs e).symm (Zbs e p)) =
    c ((Zbs e).symm (Zbs e q)) at htransported
  simpa using htransported
theorem Z75 {α β : Type u} (e : α ≃ β) (H : Set α) :
    Cardinal.mk (e '' H) = Cardinal.mk H :=
  Cardinal.mk_image_eq e.injective
end TriangleHost
end TripleSystem
end P593
end
section
namespace P593.TripleSystem.TriangleHost.ErdosRado
open Cardinal
theorem Z4O :
    Cardinal.mk TraceHeight.ToType = Cardinal.aleph 1 := by
  rw [Z9V, Cardinal.succ_aleph0]
theorem Z3E {rho : Ordinal.{0}}
    (hrho : rho < TraceHeight) : rho.card <= Cardinal.aleph0 := by
  apply Cardinal.lt_aleph_one_iff.mp
  change rho < (Order.succ (Cardinal.aleph0 : Cardinal)).ord at hrho
  rw [Cardinal.lt_ord] at hrho
  simpa only [Cardinal.succ_aleph0] using hrho
theorem Z48 {rho : Ordinal.{0}}
    (hrho : rho < TraceHeight) :
    Cardinal.mk (rho.ToType -> Nat) <= Cardinal.continuum := by
  rw [Cardinal.mk_arrow, Cardinal.mk_nat, Cardinal.lift_id, Cardinal.lift_id,
    Cardinal.mk_toType]
  calc
    Cardinal.aleph0 ^ rho.card <= Cardinal.aleph0 ^ Cardinal.aleph0 :=
      Cardinal.power_le_power_left Cardinal.aleph0_ne_zero
        (Z3E hrho)
    _ = Cardinal.continuum := Cardinal.aleph0_power_aleph0
theorem Z6L {c : Za5}
    (T : CoherentTraceSystem c) (rho : Ordinal)
    (hrho : rho < TraceHeight) (hcode : T.Z7U rho) :
    Cardinal.mk (T.level rho) <= Cardinal.continuum :=
  (Cardinal.mk_le_of_injective hcode).trans
    (Z48 hrho)
theorem Z6j {alpha iota : Type} (f : iota -> Set alpha)
    (hiota : Cardinal.mk iota <= Cardinal.aleph 1)
    (hpiece : ∀ i, Cardinal.mk (f i) <= Cardinal.continuum) :
    Cardinal.mk (⋃ i, f i) <= Cardinal.continuum := by
  have hsup : (⨆ i, Cardinal.mk (f i)) <= Cardinal.continuum := by
    exact ciSup_le' hpiece
  calc
    Cardinal.mk (⋃ i, f i) <= Cardinal.mk iota * ⨆ i, Cardinal.mk (f i) :=
      Cardinal.mk_iUnion_le f
    _ <= Cardinal.mk iota * Cardinal.continuum :=
      mul_le_mul_right hsup (Cardinal.mk iota)
    _ <= Cardinal.aleph 1 * Cardinal.continuum :=
      mul_le_mul_left hiota _
    _ = Cardinal.continuum := Cardinal.mul_eq_right Cardinal.aleph0_le_continuum
      Cardinal.aleph_one_le_continuum
      (Cardinal.aleph0_pos.trans Cardinal.aleph0_lt_aleph_one).ne'
theorem Z2f {c : Za5}
    (T : CoherentTraceSystem c) (hend : T.Z8K)
    (hstop : ∀ (rho : Ordinal) (a : T.level rho), rho < TraceHeight →
      ¬ Nonempty (TraceCandidate c (T.levelTracePrefix rho a))) :
    ∃ a : TraceCarrier, T.height a = TraceHeight := by
  by_contra hfull
  push Not at hfull
  have hshort (a : TraceCarrier) : T.height a < TraceHeight :=
    lt_of_le_of_ne (T.height_le a) (hfull a)
  let levels : TraceHeight.ToType -> Set TraceCarrier := fun eta =>
    T.level eta.toOrd
  have hcover : (Set.univ : Set TraceCarrier) ⊆ Set.iUnion levels := by
    intro a _
    let eta : TraceHeight.ToType :=
      Ordinal.ToType.mk ⟨T.height a, hshort a⟩
    apply Set.mem_iUnion.mpr
    refine ⟨eta, ?_⟩
    change T.height a = eta.toOrd
    simp [eta]
  have hunion : Cardinal.mk (Set.iUnion levels) <= Cardinal.continuum := by
    apply Z6j levels
    · exact Z4O.le
    · intro eta
      have heta : (eta.toOrd : Ordinal) < TraceHeight :=
        Set.mem_Iio.mp eta.toOrd.2
      exact Z6L T eta.toOrd heta
        (T.Z4h hend hstop eta.toOrd heta)
  have hcarrier : Cardinal.mk TraceCarrier <= Cardinal.continuum := by
    calc
      Cardinal.mk TraceCarrier = Cardinal.mk (Set.univ : Set TraceCarrier) := by simp
      _ <= Cardinal.mk (Set.iUnion levels) :=
        Cardinal.mk_le_mk_of_subset hcover
      _ <= Cardinal.continuum := hunion
  rw [Z9q] at hcarrier
  exact (not_lt_of_ge hcarrier) (Order.lt_succ Cardinal.continuum)
theorem Z2C {c : Za5}
    (T : CoherentTraceSystem c) (hend : T.Z8K)
    (hstop : ∀ (rho : Ordinal) (a : T.level rho), rho < TraceHeight →
      ¬ Nonempty (TraceCandidate c (T.levelTracePrefix rho a))) :
    ∃ (a : TraceCarrier) (p : TracePrefix a),
      p.length = TraceHeight ∧ p.EndhomogeneousTo c := by
  obtain ⟨a, ha⟩ := Z2f T hend hstop
  let aLevel : T.level TraceHeight := ⟨a, ha⟩
  exact ⟨a, T.levelTracePrefix TraceHeight aLevel, rfl,
    T.Z3Q hend TraceHeight aLevel⟩
end P593.TripleSystem.TriangleHost.ErdosRado
end
section
namespace P593
namespace TripleSystem
namespace TriangleHost
namespace ErdosRado
open scoped Cardinal Ordinal
universe u
noncomputable section
noncomputable def endColor {a : TraceCarrier}
    (p : TracePrefix a) (c : Za5) : p.length.ToType -> Nat :=
  fun x => c (tracePair (p.node x) a (p.Za2 x))
theorem Z1b
    {a : TraceCarrier} (p : TracePrefix a) (c : Za5)
    (hend : p.EndhomogeneousTo c) (A : Set p.length.ToType)
    (r : Pair TraceCarrier)
    (hr : (r.1 : Set TraceCarrier) ⊆ p.node '' A) :
    exists x, x ∈ A /\ c r = endColor p c x := by
  classical
  rcases Finset.card_eq_two.mp r.2 with ⟨x, y, hxy, hrxy⟩
  have hx : x ∈ (r.1 : Set TraceCarrier) := by
    rw [hrxy]
    simp
  have hy : y ∈ (r.1 : Set TraceCarrier) := by
    rw [hrxy]
    simp
  rcases hr hx with ⟨xi, hxiA, hxEq⟩
  rcases hr hy with ⟨zeta, hzetaA, hyEq⟩
  have hxi_zeta : xi ≠ zeta := by
    intro h
    apply hxy
    calc
      x = p.node xi := hxEq.symm
      _ = p.node zeta := by rw [h]
      _ = y := hyEq
  rcases lt_or_gt_of_ne hxi_zeta with hlt | hgt
  · refine ⟨xi, hxiA, ?_⟩
    have hr_eq : r = tracePair (p.node xi) (p.node zeta)
        (ne_of_lt (p.ZaC hlt)) := by
      apply Subtype.ext
      rw [hrxy]
      simp [tracePair, hxEq, hyEq]
    rw [hr_eq]
    simpa [endColor] using hend hlt
  · refine ⟨zeta, hzetaA, ?_⟩
    have hr_eq : r = tracePair (p.node zeta) (p.node xi)
        (ne_of_lt (p.ZaC hgt)) := by
      apply Subtype.ext
      rw [hrxy]
      ext z
      simp [tracePair, hxEq, hyEq, or_comm]
    rw [hr_eq]
    simpa [endColor] using hend hgt
theorem Z1c
    {a : TraceCarrier} (p : TracePrefix a) (c : Za5)
    (hend : p.EndhomogeneousTo c) (A : Set p.length.ToType) (n : Nat)
    (hconstant : forall x, x ∈ A -> endColor p c x = n) :
    Z9a c (p.node '' A) := by
  intro r s hr hs
  rcases Z1b p c hend A r hr with
    ⟨xi, hxiA, hrc⟩
  rcases Z1b p c hend A s hs with
    ⟨zeta, hzetaA, hsc⟩
  calc
    c r = endColor p c xi := hrc
    _ = n := hconstant xi hxiA
    _ = endColor p c zeta := (hconstant zeta hzetaA).symm
    _ = c s := hsc.symm
theorem Z93
    {a : TraceCarrier} (p : TracePrefix a) (A : Set p.length.ToType) :
    Cardinal.mk (p.node '' A) = Cardinal.mk A :=
  Cardinal.mk_image_eq p.Za1
theorem Z4t {gamma : Type u} (f : gamma -> Nat)
    (hgamma : Cardinal.aleph0 < Cardinal.mk gamma) :
    exists n : Nat, Cardinal.aleph0 < Cardinal.mk {x : gamma | f x = n} := by
  letI : Uncountable gamma := Cardinal.aleph0_lt_mk_iff.mp hgamma
  let g : gamma -> ULift.{u} Nat := fun x => ULift.up (f x)
  have hg : Cardinal.mk (ULift.{u} Nat) < Cardinal.mk gamma := by
    rw [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0]
    exact hgamma
  obtain ⟨⟨n⟩, hn⟩ := Cardinal.exists_uncountable_fiber g hg
  have heq : g ⁻¹' ({ULift.up n} : Set (ULift.{u} Nat)) =
      {x : gamma | f x = n} := by
    ext x
    simp [g]
  rw [heq] at hn
  exact ⟨n, Cardinal.aleph0_lt_mk_iff.mpr hn⟩
theorem Z3h
    {a : TraceCarrier} (p : TracePrefix a) (c : Za5)
    (hfull : p.length = TraceHeight) :
    exists n : Nat, exists A : Set p.length.ToType,
      Cardinal.aleph0 < Cardinal.mk A /\
        forall x, x ∈ A -> endColor p c x = n := by
  have huncountable : Cardinal.aleph0 < Cardinal.mk p.length.ToType := by
    rw [hfull, Z9V, Cardinal.succ_aleph0]
    exact Cardinal.aleph0_lt_aleph_one
  obtain ⟨n, hn⟩ := Z4t (endColor p c) huncountable
  refine ⟨n, {x | endColor p c x = n}, ?_, ?_⟩
  · simpa using hn
  · intro x hx
    simpa using hx
theorem Zw
    {a : TraceCarrier} (p : TracePrefix a) (c : Za5)
    (hfull : p.length = TraceHeight) (hend : p.EndhomogeneousTo c) :
    exists H : Set TraceCarrier,
      Cardinal.aleph0 < Cardinal.mk H /\ Z9a c H := by
  obtain ⟨n, A, hA, hconstant⟩ :=
    Z3h p c hfull
  refine ⟨p.node '' A, ?_, ?_⟩
  · rw [Z93]
    exact hA
  · exact Z1c
      p c hend A n hconstant
theorem Z5h
    (c : Pair ErdosRadoCarrier -> Nat)
    (htrace : exists H : Set TraceCarrier,
      Cardinal.aleph0 < Cardinal.mk H /\
        Z9a
          (Z8L erdosRadoCarrierEquivTraceCarrier c) H) :
    exists K : Set ErdosRadoCarrier,
      Cardinal.aleph0 < Cardinal.mk K /\ Z9a c K := by
  rcases htrace with ⟨H, hHcard, hHhom⟩
  refine ⟨erdosRadoCarrierEquivTraceCarrier.symm '' H, ?_, ?_⟩
  · rw [Z75 erdosRadoCarrierEquivTraceCarrier.symm H]
    exact hHcard
  · exact Z57
      erdosRadoCarrierEquivTraceCarrier c H hHhom
theorem Zk
    (c : Pair ErdosRadoCarrier -> Nat)
    (htrace : exists (a : TraceCarrier) (p : TracePrefix a),
      p.length = TraceHeight /\
        p.EndhomogeneousTo
          (Z8L erdosRadoCarrierEquivTraceCarrier c)) :
    exists K : Set ErdosRadoCarrier,
      Cardinal.aleph0 < Cardinal.mk K /\ Z9a c K := by
  rcases htrace with ⟨a, p, hfull, hend⟩
  apply Z5h c
  exact Zw
    p (Z8L erdosRadoCarrierEquivTraceCarrier c) hfull hend
def Z29 : Prop :=
  forall c : Pair ErdosRadoCarrier -> Nat,
    exists (a : TraceCarrier) (p : TracePrefix a),
      p.length = TraceHeight /\
        p.EndhomogeneousTo
          (Z8L erdosRadoCarrierEquivTraceCarrier c)
def Z1n : Prop :=
  forall c : Pair ErdosRadoCarrier -> Nat,
    exists a : TraceCarrier, exists F : TracePrefix.LimitChain a TraceHeight,
      forall eta : TraceHeight.ToType,
        (F.stage eta).EndhomogeneousTo
          (Z8L erdosRadoCarrierEquivTraceCarrier c)
theorem Zo
    (hsystem : ∀ d : Za5,
      ∃ T : CoherentTraceSystem d, T.Z8K ∧
        ∀ (ρ : Ordinal) (a : T.level ρ), ρ < TraceHeight →
          ¬ Nonempty (TraceCandidate d (T.levelTracePrefix ρ a))) :
    Z1n := by
  intro c
  let d : Za5 :=
    Z8L erdosRadoCarrierEquivTraceCarrier c
  obtain ⟨T, hend, hstop⟩ := hsystem d
  obtain ⟨a, p, hp, hpEnd⟩ :=
    Z2C T hend hstop
  let hheight : TraceHeight ≤ p.length := hp.ge
  refine ⟨a, TracePrefix.LimitChain.ofPrefix p TraceHeight hheight, ?_⟩
  intro η
  exact hpEnd.ZbT
    ((le_of_lt (Set.mem_Iio.mp η.toOrd.2)).trans hheight)
theorem ZB
    (hchain : Z1n) :
    Z29 := by
  have hlimit : Order.IsSuccLimit.{1} TraceHeight :=
    Cardinal.isSuccLimit_ord (Order.le_succ (Cardinal.aleph0))
  intro c
  rcases hchain c with ⟨a, F, hend⟩
  refine ⟨a, F.limitPrefix hlimit le_rfl, rfl, ?_⟩
  exact F.Z55 hlimit le_rfl
    (Z8L erdosRadoCarrierEquivTraceCarrier c) hend
theorem Zf
    (htrace : Z29) :
    Z2m := by
  intro c
  exact Zk
    c (htrace c)
theorem Zh
    (htrace : Z29) :
    Z7S ErdosRadoCarrier :=
  ZQ
    (Zf htrace)
end
end ErdosRado
end TriangleHost
end TripleSystem
end P593
end
section
namespace P593.TripleSystem.TriangleHost.ErdosRado
theorem Z1u :
    Z1n :=
  Zo
    TraceIteration.Z1F
theorem Z2g :
    Z29 :=
  ZB
    Z1u
theorem Z2U :
    Z7S ErdosRadoCarrier :=
  Zh
    Z2g
end P593.TripleSystem.TriangleHost.ErdosRado
end
section
namespace P593
universe u v
namespace TripleSystem
variable {V : Type u} {E : Type v} (F : TripleSystem V E)
def Z9z (S : Set E) : Set V :=
  {x | ∃ e : E, e ∈ S ∧ F.Inc x e}
theorem Z6M {S : Set E} (hS : S.Finite) :
    (F.Z9z S).Finite := by
  induction S, hS using Set.Finite.induction_on with
  | empty =>
      simp [Z9z]
  | insert hnotmem hfinite ih =>
      rename_i e S
      rw [show F.Z9z (insert e S) =
        {x : V | F.Inc x e} ∪ F.Z9z S by
          ext x
          simp [Z9z]]
      exact (Set.finite_of_ncard_ne_zero (by
        rw [F.edge_ncard e]
        decide)).union ih
abbrev ZaR (S : Set E) := F.Z9z S
def Z96 (S : Set E) : TripleSystem (F.ZaR S) S where
  Inc x e := F.Inc x.1 e.1
  edge_ncard := by
    intro e
    change Set.ncard {x : F.ZaR S |
      (x : V) ∈ {y : V | F.Inc y e.1}} = 3
    rw [Set.ncard_subtype]
    have hsubset : {x : V | F.Inc x e.1} ⊆
        F.Z9z S := by
      intro x hx
      exact ⟨e.1, e.2, hx⟩
    change Set.ncard ({x : V | F.Inc x e.1} ∩ F.Z9z S) = 3
    rw [Set.inter_eq_left.mpr hsubset]
    exact F.edge_ncard e.1
  simple := by
    intro e d h
    apply Subtype.ext
    apply F.simple
    ext x
    constructor
    · intro hxe
      let x' : F.ZaR S := ⟨x, e.1, e.2, hxe⟩
      have hx := Set.ext_iff.mp h x'
      exact hx.mp hxe
    · intro hxd
      let x' : F.ZaR S := ⟨x, d.1, d.2, hxd⟩
      have hx := Set.ext_iff.mp h x'
      exact hx.mpr hxd
@[simp]
theorem Z7P (S : Set E) (x : F.ZaR S) (e : S) :
    (F.Z96 S).Inc x e ↔ F.Inc x.1 e.1 :=
  Iff.rfl
end TripleSystem
end P593
end
section
namespace P593
universe u v
namespace TripleSystem
variable {V : Type u} {E : Type v} (F : TripleSystem V E)
def Z7f : Prop :=
  ∀ x, ¬F.IsIsolated x
theorem Z7o {x : V} {e : E} (hxe : F.Inc x e) :
    ¬F.IsIsolated x := by
  intro hx
  exact hx e hxe
theorem Z4G {x : V} :
    ¬F.IsIsolated x ↔ ∃ e, F.Inc x e := by
  classical
  simp [IsIsolated]
abbrev NonIsolatedPoint :=
  {x : V // ¬F.IsIsolated x}
def isolatedReduction : TripleSystem F.NonIsolatedPoint E where
  Inc x e := F.Inc x.1 e
  edge_ncard := by
    intro e
    change Set.ncard {x : F.NonIsolatedPoint |
      (x : V) ∈ {y : V | F.Inc y e}} = 3
    rw [Set.ncard_subtype]
    have hsubset : {x : V | F.Inc x e} ⊆ {x : V | ¬F.IsIsolated x} := by
      intro x hx
      exact F.Z7o hx
    rw [Set.inter_eq_left.mpr hsubset]
    exact F.edge_ncard e
  simple := by
    intro e f hef
    apply F.simple
    ext x
    constructor
    · intro hxe
      let x' : F.NonIsolatedPoint := ⟨x, F.Z7o hxe⟩
      have hiff := Set.ext_iff.mp hef x'
      exact hiff.mp hxe
    · intro hxf
      let x' : F.NonIsolatedPoint := ⟨x, F.Z7o hxf⟩
      have hiff := Set.ext_iff.mp hef x'
      exact hiff.mpr hxf
@[simp]
theorem Z6P {x : F.NonIsolatedPoint} {e : E} :
    F.isolatedReduction.Inc x e ↔ F.Inc x.1 e :=
  Iff.rfl
theorem Z5z (hlinear : F.Linear) :
    F.isolatedReduction.Linear := by
  intro e f x y hef hxe hxf hye hyf
  apply Subtype.ext
  exact hlinear hef hxe hxf hye hyf
theorem Z2A :
    F.isolatedReduction.Z7f := by
  intro x hx
  exact x.property hx
end TripleSystem
end P593
end
section
namespace P593
universe u v u' v' u'' v''
namespace TripleSystem
variable {V : Type u} {E : Type v}
variable {V' : Type u'} {E' : Type v'}
variable {V'' : Type u''} {E'' : Type v''}
structure Iso (F : TripleSystem V E) (F' : TripleSystem V' E') where
  vertexEquiv : V ≃ V'
  edgeEquiv : E ≃ E'
  map_inc_iff : ∀ x e,
    F.Inc x e ↔ F'.Inc (vertexEquiv x) (edgeEquiv e)
namespace Iso
variable {F : TripleSystem V E}
variable {F' : TripleSystem V' E'}
variable {F'' : TripleSystem V'' E''}
def symm (f : Iso F F') : Iso F' F where
  vertexEquiv := f.vertexEquiv.symm
  edgeEquiv := f.edgeEquiv.symm
  map_inc_iff := by
    intro x e
    simpa using
      (f.map_inc_iff (f.vertexEquiv.symm x) (f.edgeEquiv.symm e)).symm
end Iso
end TripleSystem
end P593
end
-- ARISTOTLE_TARGET G1
section
namespace P593
namespace SimpleGraph
universe u
variable {V : Type u}
def bridgeEdges (G : _root_.SimpleGraph V) : Set (Sym2 V) :=
  {e | e ∈ G.edgeSet ∧ G.IsBridge e}
theorem Z32
    (G : _root_.SimpleGraph V) {u v : V}
    (huv : G.Adj u v)
    (hv : ∀ ⦃w : V⦄, G.Adj v w → w = u) :
    G.IsBridge s(u, v) := by
  rw [_root_.SimpleGraph.isBridge_iff]
  intro hreach
  have hr := hreach.symm
  rw [_root_.SimpleGraph.reachable_eq_reflTransGen] at hr
  rcases hr.cases_head with h | ⟨w, hw, -⟩
  · exact huv.ne' h
  · rw [_root_.SimpleGraph.deleteEdges_adj] at hw
    obtain ⟨hgvw, hnot⟩ := hw
    have hwu : w = u := hv hgvw
    subst w
    exact hnot (by simp [Sym2.eq_swap])
end SimpleGraph
end P593
end
-- ARISTOTLE_TARGET B2
section
namespace P593
universe u v
namespace TripleSystem
variable {V : Type u} {E : Type v} (F : TripleSystem V E)
def incidenceRel : V ⊕ E → V ⊕ E → Prop
  | .inl x, .inr e => F.Inc x e
  | _, _ => False
def levi : _root_.SimpleGraph (V ⊕ E) :=
  _root_.SimpleGraph.fromRel F.incidenceRel
@[simp]
theorem Z7d {x : V} {e : E} :
    F.levi.Adj (.inl x) (.inr e) ↔ F.Inc x e := by
  simp [levi, incidenceRel]
@[simp]
theorem Z7n {x : V} {e : E} :
    F.levi.Adj (.inr e) (.inl x) ↔ F.Inc x e := by
  simp [levi, incidenceRel]
@[simp]
theorem Z5r {x y : V} :
    ¬F.levi.Adj (.inl x) (.inl y) := by
  simp [levi, incidenceRel]
@[simp]
theorem Z65 {e f : E} :
    ¬F.levi.Adj (.inr e) (.inr f) := by
  simp [levi, incidenceRel]
theorem Z5A (e : E) :
    (F.levi.neighborSet (.inr e)).ncard = 3 := by
  rw [show F.levi.neighborSet (.inr e) =
    Set.image (fun x : V => Sum.inl x) {x : V | F.Inc x e} by
      ext x
      cases x <;> simp +decide]
  rw [Set.ncard_image_of_injective _ Sum.inl_injective]
  exact F.Zaa e
end TripleSystem
end P593
end
section
namespace P593
universe u v
namespace TripleSystem
variable {V : Type u} {E : Type v} (F : TripleSystem V E)
def BridgeAtEveryEdge : Prop :=
  ∀ e : E, ∃ x : V,
    s(Sum.inl x, Sum.inr e) ∈ SimpleGraph.bridgeEdges F.levi
def EvenBergeCycles : Prop :=
  ∀ ⦃z : V ⊕ E⦄ (c : F.levi.Walk z z), c.IsCycle → 4 ∣ c.length
def Intrinsic : Prop :=
  F.Linear ∧ F.BridgeAtEveryEdge ∧ F.EvenBergeCycles
end TripleSystem
end P593
end
-- ARISTOTLE_ISO_TARGET I1
-- ARISTOTLE_ISO_TARGET I2
-- ARISTOTLE_ISO_TARGET I3
-- ARISTOTLE_ISO_TARGET I4
-- ARISTOTLE_ISO_TARGET I5
section
namespace P593
universe u v u' v'
namespace TripleSystem
namespace Iso
variable {V : Type u} {E : Type v}
variable {V' : Type u'} {E' : Type v'}
variable {F : TripleSystem V E} {F' : TripleSystem V' E'}
def leviIso (f : Iso F F') : F.levi ≃g F'.levi where
  toEquiv := Equiv.sumCongr f.vertexEquiv f.edgeEquiv
  map_rel_iff' := by
    rintro (x | e) (y | d) <;> simp [f.map_inc_iff]
theorem Zbi (f : Iso F F') : F.Linear ↔ F'.Linear := by
  constructor
  · intro h e' d' x' y' hed hx_e hx_d hy_e hy_d
    let e := f.edgeEquiv.symm e'
    let d := f.edgeEquiv.symm d'
    let x := f.vertexEquiv.symm x'
    let y := f.vertexEquiv.symm y'
    have hed' : e ≠ d := by
      intro heq
      apply hed
      simpa [e, d] using congrArg f.edgeEquiv heq
    have hxy : x = y := h hed'
      ((f.map_inc_iff x e).mpr (by simpa [x, e] using hx_e))
      ((f.map_inc_iff x d).mpr (by simpa [x, d] using hx_d))
      ((f.map_inc_iff y e).mpr (by simpa [y, e] using hy_e))
      ((f.map_inc_iff y d).mpr (by simpa [y, d] using hy_d))
    simpa [x, y] using congrArg f.vertexEquiv hxy
  · intro h e d x y hed hx_e hx_d hy_e hy_d
    have hed' : f.edgeEquiv e ≠ f.edgeEquiv d := f.edgeEquiv.injective.ne hed
    exact f.vertexEquiv.injective <| h hed'
      ((f.map_inc_iff x e).mp hx_e) ((f.map_inc_iff x d).mp hx_d)
      ((f.map_inc_iff y e).mp hy_e) ((f.map_inc_iff y d).mp hy_d)
private theorem Z7z {A B : Type*}
    {P : _root_.SimpleGraph A} {Q : _root_.SimpleGraph B}
    (g : P ≃g Q) (a b : A) :
    P.IsBridge s(a, b) ↔ Q.IsBridge s(g a, g b) := by
  let gd : P.deleteEdges {s(a, b)} ≃g
      Q.deleteEdges {s(g a, g b)} :=
    { toEquiv := g.toEquiv
      map_rel_iff' := by
        intro x y
        simp [g.map_adj_iff] }
  change (¬(P.deleteEdges {s(a, b)}).Reachable a b) ↔
    ¬(Q.deleteEdges {s(g a, g b)}).Reachable (g a) (g b)
  exact not_congr gd.reachable_iff.symm
theorem Z6A (f : Iso F F') :
    F.BridgeAtEveryEdge ↔ F'.BridgeAtEveryEdge := by
  let g := leviIso f
  constructor
  · intro h e'
    obtain ⟨x, hx⟩ := h (f.edgeEquiv.symm e')
    refine ⟨f.vertexEquiv x, ?_⟩
    rcases hx with ⟨hadj, hbridge⟩
    constructor
    · simpa [g, leviIso] using g.map_mem_edgeSet_iff.mpr hadj
    · simpa [g, leviIso] using
        (Z7z g (Sum.inl x)
          (Sum.inr (f.edgeEquiv.symm e'))).mp hbridge
  · intro h e
    obtain ⟨x', hx⟩ := h (f.edgeEquiv e)
    refine ⟨f.vertexEquiv.symm x', ?_⟩
    rcases hx with ⟨hadj, hbridge⟩
    constructor
    · have hm := g.symm.map_mem_edgeSet_iff.mpr hadj
      simpa [g, leviIso] using hm
    · have hb := (Z7z g.symm (Sum.inl x')
          (Sum.inr (f.edgeEquiv e))).mp hbridge
      simpa [g, leviIso] using hb
theorem Z7F (f : Iso F F') :
    F.EvenBergeCycles ↔ F'.EvenBergeCycles := by
  let g := leviIso f
  constructor
  · intro h z c hc
    let d := c.map g.symm.toHom
    have hd : d.IsCycle := hc.map g.symm.injective
    have hdiv := h d hd
    simpa [d, _root_.SimpleGraph.Walk.length_map] using hdiv
  · intro h z c hc
    let d := c.map g.toHom
    have hd : d.IsCycle := hc.map g.injective
    have hdiv := h d hd
    simpa [d, _root_.SimpleGraph.Walk.length_map] using hdiv
theorem Zap (f : Iso F F') : F.Intrinsic ↔ F'.Intrinsic := by
  simp only [Intrinsic, Zbi f, Z6A f,
    Z7F f]
end Iso
end TripleSystem
end P593
end
section
namespace P593
universe u v w x
namespace TripleSystem
namespace Embedding
variable {V : Type u} {E : Type v} {W : Type w} {D : Type x}
variable {F : TripleSystem V E} {H : TripleSystem W D}
def Zbu (f : F.Embedding H) : Set D := Set.range f.edge
noncomputable def edgeImageEdgeEquiv (f : F.Embedding H) : E ≃ f.Zbu :=
  Equiv.ofBijective (fun e => ⟨f.edge e, ⟨e, rfl⟩⟩) (by
    constructor
    · intro e e' h
      exact f.Z9P (congrArg Subtype.val h)
    · intro d
      rcases d.property with ⟨e, he⟩
      refine ⟨e, ?_⟩
      exact Subtype.ext he)
noncomputable def edgeImageVertexEquiv (f : F.Embedding H)
    (hF : F.Z7f) : V ≃ H.ZaR f.Zbu := by
  let phi : V → H.ZaR f.Zbu := fun x =>
    ⟨f.vertex x, by
      rcases F.Z4G.mp (hF x) with ⟨e, hxe⟩
      change ∃ d : D, d ∈ f.Zbu ∧ H.Inc (f.vertex x) d
      refine ⟨f.edge e, ⟨e, rfl⟩, ?_⟩
      have hset := Set.ext_iff.mp (f.map_edge e) (f.vertex x)
      exact hset.mp ⟨x, hxe, rfl⟩⟩
  apply Equiv.ofBijective phi
  constructor
  · intro x y hxy
    exact f.vertex.injective (congrArg Subtype.val hxy)
  · intro y
    rcases y.property with ⟨d, ⟨e, rfl⟩, hye⟩
    have hset := Set.ext_iff.mp (f.map_edge e) y.1
    rcases hset.mpr hye with ⟨x, hxe, hxy⟩
    refine ⟨x, ?_⟩
    exact Subtype.ext hxy
noncomputable def imageEdgeRestrictionIso (f : F.Embedding H)
    (hF : F.Z7f) :
    Iso F (H.Z96 f.Zbu) where
  vertexEquiv := f.edgeImageVertexEquiv hF
  edgeEquiv := f.edgeImageEdgeEquiv
  map_inc_iff := by
    intro x e
    change F.Inc x e ↔ H.Inc (f.vertex x) (f.edge e)
    have hset := Set.ext_iff.mp (f.map_edge e) (f.vertex x)
    constructor
    · intro hxe
      exact hset.mp ⟨x, hxe, rfl⟩
    · intro hxe
      rcases hset.mpr hxe with ⟨y, hye, hyx⟩
      have hyx' : y = x := f.vertex.injective hyx
      simpa [hyx'] using hye
theorem Z4M (f : F.Embedding H)
    (hF : F.Z7f) (hlinear : F.Linear) :
    (H.Z96 f.Zbu).Linear :=
  (f.imageEdgeRestrictionIso hF).Zbi.mp hlinear
end Embedding
end TripleSystem
end P593
end
section
namespace P593
universe u v w x
namespace TripleSystem
namespace Embedding
variable {V : Type u} {E : Type v} {W : Type w} {D : Type x}
variable {F : TripleSystem V E} {H : TripleSystem W D}
theorem Z46
    (f : F.Embedding H) (hlinear : H.Linear) : F.Linear := by
  intro e d x y hed hxe hxd hye hyd
  apply f.vertex.injective
  apply hlinear (f.Z9P.ne hed)
  · have hset := Set.ext_iff.mp (f.map_edge e) (f.vertex x)
    exact hset.mp ⟨x, hxe, rfl⟩
  · have hset := Set.ext_iff.mp (f.map_edge d) (f.vertex x)
    exact hset.mp ⟨x, hxd, rfl⟩
  · have hset := Set.ext_iff.mp (f.map_edge e) (f.vertex y)
    exact hset.mp ⟨y, hye, rfl⟩
  · have hset := Set.ext_iff.mp (f.map_edge d) (f.vertex y)
    exact hset.mp ⟨y, hyd, rfl⟩
end Embedding
end TripleSystem
end P593
end
section
namespace P593
universe u v
namespace TripleSystem
variable {V : Type u} {E : Type v} {W : Type u} {D : Type v}
variable {F : TripleSystem V E} {H : TripleSystem W D}
theorem ZH
    [DecidableEq W]
    (hnotlinear : ¬ F.Linear) (hHlinear : H.Linear)
    (hchi : Cardinal.aleph0 < H.chromaticCardinal) : ¬ F.IsObligatory := by
  intro hF
  rcases hF W D H hchi with ⟨f⟩
  exact hnotlinear (f.Z46 hHlinear)
end TripleSystem
end P593
end
section
namespace P593
universe u v w z
namespace TripleSystem
variable {V : Type u} {E : Type v} {W : Type w} {D : Type z}
def Z8H (F : TripleSystem V E) (G : TripleSystem W D) :
    V ⊕ W → E ⊕ D → Prop
  | .inl x, .inl e => F.Inc x e
  | .inr y, .inr d => G.Inc y d
  | .inl _, .inr _ => False
  | .inr _, .inl _ => False
def Za7 (F : TripleSystem V E) (G : TripleSystem W D) :
    TripleSystem (V ⊕ W) (E ⊕ D) where
  Inc := Z8H F G
  edge_ncard := by
    rintro (e | d)
    · have hset :
          {x : V ⊕ W | Z8H F G x (.inl e)} =
            Sum.inl '' F.edgeSet e := by
        ext x
        cases x <;> simp [Z8H, edgeSet]
      rw [hset, Set.ncard_image_of_injective _ Sum.inl_injective,
        F.Zaa]
    · have hset :
          {x : V ⊕ W | Z8H F G x (.inr d)} =
            Sum.inr '' G.edgeSet d := by
        ext x
        cases x <;> simp [Z8H, edgeSet]
      rw [hset, Set.ncard_image_of_injective _ Sum.inr_injective,
        G.Zaa]
  simple := by
    intro a b hab
    cases a with
    | inl e =>
        cases b with
        | inl f =>
            apply congrArg Sum.inl
            apply F.simple
            ext x
            have hx := Set.ext_iff.mp hab (Sum.inl x)
            simpa [Z8H] using hx
        | inr d =>
            exfalso
            have hne : Set.ncard {x : V | F.Inc x e} ≠ 0 := by
              rw [F.edge_ncard e]
              decide
            obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero hne
            have hmem := (Set.ext_iff.mp hab (Sum.inl x)).mp hx
            simp [Z8H] at hmem
    | inr d =>
        cases b with
        | inl e =>
            exfalso
            have hne : Set.ncard {y : W | G.Inc y d} ≠ 0 := by
              rw [G.edge_ncard d]
              decide
            obtain ⟨y, hy⟩ := Set.nonempty_of_ncard_ne_zero hne
            have hmem := (Set.ext_iff.mp hab (Sum.inr y)).mp hy
            simp [Z8H] at hmem
        | inr c =>
            apply congrArg Sum.inr
            apply G.simple
            ext y
            have hy := Set.ext_iff.mp hab (Sum.inr y)
            simpa [Z8H] using hy
@[simp]
theorem Z5k (F : TripleSystem V E) (G : TripleSystem W D)
    (x : V) (e : E) :
    (F.Za7 G).Inc (.inl x) (.inl e) ↔ F.Inc x e :=
  Iff.rfl
@[simp]
theorem Z5l (F : TripleSystem V E) (G : TripleSystem W D)
    (y : W) (d : D) :
    (F.Za7 G).Inc (.inr y) (.inr d) ↔ G.Inc y d :=
  Iff.rfl
@[simp]
theorem Z4l (F : TripleSystem V E) (G : TripleSystem W D)
    (x : V) (d : D) :
    ¬(F.Za7 G).Inc (.inl x) (.inr d) := by
  simp [Za7, Z8H]
@[simp]
theorem Z4m (F : TripleSystem V E) (G : TripleSystem W D)
    (y : W) (e : E) :
    ¬(F.Za7 G).Inc (.inr y) (.inl e) := by
  simp [Za7, Z8H]
@[simp]
theorem Z5i (F : TripleSystem V E) (G : TripleSystem W D)
    (e : E) :
    (F.Za7 G).edgeSet (.inl e) = Sum.inl '' F.edgeSet e := by
  ext x
  cases x <;> simp [edgeSet, Za7, Z8H]
@[simp]
theorem Z5j (F : TripleSystem V E) (G : TripleSystem W D)
    (d : D) :
    (F.Za7 G).edgeSet (.inr d) = Sum.inr '' G.edgeSet d := by
  ext x
  cases x <;> simp [edgeSet, Za7, Z8H]
end TripleSystem
end P593
end
section
namespace P593
open scoped Cardinal
universe u v
namespace TripleSystem
variable {V W X : Type u} {E D A : Type v}
section Restriction
variable (H : TripleSystem W D) (S : Set W)
abbrev Z9D := {d : D // H.edgeSet d ⊆ S}
def Z8j : TripleSystem S (H.Z9D S) where
  Inc x d := H.Inc x.1 d.1
  edge_ncard := by
    intro d
    have himage :
        ((fun x : S => (x : W)) ''
            {x : S | H.Inc x.1 d.1}) = H.edgeSet d.1 := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, d.2 hx⟩, hx, rfl⟩
    calc
      Set.ncard {x : S | H.Inc x.1 d.1} =
          Set.ncard ((fun x : S => (x : W)) ''
            {x : S | H.Inc x.1 d.1}) :=
        (Set.ncard_image_of_injective _ Subtype.val_injective).symm
      _ = Set.ncard (H.edgeSet d.1) := congrArg Set.ncard himage
      _ = 3 := H.Zaa d.1
  simple := by
    intro d₁ d₂ hedge
    apply Subtype.ext
    apply H.Z8n
    ext x
    constructor
    · intro hx
      have hxS : x ∈ S := d₁.2 hx
      have := Set.ext_iff.mp hedge ⟨x, hxS⟩
      exact this.mp hx
    · intro hx
      have hxS : x ∈ S := d₂.2 hx
      have := Set.ext_iff.mp hedge ⟨x, hxS⟩
      exact this.mpr hx
@[simp]
theorem Z6Q (x : S) (d : H.Z9D S) :
    (H.Z8j S).Inc x d ↔ H.Inc x.1 d.1 :=
  Iff.rfl
def Z4U : (H.Z8j S).Embedding H where
  vertex := ⟨Subtype.val, Subtype.val_injective⟩
  edge := Subtype.val
  map_edge := by
    intro d
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, d.2 hx⟩, hx, rfl⟩
abbrev Z9F (R : Set W) :
    TripleSystem (Rᶜ : Set W) (H.Z9D (Rᶜ : Set W)) :=
  H.Z8j (Rᶜ : Set W)
abbrev Z5Z (R : Set W) :
    (H.Z9F R).Embedding H :=
  H.Z4U (Rᶜ : Set W)
end Restriction
section ChromaticCardinal
variable (H : TripleSystem W D)
theorem Z6w (e : D) {x : W} (_hx : H.Inc x e) :
    ∃ y : W, H.Inc y e ∧ y ≠ x := by
  have hone : 1 < (H.edgeSet e).ncard := by
    rw [H.Zaa]
    decide
  exact Set.exists_ne_of_one_lt_ncard hone x
private theorem Z5a :
    {k : Cardinal.{u} | ∃ C : Type u, #C = k ∧
      ∃ c : W → C, H.IsProperColoring c}.Nonempty := by
  refine ⟨#W, W, rfl, id, ?_⟩
  intro e
  have hne : (H.edgeSet e).ncard ≠ 0 := by
    rw [H.Zaa]
    decide
  obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero hne
  obtain ⟨y, hy, hyx⟩ := H.Z6w e hx
  exact ⟨x, hx, y, hy, hyx.symm⟩
theorem Z1i :
    ∃ C : Type u, #C = H.chromaticCardinal ∧
      ∃ c : W → C, H.IsProperColoring c := by
  unfold chromaticCardinal
  exact csInf_mem (H.Z5a)
theorem Z4y {C : Type u} :
    H.chromaticCardinal ≤ #C ↔ ∃ c : W → C, H.IsProperColoring c := by
  constructor
  · intro hle
    obtain ⟨C₀, hC₀, c₀, hc₀⟩ :=
      H.Z1i
    have hcard : #C₀ ≤ #C := hC₀.trans_le hle
    obtain ⟨i⟩ : Nonempty (C₀ ↪ C) := by
      exact (Cardinal.lift_mk_le'.mp (by simpa using hcard))
    exact ⟨fun x => i (c₀ x), fun e => by
      obtain ⟨x, hx, y, hy, hxy⟩ := hc₀ e
      exact ⟨x, hx, y, hy, i.injective.ne hxy⟩⟩
  · rintro ⟨c, hc⟩
    unfold chromaticCardinal
    exact csInf_le' ⟨C, rfl, c, hc⟩
theorem Z3k
    (R : Set W) {C : Type u} (c : (Rᶜ : Set W) → C)
    (hc : (H.Z9F R).IsProperColoring c) :
    ∃ c' : W → (C ⊕ R), H.IsProperColoring c' := by
  classical
  let c' : W → (C ⊕ R) := fun x =>
    if hx : x ∈ R then Sum.inr ⟨x, hx⟩ else Sum.inl (c ⟨x, hx⟩)
  refine ⟨c', ?_⟩
  intro e
  by_cases hhit : ∃ x : W, H.Inc x e ∧ x ∈ R
  · obtain ⟨x, hxe, hxR⟩ := hhit
    obtain ⟨y, hye, hyx⟩ := H.Z6w e hxe
    refine ⟨x, hxe, y, hye, ?_⟩
    by_cases hyR : y ∈ R
    · rw [show c' x = Sum.inr ⟨x, hxR⟩ by simp [c', hxR],
          show c' y = Sum.inr ⟨y, hyR⟩ by simp [c', hyR]]
      intro heq
      exact hyx (congrArg (fun z : C ⊕ R => Sum.elim (fun _ => y) Subtype.val z) heq).symm
    · simp [c', hxR, hyR]
  · push Not at hhit
    let d : H.Z9D Rᶜ :=
      ⟨e, fun _ hx => hhit _ hx⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := hc d
    refine ⟨x.1, hx, y.1, hy, ?_⟩
    have hxR : x.1 ∉ R := x.2
    have hyR : y.1 ∉ R := y.2
    rw [show c' x.1 = Sum.inl (c x) by simp [c', hxR],
        show c' y.1 = Sum.inl (c y) by simp [c', hyR]]
    exact Sum.inl_injective.ne hxy
theorem Z1U
    (R : Set W) (hR : R.Finite)
    (hH : ℵ₀ < H.chromaticCardinal) :
    ℵ₀ < (H.Z9F R).chromaticCardinal := by
  by_contra hnot
  have hdel : (H.Z9F R).chromaticCardinal ≤ ℵ₀ :=
    le_of_not_gt hnot
  obtain ⟨C, hC, c, hc⟩ :=
    (H.Z9F R).Z1i
  obtain ⟨c', hc'⟩ := H.Z3k R c hc
  have hHsum : H.chromaticCardinal ≤ #(C ⊕ R) :=
    (H.Z4y).2 ⟨c', hc'⟩
  have hCcount : #C ≤ ℵ₀ := hC.trans_le hdel
  letI : Fintype R := hR.fintype
  have hRcount : #R ≤ ℵ₀ :=
    (Cardinal.lt_aleph0_of_finite R).le
  have hsum : #(C ⊕ R) ≤ ℵ₀ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_le_aleph0.2 ⟨hCcount, hRcount⟩
  exact hH.2 (hHsum.trans hsum)
end ChromaticCardinal
section DisjointEmbedding
variable {F : TripleSystem V E} {G : TripleSystem X A}
variable {H : TripleSystem W D}
def Embedding.Z5T
    (f : F.Embedding H) (g : G.Embedding H)
    (hdisj : ∀ x y, f.vertex x ≠ g.vertex y) :
    (F.Za7 G).Embedding H where
  vertex :=
    { toFun := Sum.elim f.vertex g.vertex
      inj' := by
        intro p q hpq
        cases p with
        | inl x =>
            cases q with
            | inl y => exact congrArg Sum.inl (f.vertex.injective hpq)
            | inr y => exact False.elim (hdisj x y hpq)
        | inr x =>
            cases q with
            | inl y => exact False.elim (hdisj y x hpq.symm)
            | inr y => exact congrArg Sum.inr (g.vertex.injective hpq) }
  edge := Sum.elim f.edge g.edge
  map_edge := by
    intro e
    cases e with
    | inl e =>
        rw [Z5i]
        rw [Set.image_image]
        change f.vertex '' F.edgeSet e = H.edgeSet (f.edge e)
        exact f.map_edge e
    | inr d =>
        rw [Z5j]
        rw [Set.image_image]
        change g.vertex '' G.edgeSet d = H.edgeSet (g.edge d)
        exact g.map_edge d
end DisjointEmbedding
section ObligatoryClosure
variable (F : TripleSystem V E) (G : TripleSystem X A)
theorem IsObligatory.Zao
    [Fintype V] [Fintype E] [Fintype X] [Fintype A]
    (hF : F.IsObligatory) (hG : G.IsObligatory) :
    (F.Za7 G).IsObligatory := by
  intro Y B _ H hH
  obtain ⟨f⟩ := hF Y B H hH
  let R : Set Y := Set.range f.vertex
  have hR : R.Finite := Set.finite_range f.vertex
  have hdelete : ℵ₀ < (H.Z9F R).chromaticCardinal :=
    H.Z1U R hR hH
  obtain ⟨g₀⟩ := hG (Rᶜ : Set Y) (H.Z9D (Rᶜ : Set Y))
    (H.Z9F R) hdelete
  let g : G.Embedding H := g₀.trans (H.Z5Z R)
  have hdisj : ∀ x y, f.vertex x ≠ g.vertex y := by
    intro x y heq
    have hy : (g.vertex y : Y) ∉ R := (g₀.vertex y).2
    exact hy ⟨x, heq⟩
  exact ⟨f.Z5T g hdisj⟩
end ObligatoryClosure
end TripleSystem
end P593
end
section
namespace P593
open scoped Cardinal
universe u v u' v'
namespace TripleSystem
namespace TriangleHostTransport
variable {V : Type u} {E : Type v} {V' : Type u'} {E' : Type v'}
def reindex (F : TripleSystem V E) (vertexEquiv : V ≃ V')
    (edgeEquiv : E ≃ E') : TripleSystem V' E' where
  Inc x e := F.Inc (vertexEquiv.symm x) (edgeEquiv.symm e)
  edge_ncard := by
    intro e
    let s : Set V' := {x | F.Inc (vertexEquiv.symm x) (edgeEquiv.symm e)}
    have hs : s = vertexEquiv '' F.edgeSet (edgeEquiv.symm e) := by
      ext x
      constructor
      · intro hx
        exact ⟨vertexEquiv.symm x, hx, vertexEquiv.apply_symm_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        simpa [s, TripleSystem.edgeSet] using hy
    change s.ncard = 3
    rw [hs, Set.ncard_image_of_injective _ vertexEquiv.injective]
    exact F.Zaa _
  simple := by
    intro e₁ e₂ h
    apply edgeEquiv.symm.injective
    apply F.Z8n
    ext x
    have hx := Set.ext_iff.mp h (vertexEquiv x)
    simpa [TripleSystem.edgeSet] using hx
def ZaW (κ : Type) [DecidableEq κ] :
    TripleSystem (ULift.{u} (TriangleHost.Pair κ))
      (ULift.{v} (TriangleHost.ZbI κ)) :=
  reindex (TriangleHost.system κ)
    (Equiv.ulift : ULift.{u} (TriangleHost.Pair κ) ≃ TriangleHost.Pair κ).symm
    (Equiv.ulift : ULift.{v} (TriangleHost.ZbI κ) ≃ TriangleHost.ZbI κ).symm
theorem Z8f (κ : Type) [DecidableEq κ] :
    (ZaW.{u, v} κ).Linear := by
  intro e f x y hef hxe hxf hye hyf
  apply ULift.ext
  apply TriangleHost.linear κ
  · intro hdown
    apply hef
    exact ULift.ext _ _ hdown
  · change (TriangleHost.system κ).Inc x.down e.down at hxe
    exact hxe
  · change (TriangleHost.system κ).Inc x.down f.down at hxf
    exact hxf
  · change (TriangleHost.system κ).Inc y.down e.down at hye
    exact hye
  · change (TriangleHost.system κ).Inc y.down f.down at hyf
    exact hyf
theorem Z2t
    (κ : Type) [DecidableEq κ]
    (hRamsey : TriangleHost.Z7S κ) :
    ¬ ∃ c : ULift.{u} (TriangleHost.Pair κ) → ULift.{u} ℕ,
      (ZaW.{u, v} κ).IsProperColoring c := by
  rintro ⟨c, hc⟩
  let d : TriangleHost.Pair κ → ℕ := fun p => (c (ULift.up p)).down
  apply TriangleHost.Z1d κ hRamsey d
  intro t
  rcases hc (ULift.up t) with ⟨x, hx, y, hy, hxy⟩
  refine ⟨x.down, ?_, y.down, ?_, ?_⟩
  · change (TriangleHost.system κ).Inc x.down t at hx
    exact hx
  · change (TriangleHost.system κ).Inc y.down t at hy
    exact hy
  · intro hdown
    apply hxy
    apply ULift.ext
    simpa [d] using hdown
theorem Z2h
    (κ : Type) [DecidableEq κ]
    (hRamsey : TriangleHost.Z7S κ) :
    ℵ₀ < (ZaW.{u, v} κ).chromaticCardinal := by
  by_contra hnot
  have hle : (ZaW.{u, v} κ).chromaticCardinal ≤ ℵ₀ :=
    le_of_not_gt hnot
  have hle' : (ZaW.{u, v} κ).chromaticCardinal ≤
      #(ULift.{u} ℕ) := by
    simpa using hle
  obtain ⟨c, hc⟩ :=
    ((ZaW.{u, v} κ).Z4y
      (C := ULift.{u} ℕ)).mp hle'
  exact Z2t.{u, v} κ hRamsey ⟨c, hc⟩
theorem ZO
    (F : TripleSystem V E) (hnotlinear : ¬ F.Linear)
    (κ : Type) [DecidableEq κ]
    (hRamsey : TriangleHost.Z7S κ) :
    ¬ F.IsObligatory := by
  letI : DecidableEq (TriangleHost.Pair κ) := inferInstance
  letI : DecidableEq (ULift.{u} (TriangleHost.Pair κ)) := inferInstance
  apply ZH
    (H := ZaW.{u, v} κ)
  · exact hnotlinear
  · exact Z8f.{u, v} κ
  · exact Z2h.{u, v} κ hRamsey
end TriangleHostTransport
end TripleSystem
end P593
end
section
namespace P593.TripleSystem
universe u v
theorem Z49
    {V : Type u} {E : Type v}
    (F : TripleSystem V E) (hnotlinear : ¬ F.Linear) :
    ¬ F.IsObligatory :=
  TriangleHostTransport.ZO
    F hnotlinear TriangleHost.ErdosRadoCarrier
      TriangleHost.ErdosRado.Z2U
end P593.TripleSystem
end
section
namespace P593
universe u v w
namespace SimpleGraph
variable {X : Type u} {V : Type v} {W : Type w}
variable {J : _root_.SimpleGraph X} {G : _root_.SimpleGraph V}
variable {H : _root_.SimpleGraph W}
structure NonInducedFactor (J : _root_.SimpleGraph X) (G : _root_.SimpleGraph V) where
  vertex : X ↪ V
  map_adj : ∀ {x y : X}, J.Adj x y → G.Adj (vertex x) (vertex y)
namespace NonInducedFactor
def toHom (f : NonInducedFactor J G) : J →g G where
  toFun := f.vertex
  map_rel' := f.map_adj
@[simp]
theorem Zb7 (f : NonInducedFactor J G) (x : X) : f.toHom x = f.vertex x := rfl
def toCopy (f : NonInducedFactor J G) : _root_.SimpleGraph.Copy J G where
  toHom := f.toHom
  injective' := f.vertex.injective
@[simp]
theorem ZaP (f : NonInducedFactor J G) (x : X) : f.toCopy x = f.vertex x := rfl
def ofCopy (f : _root_.SimpleGraph.Copy J G) : NonInducedFactor J G where
  vertex := f.toEmbedding
  map_adj := f.toHom.map_adj
@[simp]
theorem Zav (f : _root_.SimpleGraph.Copy J G) (x : X) :
    (ofCopy f).vertex x = f x := rfl
def refl (G : _root_.SimpleGraph V) : NonInducedFactor G G where
  vertex := Function.Embedding.refl V
  map_adj := fun hxy => hxy
@[simp]
theorem Zb6 (G : _root_.SimpleGraph V) (x : V) : (refl G).vertex x = x := rfl
def trans (f : NonInducedFactor J G) (g : NonInducedFactor G H) :
    NonInducedFactor J H where
  vertex := f.vertex.trans g.vertex
  map_adj := fun hxy => g.map_adj (f.map_adj hxy)
@[simp]
theorem ZaQ (f : NonInducedFactor J G) (g : NonInducedFactor G H) (x : X) :
    (f.trans g).vertex x = g.vertex (f.vertex x) := rfl
def mapWalk (f : NonInducedFactor J G) {x y : X} (w : J.Walk x y) :
    G.Walk (f.vertex x) (f.vertex y) :=
  w.map f.toHom
@[simp]
theorem Za4 (f : NonInducedFactor J G) {x y : X} (w : J.Walk x y) :
    (f.mapWalk w).length = w.length := by
  exact _root_.SimpleGraph.Walk.length_map f.toHom w
end NonInducedFactor
end SimpleGraph
end P593
end
section
namespace P593
namespace SimpleGraph
open scoped Sym2
universe u
variable {V : Type u}
noncomputable def bridgeFinset (G : _root_.SimpleGraph V) [Fintype G.edgeSet] :
    Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter G.IsBridge
@[simp]
lemma Z8I {G : _root_.SimpleGraph V} [Fintype G.edgeSet] {e : Sym2 V} :
    e ∈ bridgeFinset G ↔ e ∈ G.edgeSet ∧ G.IsBridge e := by
  classical
  simp [bridgeFinset]
noncomputable def bridgeFree (G : _root_.SimpleGraph V) [Fintype G.edgeSet]
    [DecidableEq V] : _root_.SimpleGraph V :=
  G.deleteEdges (bridgeFinset G : Set (Sym2 V))
noncomputable instance instDecidableRelBridgeFree (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet] [DecidableEq V] [DecidableRel G.Adj] :
    DecidableRel (bridgeFree G).Adj := by
  unfold bridgeFree
  infer_instance
lemma Z5E [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (bridgeFree G).degree v ≠ 1 := by
  classical
  let B : Set (Sym2 V) := bridgeFinset G
  let H : _root_.SimpleGraph V := G.deleteEdges B
  change H.degree v ≠ 1
  intro hdeg
  obtain ⟨w, hvw, huniq⟩ :=
    (_root_.SimpleGraph.degree_eq_one_iff_existsUnique_adj (G := H) (v := v)).mp hdeg
  have hvwG : G.Adj v w ∧ s(v, w) ∉ B := by
    simpa [H] using hvw
  have hnbridge : ¬G.IsBridge s(v, w) := by
    intro hb
    have hmem : s(v, w) ∈ bridgeFinset G :=
      Z8I.mpr ⟨hvwG.1, hb⟩
    exact hvwG.2 (by simpa [B] using hmem)
  have hreach : (G.deleteEdges {s(v, w)}).Reachable v w := by
    rw [_root_.SimpleGraph.isBridge_iff] at hnbridge
    exact not_not.mp hnbridge
  obtain ⟨u, c, hc, hmem⟩ :=
    (_root_.SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle
      (G := G) (v := v) (w := w)).mp ⟨hvwG.1, hreach⟩
  have havoid : ∀ e, e ∈ c.edges → e ∉ B := by
    intro e he hbe
    have hbe' : e ∈ bridgeFinset G := by simpa [B] using hbe
    exact (Z8I.mp hbe').2.notMem_edges_of_isCycle hc he
  let cH : H.Walk u u := c.toDeleteEdges B havoid
  have hcH : cH.IsCycle := by
    dsimp [cH]
    exact _root_.SimpleGraph.Walk.IsCycle.toDeleteEdges (G := G) B hc havoid
  have hedges : cH.edges = c.edges := by
    dsimp [cH, _root_.SimpleGraph.Walk.toDeleteEdges]
    apply _root_.SimpleGraph.Walk.edges_transfer
  have hmemH : s(v, w) ∈ cH.edges := by
    rw [hedges]
    exact hmem
  have hv : v ∈ cH.support := cH.fst_mem_support_of_mem_edges hmemH
  let r := cH.rotate v hv
  have hr : r.IsCycle := hcH.rotate hv
  have hsnd : H.Adj v r.snd := r.adj_snd hr.not_nil
  have hpen : H.Adj v r.penultimate := (r.adj_penultimate hr.not_nil).symm
  exact hr.snd_ne_penultimate ((huniq _ hsnd).trans (huniq _ hpen).symm)
lemma Z2K [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] {v w : V}
    (hvw : G.Adj v w) (hb : G.IsBridge s(v, w)) :
    (bridgeFree G).degree v < G.degree v := by
  classical
  let H : _root_.SimpleGraph V := bridgeFree G
  change H.degree v < G.degree v
  have hle : H ≤ G := by
    dsimp [H, bridgeFree]
    exact G.deleteEdges_le _
  have hsub : H.neighborFinset v ⊆ G.neighborFinset v := by
    intro x hx
    rw [_root_.SimpleGraph.mem_neighborFinset] at hx ⊢
    exact hle hx
  have hwG : w ∈ G.neighborFinset v := by
    simpa using hvw
  have hwH : w ∉ H.neighborFinset v := by
    rw [_root_.SimpleGraph.mem_neighborFinset]
    change ¬ (G.deleteEdges (bridgeFinset G : Set (Sym2 V))).Adj v w
    intro hadj
    exact (_root_.SimpleGraph.deleteEdges_adj.mp hadj).2
      (Z8I.mpr ⟨hvw, hb⟩)
  have hssub : H.neighborFinset v ⊂ G.neighborFinset v := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hsub, ?_⟩
    intro heq
    apply hwH
    rw [heq]
    exact hwG
  simpa only [_root_.SimpleGraph.card_neighborFinset_eq_degree] using
    Finset.card_lt_card hssub
theorem Z3y [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hdeg : G.degree v = 3)
    (hbridge : ∃ w, G.Adj v w ∧ G.IsBridge s(v, w)) :
    (bridgeFree G).degree v = 0 ∨ (bridgeFree G).degree v = 2 := by
  classical
  obtain ⟨w, hvw, hb⟩ := hbridge
  have hlt := Z2K G hvw hb
  have hne_one := Z5E G v
  omega
theorem ZI
    [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {u v x y : V}
    (hAdj : G.Adj u v) (hBridge : G.IsBridge s(u, v))
    (hxy : G.Adj x y)
    (hux : (bridgeFree G).Reachable u x)
    (hvy : (bridgeFree G).Reachable v y) :
    s(x, y) = s(u, v) := by
  by_contra hne
  have hBridgeOriginal := hBridge
  rw [_root_.SimpleGraph.isBridge_iff] at hBridge
  apply hBridge
  have hmono : (bridgeFree G).Adj ≤
      (G.deleteEdges {s(u, v)}).Adj := by
    intro a b hab
    rw [bridgeFree, _root_.SimpleGraph.deleteEdges_adj] at hab
    rw [_root_.SimpleGraph.deleteEdges_adj]
    apply And.intro hab.1
    intro hmem
    have heq := Set.mem_singleton_iff.mp hmem
    apply hab.2
    rw [heq]
    exact Z8I.mpr (And.intro hAdj hBridgeOriginal)
  have hux' := hux.mono hmono
  have hvy' := hvy.mono hmono
  have hxy' : (G.deleteEdges {s(u, v)}).Adj x y := by
    rw [_root_.SimpleGraph.deleteEdges_adj]
    exact And.intro hxy (by simpa using hne)
  exact hux'.trans (hxy'.reachable.trans hvy'.symm)
end SimpleGraph
end P593
end
section
namespace P593
namespace SimpleGraph
open scoped Sym2
universe u
variable {V : Type u}
noncomputable def bridgeQuotient (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet] [DecidableEq V] :
    _root_.SimpleGraph (bridgeFree G).ConnectedComponent :=
  G.map (bridgeFree G).connectedComponentMk
theorem Z68 [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (C D : (bridgeFree G).ConnectedComponent) :
    (bridgeQuotient G).Adj C D ↔
      C ≠ D ∧ ∃ u v : V, G.Adj u v ∧ u ∈ C.supp ∧ v ∈ D.supp := by
  change (G.map (bridgeFree G).connectedComponentMk).Adj C D ↔ _
  rw [_root_.SimpleGraph.map_adj']
  constructor
  · rintro ⟨hCD, u, v, huv, hu, hv⟩
    exact ⟨hCD, u, v, huv,
      by simpa [_root_.SimpleGraph.ConnectedComponent.mem_supp_iff] using hu,
      by simpa [_root_.SimpleGraph.ConnectedComponent.mem_supp_iff] using hv⟩
  · rintro ⟨hCD, u, v, huv, hu, hv⟩
    exact ⟨hCD, u, v, huv,
      by simpa [_root_.SimpleGraph.ConnectedComponent.mem_supp_iff] using hu,
      by simpa [_root_.SimpleGraph.ConnectedComponent.mem_supp_iff] using hv⟩
theorem Z2z [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {C D : (bridgeFree G).ConnectedComponent} (hCD : C ≠ D)
    {u v : V} (huv : G.Adj u v) (hu : u ∈ C.supp) (hv : v ∈ D.supp) :
    G.IsBridge s(u, v) := by
  by_contra hnot
  have hfree : (bridgeFree G).Adj u v := by
    rw [bridgeFree, _root_.SimpleGraph.deleteEdges_adj]
    refine ⟨huv, ?_⟩
    intro hmem
    exact hnot (Z8I.mp hmem).2
  apply hCD
  have hu' : (bridgeFree G).connectedComponentMk u = C :=
    (_root_.SimpleGraph.ConnectedComponent.mem_supp_iff C u).mp hu
  have hv' : (bridgeFree G).connectedComponentMk v = D :=
    (_root_.SimpleGraph.ConnectedComponent.mem_supp_iff D v).mp hv
  exact hu'.symm.trans
    ((_root_.SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hfree).trans hv')
theorem Z36 [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {C D : (bridgeFree G).ConnectedComponent} (hCD : C ≠ D)
    {u v x y : V}
    (huv : G.Adj u v) (hu : u ∈ C.supp) (hv : v ∈ D.supp)
    (hxy : G.Adj x y) (hx : x ∈ C.supp) (hy : y ∈ D.supp) :
    s(x, y) = s(u, v) := by
  apply ZI G huv
    (Z2z G hCD huv hu hv) hxy
  · exact C.reachable_of_mem_supp hu hx
  · exact D.reachable_of_mem_supp hv hy
theorem Z2c [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {C D : (bridgeFree G).ConnectedComponent} (hCD : C ≠ D)
    {u v : V} (huv : G.Adj u v) (hu : u ∈ C.supp) (hv : v ∈ D.supp)
    {A B : (bridgeFree G).ConnectedComponent}
    (p : ((bridgeQuotient G).deleteEdges {s(C, D)}).Walk A B)
    {a b : V} (ha : a ∈ A.supp) (hb : b ∈ B.supp) :
    (G.deleteEdges {s(u, v)}).Reachable a b := by
  have hBridge : G.IsBridge s(u, v) :=
    Z2z G hCD huv hu hv
  have hfreeMono : (bridgeFree G).Adj ≤
      (G.deleteEdges {s(u, v)}).Adj := by
    intro x y hxy
    rw [bridgeFree, _root_.SimpleGraph.deleteEdges_adj] at hxy
    rw [_root_.SimpleGraph.deleteEdges_adj]
    refine ⟨hxy.1, ?_⟩
    intro hmem
    have heq : s(x, y) = s(u, v) := Set.mem_singleton_iff.mp hmem
    apply hxy.2
    rw [heq]
    exact Z8I.mpr ⟨huv, hBridge⟩
  induction p generalizing a b with
  | @nil A =>
      exact (A.reachable_of_mem_supp ha hb).mono hfreeMono
  | @cons A X B hAX p ih =>
      rw [_root_.SimpleGraph.deleteEdges_adj] at hAX
      rcases hAX with ⟨hAX, hAXnot⟩
      rcases (Z68 G A X).mp hAX with
        ⟨hAneX, x, y, hxy, hxA, hyX⟩
      have hax : (G.deleteEdges {s(u, v)}).Reachable a x :=
        (A.reachable_of_mem_supp ha hxA).mono hfreeMono
      have hxyDel : (G.deleteEdges {s(u, v)}).Adj x y := by
        rw [_root_.SimpleGraph.deleteEdges_adj]
        refine ⟨hxy, ?_⟩
        intro hmem
        have hEdgeEq : s(x, y) = s(u, v) :=
          Set.mem_singleton_iff.mp hmem
        have hxA' : (bridgeFree G).connectedComponentMk x = A :=
          (_root_.SimpleGraph.ConnectedComponent.mem_supp_iff A x).mp hxA
        have hyX' : (bridgeFree G).connectedComponentMk y = X :=
          (_root_.SimpleGraph.ConnectedComponent.mem_supp_iff X y).mp hyX
        have huC' : (bridgeFree G).connectedComponentMk u = C :=
          (_root_.SimpleGraph.ConnectedComponent.mem_supp_iff C u).mp hu
        have hvD' : (bridgeFree G).connectedComponentMk v = D :=
          (_root_.SimpleGraph.ConnectedComponent.mem_supp_iff D v).mp hv
        have hQuotientEdgeEq : s(A, X) = s(C, D) := by
          have hmap := congrArg
            (fun e : Sym2 V => e.map
              (bridgeFree G).connectedComponentMk) hEdgeEq
          simpa [hxA', hyX', huC', hvD'] using hmap
        exact hAXnot (by simpa using hQuotientEdgeEq)
      exact hax.trans (hxyDel.reachable.trans (ih hyX hb))
theorem Z5w [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    (bridgeQuotient G).IsAcyclic := by
  rw [_root_.SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro C D hCDadj
  rcases (Z68 G C D).mp hCDadj with
    ⟨hCD, u, v, huv, hu, hv⟩
  have hBridge : G.IsBridge s(u, v) :=
    Z2z G hCD huv hu hv
  rw [_root_.SimpleGraph.isBridge_iff]
  rintro ⟨p⟩
  rw [_root_.SimpleGraph.isBridge_iff] at hBridge
  exact hBridge
    (Z2c G hCD huv hu hv p hu hv)
theorem Z23
    [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {C : (bridgeFree G).ConnectedComponent} {x y : V}
    (hxy : G.Adj x y) (hy : y ∈ C.supp) :
    C = (bridgeFree G).connectedComponentMk x ∨
      (bridgeQuotient G).Adj C
        ((bridgeFree G).connectedComponentMk x) := by
  by_cases hC : C = (bridgeFree G).connectedComponentMk x
  · exact Or.inl hC
  · exact Or.inr ((Z68 G C
      ((bridgeFree G).connectedComponentMk x)).mpr
        ⟨hC, y, x, hxy.symm, hy,
          _root_.SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩)
end SimpleGraph
end P593
end
section
namespace P593
universe u v
namespace TripleSystem
variable {V : Type u} {E : Type v} (F : TripleSystem V E)
theorem Z1N
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [DecidableRel F.levi.Adj]
    (hbridge : F.BridgeAtEveryEdge) (e : E) :
    Or ((P593.SimpleGraph.bridgeFree F.levi).degree (Sum.inr e) = 0)
       ((P593.SimpleGraph.bridgeFree F.levi).degree (Sum.inr e) = 2) := by
  have hdeg : F.levi.degree (Sum.inr e) = 3 := by
    rw [(_root_.SimpleGraph.card_neighborFinset_eq_degree
          F.levi (Sum.inr e)).symm,
      _root_.SimpleGraph.neighborFinset_def,
      (Set.ncard_eq_toFinset_card'
        (F.levi.neighborSet (Sum.inr e))).symm]
    exact F.Z5A e
  let x := Exists.choose (hbridge e)
  have hx := Exists.choose_spec (hbridge e)
  change And (F.levi.Adj (Sum.inl x) (Sum.inr e))
      (F.levi.IsBridge s(Sum.inl x, Sum.inr e)) at hx
  exact P593.SimpleGraph.Z3y
    F.levi (Sum.inr e) hdeg
      (Exists.intro (Sum.inl x) (And.intro hx.1.symm (by
        simpa [Sym2.eq_swap] using hx.2)))
end TripleSystem
end P593
end
section
namespace P593
open scoped Sym2
universe u v
namespace TripleSystem
variable {V : Type u} {E : Type v} (F : TripleSystem V E)
namespace BridgeBlock
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [DecidableRel F.levi.Adj]
abbrev Zbp :=
  (P593.SimpleGraph.bridgeFree F.levi).ConnectedComponent
theorem Z1l
    {C : Zbp F} {x : V} {e : E}
    (heC : Sum.inr e ∈ C.supp) (hxe : F.Inc x e) :
    C = (P593.SimpleGraph.bridgeFree F.levi).connectedComponentMk
          (Sum.inl x) ∨
      (P593.SimpleGraph.bridgeQuotient F.levi).Adj C
        ((P593.SimpleGraph.bridgeFree F.levi).connectedComponentMk
          (Sum.inl x)) := by
  exact P593.SimpleGraph.Z23
    F.levi (F.Z7d.mpr hxe) heC
abbrev Point (C : Zbp F) :=
  {x : V // Sum.inl x ∈ C.supp}
abbrev Z8F (C : Zbp F) :=
  {e : E //
    Sum.inr e ∈ C.supp ∧
      (P593.SimpleGraph.bridgeFree F.levi).degree (Sum.inr e) = 2}
def Zay (C : Zbp F) : Prop :=
  ∃ x : V, ∃ e : E,
    Sum.inl x ∈ C.supp ∧ Sum.inr e ∈ C.supp ∧
      (P593.SimpleGraph.bridgeFree F.levi).Adj (Sum.inl x) (Sum.inr e)
def Z97 (C : Zbp F) : _root_.SimpleGraph (Point F C) where
  Adj x y := x ≠ y ∧ ∃ e : Z8F F C,
    (P593.SimpleGraph.bridgeFree F.levi).Adj
        (Sum.inl x.1) (Sum.inr e.1) ∧
      (P593.SimpleGraph.bridgeFree F.levi).Adj
        (Sum.inl y.1) (Sum.inr e.1)
  symm := ⟨by
    rintro x y ⟨hxy, e, hxe, hye⟩
    exact ⟨hxy.symm, e, hye, hxe⟩⟩
  loopless := ⟨by
    intro x h
    exact h.1 rfl⟩
@[simp]
theorem Z7j (C : Zbp F) (x y : Point F C) :
    (Z97 F C).Adj x y ↔
      x ≠ y ∧ ∃ e : Z8F F C,
        (P593.SimpleGraph.bridgeFree F.levi).Adj
            (Sum.inl x.1) (Sum.inr e.1) ∧
          (P593.SimpleGraph.bridgeFree F.levi).Adj
            (Sum.inl y.1) (Sum.inr e.1) :=
  Iff.rfl
theorem Z38
    (hbridge : F.BridgeAtEveryEdge)
    {C : Zbp F} (hC : Zay F C)
    {e : E} (heC : Sum.inr e ∈ C.supp) :
    (P593.SimpleGraph.bridgeFree F.levi).degree (Sum.inr e) = 2 := by
  rcases F.Z1N hbridge e with hzero | htwo
  · rcases hC with ⟨x, f, hxC, hfC, hxf⟩
    have hre : (P593.SimpleGraph.bridgeFree F.levi).Reachable
        (Sum.inr e) (Sum.inl x) :=
      C.reachable_of_mem_supp heC hxC
    have hpos : 0 < (P593.SimpleGraph.bridgeFree F.levi).degree (Sum.inr e) :=
      hre.degree_pos_left (by simp)
    omega
  · exact htwo
theorem Z5S
    (hlinear : F.Linear)
    {C : Zbp F} {x y : Point F C}
    (hxy : x ≠ y)
    {e f : Z8F F C}
    (hxe : (P593.SimpleGraph.bridgeFree F.levi).Adj
      (Sum.inl x.1) (Sum.inr e.1))
    (hye : (P593.SimpleGraph.bridgeFree F.levi).Adj
      (Sum.inl y.1) (Sum.inr e.1))
    (hxf : (P593.SimpleGraph.bridgeFree F.levi).Adj
      (Sum.inl x.1) (Sum.inr f.1))
    (hyf : (P593.SimpleGraph.bridgeFree F.levi).Adj
      (Sum.inl y.1) (Sum.inr f.1)) :
    e = f := by
  have hle : P593.SimpleGraph.bridgeFree F.levi ≤ F.levi := by
    dsimp only [P593.SimpleGraph.bridgeFree]
    exact F.levi.deleteEdges_le _
  apply Subtype.ext
  by_contra hef
  apply hxy
  apply Subtype.ext
  apply hlinear hef
  · apply F.Z7d.mp
    exact hle hxe
  · apply F.Z7d.mp
    exact hle hxf
  · apply F.Z7d.mp
    exact hle hye
  · apply F.Z7d.mp
    exact hle hyf
theorem Z3c
    (hlinear : F.Linear)
    {C : Zbp F} {x y : Point F C}
    (hxy : (Z97 F C).Adj x y) :
    ∃! e : Z8F F C,
      (P593.SimpleGraph.bridgeFree F.levi).Adj
          (Sum.inl x.1) (Sum.inr e.1) ∧
        (P593.SimpleGraph.bridgeFree F.levi).Adj
          (Sum.inl y.1) (Sum.inr e.1) := by
  rcases (Z7j F C x y).mp hxy with ⟨hne, e, he⟩
  refine ⟨e, he, ?_⟩
  intro f hf
  exact (Z5S F hlinear hne (e := e) (f := f)
    he.1 he.2 hf.1 hf.2).symm
end BridgeBlock
end TripleSystem
end P593
end
-- ARISTOTLE_TARGET G5
section
namespace P593
namespace SimpleGraph
universe u
variable {V : Type u}
theorem Z37 (G : _root_.SimpleGraph V) :
    G.Colorable 2 ↔
      ∀ ⦃v : V⦄ (c : G.Walk v v), c.IsCycle → Even c.length := by
  rw [_root_.SimpleGraph.two_colorable_iff_forall_loop_even]
  constructor
  · intro h v c _
    exact h v c
  · intro h v w
    induction hn : w.length using Nat.strongRec generalizing v with
    | ind n ih =>
      by_cases hc : w.IsCycle
      · simpa only [hn] using h w hc
      by_cases hs : 3 ≤ w.length
      · have hnp : ¬ w.tail.IsPath := by
          intro hp
          exact hc
            (_root_.SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
              ⟨hp, hs⟩)
        cases w with
        | nil => simp at hs
        | @cons _ x _ hadj p =>
          have hnp' : ¬ p.IsPath := by
            simpa using hnp
          rw [_root_.SimpleGraph.Walk.isPath_iff_isSubwalk_imp_nil] at hnp'
          push Not at hnp'
          obtain ⟨z, q, hqsub, hqnil⟩ := hnp'
          obtain ⟨r₁, r₂, hp⟩ := hqsub
          let r : G.Walk v v := (r₁.append r₂).cons hadj
          have hlen :
              (_root_.SimpleGraph.Walk.cons hadj p).length =
                q.length + r.length := by
            simp [r, hp, _root_.SimpleGraph.Walk.length_append]
            omega
          have hq_lt :
              q.length < (_root_.SimpleGraph.Walk.cons hadj p).length := by
            simp only [_root_.SimpleGraph.Walk.length_cons]
            simp [hp, _root_.SimpleGraph.Walk.length_append]
            omega
          have hr_lt :
              r.length < (_root_.SimpleGraph.Walk.cons hadj p).length := by
            have hqpos : 0 < q.length :=
              Nat.pos_of_ne_zero
                (fun hzero =>
                  hqnil
                    (_root_.SimpleGraph.Walk.length_eq_zero_iff.mp hzero))
            omega
          have hqeven : Even q.length :=
            ih q.length (by simpa only [hn] using hq_lt) z q rfl
          have hreven : Even r.length :=
            ih r.length (by simpa only [hn] using hr_lt) v r rfl
          rw [← hn, hlen]
          exact hqeven.add hreven
      · have hne1 : w.length ≠ 1 := by
          intro hw
          exact G.loopless.irrefl v (w.adj_of_length_eq_one hw)
        have hnsmall : n = 0 ∨ n = 2 := by omega
        rcases hnsmall with rfl | rfl <;> simp
end SimpleGraph
end P593
end
section
namespace P593
open scoped Sym2
universe u v
namespace TripleSystem
namespace BridgeBlock
noncomputable section
variable {V : Type u} {E : Type v} (F : TripleSystem V E)
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [DecidableRel F.levi.Adj]
private noncomputable abbrev B := P593.SimpleGraph.bridgeFree F.levi
noncomputable def edgeWitness (hlinear : F.Linear) {C : Zbp F}
    {x y : Point F C} (hxy : (Z97 F C).Adj x y) :
    Z8F F C :=
  Exists.choose (Z3c F hlinear hxy)
theorem Z8J (hlinear : F.Linear) {C : Zbp F}
    {x y : Point F C} (hxy : (Z97 F C).Adj x y) :
    (B F).Adj (Sum.inl x.1) (Sum.inr (edgeWitness F hlinear hxy).1) ∧
      (B F).Adj (Sum.inl y.1) (Sum.inr (edgeWitness F hlinear hxy).1) :=
  Exists.choose_spec (Z3c F hlinear hxy) |>.1
noncomputable def liftWalk (hlinear : F.Linear) {C : Zbp F} {x y : Point F C} :
    (Z97 F C).Walk x y →
      (B F).Walk (Sum.inl x.1) (Sum.inl y.1)
  | .nil => .nil
  | .cons hxy p =>
      .cons (Z8J F hlinear hxy).1
        (.cons (Z8J F hlinear hxy).2.symm (liftWalk hlinear p))
theorem Z9p (hlinear : F.Linear) {C : Zbp F}
    {x y : Point F C} (p : (Z97 F C).Walk x y) :
    (liftWalk F hlinear p).length = 2 * p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [liftWalk, ih, Nat.mul_add]
theorem Z45 (hlinear : F.Linear)
    {C : Zbp F} {x y : Point F C}
    (p : (Z97 F C).Walk x y) (z : Point F C) :
    Sum.inl z.1 ∈ (liftWalk F hlinear p).support ↔ z ∈ p.support := by
  induction p with
  | nil => simp [liftWalk, Subtype.ext_iff]
  | cons h p ih => simp [liftWalk, ih, Subtype.ext_iff]
theorem Z2G (hlinear : F.Linear)
    {C : Zbp F} {x y a b : Point F C}
    (hxy : (Z97 F C).Adj x y)
    (hab : (Z97 F C).Adj a b)
    (hw : edgeWitness F hlinear hxy = edgeWitness F hlinear hab) :
    s(x, y) = s(a, b) := by
  have hxySpec := Z8J F hlinear hxy
  have haAdj :
      (B F).Adj (Sum.inl a.1)
        (Sum.inr (edgeWitness F hlinear hxy).1) := by
    rw [hw]
    exact (Z8J F hlinear hab).1
  have hbAdj :
      (B F).Adj (Sum.inl b.1)
        (Sum.inr (edgeWitness F hlinear hxy).1) := by
    rw [hw]
    exact (Z8J F hlinear hab).2
  have hxyNe : x ≠ y := ((Z7j F C x y).mp hxy).1
  have hxyNodesNe : (Sum.inl x.1 : V ⊕ E) ≠ Sum.inl y.1 := by
    intro h
    apply hxyNe
    exact Subtype.ext (Sum.inl.inj h)
  have hpairSubset :
      ({Sum.inl x.1, Sum.inl y.1} : Finset (V ⊕ E)) ⊆
        (B F).neighborFinset
          (Sum.inr (edgeWitness F hlinear hxy).1) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ((B F).mem_neighborFinset _ _).2 hxySpec.1.symm
    · exact ((B F).mem_neighborFinset _ _).2 hxySpec.2.symm
  have hneighborCard :
      ((B F).neighborFinset
          (Sum.inr (edgeWitness F hlinear hxy).1)).card = 2 := by
    rw [_root_.SimpleGraph.card_neighborFinset_eq_degree]
    exact (edgeWitness F hlinear hxy).property.2
  have hpairCard :
      ({Sum.inl x.1, Sum.inl y.1} : Finset (V ⊕ E)).card = 2 := by
    simp [hxyNodesNe]
  have hpairEq :
      ({Sum.inl x.1, Sum.inl y.1} : Finset (V ⊕ E)) =
        (B F).neighborFinset
          (Sum.inr (edgeWitness F hlinear hxy).1) := by
    apply Finset.eq_of_subset_of_card_le hpairSubset
    omega
  have haMem :
      (Sum.inl a.1 : V ⊕ E) ∈
        ({Sum.inl x.1, Sum.inl y.1} : Finset (V ⊕ E)) := by
    rw [hpairEq]
    exact ((B F).mem_neighborFinset _ _).2 haAdj.symm
  have hbMem :
      (Sum.inl b.1 : V ⊕ E) ∈
        ({Sum.inl x.1, Sum.inl y.1} : Finset (V ⊕ E)) := by
    rw [hpairEq]
    exact ((B F).mem_neighborFinset _ _).2 hbAdj.symm
  have haCases : a = x ∨ a = y := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq,
      Subtype.ext_iff] using haMem
  have hbCases : b = x ∨ b = y := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq,
      Subtype.ext_iff] using hbMem
  have habNe : a ≠ b := ((Z7j F C a b).mp hab).1
  rcases haCases with ha | ha <;> rcases hbCases with hb | hb
  · exact (habNe (ha.trans hb.symm)).elim
  · simp [ha, hb]
  · simp [ha, hb]
  · exact (habNe (ha.trans hb.symm)).elim
theorem Z2H (hlinear : F.Linear)
    {C : Zbp F} {x y z : Point F C}
    (hxy : (Z97 F C).Adj x y)
    (p : (Z97 F C).Walk y z)
    (hnot : s(x, y) ∉ p.edges) :
    Sum.inr (edgeWitness F hlinear hxy).1 ∉
      (liftWalk F hlinear p).support := by
  have aux : ∀ {u v : Point F C}
      (q : (Z97 F C).Walk u v),
      s(x, y) ∉ q.edges →
        Sum.inr (edgeWitness F hlinear hxy).1 ∉
          (liftWalk F hlinear q).support := by
    intro u v q
    induction q with
    | nil => simp [liftWalk]
    | @cons u w v huw q ih =>
        intro hqnot
        have hqnot' : s(x, y) ≠ s(u, w) ∧ s(x, y) ∉ q.edges := by
          simpa using hqnot
        have hwitness :
            edgeWitness F hlinear hxy ≠ edgeWitness F hlinear huw := by
          intro hw
          exact hqnot'.1
            (Z2G F hlinear hxy huw hw)
        have hwitnessVal :
            (edgeWitness F hlinear hxy).1 ≠
              (edgeWitness F hlinear huw).1 := by
          intro hw
          exact hwitness (Subtype.ext hw)
        have htail := ih hqnot'.2
        simpa [liftWalk, hwitnessVal] using htail
  exact aux p hnot
theorem Z9v (hlinear : F.Linear) {C : Zbp F}
    {x y : Point F C} (p : (Z97 F C).Walk x y)
    (hp : p.IsPath) :
    (liftWalk F hlinear p).IsPath := by
  induction p with
  | nil => exact _root_.SimpleGraph.Walk.IsPath.nil
  | @cons x y z hxy p ih =>
      have htrail :=
        (_root_.SimpleGraph.Walk.isTrail_cons hxy p).mp hp.isTrail
      rcases (_root_.SimpleGraph.Walk.cons_isPath_iff hxy p).mp hp with
        ⟨hpTail, hxnot⟩
      have htail :
          (_root_.SimpleGraph.Walk.cons
            (Z8J F hlinear hxy).2.symm
            (liftWalk F hlinear p)).IsPath :=
        (ih hpTail).cons
          (Z2H F hlinear hxy p htrail.2)
      apply htail.cons
      simp [Z45 F hlinear p x, hxnot]
theorem Z8X (hlinear : F.Linear) {C : Zbp F}
    {x : Point F C} (c : (Z97 F C).Walk x x)
    (hc : c.IsCycle) :
    (liftWalk F hlinear c).IsCycle := by
  cases c with
  | nil => exact (_root_.SimpleGraph.Walk.not_isCycle_nil hc).elim
  | @cons _ y _ hxy p =>
      rcases (_root_.SimpleGraph.Walk.cons_isCycle_iff p hxy).mp hc with
        ⟨hp, hedge⟩
      have htail :
          (_root_.SimpleGraph.Walk.cons
            (Z8J F hlinear hxy).2.symm
            (liftWalk F hlinear p)).IsPath :=
        (Z9v F hlinear p hp).cons
          (Z2H F hlinear hxy p hedge)
      apply (_root_.SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length).2
      constructor
      · simpa [liftWalk] using htail
      · rw [Z9p]
        have := hc.three_le_length
        omega
theorem Z1Q
    (hlinear : F.Linear) {C : Zbp F} {x : Point F C}
    (c : (Z97 F C).Walk x x) (hc : c.IsCycle) :
    ∃ d : F.levi.Walk (Sum.inl x.1) (Sum.inl x.1),
      d.IsCycle ∧ d.length = 2 * c.length := by
  let hle : B F ≤ F.levi := by
    dsimp only [B, P593.SimpleGraph.bridgeFree]
    exact F.levi.deleteEdges_le _
  let d := (liftWalk F hlinear c).mapLe hle
  refine ⟨d, ?_, ?_⟩
  · exact (Z8X F hlinear c hc).mapLe hle
  · exact (_root_.SimpleGraph.Walk.length_map
      (_root_.SimpleGraph.Hom.ofLE hle) (liftWalk F hlinear c)).trans
        (Z9p F hlinear c)
theorem Z3A
    (hlinear : F.Linear) (hberge : F.EvenBergeCycles)
    (C : Zbp F) {x : Point F C}
    (c : (Z97 F C).Walk x x) (hc : c.IsCycle) :
    Even c.length := by
  obtain ⟨d, hdcycle, hdlen⟩ :=
    Z1Q F hlinear c hc
  obtain ⟨k, hk⟩ := hberge d hdcycle
  use k
  omega
theorem Z4f
    (hlinear : F.Linear) (hberge : F.EvenBergeCycles)
    (C : Zbp F) :
    (Z97 F C).Colorable 2 := by
  apply (P593.SimpleGraph.Z37
    (Z97 F C)).2
  intro x c hc
  exact Z3A F hlinear hberge C c hc
end
end BridgeBlock
end TripleSystem
end P593
end
section
namespace P593
open scoped Sym2
universe u v
namespace TripleSystem
namespace BridgeBlock
noncomputable section
variable {V : Type u} {E : Type v} (F : TripleSystem V E)
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [DecidableRel F.levi.Adj]
private noncomputable abbrev expansionCore :=
  P593.SimpleGraph.bridgeFree F.levi
abbrev Zbx (C : Zbp F) :=
  {e : E // Sum.inr e ∈ C.supp}
theorem Z1J
    {C : Zbp F} (e : Z8F F C) :
    ∃! x : V,
      F.Inc x e.1 ∧ ¬(expansionCore F).Adj (Sum.inl x) (Sum.inr e.1) := by
  classical
  let T := F.levi.neighborFinset (Sum.inr e.1)
  let S := (expansionCore F).neighborFinset (Sum.inr e.1)
  have hle : expansionCore F ≤ F.levi := by
    dsimp only [expansionCore, P593.SimpleGraph.bridgeFree]
    exact F.levi.deleteEdges_le _
  have hsub : S ⊆ T := by
    intro z hz
    rw [_root_.SimpleGraph.mem_neighborFinset] at hz ⊢
    exact hle hz
  have hdeg : F.levi.degree (Sum.inr e.1) = 3 := by
    rw [(_root_.SimpleGraph.card_neighborFinset_eq_degree
          F.levi (Sum.inr e.1)).symm,
      _root_.SimpleGraph.neighborFinset_def,
      (Set.ncard_eq_toFinset_card'
        (F.levi.neighborSet (Sum.inr e.1))).symm]
    exact F.Z5A e.1
  have hTcard : T.card = 3 := by
    dsimp only [T]
    rw [_root_.SimpleGraph.card_neighborFinset_eq_degree, hdeg]
  have hScard : S.card = 2 := by
    dsimp only [S]
    rw [_root_.SimpleGraph.card_neighborFinset_eq_degree]
    exact e.2.2
  have hdiff : (T \ S).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hTcard, hScard]
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hdiff
  have hzmem : z ∈ T \ S := by
    rw [hz]
    simp
  rcases Finset.mem_sdiff.mp hzmem with ⟨hzT, hzS⟩
  cases z with
  | inl x =>
      have hxFull : F.levi.Adj (Sum.inr e.1) (Sum.inl x) := by
        exact (F.levi.mem_neighborFinset _ _).mp hzT
      have hxNot : ¬(expansionCore F).Adj (Sum.inl x) (Sum.inr e.1) := by
        intro hx
        apply hzS
        exact ((expansionCore F).mem_neighborFinset _ _).mpr hx.symm
      refine ⟨x, ⟨F.Z7n.mp hxFull, hxNot⟩, ?_⟩
      intro y hy
      have hyT : (Sum.inl y : V ⊕ E) ∈ T := by
        exact (F.levi.mem_neighborFinset _ _).mpr
          (F.Z7d.mpr hy.1).symm
      have hyS : (Sum.inl y : V ⊕ E) ∉ S := by
        intro hymem
        apply hy.2
        exact (((expansionCore F).mem_neighborFinset _ _).mp hymem).symm
      have hymem : (Sum.inl y : V ⊕ E) ∈ T \ S :=
        Finset.mem_sdiff.mpr ⟨hyT, hyS⟩
      rw [hz] at hymem
      simpa using hymem
  | inr f =>
      have hef : F.levi.Adj (Sum.inr e.1) (Sum.inr f) :=
        (F.levi.mem_neighborFinset _ _).mp hzT
      exact (F.Z65 hef).elim
noncomputable def privatePoint {C : Zbp F}
    (e : Z8F F C) : V :=
  Exists.choose (Z1J F e)
theorem Z8l {C : Zbp F}
    (e : Z8F F C) :
    F.Inc (privatePoint F e) e.1 ∧
      ¬(expansionCore F).Adj
        (Sum.inl (privatePoint F e)) (Sum.inr e.1) :=
  (Exists.choose_spec (Z1J F e)).1
theorem Z6z {C : Zbp F}
    (e : Z8F F C) :
    F.levi.IsBridge
      s(Sum.inl (privatePoint F e), Sum.inr e.1) := by
  have hspec := Z8l F e
  have hadj : F.levi.Adj
      (Sum.inl (privatePoint F e)) (Sum.inr e.1) :=
    F.Z7d.mpr hspec.1
  have hmem :
      s(Sum.inl (privatePoint F e), Sum.inr e.1) ∈
        P593.SimpleGraph.bridgeFinset F.levi := by
    by_contra hnot
    apply hspec.2
    change (P593.SimpleGraph.bridgeFree F.levi).Adj
      (Sum.inl (privatePoint F e)) (Sum.inr e.1)
    dsimp only [P593.SimpleGraph.bridgeFree]
    rw [_root_.SimpleGraph.deleteEdges_adj]
    exact ⟨hadj, hnot⟩
  exact (P593.SimpleGraph.Z8I.mp hmem).2
theorem Z3Z {C : Zbp F}
    (e : Z8F F C) :
    Sum.inl (privatePoint F e) ∉ C.supp := by
  intro hpC
  have hreach : (expansionCore F).Reachable
      (Sum.inl (privatePoint F e)) (Sum.inr e.1) :=
    C.reachable_of_mem_supp hpC e.2.1
  have hadj : F.levi.Adj
      (Sum.inl (privatePoint F e)) (Sum.inr e.1) :=
    F.Z7d.mpr (Z8l F e).1
  have hbridge := Z6z F e
  have hmono : (expansionCore F).Adj ≤
      (F.levi.deleteEdges
        {s(Sum.inl (privatePoint F e), Sum.inr e.1)}).Adj := by
    intro a b hab
    change (P593.SimpleGraph.bridgeFree F.levi).Adj a b at hab
    dsimp only [P593.SimpleGraph.bridgeFree] at hab
    rw [_root_.SimpleGraph.deleteEdges_adj] at hab
    rw [_root_.SimpleGraph.deleteEdges_adj]
    refine ⟨hab.1, ?_⟩
    intro heq
    apply hab.2
    have heq' : s(a, b) =
        s(Sum.inl (privatePoint F e), Sum.inr e.1) := by
      simpa using heq
    rw [heq']
    exact P593.SimpleGraph.Z8I.mpr ⟨hadj, hbridge⟩
  rw [_root_.SimpleGraph.isBridge_iff] at hbridge
  exact hbridge (hreach.mono hmono)
theorem Z6e (C : Zbp F) :
    Function.Injective (fun e : Z8F F C => privatePoint F e) := by
  intro e f hef
  change privatePoint F e = privatePoint F f at hef
  have heAdj : F.levi.Adj
      (Sum.inl (privatePoint F e)) (Sum.inr e.1) :=
    F.Z7d.mpr (Z8l F e).1
  have hfAdj : F.levi.Adj
      (Sum.inl (privatePoint F e)) (Sum.inr f.1) := by
    rw [hef]
    exact F.Z7d.mpr (Z8l F f).1
  have hreach : (expansionCore F).Reachable
      (Sum.inr e.1) (Sum.inr f.1) :=
    C.reachable_of_mem_supp e.2.1 f.2.1
  have hedge :=
    P593.SimpleGraph.ZI
      F.levi heAdj (Z6z F e) hfAdj
        (_root_.SimpleGraph.Reachable.refl _) hreach
  have hmem : (Sum.inr e.1 : V ⊕ E) ∈
      s(Sum.inl (privatePoint F e), Sum.inr f.1) := by
    rw [hedge]
    simp
  apply Subtype.ext
  simpa using hmem
theorem Z30 {C : Zbp F}
    (e : Z8F F C) (z : V) :
    F.Inc z e.1 ↔
      (expansionCore F).Adj (Sum.inl z) (Sum.inr e.1) ∨
        z = privatePoint F e := by
  constructor
  · intro hinc
    by_cases hsurvives :
        (expansionCore F).Adj (Sum.inl z) (Sum.inr e.1)
    · exact Or.inl hsurvives
    · exact Or.inr
        ((Exists.choose_spec
          (Z1J F e)).2 z
            ⟨hinc, hsurvives⟩)
  · rintro (hsurvives | rfl)
    · have hle : expansionCore F ≤ F.levi := by
        dsimp only [expansionCore, P593.SimpleGraph.bridgeFree]
        exact F.levi.deleteEdges_le _
      exact F.Z7d.mp (hle hsurvives)
    · exact (Z8l F e).1
def Z4L
    (hbridge : F.BridgeAtEveryEdge) {C : Zbp F}
    (hC : Zay F C) (e : Zbx F C) : Z8F F C :=
  ⟨e.1, e.2, Z38 F hbridge hC e.2⟩
end
end BridgeBlock
end TripleSystem
end P593
end
section
namespace P593
universe u
namespace TripleSystem
namespace PrivateVertexExpansion
variable {V : Type u} (G : _root_.SimpleGraph V)
abbrev Zbd (_G : _root_.SimpleGraph V) := V
abbrev Zad := G.edgeSet
abbrev Point := Zbd G ⊕ Zad G
abbrev Edge := G.edgeSet
def core (x : Zbd G) : Point G :=
  .inl x
def Za6 (e : Zad G) : Point G :=
  .inr e
def Inc (p : Point G) (e : Edge G) : Prop :=
  match p with
  | .inl x => x ∈ (e : Sym2 V)
  | .inr f => f = e
@[simp]
theorem ZbX (x : Zbd G) (e : Edge G) :
    Inc G (core G x) e ↔ x ∈ (e : Sym2 V) :=
  Iff.rfl
@[simp]
theorem Z8E (f : Zad G) (e : Edge G) :
    Inc G (Za6 G f) e ↔ f = e :=
  Iff.rfl
theorem Z9k {x y : V} (he : s(x, y) ∈ G.edgeSet) :
    {p : Point G | Inc G p ⟨s(x, y), he⟩} =
      {core G x, core G y, Za6 G ⟨s(x, y), he⟩} := by
  ext p
  rcases p with z | f <;> simp [Inc, core, Za6]
theorem Z8b (e : Edge G) :
    Set.ncard {p : Point G | Inc G p e} = 3 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : x ≠ y := (show G.Adj x y from he).ne
      rw [Z9k G he]
      exact Set.ncard_eq_three.mpr
        ⟨core G x, core G y, Za6 G ⟨s(x, y), he⟩,
          by simpa [core] using hxy, by simp [core, Za6],
          by simp [core, Za6], rfl⟩
theorem Z6g :
    Function.Injective (fun e : Edge G => {p : Point G | Inc G p e}) := by
  intro e f hef
  have h := Set.ext_iff.mp hef (Za6 G e)
  simpa [Inc, Za6] using h
end PrivateVertexExpansion
def Z64 (G : _root_.SimpleGraph V) :
    TripleSystem (PrivateVertexExpansion.Point G) (PrivateVertexExpansion.Edge G) where
  Inc := PrivateVertexExpansion.Inc G
  edge_ncard := PrivateVertexExpansion.Z8b G
  simple := PrivateVertexExpansion.Z6g G
@[simp]
theorem Z3T
    (G : _root_.SimpleGraph V) (x : PrivateVertexExpansion.Zbd G)
    (e : PrivateVertexExpansion.Edge G) :
    (Z64 G).Inc (PrivateVertexExpansion.core G x) e ↔
      x ∈ (e : Sym2 V) :=
  Iff.rfl
@[simp]
theorem Z27
    (G : _root_.SimpleGraph V) (f : PrivateVertexExpansion.Zad G)
    (e : PrivateVertexExpansion.Edge G) :
    (Z64 G).Inc (PrivateVertexExpansion.Za6 G f) e ↔
      f = e :=
  Iff.rfl
end TripleSystem
end P593
end
-- ARISTOTLE_REVERSE_TARGET P1
-- ARISTOTLE_REVERSE_TARGET P2
-- ARISTOTLE_REVERSE_TARGET P3
-- ARISTOTLE_REVERSE_TARGET P4
section
namespace P593
open scoped Sym2
universe u v
namespace TripleSystem
namespace BridgeBlock
noncomputable section
variable {V : Type u} {E : Type v} (F : TripleSystem V E)
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [DecidableRel F.levi.Adj]
private noncomputable abbrev packagingCore :=
  P593.SimpleGraph.bridgeFree F.levi
noncomputable def graphEdgeWitness (hlinear : F.Linear) {C : Zbp F} :
    (Z97 F C).edgeSet → Z8F F C := by
  intro a
  let x := a.1.out.1
  let y := a.1.out.2
  have hxy : (Z97 F C).Adj x y := by
    change Quot.mk (Sym2.Rel (Point F C)) a.1.out ∈
      (Z97 F C).edgeSet
    simpa only [Quot.out_eq] using a.2
  exact edgeWitness F hlinear hxy
theorem Z6y (hlinear : F.Linear) {C : Zbp F}
    (a : (Z97 F C).edgeSet) :
    (P593.SimpleGraph.bridgeFree F.levi).Adj
        (Sum.inl a.1.out.1.1)
        (Sum.inr (graphEdgeWitness F hlinear (C := C) a).1) ∧
      (P593.SimpleGraph.bridgeFree F.levi).Adj
        (Sum.inl a.1.out.2.1)
        (Sum.inr (graphEdgeWitness F hlinear (C := C) a).1) := by
  unfold graphEdgeWitness
  dsimp only
  exact Z8J F hlinear _
theorem Z4Y (hlinear : F.Linear) (C : Zbp F) :
    Function.Bijective (graphEdgeWitness F hlinear (C := C)) := by
  constructor
  · intro a b hw
    apply Subtype.ext
    have ha : (Z97 F C).Adj a.1.out.1 a.1.out.2 := by
      change Quot.mk (Sym2.Rel (Point F C)) a.1.out ∈
        (Z97 F C).edgeSet
      simpa only [Quot.out_eq] using a.2
    have hb : (Z97 F C).Adj b.1.out.1 b.1.out.2 := by
      change Quot.mk (Sym2.Rel (Point F C)) b.1.out ∈
        (Z97 F C).edgeSet
      simpa only [Quot.out_eq] using b.2
    have hw' : edgeWitness F hlinear ha = edgeWitness F hlinear hb := by
      simpa only [graphEdgeWitness] using hw
    have hout := Z2G F hlinear ha hb hw'
    exact a.1.out_eq.symm.trans (hout.trans b.1.out_eq)
  · intro e
    let B := packagingCore F
    have hcard : (B.neighborFinset (Sum.inr e.1)).card = 2 := by
      rw [_root_.SimpleGraph.card_neighborFinset_eq_degree]
      exact e.2.2
    obtain ⟨z, w, hzw, hneighbors⟩ := Finset.card_eq_two.mp hcard
    have hzmem : z ∈ B.neighborFinset (Sum.inr e.1) := by
      rw [hneighbors]
      simp
    have hwmem : w ∈ B.neighborFinset (Sum.inr e.1) := by
      rw [hneighbors]
      simp
    have hze : B.Adj (Sum.inr e.1) z :=
      (B.mem_neighborFinset _ _).mp hzmem
    have hwe : B.Adj (Sum.inr e.1) w :=
      (B.mem_neighborFinset _ _).mp hwmem
    have hle : B ≤ F.levi := by
      dsimp only [B, packagingCore, P593.SimpleGraph.bridgeFree]
      exact F.levi.deleteEdges_le _
    rcases z with x | f
    · rcases w with y | g
      · change (packagingCore F).Adj (Sum.inr e.1) (Sum.inl x) at hze
        change (packagingCore F).Adj (Sum.inr e.1) (Sum.inl y) at hwe
        have hxC : Sum.inl x ∈ C.supp :=
          C.mem_supp_of_adj_mem_supp e.2.1 hze
        have hyC : Sum.inl y ∈ C.supp :=
          C.mem_supp_of_adj_mem_supp e.2.1 hwe
        let px : Point F C := ⟨x, hxC⟩
        let py : Point F C := ⟨y, hyC⟩
        have hxy : px ≠ py := by
          intro h
          apply hzw
          simpa [px, py] using congrArg Subtype.val h
        have hadj : (Z97 F C).Adj px py := by
          refine (Z7j F C px py).mpr ⟨hxy, e, ?_, ?_⟩
          · exact hze.symm
          · exact hwe.symm
        let a : (Z97 F C).edgeSet :=
          ⟨s(px, py), hadj⟩
        refine ⟨a, ?_⟩
        have houtAdj : (Z97 F C).Adj a.1.out.1 a.1.out.2 := by
          change Quot.mk (Sym2.Rel (Point F C)) a.1.out ∈
            (Z97 F C).edgeSet
          simpa only [Quot.out_eq] using a.2
        have hout1 : a.1.out.1 = px ∨ a.1.out.1 = py := by
          simpa only [a, Sym2.mem_iff] using Sym2.out_fst_mem a.1
        have hout2 : a.1.out.2 = px ∨ a.1.out.2 = py := by
          simpa only [a, Sym2.mem_iff] using Sym2.out_snd_mem a.1
        have heout1 : (packagingCore F).Adj
            (Sum.inl a.1.out.1.1) (Sum.inr e.1) := by
          rcases hout1 with h | h
          · simpa only [h] using hze.symm
          · simpa only [h] using hwe.symm
        have heout2 : (packagingCore F).Adj
            (Sum.inl a.1.out.2.1) (Sum.inr e.1) := by
          rcases hout2 with h | h
          · simpa only [h] using hze.symm
          · simpa only [h] using hwe.symm
        apply (Z3c F hlinear houtAdj).unique
        · exact Z6y F hlinear a
        · exact ⟨heout1, heout2⟩
      · exact (F.Z65 (hle hwe)).elim
    · exact (F.Z65 (hle hze)).elim
noncomputable def graphEdgeEquivContractibleEdge (hlinear : F.Linear)
    (C : Zbp F) :
    (Z97 F C).edgeSet ≃ Z8F F C :=
  Equiv.ofBijective (graphEdgeWitness F hlinear (C := C))
    (Z4Y F hlinear C)
noncomputable def contractibleEdgeEquivHyperedge
    (hbridge : F.BridgeAtEveryEdge) {C : Zbp F}
    (hC : Zay F C) : Z8F F C ≃ Zbx F C := by
  exact
    { toFun := fun e => ⟨e.1, e.2.1⟩
      invFun := Z4L F hbridge hC
      left_inv := by
        intro e
        apply Subtype.ext
        rfl
      right_inv := by
        intro e
        apply Subtype.ext
        rfl }
noncomputable def graphEdgeEquivHyperedge
    (hlinear : F.Linear) (hbridge : F.BridgeAtEveryEdge)
    {C : Zbp F} (hC : Zay F C) :
    (Z97 F C).edgeSet ≃ Zbx F C :=
  (graphEdgeEquivContractibleEdge F hlinear C).trans
    (contractibleEdgeEquivHyperedge F hbridge hC)
theorem ZS
    (hlinear : F.Linear) {C : Zbp F}
    (a : (Z97 F C).edgeSet) (x : Point F C) :
    x ∈ (a.1 : Sym2 (Point F C)) ↔
      (packagingCore F).Adj (Sum.inl x.1)
        (Sum.inr (graphEdgeWitness F hlinear (C := C) a).1) := by
  have hspec := Z6y F hlinear a
  change (packagingCore F).Adj
        (Sum.inl a.1.out.1.1)
        (Sum.inr (graphEdgeWitness F hlinear (C := C) a).1) ∧
      (packagingCore F).Adj
        (Sum.inl a.1.out.2.1)
        (Sum.inr (graphEdgeWitness F hlinear (C := C) a).1) at hspec
  have houtAdj : (Z97 F C).Adj a.1.out.1 a.1.out.2 := by
    change Quot.mk (Sym2.Rel (Point F C)) a.1.out ∈
      (Z97 F C).edgeSet
    simpa only [Quot.out_eq] using a.2
  have houtNe : a.1.out.1 ≠ a.1.out.2 :=
    ((Z7j F C _ _).mp houtAdj).1
  constructor
  · intro hx
    have hx' : x ∈ s(a.1.out.1, a.1.out.2) := by
      change x ∈ Quot.mk (Sym2.Rel (Point F C)) a.1.out
      simpa only [Quot.out_eq] using hx
    rcases (Sym2.mem_iff.mp hx') with h | h
    · simpa only [h] using hspec.1
    · simpa only [h] using hspec.2
  · intro hx
    have hnodesNe : (Sum.inl a.1.out.1.1 : V ⊕ E) ≠
        Sum.inl a.1.out.2.1 := by
      intro h
      apply houtNe
      apply Subtype.ext
      exact Sum.inl.inj h
    have hpairSubset :
        ({Sum.inl a.1.out.1.1, Sum.inl a.1.out.2.1} : Finset (V ⊕ E)) ⊆
          (packagingCore F).neighborFinset
            (Sum.inr (graphEdgeWitness F hlinear (C := C) a).1) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact ((packagingCore F).mem_neighborFinset _ _).mpr hspec.1.symm
      · exact ((packagingCore F).mem_neighborFinset _ _).mpr hspec.2.symm
    have hneighborCard :
        ((packagingCore F).neighborFinset
          (Sum.inr (graphEdgeWitness F hlinear (C := C) a).1)).card = 2 := by
      rw [_root_.SimpleGraph.card_neighborFinset_eq_degree]
      exact (graphEdgeWitness F hlinear (C := C) a).2.2
    have hpairCard :
        ({Sum.inl a.1.out.1.1, Sum.inl a.1.out.2.1} :
          Finset (V ⊕ E)).card = 2 := by
      simp [hnodesNe]
    have hpairEq :
        ({Sum.inl a.1.out.1.1, Sum.inl a.1.out.2.1} : Finset (V ⊕ E)) =
          (packagingCore F).neighborFinset
            (Sum.inr (graphEdgeWitness F hlinear (C := C) a).1) := by
      apply Finset.eq_of_subset_of_card_le hpairSubset
      omega
    have hxMem : (Sum.inl x.1 : V ⊕ E) ∈
        ({Sum.inl a.1.out.1.1, Sum.inl a.1.out.2.1} : Finset (V ⊕ E)) := by
      rw [hpairEq]
      exact ((packagingCore F).mem_neighborFinset _ _).mpr hx.symm
    have hxCases : x = a.1.out.1 ∨ x = a.1.out.2 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq,
        Subtype.ext_iff] using hxMem
    rcases hxCases with h | h
    · rw [h]
      exact Sym2.out_fst_mem a.1
    · rw [h]
      exact Sym2.out_snd_mem a.1
noncomputable def componentExpansionEmbedding
    (hlinear : F.Linear) (C : Zbp F) :
    (Z64 (Z97 F C)).Embedding F := by
  let G := Z97 F C
  let witness : G.edgeSet → Z8F F C :=
    graphEdgeWitness F hlinear (C := C)
  let vertexMap : PrivateVertexExpansion.Point G → V
    | .inl x => x.1
    | .inr a => privatePoint F (witness a)
  have hvertexMap : Function.Injective vertexMap := by
    intro p q hpq
    rcases p with x | a <;> rcases q with y | b
    · change x.1 = y.1 at hpq
      exact congrArg Sum.inl (Subtype.ext hpq)
    · exfalso
      change x.1 = privatePoint F (witness b) at hpq
      apply Z3Z F (witness b)
      rw [← hpq]
      exact x.2
    · exfalso
      change privatePoint F (witness a) = y.1 at hpq
      apply Z3Z F (witness a)
      rw [hpq]
      exact y.2
    · change privatePoint F (witness a) = privatePoint F (witness b) at hpq
      have hab : a = b := (Z4Y F hlinear C).1
        (Z6e F C hpq)
      exact congrArg Sum.inr hab
  let vertexEmbedding : PrivateVertexExpansion.Point G ↪ V :=
    { toFun := vertexMap
      inj' := hvertexMap }
  exact
    { vertex := vertexEmbedding
      edge := fun a => (witness a).1
      map_edge := by
        intro a
        ext z
        constructor
        · rintro ⟨p, hp, rfl⟩
          change (Z64 G).Inc p a at hp
          rcases p with x | b
          · change x ∈ (a.1 : Sym2 (Point F C)) at hp
            apply (Z30 F (witness a) x.1).mpr
            left
            exact (ZS
              F hlinear a x).mp hp
          · change b = a at hp
            subst b
            exact (Z8l F (witness a)).1
        · intro hz
          change F.Inc z (witness a).1 at hz
          rcases (Z30 F (witness a) z).mp hz with
            hcore | hprivate
          · have hzC : Sum.inl z ∈ C.supp :=
              C.mem_supp_of_adj_mem_supp (witness a).2.1 hcore.symm
            let x : Point F C := ⟨z, hzC⟩
            refine ⟨Sum.inl x, ?_, ?_⟩
            · change x ∈ (a.1 : Sym2 (Point F C))
              exact (ZS
                F hlinear a x).mpr hcore
            · rfl
          · refine ⟨Sum.inr a, ?_, ?_⟩
            · rfl
            · exact hprivate.symm }
end
end BridgeBlock
end TripleSystem
end P593
end
section
namespace P593
universe u₀ v₀ u₁ v₁
namespace TripleSystem.OnePointAmalgamation
variable {V₀ : Type u₀} {E₀ : Type v₀}
variable {V₁ : Type u₁} {E₁ : Type v₁}
def Rel (r₀ : V₀) (r₁ : V₁) : Sum V₀ V₁ → Sum V₀ V₁ → Prop
  | .inl x, .inl y => x = y
  | .inr x, .inr y => x = y
  | .inl x, .inr y => x = r₀ ∧ y = r₁
  | .inr y, .inl x => y = r₁ ∧ x = r₀
private theorem ZbV (r₀ : V₀) (r₁ : V₁) (x : Sum V₀ V₁) :
    Rel r₀ r₁ x x := by
  cases x <;> simp [Rel]
private theorem ZbW (r₀ : V₀) (r₁ : V₁) {x y : Sum V₀ V₁}
    (h : Rel r₀ r₁ x y) : Rel r₀ r₁ y x := by
  cases x <;> cases y <;> simp_all [Rel]
private theorem ZbE (r₀ : V₀) (r₁ : V₁) {x y z : Sum V₀ V₁}
    (hxy : Rel r₀ r₁ x y) (hyz : Rel r₀ r₁ y z) : Rel r₀ r₁ x z := by
  cases x <;> cases y <;> cases z <;> simp_all [Rel]
def ZaF (r₀ : V₀) (r₁ : V₁) : Setoid (Sum V₀ V₁) where
  r := Rel r₀ r₁
  iseqv := ⟨
    fun x => ZbV r₀ r₁ x,
    fun h => ZbW r₀ r₁ h,
    fun hxy hyz => ZbE r₀ r₁ hxy hyz⟩
abbrev Vertex (r₀ : V₀) (r₁ : V₁) := Quotient (ZaF r₀ r₁)
def left (r₀ : V₀) (r₁ : V₁) (x : V₀) : Vertex r₀ r₁ :=
  Quotient.mk (ZaF r₀ r₁) (.inl x)
def right (r₀ : V₀) (r₁ : V₁) (y : V₁) : Vertex r₀ r₁ :=
  Quotient.mk (ZaF r₀ r₁) (.inr y)
@[simp]
theorem Z8Y (r₀ : V₀) (r₁ : V₁) (x y : V₀) :
    left r₀ r₁ x = left r₀ r₁ y ↔ x = y := by
  constructor
  · intro h
    exact Quotient.exact h
  · rintro rfl
    rfl
@[simp]
theorem Z8a (r₀ : V₀) (r₁ : V₁) (x y : V₁) :
    right r₀ r₁ x = right r₀ r₁ y ↔ x = y := by
  constructor
  · intro h
    exact Quotient.exact h
  · rintro rfl
    rfl
@[simp]
theorem Z8o (r₀ : V₀) (r₁ : V₁) (x : V₀) (y : V₁) :
    left r₀ r₁ x = right r₀ r₁ y ↔ x = r₀ ∧ y = r₁ := by
  constructor
  · intro h
    exact Quotient.exact h
  · rintro ⟨rfl, rfl⟩
    apply Quotient.sound
    exact ⟨rfl, rfl⟩
@[simp]
theorem Z8u (r₀ : V₀) (r₁ : V₁) (y : V₁) (x : V₀) :
    right r₀ r₁ y = left r₀ r₁ x ↔ y = r₁ ∧ x = r₀ := by
  rw [eq_comm, Z8o, and_comm]
theorem root_eq (r₀ : V₀) (r₁ : V₁) :
    left r₀ r₁ r₀ = right r₀ r₁ r₁ := by
  simp
theorem Z9G (r₀ : V₀) (r₁ : V₁) :
    Function.Injective (left r₀ r₁) := by
  intro x y h
  exact (Z8Y r₀ r₁ x y).mp h
theorem Z9h (r₀ : V₀) (r₁ : V₁) :
    Function.Injective (right r₀ r₁) := by
  intro x y h
  exact (Z8a r₀ r₁ x y).mp h
def lift {X : Type*} (r₀ : V₀) (r₁ : V₁)
    (f₀ : V₀ → X) (f₁ : V₁ → X) (hroot : f₀ r₀ = f₁ r₁) :
    Vertex r₀ r₁ → X :=
  Quotient.lift (Sum.elim f₀ f₁) (by
    intro a b hab
    change Rel r₀ r₁ a b at hab
    cases a <;> cases b <;> simp_all [Rel])
@[simp]
theorem ZbF {X : Type*} (r₀ : V₀) (r₁ : V₁)
    (f₀ : V₀ → X) (f₁ : V₁ → X) (hroot : f₀ r₀ = f₁ r₁) (x : V₀) :
    lift r₀ r₁ f₀ f₁ hroot (left r₀ r₁ x) = f₀ x := rfl
@[simp]
theorem Zbn {X : Type*} (r₀ : V₀) (r₁ : V₁)
    (f₀ : V₀ → X) (f₁ : V₁ → X) (hroot : f₀ r₀ = f₁ r₁) (y : V₁) :
    lift r₀ r₁ f₀ f₁ hroot (right r₀ r₁ y) = f₁ y := rfl
theorem Z9Q {X : Type*} (r₀ : V₀) (r₁ : V₁)
    (f₀ : V₀ → X) (f₁ : V₁ → X) (hroot : f₀ r₀ = f₁ r₁)
    (h₀ : Function.Injective f₀) (h₁ : Function.Injective f₁)
    (hcross : ∀ x y, f₀ x = f₁ y ↔ x = r₀ ∧ y = r₁) :
    Function.Injective (lift r₀ r₁ f₀ f₁ hroot) := by
  intro q q' h
  induction q using Quotient.inductionOn with
  | _ a =>
      induction q' using Quotient.inductionOn with
      | _ b =>
          cases a with
          | inl x =>
              cases b with
              | inl y =>
                  apply Quotient.sound
                  exact h₀ h
              | inr y =>
                  apply Quotient.sound
                  exact (hcross x y).mp h
          | inr x =>
              cases b with
              | inl y =>
                  apply Quotient.sound
                  have hyx := (hcross y x).mp h.symm
                  exact ⟨hyx.2, hyx.1⟩
              | inr y =>
                  apply Quotient.sound
                  exact h₁ h
noncomputable def vertexEquivOfMaps {W : Type*}
    (r₀ : V₀) (r₁ : V₁) (f₀ : V₀ → W) (f₁ : V₁ → W)
    (hroot : f₀ r₀ = f₁ r₁)
    (h₀ : Function.Injective f₀) (h₁ : Function.Injective f₁)
    (hcross : ∀ x y, f₀ x = f₁ y ↔ x = r₀ ∧ y = r₁)
    (hcover : ∀ w, (∃ x, f₀ x = w) ∨ (∃ y, f₁ y = w)) :
    Vertex r₀ r₁ ≃ W :=
  Equiv.ofBijective (lift r₀ r₁ f₀ f₁ hroot) ⟨
    Z9Q r₀ r₁ f₀ f₁ hroot h₀ h₁ hcross,
    by
      intro w
      rcases hcover w with ⟨x, rfl⟩ | ⟨y, rfl⟩
      · exact ⟨left r₀ r₁ x, rfl⟩
      · exact ⟨right r₀ r₁ y, rfl⟩⟩
theorem Z40 (r₀ : V₀) (r₁ : V₁)
    (s : Set V₀) (t : Set V₁) :
    (left r₀ r₁ '' s ∩ right r₀ r₁ '' t).Subsingleton := by
  intro q hq q' hq'
  rcases hq.1 with ⟨x, hx, hxq⟩
  rcases hq.2 with ⟨y, hy, hyq⟩
  rcases hq'.1 with ⟨x', hx', hxq'⟩
  rcases hq'.2 with ⟨y', hy', hyq'⟩
  have hxy := (Z8o r₀ r₁ x y).mp (hxq.trans hyq.symm)
  have hxy' := (Z8o r₀ r₁ x' y').mp (hxq'.trans hyq'.symm)
  exact hxq.symm.trans ((congrArg (left r₀ r₁) (hxy.1.trans hxy'.1.symm)).trans hxq')
abbrev Edge (E₀ : Type v₀) (E₁ : Type v₁) := E₀ ⊕ E₁
def Inc (F₀ : TripleSystem V₀ E₀) (F₁ : TripleSystem V₁ E₁)
    (r₀ : V₀) (r₁ : V₁) : Vertex r₀ r₁ → Edge E₀ E₁ → Prop
  | q, .inl e => q ∈ left r₀ r₁ '' F₀.edgeSet e
  | q, .inr e => q ∈ right r₀ r₁ '' F₁.edgeSet e
@[simp]
theorem Z8C (F₀ : TripleSystem V₀ E₀)
    (F₁ : TripleSystem V₁ E₁) (r₀ : V₀) (r₁ : V₁) (e : E₀) :
    {q | Inc F₀ F₁ r₀ r₁ q (.inl e)} =
      left r₀ r₁ '' F₀.edgeSet e := rfl
@[simp]
theorem Z89 (F₀ : TripleSystem V₀ E₀)
    (F₁ : TripleSystem V₁ E₁) (r₀ : V₀) (r₁ : V₁) (e : E₁) :
    {q | Inc F₀ F₁ r₀ r₁ q (.inr e)} =
      right r₀ r₁ '' F₁.edgeSet e := rfl
@[simp]
theorem Z8B (F₀ : TripleSystem V₀ E₀)
    (F₁ : TripleSystem V₁ E₁) (r₀ : V₀) (r₁ : V₁)
    (x : V₀) (e : E₀) :
    Inc F₀ F₁ r₀ r₁ (left r₀ r₁ x) (.inl e) ↔ F₀.Inc x e := by
  simp [Inc]
@[simp]
theorem Z7G (F₀ : TripleSystem V₀ E₀)
    (F₁ : TripleSystem V₁ E₁) (r₀ : V₀) (r₁ : V₁)
    (y : V₁) (e : E₁) :
    Inc F₀ F₁ r₀ r₁ (right r₀ r₁ y) (.inr e) ↔ F₁.Inc y e := by
  simp [Inc]
theorem Z88 (F₀ : TripleSystem V₀ E₀)
    (F₁ : TripleSystem V₁ E₁) (r₀ : V₀) (r₁ : V₁) :
    ∀ e : Edge E₀ E₁,
      Set.ncard {q | Inc F₀ F₁ r₀ r₁ q e} = 3 := by
  rintro (e | e)
  · rw [Z8C,
      Set.ncard_image_of_injective _ (Z9G r₀ r₁)]
    exact F₀.Zaa e
  · rw [Z89,
      Set.ncard_image_of_injective _ (Z9h r₀ r₁)]
    exact F₁.Zaa e
theorem Z8s (F₀ : TripleSystem V₀ E₀)
    (F₁ : TripleSystem V₁ E₁) (r₀ : V₀) (r₁ : V₁)
    (e : E₀) (f : E₁) :
    left r₀ r₁ '' F₀.edgeSet e ≠ right r₀ r₁ '' F₁.edgeSet f := by
  intro hsets
  have hsub : F₀.edgeSet e ⊆ ({r₀} : Set V₀) := by
    intro x hx
    have hx' : left r₀ r₁ x ∈ left r₀ r₁ '' F₀.edgeSet e :=
      ⟨x, hx, rfl⟩
    rw [hsets] at hx'
    rcases hx' with ⟨y, hy, hyx⟩
    exact (Z8o r₀ r₁ x y).mp hyx.symm |>.1
  have hcard := Set.ncard_le_ncard hsub (Set.finite_singleton r₀)
  rw [F₀.Zaa, Set.ncard_singleton] at hcard
  omega
theorem Z6f (F₀ : TripleSystem V₀ E₀)
    (F₁ : TripleSystem V₁ E₁) (r₀ : V₀) (r₁ : V₁) :
    Function.Injective (fun e : Edge E₀ E₁ =>
      {q | Inc F₀ F₁ r₀ r₁ q e}) := by
  intro e f h
  cases e with
  | inl e =>
      cases f with
      | inl f =>
          congr 1
          apply F₀.Z8n
          apply (Set.image_eq_image (Z9G r₀ r₁)).mp
          exact h
      | inr f =>
          exact False.elim (Z8s F₀ F₁ r₀ r₁ e f h)
  | inr e =>
      cases f with
      | inl f =>
          exact False.elim (Z8s F₀ F₁ r₀ r₁ f e h.symm)
      | inr f =>
          congr 1
          apply F₁.Z8n
          apply (Set.image_eq_image (Z9h r₀ r₁)).mp
          exact h
def amalgam (F₀ : TripleSystem V₀ E₀) (F₁ : TripleSystem V₁ E₁)
    (r₀ : V₀) (r₁ : V₁) : TripleSystem (Vertex r₀ r₁) (Edge E₀ E₁) where
  Inc := Inc F₀ F₁ r₀ r₁
  edge_ncard := Z88 F₀ F₁ r₀ r₁
  simple := Z6f F₀ F₁ r₀ r₁
noncomputable def isoOfMaps {W : Type*} {D : Type*}
    (F₀ : TripleSystem V₀ E₀) (F₁ : TripleSystem V₁ E₁)
    (K : TripleSystem W D) (r₀ : V₀) (r₁ : V₁)
    (f₀ : V₀ → W) (f₁ : V₁ → W)
    (hroot : f₀ r₀ = f₁ r₁)
    (h₀ : Function.Injective f₀) (h₁ : Function.Injective f₁)
    (hcross : ∀ x y, f₀ x = f₁ y ↔ x = r₀ ∧ y = r₁)
    (hcover : ∀ w, (∃ x, f₀ x = w) ∨ (∃ y, f₁ y = w))
    (edgeEquiv : Edge E₀ E₁ ≃ D)
    (hmap₀ : ∀ e, f₀ '' F₀.edgeSet e = K.edgeSet (edgeEquiv (.inl e)))
    (hmap₁ : ∀ e, f₁ '' F₁.edgeSet e = K.edgeSet (edgeEquiv (.inr e))) :
    Iso (amalgam F₀ F₁ r₀ r₁) K where
  vertexEquiv := vertexEquivOfMaps r₀ r₁ f₀ f₁ hroot h₀ h₁ hcross hcover
  edgeEquiv := edgeEquiv
  map_inc_iff := by
    intro q e
    let ve := vertexEquivOfMaps r₀ r₁ f₀ f₁ hroot h₀ h₁ hcross hcover
    have hve_injective : Function.Injective ve := ve.injective
    have himage : ve '' (amalgam F₀ F₁ r₀ r₁).edgeSet e =
        K.edgeSet (edgeEquiv e) := by
      cases e with
      | inl e =>
          change ve '' (left r₀ r₁ '' F₀.edgeSet e) = _
          rw [Set.image_image]
          change f₀ '' F₀.edgeSet e = _
          exact hmap₀ e
      | inr e =>
          change ve '' (right r₀ r₁ '' F₁.edgeSet e) = _
          rw [Set.image_image]
          change f₁ '' F₁.edgeSet e = _
          exact hmap₁ e
    change q ∈ (amalgam F₀ F₁ r₀ r₁).edgeSet e ↔
      ve q ∈ K.edgeSet (edgeEquiv e)
    rw [← himage]
    constructor
    · intro hq
      exact ⟨q, hq, rfl⟩
    · rintro ⟨q', hq', hqq'⟩
      exact hqq' |> hve_injective |> fun h => h ▸ hq'
noncomputable abbrev vertexFintype (r₀ : V₀) (r₁ : V₁)
    [Fintype V₀] [Fintype V₁] : Fintype (Vertex r₀ r₁) :=
  Fintype.ofFinite _
end TripleSystem.OnePointAmalgamation
end P593
end
section
namespace P593
universe w
namespace TripleSystem
abbrev ZaL : Type w := ULift.{w} Empty
def ZbJ (V : Type w) : TripleSystem V ZaL where
  Inc _ e := nomatch e.down
  edge_ncard e := nomatch e.down
  simple e := nomatch e.down
inductive Constructible : {V E : Type w} → TripleSystem V E → Prop
  | ofEdgeless (V : Type w) [Fintype V] : Constructible (ZbJ V)
  | ofExpansion {V : Type w} [Fintype V] (G : _root_.SimpleGraph V)
      (hG : G.Colorable 2) : Constructible (Z64 G)
  | disjointUnion {V E W D : Type w}
      {F : TripleSystem V E} {G : TripleSystem W D}
      (hF : Constructible F) (hG : Constructible G) :
      Constructible (F.Za7 G)
  | amalgam {V₀ E₀ V₁ E₁ : Type w}
      {F₀ : TripleSystem V₀ E₀} {F₁ : TripleSystem V₁ E₁}
      (h₀ : Constructible F₀) (h₁ : Constructible F₁)
      (r₀ : V₀) (r₁ : V₁) :
      Constructible (OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁)
  | ofIso {V E V' E' : Type w}
      {F : TripleSystem V E} {F' : TripleSystem V' E'}
      (hF : Constructible F) (f : Iso F F') : Constructible F'
theorem Z83 (V : Type w) : (ZbJ V).Intrinsic := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    exact Empty.elim e.down
  · intro e
    exact Empty.elim e.down
  · intro z c hc
    cases c with
    | nil => simp at hc
    | @cons u v w h p =>
        cases z with
        | inl x =>
            cases v with
            | inl y => exact ((ZbJ V).Z5r h).elim
            | inr e => exact Empty.elim e.down
        | inr e => exact Empty.elim e.down
end TripleSystem
end P593
end
section
namespace P593
open scoped Sym2
universe u v w
namespace TripleSystem
namespace BridgeBlock
noncomputable section
variable {V : Type u} {E : Type v} (F : TripleSystem V E)
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [DecidableRel F.levi.Adj]
private noncomputable abbrev restrictionCore :=
  P593.SimpleGraph.bridgeFree F.levi
def Z6q (C : Zbp F) : Set E :=
  {e | Sum.inr e ∈ C.supp}
@[simp]
theorem Z4r {C : Zbp F} {e : E} :
    e ∈ Z6q F C ↔ Sum.inr e ∈ C.supp :=
  Iff.rfl
theorem Z2S {C : Zbp F}
    (hC : Zay F C) (x : Point F C) :
    x.1 ∈ F.Z9z (Z6q F C) := by
  rcases hC with ⟨u, e, huC, heC, hue⟩
  have hreach : (restrictionCore F).Reachable (Sum.inl x.1) (Sum.inr e) :=
    C.reachable_of_mem_supp x.2 heC
  have hne : (Sum.inl x.1 : V ⊕ E) ≠ Sum.inr e := by simp
  obtain ⟨z, hxz⟩ := hreach.nonempty_neighborSet_left hne
  rcases z with y | f
  · exact (F.Z5r
      ((show restrictionCore F ≤ F.levi by
        dsimp only [restrictionCore, P593.SimpleGraph.bridgeFree]
        exact F.levi.deleteEdges_le _) hxz)).elim
  · have hfC : Sum.inr f ∈ C.supp :=
      C.mem_supp_of_adj_mem_supp x.2 hxz
    refine ⟨f, hfC, ?_⟩
    apply F.Z7d.mp
    exact (show restrictionCore F ≤ F.levi by
      dsimp only [restrictionCore, P593.SimpleGraph.bridgeFree]
      exact F.levi.deleteEdges_le _) hxz
noncomputable def componentExpansionSupportMap
    (hlinear : F.Linear) {C : Zbp F} (hC : Zay F C) :
    PrivateVertexExpansion.Point (Z97 F C) →
      F.ZaR (Z6q F C)
  | .inl x =>
      ⟨x.1, Z2S F hC x⟩
  | .inr a =>
      ⟨privatePoint F (graphEdgeWitness F hlinear (C := C) a),
        ⟨(graphEdgeWitness F hlinear (C := C) a).1,
          (graphEdgeWitness F hlinear (C := C) a).2.1,
          (Z8l F
            (graphEdgeWitness F hlinear (C := C) a)).1⟩⟩
theorem Z2r
    (hlinear : F.Linear) {C : Zbp F} (hC : Zay F C) :
    Function.Injective (componentExpansionSupportMap F hlinear hC) := by
  intro p q hpq
  apply (componentExpansionEmbedding F hlinear C).vertex.injective
  have hpqVal := congrArg Subtype.val hpq
  rcases p with x | a <;> rcases q with y | b <;>
    exact hpqVal
theorem Z2d
    (hlinear : F.Linear) (hbridge : F.BridgeAtEveryEdge)
    {C : Zbp F} (hC : Zay F C) :
    Function.Surjective (componentExpansionSupportMap F hlinear hC) := by
  intro z
  rcases z.2 with ⟨e, heC, hze⟩
  let eC : Zbx F C := ⟨e, heC⟩
  let edgeEquiv := graphEdgeEquivHyperedge F hlinear hbridge hC
  let a : (Z97 F C).edgeSet := edgeEquiv.symm eC
  have ha : edgeEquiv a = eC := edgeEquiv.apply_symm_apply eC
  have hwitness :
      (graphEdgeWitness F hlinear (C := C) a).1 = e := by
    have hval := congrArg Subtype.val ha
    simpa [edgeEquiv, graphEdgeEquivHyperedge,
      graphEdgeEquivContractibleEdge, contractibleEdgeEquivHyperedge] using hval
  have hzWitness :
      F.Inc z.1 (graphEdgeWitness F hlinear (C := C) a).1 := by
    rw [hwitness]
    exact hze
  rcases (Z30 F
      (graphEdgeWitness F hlinear (C := C) a) z.1).mp hzWitness with
    hcore | hprivate
  · have hzC : Sum.inl z.1 ∈ C.supp :=
      C.mem_supp_of_adj_mem_supp
        (graphEdgeWitness F hlinear (C := C) a).2.1 hcore.symm
    let x : Point F C := ⟨z.1, hzC⟩
    refine ⟨Sum.inl x, ?_⟩
    apply Subtype.ext
    rfl
  · refine ⟨Sum.inr a, ?_⟩
    apply Subtype.ext
    exact hprivate.symm
noncomputable def componentExpansionVertexEquiv
    (hlinear : F.Linear) (hbridge : F.BridgeAtEveryEdge)
    {C : Zbp F} (hC : Zay F C) :
    PrivateVertexExpansion.Point (Z97 F C) ≃
      F.ZaR (Z6q F C) :=
  Equiv.ofBijective (componentExpansionSupportMap F hlinear hC)
    ⟨Z2r F hlinear hC,
      Z2d F hlinear hbridge hC⟩
noncomputable def componentExpansionEdgeEquiv
    (hlinear : F.Linear) (hbridge : F.BridgeAtEveryEdge)
    {C : Zbp F} (hC : Zay F C) :
    (Z97 F C).edgeSet ≃ Z6q F C := by
  change (Z97 F C).edgeSet ≃ Zbx F C
  exact graphEdgeEquivHyperedge F hlinear hbridge hC
@[simp]
theorem Z3P
    (hlinear : F.Linear) (hbridge : F.BridgeAtEveryEdge)
    {C : Zbp F} (hC : Zay F C)
    (a : (Z97 F C).edgeSet) :
    (componentExpansionEdgeEquiv F hlinear hbridge hC a).1 =
      (graphEdgeWitness F hlinear (C := C) a).1 :=
  rfl
@[simp]
theorem Z3z
    (hlinear : F.Linear) {C : Zbp F} (hC : Zay F C)
    (p : PrivateVertexExpansion.Point (Z97 F C)) :
    (componentExpansionSupportMap F hlinear hC p).1 =
      (componentExpansionEmbedding F hlinear C).vertex p := by
  rcases p with x | a <;> rfl
noncomputable def activeComponentExpansionRestrictionIso
    (hlinear : F.Linear) (hbridge : F.BridgeAtEveryEdge)
    {C : Zbp F} (hC : Zay F C) :
    Iso (Z64 (Z97 F C))
      (F.Z96 (Z6q F C)) where
  vertexEquiv := componentExpansionVertexEquiv F hlinear hbridge hC
  edgeEquiv := componentExpansionEdgeEquiv F hlinear hbridge hC
  map_inc_iff := by
    intro p a
    let emb := componentExpansionEmbedding F hlinear C
    have hset := Set.ext_iff.mp (emb.map_edge a) (emb.vertex p)
    change (Z64 (Z97 F C)).Inc p a ↔
      F.Inc
        (componentExpansionSupportMap F hlinear hC p).1
        (componentExpansionEdgeEquiv F hlinear hbridge hC a).1
    rw [Z3z, Z3P]
    change _ ↔ F.Inc
      ((componentExpansionEmbedding F hlinear C).vertex p)
      ((componentExpansionEmbedding F hlinear C).edge a)
    constructor
    · intro hp
      apply hset.mp
      exact ⟨p, hp, rfl⟩
    · intro hp
      rcases hset.mpr hp with ⟨q, hqa, hqp⟩
      have hq : q = p := emb.vertex.injective hqp
      subst q
      exact hqa
section Constructible
variable {V₀ E₀ : Type w} (K : TripleSystem V₀ E₀)
variable [Fintype V₀] [Fintype E₀] [DecidableEq V₀] [DecidableEq E₀]
  [DecidableRel K.levi.Adj]
theorem Z24
    (hlinear : K.Linear) (hbridge : K.BridgeAtEveryEdge)
    (hberge : K.EvenBergeCycles) {C : Zbp K}
    (hC : Zay K C) :
    Constructible (K.Z96 (Z6q K C)) := by
  letI : Fintype (Point K C) := Fintype.ofFinite (Point K C)
  have hExpansion :
      Constructible (Z64 (Z97 K C)) :=
    Constructible.ofExpansion (Z97 K C)
      (Z4f K hlinear hberge C)
  exact Constructible.ofIso hExpansion
    (activeComponentExpansionRestrictionIso K hlinear hbridge hC)
end Constructible
end
end BridgeBlock
end TripleSystem
end P593
end
-- ARISTOTLE_FORWARD_TARGET DU1
-- ARISTOTLE_FORWARD_TARGET DU2
-- ARISTOTLE_FORWARD_TARGET DU3
-- ARISTOTLE_FORWARD_TARGET DU4
section
namespace P593
universe u v w z
namespace TripleSystem
variable {V : Type u} {E : Type v} {W : Type w} {D : Type z}
theorem Z76 (F : TripleSystem V E) (G : TripleSystem W D)
    (hF : F.Linear) (hG : G.Linear) :
    (F.Za7 G).Linear := by
  intro e f x y hef hxe hxf hye hyf
  rcases e with e | d <;> rcases f with f | c <;>
    rcases x with x | x <;> rcases y with y | y <;>
    simp only [Z5k, Z5l,
      Z4l, Z4m] at *
  · exact congrArg Sum.inl (hF (Sum.inl_injective.ne_iff.mp hef) hxe hxf hye hyf)
  · exact congrArg Sum.inr (hG (Sum.inr_injective.ne_iff.mp hef) hxe hxf hye hyf)
def Z6T (F : TripleSystem V E) (G : TripleSystem W D) :
    (F.Za7 G).levi ≃g F.levi ⊕g G.levi := by
  let e : ((V ⊕ W) ⊕ (E ⊕ D)) ≃ ((V ⊕ E) ⊕ (W ⊕ D)) :=
    { toFun := fun
        | .inl (.inl x) => .inl (.inl x)
        | .inl (.inr y) => .inr (.inl y)
        | .inr (.inl a) => .inl (.inr a)
        | .inr (.inr b) => .inr (.inr b)
      invFun := fun
        | .inl (.inl x) => .inl (.inl x)
        | .inl (.inr a) => .inr (.inl a)
        | .inr (.inl y) => .inl (.inr y)
        | .inr (.inr b) => .inr (.inr b)
      left_inv := by rintro ((x | y) | (a | b)) <;> rfl
      right_inv := by rintro ((x | a) | (y | b)) <;> rfl }
  exact
    { toEquiv := e
      map_rel_iff' := by
        rintro ((x | y) | (a | b)) ((x' | y') | (a' | b')) <;>
          simp [e] }
private theorem Z7r {A B : Type*}
    {P : _root_.SimpleGraph A} {Q : _root_.SimpleGraph B}
    (f : P ≃g Q) (a b : A) :
    P.IsBridge s(a, b) ↔ Q.IsBridge s(f a, f b) := by
  let fd : P.deleteEdges {s(a, b)} ≃g
      Q.deleteEdges {s(f a, f b)} :=
    { toEquiv := f.toEquiv
      map_rel_iff' := by
        intro x y
        simp [f.map_adj_iff] }
  change (¬(P.deleteEdges {s(a, b)}).Reachable a b) ↔
    ¬(Q.deleteEdges {s(f a, f b)}).Reachable (f a) (f b)
  exact not_congr fd.reachable_iff.symm
private theorem Z6O {A B : Type*}
    (P : _root_.SimpleGraph A) (Q : _root_.SimpleGraph B) (a b : A) :
    (P ⊕g Q).Reachable (.inl a) (.inl b) ↔ P.Reachable a b := by
  constructor
  · rintro ⟨p⟩
    let pull {s t : A ⊕ B} (p : (P ⊕g Q).Walk s t) :
        ∀ a : A, s = .inl a →
          ∃ b : A, t = .inl b ∧ Nonempty (P.Walk a b) := by
      induction p with
      | nil =>
          intro a ha
          exact ⟨a, ha, ⟨.nil⟩⟩
      | @cons u v t h p ih =>
          intro a ha
          subst u
          cases v with
          | inl a' =>
              have h' : P.Adj a a' := by simpa using h
              obtain ⟨b, hb, ⟨q⟩⟩ := ih a' rfl
              exact ⟨b, hb, ⟨.cons h' q⟩⟩
          | inr y => simp at h
    obtain ⟨b', hb', ⟨q⟩⟩ := pull p a rfl
    have hbb' : b = b' := Sum.inl_injective hb'
    subst b'
    exact ⟨q⟩
  · intro h
    exact h.map (_root_.SimpleGraph.Embedding.sumInl (G := P) (H := Q)).toHom
private theorem Z8R {A B : Type*}
    (P : _root_.SimpleGraph A) (Q : _root_.SimpleGraph B) (a b : A)
    (h : P.IsBridge s(a, b)) :
    (P ⊕g Q).IsBridge s(.inl a, .inl b) := by
  rw [_root_.SimpleGraph.isBridge_iff] at h ⊢
  intro hr
  apply h
  apply (Z6O (P.deleteEdges {s(a, b)}) Q a b).mp
  have hdelete :
      (P ⊕g Q).deleteEdges {s(.inl a, .inl b)} =
        P.deleteEdges {s(a, b)} ⊕g Q := by
    ext (x | x) (y | y) <;> simp
  rw [← hdelete]
  exact hr
private theorem Z94 {A B : Type*}
    (P : _root_.SimpleGraph A) (Q : _root_.SimpleGraph B) (a b : B)
    (h : Q.IsBridge s(a, b)) :
    (P ⊕g Q).IsBridge s(.inr a, .inr b) := by
  have hleft : (Q ⊕g P).IsBridge s(.inl a, .inl b) :=
    Z8R Q P a b h
  exact (Z7r (_root_.SimpleGraph.Iso.sumComm)
    (.inl a) (.inl b)).mp hleft
theorem Z5O {A B : Type*}
    (P : _root_.SimpleGraph A) (Q : _root_.SimpleGraph B)
    {a : A} (c : (P ⊕g Q).Walk (.inl a) (.inl a)) (hc : c.IsCycle) :
    ∃ (a' : A) (d : P.Walk a' a'), d.IsCycle ∧ c.length = d.length := by
  classical
  have hsupp : ∀ x ∈ c.support,
      x ∈ Set.range (Sum.inl : A → A ⊕ B) := by
    intro x hx
    cases x with
    | inl x => exact ⟨x, rfl⟩
    | inr y =>
        exact False.elim
          ((_root_.SimpleGraph.not_reachable_sum_inl_inr (G := P) (H := Q) a y)
            ⟨c.takeUntil (.inr y) hx⟩)
  let ci := c.induce (Set.range (Sum.inl : A → A ⊕ B)) hsupp
  let proj : (P ⊕g Q).induce (Set.range (Sum.inl : A → A ⊕ B)) →g P :=
    { toFun := fun x => Classical.choose x.2
      map_rel' := by
        intro x y hxy
        have hx := Classical.choose_spec x.2
        have hy := Classical.choose_spec y.2
        have hxy' : (P ⊕g Q).Adj x.1 y.1 :=
          _root_.SimpleGraph.induce_adj.mp hxy
        rw [← hx, ← hy] at hxy'
        simpa using hxy' }
  have hproj : Function.Injective proj := by
    intro x y hxy
    apply Subtype.ext
    have hx := Classical.choose_spec x.2
    have hy := Classical.choose_spec y.2
    rw [← hx, ← hy]
    exact congrArg Sum.inl hxy
  have hmap_ci :
      ci.map (_root_.SimpleGraph.Embedding.induce
        (G := P ⊕g Q) (Set.range (Sum.inl : A → A ⊕ B))).toHom = c := by
    simp [ci]
  have hci : ci.IsCycle := by
    apply _root_.SimpleGraph.Walk.IsCycle.of_map
    rw [hmap_ci]
    exact hc
  let d := ci.map proj
  have hd : d.IsCycle := hci.map hproj
  have hci_len : ci.length = c.length := by
    calc
      ci.length =
          (ci.map (_root_.SimpleGraph.Embedding.induce
            (G := P ⊕g Q) (Set.range (Sum.inl : A → A ⊕ B))).toHom).length := by
        symm
        apply _root_.SimpleGraph.Walk.length_map
      _ = c.length := congrArg
        (fun w : (P ⊕g Q).Walk (.inl a) (.inl a) => w.length) hmap_ci
  have hd_len : d.length = ci.length := by simp [d]
  exact ⟨proj ⟨Sum.inl a, ⟨a, rfl⟩⟩, d, hd,
    hci_len.symm.trans hd_len.symm⟩
theorem Z61 {A B : Type*}
    (P : _root_.SimpleGraph A) (Q : _root_.SimpleGraph B)
    {b : B} (c : (P ⊕g Q).Walk (.inr b) (.inr b)) (hc : c.IsCycle) :
    ∃ (b' : B) (d : Q.Walk b' b'), d.IsCycle ∧ c.length = d.length := by
  let f : P ⊕g Q ≃g Q ⊕g P := _root_.SimpleGraph.Iso.sumComm
  let c' := c.map f.toHom
  have hc' : c'.IsCycle := hc.map f.injective
  obtain ⟨b', d, hd, hlen⟩ := Z5O Q P c' hc'
  refine ⟨b', d, hd, ?_⟩
  calc
    c.length = c'.length := by
      symm
      exact _root_.SimpleGraph.Walk.length_map f.toHom c
    _ = d.length := hlen
private theorem Z5u {A B : Type*}
    (P : _root_.SimpleGraph A) (Q : _root_.SimpleGraph B) (n : ℕ)
    (hP : ∀ ⦃a : A⦄ (c : P.Walk a a), c.IsCycle → n ∣ c.length)
    {a : A} (c : (P ⊕g Q).Walk (.inl a) (.inl a)) (hc : c.IsCycle) :
    n ∣ c.length := by
  classical
  have hsupp : ∀ x ∈ c.support,
      x ∈ Set.range (Sum.inl : A → A ⊕ B) := by
    intro x hx
    cases x with
    | inl x => exact ⟨x, rfl⟩
    | inr y =>
        exact False.elim
          ((_root_.SimpleGraph.not_reachable_sum_inl_inr (G := P) (H := Q) a y)
            ⟨c.takeUntil (.inr y) hx⟩)
  let ci := c.induce (Set.range (Sum.inl : A → A ⊕ B)) hsupp
  let proj : (P ⊕g Q).induce (Set.range (Sum.inl : A → A ⊕ B)) →g P :=
    { toFun := fun x => Classical.choose x.2
      map_rel' := by
        intro x y hxy
        have hx := Classical.choose_spec x.2
        have hy := Classical.choose_spec y.2
        have hxy' : (P ⊕g Q).Adj x.1 y.1 :=
          _root_.SimpleGraph.induce_adj.mp hxy
        rw [← hx, ← hy] at hxy'
        simpa using hxy' }
  have hproj : Function.Injective proj := by
    intro x y hxy
    apply Subtype.ext
    have hx := Classical.choose_spec x.2
    have hy := Classical.choose_spec y.2
    rw [← hx, ← hy]
    exact congrArg Sum.inl hxy
  have hmap_ci :
      ci.map (_root_.SimpleGraph.Embedding.induce
        (G := P ⊕g Q) (Set.range (Sum.inl : A → A ⊕ B))).toHom = c := by
    simp [ci]
  have hci : ci.IsCycle := by
    apply _root_.SimpleGraph.Walk.IsCycle.of_map
    rw [hmap_ci]
    exact hc
  let q := ci.map proj
  have hq : q.IsCycle := hci.map hproj
  have hci_len : ci.length = c.length := by
    calc
      ci.length =
          (ci.map (_root_.SimpleGraph.Embedding.induce
            (G := P ⊕g Q) (Set.range (Sum.inl : A → A ⊕ B))).toHom).length := by
        symm
        apply _root_.SimpleGraph.Walk.length_map
      _ = c.length := congrArg
        (fun w : (P ⊕g Q).Walk (.inl a) (.inl a) => w.length) hmap_ci
  have hq_len : q.length = ci.length := by simp [q]
  rw [← hci_len, ← hq_len]
  exact hP q hq
private theorem Z5B {A B : Type*}
    (P : _root_.SimpleGraph A) (Q : _root_.SimpleGraph B) (n : ℕ)
    (hQ : ∀ ⦃b : B⦄ (c : Q.Walk b b), c.IsCycle → n ∣ c.length)
    {b : B} (c : (P ⊕g Q).Walk (.inr b) (.inr b)) (hc : c.IsCycle) :
    n ∣ c.length := by
  let f : P ⊕g Q ≃g Q ⊕g P := _root_.SimpleGraph.Iso.sumComm
  let c' := c.map f.toHom
  have hc' : c'.IsCycle := hc.map f.injective
  have hdiv := Z5u Q P n hQ c' hc'
  rw [← _root_.SimpleGraph.Walk.length_map f.toHom c]
  exact hdiv
theorem Z3L (F : TripleSystem V E)
    (G : TripleSystem W D) (hF : F.BridgeAtEveryEdge)
    (hG : G.BridgeAtEveryEdge) :
    (F.Za7 G).BridgeAtEveryEdge := by
  intro e
  cases e with
  | inl e =>
      rcases hF e with ⟨x, hxedge, hxbridge⟩
      refine ⟨.inl x, ?_, ?_⟩
      · simpa using hxedge
      · have hsum := Z8R F.levi G.levi
          (.inl x) (.inr e) hxbridge
        have hiso := (Z7r (Z6T F G)
          (.inl (.inl x)) (.inr (.inl e))).mpr hsum
        simpa [Z6T] using hiso
  | inr e =>
      rcases hG e with ⟨y, hyedge, hybridge⟩
      refine ⟨.inr y, ?_, ?_⟩
      · simpa using hyedge
      · have hsum := Z94 F.levi G.levi
          (.inl y) (.inr e) hybridge
        have hiso := (Z7r (Z6T F G)
          (.inl (.inr y)) (.inr (.inr e))).mpr hsum
        simpa [Z6T] using hiso
theorem Z4k (F : TripleSystem V E)
    (G : TripleSystem W D) (hF : F.EvenBergeCycles)
    (hG : G.EvenBergeCycles) :
    (F.Za7 G).EvenBergeCycles := by
  intro z c hc
  let f := Z6T F G
  let c' := c.map f.toHom
  have hc' : c'.IsCycle := hc.map f.injective
  have hlen : c'.length = c.length := by simp [c']
  rw [← hlen]
  cases z with
  | inl z =>
      cases z with
      | inl x =>
          exact Z5u F.levi G.levi 4 hF c' hc'
      | inr y =>
          exact Z5B F.levi G.levi 4 hG c' hc'
  | inr z =>
      cases z with
      | inl e =>
          exact Z5u F.levi G.levi 4 hF c' hc'
      | inr d =>
          exact Z5B F.levi G.levi 4 hG c' hc'
theorem Z60 (F : TripleSystem V E)
    (G : TripleSystem W D) (hF : F.Intrinsic) (hG : G.Intrinsic) :
    (F.Za7 G).Intrinsic := by
  exact ⟨Z76 F G hF.1 hG.1,
    Z3L F G hF.2.1 hG.2.1,
    Z4k F G hF.2.2 hG.2.2⟩
end TripleSystem
end P593
end
-- ARISTOTLE_TARGET F2
section
namespace P593
universe u
namespace TripleSystem
theorem Z20 {V : Type u}
    (G : _root_.SimpleGraph V) :
    (Z64 G).BridgeAtEveryEdge := by
  intro e
  let x := PrivateVertexExpansion.Za6 G e
  have hAdj : (Z64 G).levi.Adj (.inl x) (.inr e) := by
    simp [x]
  refine ⟨x, hAdj, ?_⟩
  rw [show s(Sum.inl x, Sum.inr e) = s(Sum.inr e, Sum.inl x) from Sym2.eq_swap]
  apply P593.SimpleGraph.Z32 _ hAdj.symm
  intro w hw
  rcases w with y | f
  · exact (Z5r (Z64 G) hw).elim
  · congr 1
    exact (by simpa [x] using hw : e = f).symm
end TripleSystem
end P593
end
-- ARISTOTLE_TARGET F1
-- ARISTOTLE_TARGET F3A
-- ARISTOTLE_TARGET F3B
-- ARISTOTLE_TARGET F3
-- ARISTOTLE_TARGET F4
section
namespace P593
universe u
namespace TripleSystem
theorem Z4n {V : Type u}
    (G : _root_.SimpleGraph V) :
    (Z64 G).Linear := by
  unfold TripleSystem.Linear
  intro e f x y
  simp [Z64] at *
  cases x <;> cases y <;>
    simp_all +decide [PrivateVertexExpansion.Inc]
  all_goals grind +suggestions
theorem Z2O {V : Type u}
    (G : _root_.SimpleGraph V)
    {z : PrivateVertexExpansion.Point G ⊕ PrivateVertexExpansion.Edge G}
    (c : (Z64 G).levi.Walk z z) (hc : c.IsCycle)
    (e : PrivateVertexExpansion.Edge G) :
    Sum.inl (PrivateVertexExpansion.Za6 G e) ∉ c.support := by
  let x := PrivateVertexExpansion.Za6 G e
  let v : PrivateVertexExpansion.Point G ⊕
      PrivateVertexExpansion.Edge G := Sum.inl x
  have hAdj : (Z64 G).levi.Adj v (.inr e) := by
    simp [v, x]
  have hbridge :
      (Z64 G).levi.IsBridge s(v, Sum.inr e) := by
    rw [show s(v, Sum.inr e) = s(Sum.inr e, v) from Sym2.eq_swap]
    apply P593.SimpleGraph.Z32 _ hAdj.symm
    intro w hw
    rcases w with y | f
    · exact (Z5r (Z64 G) hw).elim
    · congr 1
      exact (by simpa [v, x] using hw : e = f).symm
  intro hx
  obtain ⟨a, ha, hxa⟩ :=
    (c.mem_support_iff_exists_mem_edges_of_not_nil hc.not_nil).mp hx
  obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp hxa
  have haw : (Z64 G).levi.Adj v w :=
    c.edges_subset_edgeSet ha
  rcases w with y | f
  · exact (Z5r (Z64 G) haw).elim
  · have hef : e = f := by simpa [v, x] using haw
    subst f
    exact hbridge.notMem_edges_of_isCycle hc ha
theorem ZY {V : Type u}
    (G : _root_.SimpleGraph V) {x y : V}
    (p : (Z64 G).levi.Walk
      (Sum.inl (PrivateVertexExpansion.core G x))
      (Sum.inl (PrivateVertexExpansion.core G y)))
    (hp : p.IsTrail)
    (hprivate : ∀ e : PrivateVertexExpansion.Edge G,
      Sum.inl (PrivateVertexExpansion.Za6 G e) ∉ p.support) :
    ∃ q : G.Walk x y, p.length = 2 * q.length := by
  induction hn : p.length using Nat.strongRec generalizing x y with
  | ind n ih =>
      cases p with
      | nil =>
          exact ⟨.nil, by simpa using hn.symm⟩
      | @cons _ w _ hxw p =>
          rcases w with w | e
          · exact (Z5r
              (Z64 G) hxw).elim
          · obtain ⟨w, hew, r, rfl⟩ := p.exists_eq_cons_of_ne (by simp)
            rcases w with w | f
            · rcases w with x' | f
              · have hxe : x ∈ (e : Sym2 V) := by simpa using hxw
                have hx'Inc : (Z64 G).Inc
                    (PrivateVertexExpansion.core G x') e := by
                  simpa [PrivateVertexExpansion.core] using hew
                have hx'e : x' ∈ (e : Sym2 V) :=
                  (Z3T G x' e).mp hx'Inc
                have hxx' : x ≠ x' := by
                  intro h
                  subst x'
                  have hnot :=
                    (_root_.SimpleGraph.Walk.isTrail_cons hxw
                      (_root_.SimpleGraph.Walk.cons hew r)).mp hp |>.2
                  apply hnot
                  rw [_root_.SimpleGraph.Walk.edges_cons]
                  exact List.mem_cons.mpr (Or.inl (Sym2.eq_swap))
                have heq : (e : Sym2 V) = s(x, x') :=
                  (Sym2.mem_and_mem_iff hxx').mp ⟨hxe, hx'e⟩
                have hxx'Edge : s(x, x') ∈ G.edgeSet := by
                  rw [← heq]
                  exact e.property
                have hxx'Adj : G.Adj x x' := by
                  simpa using hxx'Edge
                have hrtrail : r.IsTrail :=
                  (_root_.SimpleGraph.Walk.isTrail_cons hew r).mp
                    ((_root_.SimpleGraph.Walk.isTrail_cons hxw
                      (_root_.SimpleGraph.Walk.cons hew r)).mp hp).1 |>.1
                have hrprivate : ∀ d : PrivateVertexExpansion.Edge G,
                    Sum.inl (PrivateVertexExpansion.Za6 G d) ∉
                      r.support := by
                  intro d hd
                  exact hprivate d (by simp [hd])
                have hr_lt : r.length <
                    (_root_.SimpleGraph.Walk.cons hxw
                      (_root_.SimpleGraph.Walk.cons hew r)).length := by
                  simp
                obtain ⟨q, hq⟩ :=
                  ih r.length (by simpa only [hn] using hr_lt)
                    r hrtrail hrprivate rfl
                refine ⟨q.cons hxx'Adj, ?_⟩
                simp only [_root_.SimpleGraph.Walk.length_cons] at hn ⊢
                omega
              · have hfmem :
                    Sum.inl (PrivateVertexExpansion.Za6 G f) ∈
                      (_root_.SimpleGraph.Walk.cons hxw
                        (_root_.SimpleGraph.Walk.cons hew r)).support := by
                  simp only [_root_.SimpleGraph.Walk.support_cons, List.mem_cons]
                  exact Or.inr (Or.inr r.start_mem_support)
                exact (hprivate f hfmem).elim
            · exact (Z65
                (Z64 G) hew).elim
theorem Z2v {V : Type u}
    (G : _root_.SimpleGraph V) (hG : G.Colorable 2) :
    (Z64 G).EvenBergeCycles := by
  classical
  intro z c hc
  obtain ⟨x, hx⟩ : ∃ x : V,
      Sum.inl (PrivateVertexExpansion.core G x) ∈ c.support := by
    rcases z with (x | e) | e
    · exact ⟨x, c.start_mem_support⟩
    · exact (Z2O G c hc e
        c.start_mem_support).elim
    · obtain ⟨w, hw, hew⟩ :=
        _root_.SimpleGraph.adj_of_mem_walk_support c hc.not_nil
          c.start_mem_support
      rcases w with (x | f) | f
      · exact ⟨x, hw⟩
      · exact (Z2O G c hc f hw).elim
      · exact (Z65 (Z64 G) hew).elim
  let d := c.rotate (Sum.inl (PrivateVertexExpansion.core G x)) hx
  have hdcycle : d.IsCycle := by
    exact hc.rotate hx
  have hdprivate : ∀ e : PrivateVertexExpansion.Edge G,
      Sum.inl (PrivateVertexExpansion.Za6 G e) ∉ d.support := by
    intro e he
    apply Z2O G c hc e
    exact (c.mem_support_rotate_iff
      (Sum.inl (PrivateVertexExpansion.core G x)) hx).mp he
  obtain ⟨q, hq⟩ :=
    ZY G d hdcycle.isTrail
      hdprivate
  have hqeven : Even q.length :=
    (_root_.SimpleGraph.two_colorable_iff_forall_loop_even.mp hG) x q
  obtain ⟨k, hk⟩ := hqeven
  use k
  dsimp only [d] at hq
  simp only [_root_.SimpleGraph.Walk.length_rotate] at hq
  omega
theorem Z3H {V : Type u}
    (G : _root_.SimpleGraph V) (hG : G.Colorable 2) :
    (Z64 G).Intrinsic := by
  exact ⟨Z4n G,
    Z20 G,
    Z2v G hG⟩
end TripleSystem
end P593
end
section
namespace P593
universe u₀ v₀ u₁ v₁
namespace TripleSystem.OnePointAmalgamation
variable {V₀ : Type u₀} {E₀ : Type v₀}
variable {V₁ : Type u₁} {E₁ : Type v₁}
private theorem Z4b
    {X : Type*} (G : SimpleGraph X) (A B : Set X) (root : X)
    (hinter : A ∩ B ⊆ {root})
    (hadj : ∀ ⦃x y⦄, G.Adj x y →
      (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B))
    {u v : X} (p : G.Walk u v) (hroot : root ∉ p.support)
    (hu : u ∈ A) : ∀ x ∈ p.support, x ∈ A := by
  induction p <;> simp_all +decide [Set.subset_def]
  grind
private theorem Z2l
    {X : Type*} (G : SimpleGraph X) (A B : Set X) (root : X)
    (hrootA : root ∈ A) (hrootB : root ∈ B)
    (hinter : A ∩ B ⊆ {root})
    (hadj : ∀ ⦃x y⦄, G.Adj x y →
      (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B))
    (c : G.Walk root root) (hc : c.IsCycle) :
    (∀ x ∈ c.support, x ∈ A) ∨ (∀ x ∈ c.support, x ∈ B) := by
  cases c with
  | nil => exact (hc.not_nil (by simp)).elim
  | cons h p =>
      have hpPath : p.IsPath := (SimpleGraph.Walk.cons_isCycle_iff p h).mp hc |>.1
      have hpNonNil : ¬ p.Nil := by
        intro hp
        exact h.ne hp.eq.symm
      have hdecomp : p.dropLast.support ++ [root] = p.support :=
        p.support_dropLast_concat hpNonNil
      have hrootNot : root ∉ p.dropLast.support := by
        intro hr
        have hn := hpPath.support_nodup
        rw [← hdecomp, List.nodup_append] at hn
        exact (hn.2.2 root hr root (by simp)) rfl
      rcases hadj h with hA | hB
      · left
        intro x hx
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hrootA
        · rw [← hdecomp] at hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact Z4b G A B root hinter hadj
              p.dropLast hrootNot hA.2 x hx
          · exact hrootA
      · right
        intro x hx
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hrootB
        · rw [← hdecomp] at hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact Z4b G B A root
              (by intro x hx; exact hinter ⟨hx.2, hx.1⟩)
              (by intro x y hxy; exact (hadj hxy).symm)
              p.dropLast hrootNot hB.2 x hx
          · exact hrootB
theorem Z3u
    {X : Type*} (G : SimpleGraph X) (A B : Set X) (root : X)
    (hrootA : root ∈ A) (hrootB : root ∈ B)
    (hinter : A ∩ B ⊆ {root})
    (hadj : ∀ ⦃x y⦄, G.Adj x y →
      (x ∈ A ∧ y ∈ A) ∨ (x ∈ B ∧ y ∈ B))
    {z : X} (c : G.Walk z z) (hc : c.IsCycle) :
    (∀ x ∈ c.support, x ∈ A) ∨ (∀ x ∈ c.support, x ∈ B) := by
  classical
  by_cases hr : root ∈ c.support
  · let d := c.rotate root hr
    have hd : d.IsCycle := hc.rotate hr
    rcases Z2l G A B root
        hrootA hrootB hinter hadj d hd with hA | hB
    · left
      intro x hx
      exact hA x ((c.mem_support_rotate_iff root hr).2 hx)
    · right
      intro x hx
      exact hB x ((c.mem_support_rotate_iff root hr).2 hx)
  · cases c with
    | nil => exact (hc.not_nil (by simp)).elim
    | cons h p =>
        rcases hadj h with hA | hB
        · exact Or.inl
            (Z4b G A B root hinter hadj
              (.cons h p) hr hA.1)
        · exact Or.inr
            (Z4b G B A root
              (by intro x hx; exact hinter ⟨hx.2, hx.1⟩)
              (by intro x y hxy; exact (hadj hxy).symm)
              (.cons h p) hr hB.1)
theorem Z4a
    {X Y : Type*} {G : SimpleGraph X} {H : SimpleGraph Y}
    (f : G ↪g H) {z : Y} (c : H.Walk z z) (hc : c.IsCycle)
    (hsupp : ∀ y ∈ c.support, y ∈ Set.range f) :
    ∃ (x : X) (d : G.Walk x x), d.IsCycle ∧ c.length = d.length := by
  classical
  let ci := c.induce (Set.range f) hsupp
  let g := f.isoInduceRange
  let d := ci.map g.symm.toHom
  refine ⟨g.symm ⟨z, hsupp z c.start_mem_support⟩, d, ?_, ?_⟩
  · have hmap_ci :
        ci.map (SimpleGraph.Embedding.induce
          (G := H) (Set.range f)).toHom = c := by
      simp [ci]
    have hci : ci.IsCycle := by
      apply SimpleGraph.Walk.IsCycle.of_map
      rw [hmap_ci]
      exact hc
    exact hci.map g.symm.injective
  · have hmap_ci :
        ci.map (SimpleGraph.Embedding.induce
          (G := H) (Set.range f)).toHom = c := by
      simp [ci]
    have hci_len : ci.length = c.length := by
      calc
        ci.length =
            (ci.map (SimpleGraph.Embedding.induce
              (G := H) (Set.range f)).toHom).length := by
          symm
          apply SimpleGraph.Walk.length_map
        _ = c.length := congrArg
          (fun w : H.Walk z z => w.length) hmap_ci
    have hd_len : d.length = ci.length := by simp [d]
    exact hci_len.symm.trans hd_len.symm
def Z8t
    (F₀ : TripleSystem V₀ E₀) (F₁ : TripleSystem V₁ E₁)
    (r₀ : V₀) (r₁ : V₁) :
    F₀.levi ↪g (amalgam F₀ F₁ r₀ r₁).levi where
  toFun
    | .inl x => .inl (left r₀ r₁ x)
    | .inr e => .inr (.inl e)
  inj' := by
    rintro (x | e) (y | f) h <;> simp_all
  map_rel_iff' := by
    rintro (x | e) (y | f)
    · change (amalgam F₀ F₁ r₀ r₁).levi.Adj (.inl (left r₀ r₁ x)) (.inl (left r₀ r₁ y)) ↔ _
      simp
    · change (amalgam F₀ F₁ r₀ r₁).levi.Adj (.inl (left r₀ r₁ x)) (.inr (.inl f)) ↔ _
      simp [amalgam]
    · change (amalgam F₀ F₁ r₀ r₁).levi.Adj (.inr (.inl e)) (.inl (left r₀ r₁ y)) ↔ _
      simp [amalgam]
    · change (amalgam F₀ F₁ r₀ r₁).levi.Adj (.inr (.inl e)) (.inr (.inl f)) ↔ _
      simp
def Z7Y
    (F₀ : TripleSystem V₀ E₀) (F₁ : TripleSystem V₁ E₁)
    (r₀ : V₀) (r₁ : V₁) :
    F₁.levi ↪g (amalgam F₀ F₁ r₀ r₁).levi where
  toFun
    | .inl y => .inl (right r₀ r₁ y)
    | .inr e => .inr (.inr e)
  inj' := by
    rintro (x | e) (y | f) h <;> simp_all
  map_rel_iff' := by
    rintro (x | e) (y | f)
    · change (amalgam F₀ F₁ r₀ r₁).levi.Adj (.inl (right r₀ r₁ x)) (.inl (right r₀ r₁ y)) ↔ _
      simp
    · change (amalgam F₀ F₁ r₀ r₁).levi.Adj (.inl (right r₀ r₁ x)) (.inr (.inr f)) ↔ _
      simp [amalgam]
    · change (amalgam F₀ F₁ r₀ r₁).levi.Adj (.inr (.inr e)) (.inl (right r₀ r₁ y)) ↔ _
      simp [amalgam]
    · change (amalgam F₀ F₁ r₀ r₁).levi.Adj (.inr (.inr e)) (.inr (.inr f)) ↔ _
      simp
theorem Z9Z
    (F₀ : TripleSystem V₀ E₀) (F₁ : TripleSystem V₁ E₁)
    (r₀ : V₀) (r₁ : V₁) (h₀ : F₀.Linear) (h₁ : F₁.Linear) :
    (amalgam F₀ F₁ r₀ r₁).Linear := by
  rw [TripleSystem.Z2u]
  intro e f hef
  cases e with
  | inl e =>
      cases f with
      | inl f =>
          intro q hq q' hq'
          rcases hq.1 with ⟨x, hxe, hxq⟩
          rcases hq.2 with ⟨y, hyf, hyq⟩
          rcases hq'.1 with ⟨x', hx'e, hx'q⟩
          rcases hq'.2 with ⟨y', hy'f, hy'q⟩
          have hxy : x = y :=
            Z9G r₀ r₁ (hxq.trans hyq.symm)
          have hxy' : x' = y' :=
            Z9G r₀ r₁ (hx'q.trans hy'q.symm)
          subst y
          subst y'
          have he_ne_f : e ≠ f := by
            intro h
            exact hef (congrArg Sum.inl h)
          have hxx' : x = x' := h₀ he_ne_f hxe hyf hx'e hy'f
          exact hxq.symm.trans ((congrArg (left r₀ r₁) hxx').trans hx'q)
      | inr f =>
          exact Z40 r₀ r₁
            (F₀.edgeSet e) (F₁.edgeSet f)
  | inr e =>
      cases f with
      | inl f =>
          intro q hq q' hq'
          exact Z40 r₀ r₁
            (F₀.edgeSet f) (F₁.edgeSet e) ⟨hq.2, hq.1⟩ ⟨hq'.2, hq'.1⟩
      | inr f =>
          intro q hq q' hq'
          rcases hq.1 with ⟨x, hxe, hxq⟩
          rcases hq.2 with ⟨y, hyf, hyq⟩
          rcases hq'.1 with ⟨x', hx'e, hx'q⟩
          rcases hq'.2 with ⟨y', hy'f, hy'q⟩
          have hxy : x = y :=
            Z9h r₀ r₁ (hxq.trans hyq.symm)
          have hxy' : x' = y' :=
            Z9h r₀ r₁ (hx'q.trans hy'q.symm)
          subst y
          subst y'
          have he_ne_f : e ≠ f := by
            intro h
            exact hef (congrArg Sum.inr h)
          have hxx' : x = x' := h₁ he_ne_f hxe hyf hx'e hy'f
          exact hxq.symm.trans ((congrArg (right r₀ r₁) hxx').trans hx'q)
theorem Z5V
    (F₀ : TripleSystem V₀ E₀) (F₁ : TripleSystem V₁ E₁)
    (r₀ : V₀) (r₁ : V₁) {x : V₀} {e : E₀}
    (h : s(Sum.inl x, Sum.inr e) ∈ SimpleGraph.bridgeEdges F₀.levi) :
    s(Sum.inl (left r₀ r₁ x), Sum.inr (Sum.inl e)) ∈
      SimpleGraph.bridgeEdges (amalgam F₀ F₁ r₀ r₁).levi := by
  let pp : Vertex r₀ r₁ → V₀ := lift r₀ r₁ id (fun _ => r₀) rfl
  let p : (Vertex r₀ r₁ ⊕ Edge E₀ E₁) → (V₀ ⊕ E₀)
    | .inl q => .inl (pp q)
    | .inr (.inl f) => .inr f
    | .inr (.inr _) => .inl r₀
  have hp_left (y : V₀) : p (.inl (left r₀ r₁ y)) = .inl y := by
    rfl
  have hp_right (y : V₁) : p (.inl (right r₀ r₁ y)) = .inl r₀ := by
    rfl
  have hpoint_left (q : Vertex r₀ r₁) (f : E₀)
      (hqf : ((amalgam F₀ F₁ r₀ r₁).levi.deleteEdges
        {s(Sum.inl (left r₀ r₁ x), Sum.inr (Sum.inl e))}).Adj
          (.inl q) (.inr (.inl f))) :
      (F₀.levi.deleteEdges {s(Sum.inl x, Sum.inr e)}).Adj
          (p (.inl q)) (p (.inr (.inl f))) := by
    rw [_root_.SimpleGraph.deleteEdges_adj] at hqf ⊢
    rw [TripleSystem.Z7d] at hqf ⊢
    have hi := hqf.1
    change q ∈ left r₀ r₁ '' F₀.edgeSet f at hi
    rcases hi with ⟨y, hy, rfl⟩
    refine ⟨hy, ?_⟩
    intro heq
    apply hqf.2
    simpa [p, pp, Sym2.eq_iff] using heq
  have hpoint_right (q : Vertex r₀ r₁) (f : E₁)
      (hqf : ((amalgam F₀ F₁ r₀ r₁).levi.deleteEdges
        {s(Sum.inl (left r₀ r₁ x), Sum.inr (Sum.inl e))}).Adj
          (.inl q) (.inr (.inr f))) :
      p (.inl q) = p (.inr (.inr f)) := by
    rw [_root_.SimpleGraph.deleteEdges_adj,
      TripleSystem.Z7d] at hqf
    have hi := hqf.1
    change q ∈ right r₀ r₁ '' F₁.edgeSet f at hi
    rcases hi with ⟨y, hy, rfl⟩
    rfl
  have hstep : ∀ {a b},
      ((amalgam F₀ F₁ r₀ r₁).levi.deleteEdges
        {s(Sum.inl (left r₀ r₁ x), Sum.inr (Sum.inl e))}).Adj a b →
      (F₀.levi.deleteEdges {s(Sum.inl x, Sum.inr e)}).Adj (p a) (p b) ∨
        p a = p b := by
    intro a b hab
    rcases a with q | (f | f) <;> rcases b with q' | (g | g)
    · exact False.elim (TripleSystem.Z5r
        (F := amalgam F₀ F₁ r₀ r₁)
        (((amalgam F₀ F₁ r₀ r₁).levi.deleteEdges_le _) hab))
    · exact Or.inl (hpoint_left q g hab)
    · exact Or.inr (hpoint_right q g hab)
    · have hr := hpoint_left q' f
          (((amalgam F₀ F₁ r₀ r₁).levi.deleteEdges _).adj_comm _ _ |>.mp hab)
      exact Or.inl ((F₀.levi.deleteEdges _).adj_comm _ _ |>.mp hr)
    · exact False.elim (TripleSystem.Z65
        (F := amalgam F₀ F₁ r₀ r₁)
        (((amalgam F₀ F₁ r₀ r₁).levi.deleteEdges_le _) hab))
    · exact False.elim (TripleSystem.Z65
        (F := amalgam F₀ F₁ r₀ r₁)
        (((amalgam F₀ F₁ r₀ r₁).levi.deleteEdges_le _) hab))
    · exact Or.inr (hpoint_right q' f
        (((amalgam F₀ F₁ r₀ r₁).levi.deleteEdges _).adj_comm _ _ |>.mp hab)).symm
    · exact False.elim (TripleSystem.Z65
        (F := amalgam F₀ F₁ r₀ r₁)
        (((amalgam F₀ F₁ r₀ r₁).levi.deleteEdges_le _) hab))
    · exact False.elim (TripleSystem.Z65
        (F := amalgam F₀ F₁ r₀ r₁)
        (((amalgam F₀ F₁ r₀ r₁).levi.deleteEdges_le _) hab))
  change F₀.levi.Adj (.inl x) (.inr e) ∧
    F₀.levi.IsBridge s(Sum.inl x, Sum.inr e) at h
  change (amalgam F₀ F₁ r₀ r₁).levi.Adj
      (.inl (left r₀ r₁ x)) (.inr (.inl e)) ∧
    (amalgam F₀ F₁ r₀ r₁).levi.IsBridge
      s(Sum.inl (left r₀ r₁ x), Sum.inr (Sum.inl e))
  constructor
  · rw [TripleSystem.Z7d] at h ⊢
    exact (Z8B F₀ F₁ r₀ r₁ x e).mpr h.1
  · rw [_root_.SimpleGraph.isBridge_iff] at h ⊢
    intro hab
    apply h.2
    rw [_root_.SimpleGraph.reachable_eq_reflTransGen] at hab ⊢
    have hmap : ∀ {a b}, Relation.ReflTransGen
        ((amalgam F₀ F₁ r₀ r₁).levi.deleteEdges
          {s(Sum.inl (left r₀ r₁ x), Sum.inr (Sum.inl e))}).Adj a b →
        Relation.ReflTransGen (F₀.levi.deleteEdges
          {s(Sum.inl x, Sum.inr e)}).Adj (p a) (p b) := by
      intro a b hr
      induction hr with
      | refl => exact .refl
      | tail hr hadj ih =>
          rcases hstep hadj with hs | heq
          · exact ih.tail hs
          · simpa [heq] using ih
    simpa [hp_left, p] using hmap hab
theorem Z5G
    (F₀ : TripleSystem V₀ E₀) (F₁ : TripleSystem V₁ E₁)
    (r₀ : V₀) (r₁ : V₁) {y : V₁} {e : E₁}
    (h : s(Sum.inl y, Sum.inr e) ∈ SimpleGraph.bridgeEdges F₁.levi) :
    s(Sum.inl (right r₀ r₁ y), Sum.inr (Sum.inr e)) ∈
      SimpleGraph.bridgeEdges (amalgam F₀ F₁ r₀ r₁).levi := by
  let pp : Vertex r₀ r₁ → V₁ := lift r₀ r₁ (fun _ => r₁) id rfl
  let p : (Vertex r₀ r₁ ⊕ Edge E₀ E₁) → (V₁ ⊕ E₁)
    | .inl q => .inl (pp q)
    | .inr (.inl _) => .inl r₁
    | .inr (.inr f) => .inr f
  have hp_left (x : V₀) : p (.inl (left r₀ r₁ x)) = .inl r₁ := by
    rfl
  have hp_right (x : V₁) : p (.inl (right r₀ r₁ x)) = .inl x := by
    rfl
  have hpoint_right (q : Vertex r₀ r₁) (f : E₁)
      (hqf : ((amalgam F₀ F₁ r₀ r₁).levi.deleteEdges
        {s(Sum.inl (right r₀ r₁ y), Sum.inr (Sum.inr e))}).Adj
          (.inl q) (.inr (.inr f))) :
      (F₁.levi.deleteEdges {s(Sum.inl y, Sum.inr e)}).Adj
          (p (.inl q)) (p (.inr (.inr f))) := by
    rw [_root_.SimpleGraph.deleteEdges_adj] at hqf ⊢
    rw [TripleSystem.Z7d] at hqf ⊢
    have hi := hqf.1
    change q ∈ right r₀ r₁ '' F₁.edgeSet f at hi
    rcases hi with ⟨x, hx, rfl⟩
    refine ⟨hx, ?_⟩
    intro heq
    apply hqf.2
    simpa [p, pp, Sym2.eq_iff] using heq
  have hpoint_left (q : Vertex r₀ r₁) (f : E₀)
      (hqf : ((amalgam F₀ F₁ r₀ r₁).levi.deleteEdges
        {s(Sum.inl (right r₀ r₁ y), Sum.inr (Sum.inr e))}).Adj
          (.inl q) (.inr (.inl f))) :
      p (.inl q) = p (.inr (.inl f)) := by
    rw [_root_.SimpleGraph.deleteEdges_adj,
      TripleSystem.Z7d] at hqf
    have hi := hqf.1
    change q ∈ left r₀ r₁ '' F₀.edgeSet f at hi
    rcases hi with ⟨x, hx, rfl⟩
    rfl
  have hstep : ∀ {a b},
      ((amalgam F₀ F₁ r₀ r₁).levi.deleteEdges
        {s(Sum.inl (right r₀ r₁ y), Sum.inr (Sum.inr e))}).Adj a b →
      (F₁.levi.deleteEdges {s(Sum.inl y, Sum.inr e)}).Adj (p a) (p b) ∨
        p a = p b := by
    intro a b hab
    rcases a with q | (f | f) <;> rcases b with q' | (g | g)
    · exact False.elim (TripleSystem.Z5r
        (F := amalgam F₀ F₁ r₀ r₁)
        (((amalgam F₀ F₁ r₀ r₁).levi.deleteEdges_le _) hab))
    · exact Or.inr (hpoint_left q g hab)
    · exact Or.inl (hpoint_right q g hab)
    · exact Or.inr (hpoint_left q' f
        (((amalgam F₀ F₁ r₀ r₁).levi.deleteEdges _).adj_comm _ _ |>.mp hab)).symm
    · exact False.elim (TripleSystem.Z65
        (F := amalgam F₀ F₁ r₀ r₁)
        (((amalgam F₀ F₁ r₀ r₁).levi.deleteEdges_le _) hab))
    · exact False.elim (TripleSystem.Z65
        (F := amalgam F₀ F₁ r₀ r₁)
        (((amalgam F₀ F₁ r₀ r₁).levi.deleteEdges_le _) hab))
    · have hr := hpoint_right q' f
          (((amalgam F₀ F₁ r₀ r₁).levi.deleteEdges _).adj_comm _ _ |>.mp hab)
      exact Or.inl ((F₁.levi.deleteEdges _).adj_comm _ _ |>.mp hr)
    · exact False.elim (TripleSystem.Z65
        (F := amalgam F₀ F₁ r₀ r₁)
        (((amalgam F₀ F₁ r₀ r₁).levi.deleteEdges_le _) hab))
    · exact False.elim (TripleSystem.Z65
        (F := amalgam F₀ F₁ r₀ r₁)
        (((amalgam F₀ F₁ r₀ r₁).levi.deleteEdges_le _) hab))
  change F₁.levi.Adj (.inl y) (.inr e) ∧
    F₁.levi.IsBridge s(Sum.inl y, Sum.inr e) at h
  change (amalgam F₀ F₁ r₀ r₁).levi.Adj
      (.inl (right r₀ r₁ y)) (.inr (.inr e)) ∧
    (amalgam F₀ F₁ r₀ r₁).levi.IsBridge
      s(Sum.inl (right r₀ r₁ y), Sum.inr (Sum.inr e))
  constructor
  · rw [TripleSystem.Z7d] at h ⊢
    exact (Z7G F₀ F₁ r₀ r₁ y e).mpr h.1
  · rw [_root_.SimpleGraph.isBridge_iff] at h ⊢
    intro hab
    apply h.2
    rw [_root_.SimpleGraph.reachable_eq_reflTransGen] at hab ⊢
    have hmap : ∀ {a b}, Relation.ReflTransGen
        ((amalgam F₀ F₁ r₀ r₁).levi.deleteEdges
          {s(Sum.inl (right r₀ r₁ y), Sum.inr (Sum.inr e))}).Adj a b →
        Relation.ReflTransGen (F₁.levi.deleteEdges
          {s(Sum.inl y, Sum.inr e)}).Adj (p a) (p b) := by
      intro a b hr
      induction hr with
      | refl => exact .refl
      | tail hr hadj ih =>
          rcases hstep hadj with hs | heq
          · exact ih.tail hs
          · simpa [heq] using ih
    simpa [hp_right, p] using hmap hab
theorem Z5e
    (F₀ : TripleSystem V₀ E₀) (F₁ : TripleSystem V₁ E₁)
    (r₀ : V₀) (r₁ : V₁)
    (h₀ : F₀.BridgeAtEveryEdge) (h₁ : F₁.BridgeAtEveryEdge) :
    (amalgam F₀ F₁ r₀ r₁).BridgeAtEveryEdge := by
  intro e
  cases e with
  | inl e =>
      rcases h₀ e with ⟨x, hx⟩
      exact ⟨left r₀ r₁ x, Z5V F₀ F₁ r₀ r₁ hx⟩
  | inr e =>
      rcases h₁ e with ⟨y, hy⟩
      exact ⟨right r₀ r₁ y, Z5G F₀ F₁ r₀ r₁ hy⟩
theorem Z5U
    (F₀ : TripleSystem V₀ E₀) (F₁ : TripleSystem V₁ E₁)
    (r₀ : V₀) (r₁ : V₁)
    (h₀ : F₀.EvenBergeCycles) (h₁ : F₁.EvenBergeCycles) :
    (amalgam F₀ F₁ r₀ r₁).EvenBergeCycles := by
  intro z c hc
  let f₀ := Z8t F₀ F₁ r₀ r₁
  let f₁ := Z7Y F₀ F₁ r₀ r₁
  let A : Set (Vertex r₀ r₁ ⊕ Edge E₀ E₁) := Set.range f₀
  let B : Set (Vertex r₀ r₁ ⊕ Edge E₀ E₁) := Set.range f₁
  let root : Vertex r₀ r₁ ⊕ Edge E₀ E₁ := .inl (left r₀ r₁ r₀)
  have hrootA : root ∈ A := by
    exact ⟨.inl r₀, rfl⟩
  have hrootB : root ∈ B := by
    refine ⟨.inl r₁, ?_⟩
    exact congrArg Sum.inl (root_eq r₀ r₁).symm
  have hinter : A ∩ B ⊆ {root} := by
    rintro w ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
    rcases a with x | e <;> rcases b with y | f
    · change Sum.inl (right r₀ r₁ y) = Sum.inl (left r₀ r₁ x) at hb
      have hx := (Z8u r₀ r₁ y x).mp (Sum.inl.inj hb)
      change Sum.inl (left r₀ r₁ x) = Sum.inl (left r₀ r₁ r₀)
      rw [hx.2]
    · change Sum.inr (Sum.inr f) = Sum.inl (left r₀ r₁ x) at hb
      cases hb
    · change Sum.inl (right r₀ r₁ y) = Sum.inr (Sum.inl e) at hb
      cases hb
    · change Sum.inr (Sum.inr f) = Sum.inr (Sum.inl e) at hb
      cases Sum.inr.inj hb
  have hadj : ∀ ⦃a b⦄, (amalgam F₀ F₁ r₀ r₁).levi.Adj a b →
      (a ∈ A ∧ b ∈ A) ∨ (a ∈ B ∧ b ∈ B) := by
    intro a b hab
    rcases a with q | (e | e)
    · rcases b with q' | (f | f)
      · exact ((amalgam F₀ F₁ r₀ r₁).Z5r hab).elim
      · have hi := (amalgam F₀ F₁ r₀ r₁).Z7d.mp hab
        change q ∈ left r₀ r₁ '' F₀.edgeSet f at hi
        rcases hi with ⟨x, hx, rfl⟩
        exact Or.inl ⟨⟨.inl x, rfl⟩, ⟨.inr f, rfl⟩⟩
      · have hi := (amalgam F₀ F₁ r₀ r₁).Z7d.mp hab
        change q ∈ right r₀ r₁ '' F₁.edgeSet f at hi
        rcases hi with ⟨y, hy, rfl⟩
        exact Or.inr ⟨⟨.inl y, rfl⟩, ⟨.inr f, rfl⟩⟩
    · rcases b with q' | (f | f)
      · have hi := (amalgam F₀ F₁ r₀ r₁).Z7n.mp hab
        change q' ∈ left r₀ r₁ '' F₀.edgeSet e at hi
        rcases hi with ⟨x, hx, rfl⟩
        exact Or.inl ⟨⟨.inr e, rfl⟩, ⟨.inl x, rfl⟩⟩
      · exact ((amalgam F₀ F₁ r₀ r₁).Z65 hab).elim
      · exact ((amalgam F₀ F₁ r₀ r₁).Z65 hab).elim
    · rcases b with q' | (f | f)
      · have hi := (amalgam F₀ F₁ r₀ r₁).Z7n.mp hab
        change q' ∈ right r₀ r₁ '' F₁.edgeSet e at hi
        rcases hi with ⟨y, hy, rfl⟩
        exact Or.inr ⟨⟨.inr e, rfl⟩, ⟨.inl y, rfl⟩⟩
      · exact ((amalgam F₀ F₁ r₀ r₁).Z65 hab).elim
      · exact ((amalgam F₀ F₁ r₀ r₁).Z65 hab).elim
  rcases Z3u
      (amalgam F₀ F₁ r₀ r₁).levi A B root
      hrootA hrootB hinter hadj c hc with hsupp | hsupp
  · rcases Z4a f₀ c hc hsupp with ⟨x, d, hd, hlen⟩
    rw [hlen]
    exact h₀ d hd
  · rcases Z4a f₁ c hc hsupp with ⟨y, d, hd, hlen⟩
    rw [hlen]
    exact h₁ d hd
theorem Z8A
    (F₀ : TripleSystem V₀ E₀) (F₁ : TripleSystem V₁ E₁)
    (r₀ : V₀) (r₁ : V₁) (h₀ : F₀.Intrinsic) (h₁ : F₁.Intrinsic) :
    (amalgam F₀ F₁ r₀ r₁).Intrinsic := by
  exact ⟨Z9Z F₀ F₁ r₀ r₁ h₀.1 h₁.1,
    Z5e F₀ F₁ r₀ r₁ h₀.2.1 h₁.2.1,
    Z5U F₀ F₁ r₀ r₁ h₀.2.2 h₁.2.2⟩
end TripleSystem.OnePointAmalgamation
end P593
end
section
namespace P593
universe w
namespace TripleSystem
theorem Constructible.ZbC {V E : Type w}
    {F : TripleSystem V E} (h : Constructible F) : F.Intrinsic := by
  induction h with
  | ofEdgeless V =>
      exact Z83 V
  | ofExpansion G hG =>
      exact Z3H G hG
  | disjointUnion hF hG ihF ihG =>
      exact Z60 _ _ ihF ihG
  | amalgam h₀ h₁ r₀ r₁ ih₀ ih₁ =>
      exact OnePointAmalgamation.Z8A _ _ r₀ r₁ ih₀ ih₁
  | ofIso hF f ihF =>
      exact (f.Zap).mp ihF
end TripleSystem
end P593
end
section
namespace P593
universe u v
namespace TripleSystem
variable {V : Type u} {E : Type v} (F : TripleSystem V E)
abbrev SingleEdgeIndex : Type u := ULift.{u} Unit
def Z9n (e : E) :
    TripleSystem (F.edgeSet e) SingleEdgeIndex where
  Inc _ _ := True
  edge_ncard := by
    intro d
    rw [show {x : F.edgeSet e | True} =
        {x : F.edgeSet e | (x.1 : V) ∈ (Set.univ : Set V)} by simp]
    rw [Set.ncard_subtype]
    simpa using F.edge_ncard e
  simple := by
    intro a b _
    exact Subsingleton.elim a b
end TripleSystem
end P593
end
section
namespace P593
open scoped Sym2
universe u w
namespace TripleSystem
abbrev OneEdgeVertex : Type w := ULift.{w} (Fin 2)
abbrev oneEdgeGraph : _root_.SimpleGraph (OneEdgeVertex.{w}) :=
  _root_.SimpleGraph.completeGraph OneEdgeVertex
def oneEdgeGraphEdge : oneEdgeGraph.{w}.edgeSet :=
  ⟨s(ULift.up 0, ULift.up 1), by simp [oneEdgeGraph]⟩
theorem Z6X (a : oneEdgeGraph.{w}.edgeSet) :
    a = oneEdgeGraphEdge.{w} := by
  apply Subtype.ext
  rcases a with ⟨a, ha⟩
  induction a using Sym2.inductionOn with
  | _ x y =>
      change x ≠ y at ha
      rcases x with ⟨x⟩
      rcases y with ⟨y⟩
      fin_cases x <;> fin_cases y
      · exact (ha rfl).elim
      · rfl
      · simp [oneEdgeGraphEdge]
      · exact (ha rfl).elim
theorem Z77
    (p : PrivateVertexExpansion.Point oneEdgeGraph.{w})
    (a : PrivateVertexExpansion.Edge oneEdgeGraph.{w}) :
    (Z64 oneEdgeGraph.{w}).Inc p a := by
  have ha : a = oneEdgeGraphEdge.{w} := Z6X a
  subst a
  rcases p with x | b
  · change x ∈ (s(ULift.up 0, ULift.up 1) : Sym2 OneEdgeVertex)
    rcases x with ⟨x⟩
    fin_cases x <;> simp
  · change b = oneEdgeGraphEdge.{w}
    exact Z6X b
theorem Z59 : oneEdgeGraph.{w}.Colorable 2 := by
  refine ⟨_root_.SimpleGraph.Coloring.mk (fun x => x.down) ?_⟩
  intro x y hxy h
  apply hxy
  apply ULift.ext
  exact h
theorem Z4u :
    Fintype.card (PrivateVertexExpansion.Point oneEdgeGraph.{w}) = 3 := by
  have hedge : Fintype.card oneEdgeGraph.{w}.edgeSet = 1 := by
    letI : Unique oneEdgeGraph.{w}.edgeSet :=
      { default := oneEdgeGraphEdge.{w}
        uniq := Z6X }
    exact Fintype.card_unique
  simp only [PrivateVertexExpansion.Point, PrivateVertexExpansion.Zbd,
    PrivateVertexExpansion.Zad, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_ulift, hedge]
theorem Z58 :
    Fintype.card (PrivateVertexExpansion.Edge oneEdgeGraph.{w}) = 1 := by
  letI : Unique oneEdgeGraph.{w}.edgeSet :=
    { default := oneEdgeGraphEdge.{w}
      uniq := Z6X }
  exact Fintype.card_unique
noncomputable section
variable {V : Type u} {E : Type u} (F : TripleSystem V E)
noncomputable def oneEdgeExpansionSingleEdgePieceIso [Fintype V] (e : E) :
    Iso (Z64 oneEdgeGraph.{u}) (F.Z9n e) := by
  letI : Fintype (F.edgeSet e) := Fintype.ofFinite _
  exact
    { vertexEquiv := Fintype.equivOfCardEq (by
        rw [Z4u, Set.fintypeCard_eq_ncard]
        exact (F.edge_ncard e).symm)
      edgeEquiv := Fintype.equivOfCardEq (by
        rw [Z58]
        simp [SingleEdgeIndex])
      map_inc_iff := by
        intro p a
        constructor
        · intro _
          trivial
        · intro _
          exact Z77 p a }
theorem Z4p [Fintype V] (e : E) :
    Constructible (F.Z9n e) := by
  have hExpansion : Constructible
      (Z64 oneEdgeGraph.{u}) :=
    Constructible.ofExpansion oneEdgeGraph.{u} Z59
  exact Constructible.ofIso hExpansion
    (oneEdgeExpansionSingleEdgePieceIso F e)
def Z2E (e : E) :
    F.edgeSet e ≃ F.ZaR ({e} : Set E) where
  toFun x := ⟨x.1, e, Set.mem_singleton e, x.2⟩
  invFun x := ⟨x.1, by
    rcases x.2 with ⟨f, hf, hxf⟩
    have hfe : f = e := Set.mem_singleton_iff.mp hf
    subst f
    exact hxf⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl
def Z2W (e : E) :
    SingleEdgeIndex.{u} ≃ ({e} : Set E) where
  toFun _ := ⟨e, Set.mem_singleton e⟩
  invFun _ := ULift.up ()
  left_inv x := Subsingleton.elim _ _
  right_inv x := by
    apply Subtype.ext
    exact (Set.mem_singleton_iff.mp x.2).symm
def Z4o (e : E) :
    Iso (F.Z9n e) (F.Z96 ({e} : Set E)) where
  vertexEquiv := Z2E F e
  edgeEquiv := Z2W e
  map_inc_iff := by
    intro x d
    constructor
    · intro _
      exact x.2
    · intro _
      trivial
theorem Z2w [Fintype V] (e : E) :
    Constructible (F.Z96 ({e} : Set E)) :=
  Constructible.ofIso (Z4p F e)
    (Z4o F e)
end
end TripleSystem
end P593
end
section
namespace P593
universe w
namespace TripleSystem
namespace BridgeBlock
variable {V E : Type w} (F : TripleSystem V E)
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [DecidableRel F.levi.Adj]
theorem ZE
    {C : Zbp F} {e : E} (heC : Sum.inr e ∈ C.supp)
    (hzero : (P593.SimpleGraph.bridgeFree F.levi).degree (Sum.inr e) = 0) :
    Z6q F C = {e} := by
  ext f
  constructor
  · intro hfC
    have hre : (P593.SimpleGraph.bridgeFree F.levi).Reachable
        (Sum.inr e) (Sum.inr f) :=
      C.reachable_of_mem_supp heC hfC
    by_contra hef
    have hnodes : (Sum.inr e : V ⊕ E) ≠ Sum.inr f := by
      intro h
      apply hef
      exact (Sum.inr.inj h).symm
    have hpos : 0 <
        (P593.SimpleGraph.bridgeFree F.levi).degree (Sum.inr e) :=
      hre.degree_pos_left hnodes
    omega
  · intro hf
    have hfe : f = e := Set.mem_singleton_iff.mp hf
    subst f
    exact heC
theorem Z1r
    {C : Zbp F} {e : E} (heC : Sum.inr e ∈ C.supp)
    (hzero : (P593.SimpleGraph.bridgeFree F.levi).degree (Sum.inr e) = 0) :
    Constructible (F.Z96 (Z6q F C)) := by
  rw [ZE F heC hzero]
  exact Z2w F e
end BridgeBlock
end TripleSystem
end P593
end
section
namespace P593
universe u v
namespace TripleSystem
variable {V : Type u} {E : Type v} (F : TripleSystem V E)
theorem Z62 (hF : F.Z7f) (x : V) :
    x ∈ F.Z9z Set.univ := by
  rcases F.Z4G.mp (hF x) with ⟨e, hxe⟩
  exact ⟨e, Set.mem_univ e, hxe⟩
def Z6m (hF : F.Z7f) :
    Iso (F.Z96 Set.univ) F where
  vertexEquiv :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, F.Z62 hF x⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => rfl }
  edgeEquiv :=
    { toFun := Subtype.val
      invFun := fun e => ⟨e, Set.mem_univ e⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => rfl }
  map_inc_iff := fun _ _ => Iff.rfl
end TripleSystem
end P593
end
section
namespace P593
universe u v w
namespace TripleSystem
variable {V : Type u} {E : Type v} (F : TripleSystem V E)
theorem Z6V (S T : Set E) :
    F.Z9z (S ∪ T) = F.Z9z S ∪ F.Z9z T := by
  ext x
  simp only [Z9z, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨e, heS | heT, hxe⟩
    · exact Or.inl ⟨e, heS, hxe⟩
    · exact Or.inr ⟨e, heT, hxe⟩
  · rintro (⟨e, heS, hxe⟩ | ⟨e, heT, hxe⟩)
    · exact ⟨e, Or.inl heS, hxe⟩
    · exact ⟨e, Or.inr heT, hxe⟩
noncomputable def edgeUnionEquiv {S T : Set E} (hST : Disjoint S T) :
    S ⊕ T ≃ (S ∪ T : Set E) := by
  classical
  exact (Equiv.Set.union hST).symm
noncomputable def edgeSupportUnionEquiv {S T : Set E}
    (hST : Disjoint (F.Z9z S) (F.Z9z T)) :
    F.ZaR S ⊕ F.ZaR T ≃ F.ZaR (S ∪ T) := by
  classical
  exact (Equiv.Set.union hST).symm |>.trans
    (Equiv.setCongr (F.Z6V S T).symm)
noncomputable def edgeRestrictionUnionIsoDisjointUnion {S T : Set E}
    (hEdges : Disjoint S T)
    (hSupports : Disjoint (F.Z9z S) (F.Z9z T)) :
    Iso ((F.Z96 S).Za7 (F.Z96 T))
      (F.Z96 (S ∪ T)) where
  vertexEquiv := F.edgeSupportUnionEquiv hSupports
  edgeEquiv := edgeUnionEquiv hEdges
  map_inc_iff := by
    intro x e
    cases x with
    | inl x =>
        cases e with
        | inl e =>
            change F.Inc x.1 e.1 ↔ F.Inc _ _
            simp [edgeSupportUnionEquiv, edgeUnionEquiv]
        | inr e =>
            change False ↔ F.Inc _ _
            simp only [edgeSupportUnionEquiv, edgeUnionEquiv,
              Equiv.trans_apply, Equiv.Set.union_symm_apply_left,
              Equiv.Set.union_symm_apply_right, Equiv.setCongr_apply]
            exact (iff_false_intro fun hxe =>
              Set.disjoint_left.mp hSupports x.2 ⟨e.1, e.2, hxe⟩).symm
    | inr x =>
        cases e with
        | inl e =>
            change False ↔ F.Inc _ _
            simp only [edgeSupportUnionEquiv, edgeUnionEquiv,
              Equiv.trans_apply, Equiv.Set.union_symm_apply_left,
              Equiv.Set.union_symm_apply_right, Equiv.setCongr_apply]
            exact (iff_false_intro fun hxe =>
              Set.disjoint_left.mp hSupports ⟨e.1, e.2, hxe⟩ x.2).symm
        | inr e =>
            change F.Inc x.1 e.1 ↔ F.Inc _ _
            simp [edgeSupportUnionEquiv, edgeUnionEquiv]
def Z70 (S T : Set E) :
    F.ZaR S → F.ZaR (S ∪ T) :=
  fun x => ⟨x.1, by
    change x.1 ∈ F.Z9z (S ∪ T)
    rw [F.Z6V S T]
    exact Or.inl x.2⟩
def Z6D (S T : Set E) :
    F.ZaR T → F.ZaR (S ∪ T) :=
  fun x => ⟨x.1, by
    change x.1 ∈ F.Z9z (S ∪ T)
    rw [F.Z6V S T]
    exact Or.inr x.2⟩
@[simp]
theorem Z5L (S T : Set E) (x : F.ZaR S) :
    (F.Z70 S T x).1 = x.1 :=
  rfl
@[simp]
theorem Z5q (S T : Set E) (x : F.ZaR T) :
    (F.Z6D S T x).1 = x.1 :=
  rfl
def Z7m {S T : Set E} {r : V}
    (h : F.Z9z S ∩ F.Z9z T = {r}) :
    F.ZaR S := by
  refine ⟨r, ?_⟩
  have hr : r ∈ F.Z9z S ∩ F.Z9z T := by
    rw [h]
    simp
  exact hr.1
def Z6U {S T : Set E} {r : V}
    (h : F.Z9z S ∩ F.Z9z T = {r}) :
    F.ZaR T := by
  refine ⟨r, ?_⟩
  have hr : r ∈ F.Z9z S ∩ F.Z9z T := by
    rw [h]
    simp
  exact hr.2
@[simp]
theorem Z63 {S T : Set E} {r : V}
    (h : F.Z9z S ∩ F.Z9z T = {r}) :
    (F.Z7m h).1 = r :=
  rfl
@[simp]
theorem Z5K {S T : Set E} {r : V}
    (h : F.Z9z S ∩ F.Z9z T = {r}) :
    (F.Z6U h).1 = r :=
  rfl
noncomputable def edgeRestrictionUnionIsoOnePointAmalgamation
    {S T : Set E} (hEdges : Disjoint S T) {r : V}
    (hSupport : F.Z9z S ∩ F.Z9z T = {r}) :
    Iso
      (OnePointAmalgamation.amalgam
        (F.Z96 S) (F.Z96 T)
        (F.Z7m hSupport) (F.Z6U hSupport))
      (F.Z96 (S ∪ T)) := by
  let f₀ : F.ZaR S → F.ZaR (S ∪ T) :=
    F.Z70 S T
  let f₁ : F.ZaR T → F.ZaR (S ∪ T) :=
    F.Z6D S T
  let eEquiv : S ⊕ T ≃ (S ∪ T : Set E) := edgeUnionEquiv hEdges
  apply OnePointAmalgamation.isoOfMaps
    (F.Z96 S) (F.Z96 T)
    (F.Z96 (S ∪ T))
    (F.Z7m hSupport) (F.Z6U hSupport)
    f₀ f₁ (edgeEquiv := eEquiv)
  · apply Subtype.ext
    rfl
  · intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : F.ZaR (S ∪ T) => z.1) hxy
  · intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : F.ZaR (S ∪ T) => z.1) hxy
  · intro x y
    constructor
    · intro hxy
      have hval : x.1 = y.1 := congrArg Subtype.val hxy
      have hxInter : x.1 ∈ F.Z9z S ∩ F.Z9z T :=
        ⟨x.2, hval ▸ y.2⟩
      have hxr : x.1 = r := by
        have : x.1 ∈ ({r} : Set V) := hSupport ▸ hxInter
        simpa using this
      constructor
      · apply Subtype.ext
        exact hxr
      · apply Subtype.ext
        exact hval.symm.trans hxr
    · rintro ⟨rfl, rfl⟩
      apply Subtype.ext
      rfl
  · intro z
    have hz : z.1 ∈ F.Z9z S ∪ F.Z9z T :=
      (F.Z6V S T) ▸ z.2
    rcases hz with hzS | hzT
    · exact Or.inl ⟨⟨z.1, hzS⟩, Subtype.ext rfl⟩
    · exact Or.inr ⟨⟨z.1, hzT⟩, Subtype.ext rfl⟩
  · intro e
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hz
      refine ⟨⟨z.1, ⟨e.1, e.2, hz⟩⟩, hz, ?_⟩
      apply Subtype.ext
      rfl
  · intro e
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hz
      refine ⟨⟨z.1, ⟨e.1, e.2, hz⟩⟩, hz, ?_⟩
      apply Subtype.ext
      rfl
noncomputable def edgelessIsoEdgeRestrictionEmpty
    (F : TripleSystem (V := V) (E := E)) :
    Iso (ZbJ (F.ZaR ∅)) (F.Z96 ∅) where
  vertexEquiv := Equiv.refl _
  edgeEquiv := Equiv.equivOfIsEmpty _ _
  map_inc_iff := by
    intro x e
    exact isEmptyElim e
section ConstructibleReconstruction
variable {X I : Type w} (K : TripleSystem X I)
def Z9A : List (Set I) → Set I
  | [] => ∅
  | S :: pieces => Z9A pieces ∪ S
def Z7g : List (Set I) → Prop
  | [] => True
  | S :: pieces =>
      Z7g pieces ∧
      Constructible (K.Z96 S) ∧
      Disjoint (Z9A pieces) S ∧
      (Disjoint
          (K.Z9z (Z9A pieces))
          (K.Z9z S) ∨
        ∃ r : X,
          K.Z9z (Z9A pieces) ∩
            K.Z9z S = {r})
theorem Z2V :
    Constructible (K.Z96 ∅) := by
  letI : IsEmpty (K.ZaR ∅) := ⟨by
    intro x
    rcases x.2 with ⟨e, he, hxe⟩
    exact he⟩
  letI : Fintype (K.ZaR ∅) := Fintype.ofFinite _
  exact Constructible.ofIso
    (Constructible.ofEdgeless (K.ZaR ∅))
    (edgelessIsoEdgeRestrictionEmpty K)
theorem Z3m (pieces : List (Set I))
    (hpieces : K.Z7g pieces) :
    Constructible (K.Z96 (Z9A pieces)) := by
  induction pieces with
  | nil =>
      exact K.Z2V
  | cons S pieces ih =>
      rcases hpieces with ⟨hprevious, hS, hEdges, hSupports⟩
      have hPrev :
          Constructible (K.Z96 (Z9A pieces)) :=
        ih hprevious
      rcases hSupports with hDisjoint | ⟨r, hRoot⟩
      · exact Constructible.ofIso
          (Constructible.disjointUnion hPrev hS)
          (K.edgeRestrictionUnionIsoDisjointUnion hEdges hDisjoint)
      · exact Constructible.ofIso
          (Constructible.amalgam hPrev hS
            (K.Z7m hRoot)
            (K.Z6U hRoot))
          (K.edgeRestrictionUnionIsoOnePointAmalgamation hEdges hRoot)
end ConstructibleReconstruction
end TripleSystem
end P593
end
section
namespace P593
universe u v w
namespace TripleSystem
namespace BridgeBlock
noncomputable section
variable {V : Type u} {E : Type v} (F : TripleSystem V E)
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [DecidableRel F.levi.Adj]
private noncomputable abbrev core :=
  P593.SimpleGraph.bridgeFree F.levi
private noncomputable abbrev quotientForest :=
  P593.SimpleGraph.bridgeQuotient F.levi
abbrev Z7Q :=
  {C : Zbp F // (Z6q F C).Nonempty}
noncomputable def hyperedgeComponentOf (e : E) : Z7Q F :=
  ⟨(core F).connectedComponentMk (Sum.inr e),
    e, _root_.SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
@[simp]
theorem Z5J (e : E) :
    (hyperedgeComponentOf F e : Zbp F) =
      (core F).connectedComponentMk (Sum.inr e) :=
  rfl
@[simp]
theorem Z4s (e : E) :
    e ∈ Z6q F (hyperedgeComponentOf F e) :=
  _root_.SimpleGraph.ConnectedComponent.connectedComponentMk_mem
theorem Z44
    {C D : Z7Q F} (hCD : C ≠ D) :
    Disjoint (Z6q F C) (Z6q F D) := by
  rw [Set.disjoint_left]
  intro e heC heD
  apply hCD
  apply Subtype.ext
  change Sum.inr e ∈ (C : Zbp F).supp at heC
  change Sum.inr e ∈ (D : Zbp F).supp at heD
  change (core F).connectedComponentMk (Sum.inr e) = (C : Zbp F) at heC
  change (core F).connectedComponentMk (Sum.inr e) = (D : Zbp F) at heD
  have hC := heC
  have hD := heD
  exact hC.symm.trans hD
theorem Z3b
    (C : Z7Q F) {x : V}
    (hx : x ∈ F.Z9z (Z6q F C)) :
    (C : Zbp F) = (core F).connectedComponentMk (Sum.inl x) ∨
      (quotientForest F).Adj C
        ((core F).connectedComponentMk (Sum.inl x)) := by
  rcases hx with ⟨e, heC, hxe⟩
  exact Z1l F heC hxe
abbrev Z6t :=
  (quotientForest F).ConnectedComponent
def Z6r (C : Zbp F) : Z6t F :=
  (quotientForest F).connectedComponentMk C
noncomputable def quotientTreeRoot (T : Z6t F) : Zbp F :=
  Classical.choose T.nonempty_supp
theorem Z6Y (T : Z6t F) :
    quotientTreeRoot F T ∈ T.supp :=
  Classical.choose_spec T.nonempty_supp
noncomputable def componentDepth (C : Zbp F) : ℕ :=
  (quotientForest F).dist
    (quotientTreeRoot F (Z6r F C)) C
noncomputable local instance componentFintype : Fintype (Zbp F) :=
  Fintype.ofFinite _
noncomputable local instance quotientTreeComponentFintype :
    Fintype (Z6t F) :=
  Fintype.ofFinite _
noncomputable local instance hyperedgeComponentFintype :
    Fintype (Z7Q F) :=
  Fintype.ofFinite _
noncomputable def componentOrderKey (C : Z7Q F) :
    Fin (Fintype.card (Z6t F)) ×ₗ
      (ℕ ×ₗ Fin (Fintype.card (Z7Q F))) :=
  toLex
    ((Fintype.equivFin (Z6t F))
        (Z6r F C),
      toLex (componentDepth F C,
        (Fintype.equivFin (Z7Q F)) C))
theorem Z4K :
    Function.Injective (componentOrderKey F) := by
  intro C D hCD
  have hlast := congrArg
    (fun z : Fin (Fintype.card (Z6t F)) ×ₗ
        (ℕ ×ₗ Fin (Fintype.card (Z7Q F))) =>
      (ofLex (ofLex z).2).2) hCD
  exact (Fintype.equivFin (Z7Q F)).injective hlast
noncomputable abbrev hyperedgeComponentLinearOrder :
    LinearOrder (Z7Q F) :=
  LinearOrder.lift' (componentOrderKey F) (Z4K F)
noncomputable def rootedHyperedgeComponentList : List (Z7Q F) := by
  letI := hyperedgeComponentLinearOrder F
  exact Finset.univ.sort (fun C D => D ≤ C)
@[simp]
theorem Z3C (C : Z7Q F) :
    C ∈ rootedHyperedgeComponentList F := by
  classical
  letI := hyperedgeComponentLinearOrder F
  simp [rootedHyperedgeComponentList]
theorem Z39 :
    (rootedHyperedgeComponentList F).Nodup := by
  classical
  letI := hyperedgeComponentLinearOrder F
  simp [rootedHyperedgeComponentList]
theorem Z1E :
    (rootedHyperedgeComponentList F).Pairwise
      (fun C D : Z7Q F =>
        Z6r F D = Z6r F C →
          componentDepth F D ≤ componentDepth F C) := by
  classical
  letI := hyperedgeComponentLinearOrder F
  have hsorted :
      (Finset.univ.sort (fun C D : Z7Q F => D ≤ C)).Pairwise
        (fun C D => D ≤ C) :=
    Finset.pairwise_sort _ _
  rw [rootedHyperedgeComponentList]
  refine hsorted.imp ?_
  intro C D hDC htree
  change componentOrderKey F D ≤ componentOrderKey F C at hDC
  unfold componentOrderKey at hDC
  rw [Prod.Lex.toLex_le_toLex] at hDC
  have hq :
      (Fintype.equivFin (Z6t F))
          (Z6r F D) =
        (Fintype.equivFin (Z6t F))
          (Z6r F C) :=
    congrArg (Fintype.equivFin (Z6t F)) htree
  rcases hDC with hless | ⟨heq, hrest⟩
  · exact (lt_irrefl _ (hq ▸ hless)).elim
  · rw [Prod.Lex.toLex_le_toLex] at hrest
    rcases hrest with hdepth | ⟨hdepth, _⟩
    · exact hdepth.le
    · exact hdepth.le
theorem Z1K
    {C D : Z7Q F} {x : V}
    (hxC : x ∈ F.Z9z (Z6q F C))
    (hxD : x ∈ F.Z9z (Z6q F D)) :
    Z6r F C = Z6r F D := by
  let X : Zbp F := (core F).connectedComponentMk (Sum.inl x)
  have hC := Z3b F C hxC
  have hD := Z3b F D hxD
  have hCX :
      (quotientForest F).connectedComponentMk (C : Zbp F) =
        (quotientForest F).connectedComponentMk X := by
    rcases hC with hCX | hCX
    · exact congrArg (quotientForest F).connectedComponentMk hCX
    · exact
        _root_.SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hCX
  have hDX :
      (quotientForest F).connectedComponentMk (D : Zbp F) =
        (quotientForest F).connectedComponentMk X := by
    rcases hD with hDX | hDX
    · exact congrArg (quotientForest F).connectedComponentMk hDX
    · exact
        _root_.SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hDX
  exact hCX.trans hDX.symm
private theorem Z2P
    {W : Type*} {G : _root_.SimpleGraph W} (hG : G.IsAcyclic)
    (root : W) {C D X : W}
    (hCX : G.Adj C X) (hDX : G.Adj D X)
    (hrootC : G.Reachable root C) (hrootD : G.Reachable root D)
    (hCdepth : G.dist root C + 1 = G.dist root X)
    (hDdepth : G.dist root D + 1 = G.dist root X) :
    C = D := by
  classical
  obtain ⟨pC, hpC, hpCdist⟩ := hrootC.exists_path_of_dist
  obtain ⟨pD, hpD, hpDdist⟩ := hrootD.exists_path_of_dist
  have hXnotC : X ∉ pC.support := by
    intro hX
    have hdist := G.dist_le (pC.takeUntil X hX)
    have htake := pC.length_takeUntil_le_length hX
    omega
  have hXnotD : X ∉ pD.support := by
    intro hX
    have hdist := G.dist_le (pD.takeUntil X hX)
    have htake := pD.length_takeUntil_le_length hX
    omega
  have hpCX : (pC.concat hCX).IsPath := hpC.concat hXnotC hCX
  have hpDX : (pD.concat hDX).IsPath := hpD.concat hXnotD hDX
  have hpaths : pC.concat hCX = pD.concat hDX := by
    exact Subtype.mk.inj (hG.path_unique ⟨_, hpCX⟩ ⟨_, hpDX⟩)
  have hpenultimate := congrArg (fun p => p.penultimate) hpaths
  simpa using hpenultimate
private theorem Z2y
    {W : Type*} {G : _root_.SimpleGraph W} (hG : G.IsAcyclic)
    (root C D X : W)
    (hCD : C ≠ D)
    (hC : C = X ∨ G.Adj C X)
    (hD : D = X ∨ G.Adj D X)
    (hdepth : G.dist root D ≤ G.dist root C)
    (hrootC : G.Reachable root C) (hrootD : G.Reachable root D) :
    (X = C ∧ G.Adj D C ∧ G.dist root D + 1 = G.dist root C) ∨
      (X ≠ C ∧ G.Adj C X ∧ G.dist root X + 1 = G.dist root C) := by
  rcases hC with (rfl | hCX)
  · left
    have hDC : G.Adj D C := by
      rcases hD with (rfl | hDC)
      · exact (hCD rfl).elim
      · exact hDC
    refine ⟨rfl, hDC, ?_⟩
    rcases hG.dist_eq_dist_add_one_of_adj_of_reachable root hDC hrootD with h | h
    · omega
    · exact h.symm
  · right
    refine ⟨hCX.ne', hCX, ?_⟩
    rcases hG.dist_eq_dist_add_one_of_adj_of_reachable root hCX hrootC with
      hCXup | hXup
    · exact hCXup.symm
    · exfalso
      have hDX : G.Adj D X := by
        rcases hD with (rfl | hDX)
        · omega
        · exact hDX
      rcases hG.dist_eq_dist_add_one_of_adj_of_reachable root hDX hrootD with
        hDup | hXupD
      · omega
      · have hDC : D = C :=
          Z2P hG root hDX hCX
            hrootD hrootC hXupD.symm hXup.symm
        exact hCD hDC.symm
structure ParentBridgeWitness (C : Z7Q F) (x : V) where
  parent : Zbp F
  edge : E
  inside : V ⊕ E
  outside : V ⊕ E
  quotientAdj :
    (quotientForest F).Adj parent (C : Zbp F)
  parentDepth :
    (quotientForest F).dist
        (quotientTreeRoot F (Z6r F C)) parent + 1 =
      componentDepth F C
  leviAdj : F.levi.Adj inside outside
  inside_mem : inside ∈ (C : Zbp F).supp
  outside_mem : outside ∈ parent.supp
  incidence : F.Inc x edge
  edge_eq_incidence : s(inside, outside) = s(Sum.inl x, Sum.inr edge)
theorem Z1X
    {C D : Z7Q F} (hCD : C ≠ D) {x : V}
    (hxC : x ∈ F.Z9z (Z6q F C))
    (hxD : x ∈ F.Z9z (Z6q F D))
    (hdepth : componentDepth F D ≤ componentDepth F C) :
    Nonempty (ParentBridgeWitness F C x) := by
  let T : Z6t F := Z6r F C
  let X : Zbp F := (core F).connectedComponentMk (Sum.inl x)
  have htreeDC : Z6r F D = T :=
    Z1K F hxD hxC
  have hCstar := Z3b F C hxC
  have hDstar := Z3b F D hxD
  have hCDval : (C : Zbp F) ≠ (D : Zbp F) := by
    intro h
    exact hCD (Subtype.ext h)
  have hrootC : (quotientForest F).Reachable
      (quotientTreeRoot F T) (C : Zbp F) :=
    T.reachable_of_mem_supp (Z6Y F T)
      _root_.SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hrootD : (quotientForest F).Reachable
      (quotientTreeRoot F T) (D : Zbp F) :=
    T.reachable_of_mem_supp (Z6Y F T)
      ((_root_.SimpleGraph.ConnectedComponent.mem_supp_iff T D).mpr htreeDC)
  have hdepth' :
      (quotientForest F).dist (quotientTreeRoot F T) (D : Zbp F) ≤
        (quotientForest F).dist (quotientTreeRoot F T) (C : Zbp F) := by
    simpa [componentDepth, T, htreeDC] using hdepth
  have hAcyclic := P593.SimpleGraph.Z5w F.levi
  rcases Z2y hAcyclic
      (quotientTreeRoot F T) (C : Zbp F) (D : Zbp F) X
      hCDval hCstar hDstar hdepth' hrootC hrootD with hparent | hparent
  · rcases hparent with ⟨hXC, hDCadj, hDdepth⟩
    rcases hxD with ⟨e, heD, hxe⟩
    refine ⟨
      { parent := D
        edge := e
        inside := Sum.inl x
        outside := Sum.inr e
        quotientAdj := hDCadj
        parentDepth := hDdepth
        leviAdj := F.Z7d.mpr hxe
        inside_mem := ?_
        outside_mem := heD
        incidence := hxe
        edge_eq_incidence := rfl }⟩
    simp [X, hXC]
  · rcases hparent with ⟨_, hCXadj, hXdepth⟩
    rcases hxC with ⟨e, heC, hxe⟩
    refine ⟨
      { parent := X
        edge := e
        inside := Sum.inr e
        outside := Sum.inl x
        quotientAdj := hCXadj.symm
        parentDepth := hXdepth
        leviAdj := (F.Z7d.mpr hxe).symm
        inside_mem := heC
        outside_mem := by
          simp [X]
        incidence := hxe
        edge_eq_incidence := Sym2.eq_swap }⟩
noncomputable def parentBridgeWitnessOfCommonPoint
    {C D : Z7Q F} (hCD : C ≠ D) {x : V}
    (hxC : x ∈ F.Z9z (Z6q F C))
    (hxD : x ∈ F.Z9z (Z6q F D))
    (hdepth : componentDepth F D ≤ componentDepth F C) :
    ParentBridgeWitness F C x :=
  Classical.choice
    (Z1X F hCD hxC hxD hdepth)
theorem ParentBridgeWitness.Zan
    {C : Z7Q F} {x y : V}
    (hx : ParentBridgeWitness F C x)
    (hy : ParentBridgeWitness F C y) :
    hx.parent = hy.parent := by
  let T := Z6r F C
  have hrootC : (quotientForest F).Reachable
      (quotientTreeRoot F T) (C : Zbp F) :=
    T.reachable_of_mem_supp (Z6Y F T)
      _root_.SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hrootX : (quotientForest F).Reachable
      (quotientTreeRoot F T) hx.parent :=
    hrootC.trans hx.quotientAdj.symm.reachable
  have hrootY : (quotientForest F).Reachable
      (quotientTreeRoot F T) hy.parent :=
    hrootC.trans hy.quotientAdj.symm.reachable
  apply Z2P
    (P593.SimpleGraph.Z5w F.levi)
    (quotientTreeRoot F T) hx.quotientAdj hy.quotientAdj hrootX hrootY
  · simpa [componentDepth, T] using hx.parentDepth
  · simpa [componentDepth, T] using hy.parentDepth
theorem Z3B
    {C D A : Z7Q F}
    (hCD : C ≠ D) (hCA : C ≠ A) {x y : V}
    (hxC : x ∈ F.Z9z (Z6q F C))
    (hxD : x ∈ F.Z9z (Z6q F D))
    (hyC : y ∈ F.Z9z (Z6q F C))
    (hyA : y ∈ F.Z9z (Z6q F A))
    (hdepthD : componentDepth F D ≤ componentDepth F C)
    (hdepthA : componentDepth F A ≤ componentDepth F C) :
    x = y := by
  let wx := parentBridgeWitnessOfCommonPoint F hCD hxC hxD hdepthD
  let wy := parentBridgeWitnessOfCommonPoint F hCA hyC hyA hdepthA
  have hparent : wx.parent = wy.parent :=
    ParentBridgeWitness.Zan F wx wy
  have hCparent : (C : Zbp F) ≠ wx.parent := by
    intro h
    apply wx.quotientAdj.ne
    exact h.symm
  have hedge : s(wy.inside, wy.outside) = s(wx.inside, wx.outside) := by
    apply P593.SimpleGraph.Z36 F.levi hCparent
      wx.leviAdj wx.inside_mem wx.outside_mem wy.leviAdj wy.inside_mem
    simpa [hparent] using wy.outside_mem
  have hincidence :
      s(Sum.inl y, Sum.inr wy.edge) = s(Sum.inl x, Sum.inr wx.edge) :=
    wy.edge_eq_incidence.symm.trans (hedge.trans wx.edge_eq_incidence)
  rcases Sym2.eq_iff.mp hincidence with h | h
  · exact Sum.inl.inj h.1 |>.symm
  · exact (Sum.inl_ne_inr h.1).elim
def Z6s (C : Z7Q F) : Set E :=
  Z6q F (C : Zbp F)
noncomputable def rootedComponentPieceList : List (Set E) :=
  (rootedHyperedgeComponentList F).map (Z6s F)
theorem Z3q
    (components : List (Z7Q F)) {e : E} :
    e ∈ Z9A
        (components.map (Z6s F)) ↔
      ∃ C : Z7Q F,
        C ∈ components ∧ e ∈ Z6s F C := by
  induction components with
  | nil => simp [Z9A]
  | cons C components ih =>
      change
        (e ∈ Z9A
            (components.map (Z6s F)) ∨
          e ∈ Z6s F C) ↔ _
      rw [ih]
      constructor
      · rintro (⟨D, hD, heD⟩ | heC)
        · exact ⟨D, List.mem_cons.mpr (Or.inr hD), heD⟩
        · exact ⟨C, List.mem_cons.mpr (Or.inl rfl), heC⟩
      · rintro ⟨D, hD, heD⟩
        rcases List.mem_cons.mp hD with rfl | hD
        · exact Or.inr heD
        · exact Or.inl ⟨D, hD, heD⟩
theorem Z2e :
    Z9A (rootedComponentPieceList F) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro e
  rw [rootedComponentPieceList,
    Z3q]
  exact ⟨hyperedgeComponentOf F e,
    Z3C F _,
    Z4s F e⟩
def RunningEdgeAssemblyGeometry (pieces : List (Set E)) : Prop :=
  match pieces with
  | [] => True
  | S :: pieces =>
      RunningEdgeAssemblyGeometry pieces ∧
      Disjoint (Z9A pieces) S ∧
      (Disjoint
          (F.Z9z (Z9A pieces))
          (F.Z9z S) ∨
        ∃ r : V,
          F.Z9z (Z9A pieces) ∩
            F.Z9z S = {r})
theorem Z1W
    (components : List (Z7Q F))
    (hnodup : components.Nodup)
    (hdepth : components.Pairwise
      (fun C D : Z7Q F =>
        Z6r F D = Z6r F C →
          componentDepth F D ≤ componentDepth F C)) :
    RunningEdgeAssemblyGeometry F
      (components.map (Z6s F)) := by
  induction components with
  | nil => trivial
  | cons C components ih =>
      rw [List.nodup_cons] at hnodup
      rw [List.pairwise_cons] at hdepth
      refine ⟨ih hnodup.2 hdepth.2, ?_, ?_⟩
      · rw [Set.disjoint_left]
        intro e hePrevious heC
        rcases (Z3q F components).mp hePrevious with
          ⟨D, hD, heD⟩
        have hDC : D ≠ C := by
          intro h
          apply hnodup.1
          exact h ▸ hD
        exact (Set.disjoint_left.mp
          (Z44 F hDC)) heD heC
      · by_cases hdisjoint : Disjoint
            (F.Z9z
              (Z9A (components.map (Z6s F))))
            (F.Z9z (Z6s F C))
        · exact Or.inl hdisjoint
        · right
          rcases Set.not_disjoint_iff.mp hdisjoint with
            ⟨r, hrPrevious, hrC⟩
          refine ⟨r, Set.Subset.antisymm ?_ ?_⟩
          · intro x hx
            rcases hx.1 with ⟨e, hePrevious, hxe⟩
            rcases (Z3q F components).mp
                hePrevious with ⟨D, hD, heD⟩
            have hxD :
                x ∈ F.Z9z (Z6s F D) :=
              ⟨e, heD, hxe⟩
            rcases hrPrevious with ⟨f, hfPrevious, hrf⟩
            rcases (Z3q F components).mp
                hfPrevious with ⟨A, hA, hfA⟩
            have hrA :
                r ∈ F.Z9z (Z6s F A) :=
              ⟨f, hfA, hrf⟩
            have hCD : C ≠ D := by
              intro h
              apply hnodup.1
              exact h.symm ▸ hD
            have hCA : C ≠ A := by
              intro h
              apply hnodup.1
              exact h.symm ▸ hA
            have hdepthD : componentDepth F D ≤ componentDepth F C :=
              hdepth.1 D hD
                (Z1K F hxD hx.2)
            have hdepthA : componentDepth F A ≤ componentDepth F C :=
              hdepth.1 A hA
                (Z1K F hrA hrC)
            have hxr : x = r :=
              Z3B F hCD hCA
                hx.2 hxD hrC hrA hdepthD hdepthA
            simp [hxr]
          · intro x hx
            have hxr : x = r := Set.mem_singleton_iff.mp hx
            simpa [hxr] using And.intro hrPrevious hrC
theorem ZL :
    RunningEdgeAssemblyGeometry F (rootedComponentPieceList F) := by
  apply Z1W F
  · exact Z39 F
  · exact Z1E F
theorem RunningEdgeAssemblyGeometry.Z6H
    {X I : Type w} (K : TripleSystem X I)
    (pieces : List (Set I))
    (hgeometry : RunningEdgeAssemblyGeometry K pieces)
    (hconstructible : ∀ S ∈ pieces,
      Constructible (K.Z96 S)) :
    K.Z7g pieces := by
  induction pieces with
  | nil => trivial
  | cons S pieces ih =>
      rcases hgeometry with ⟨hprevious, hEdges, hSupports⟩
      refine ⟨ih hprevious ?_, hconstructible S (by simp), hEdges, hSupports⟩
      intro T hT
      exact hconstructible T (by simp [hT])
theorem Z1s
    {X I : Type w} (K : TripleSystem X I)
    [Fintype X] [Fintype I] [DecidableEq X] [DecidableEq I]
    [DecidableRel K.levi.Adj]
    (hconstructible : ∀ C : Z7Q K,
      Constructible
        (K.Z96 (Z6s K C))) :
    K.Z7g (rootedComponentPieceList K) := by
  apply (ZL K).Z6H K
  intro S hS
  rw [rootedComponentPieceList, List.mem_map] at hS
  rcases hS with ⟨C, _, rfl⟩
  exact hconstructible C
theorem Z1D
    {X I : Type w} (K : TripleSystem X I)
    [Fintype X] [Fintype I] [DecidableEq X] [DecidableEq I]
    [DecidableRel K.levi.Adj]
    (hlinear : K.Linear) (hbridge : K.BridgeAtEveryEdge)
    (hberge : K.EvenBergeCycles) (C : Z7Q K) :
    Constructible (K.Z96 (Z6s K C)) := by
  rcases C.2 with ⟨e, heC⟩
  change Sum.inr e ∈ (C : Zbp K).supp at heC
  rcases K.Z1N hbridge e with
    hzero | htwo
  · change Constructible
      (K.Z96 (Z6q K (C : Zbp K)))
    exact Z1r K heC hzero
  · have hpositive : 0 <
        (P593.SimpleGraph.bridgeFree K.levi).degree (Sum.inr e) := by
      omega
    rcases ((P593.SimpleGraph.bridgeFree K.levi).degree_pos_iff_exists_adj
        (Sum.inr e)).mp hpositive with ⟨z, hez⟩
    have hC : Zay K C := by
      rcases z with x | f
      · refine ⟨x, e, ?_, heC, hez.symm⟩
        exact (C : Zbp K).mem_supp_of_adj_mem_supp heC hez
      · have hle : P593.SimpleGraph.bridgeFree K.levi ≤ K.levi := by
          dsimp only [P593.SimpleGraph.bridgeFree]
          exact K.levi.deleteEdges_le _
        exact (K.Z65 (hle hez)).elim
    change Constructible
      (K.Z96 (Z6q K (C : Zbp K)))
    exact Z24 K
      hlinear hbridge hberge hC
theorem ZF
    {X I : Type w} (K : TripleSystem X I)
    [Fintype X] [Fintype I] [DecidableEq X] [DecidableEq I]
    [DecidableRel K.levi.Adj]
    (hlinear : K.Linear) (hbridge : K.BridgeAtEveryEdge)
    (hberge : K.EvenBergeCycles) :
    K.Z7g (rootedComponentPieceList K) := by
  exact Z1s K
    (Z1D K hlinear hbridge hberge)
theorem ZV
    {X I : Type w} (K : TripleSystem X I)
    [Fintype X] [Fintype I] [DecidableEq X] [DecidableEq I]
    [DecidableRel K.levi.Adj]
    (hintrinsic : K.Intrinsic) (hnoisolated : K.Z7f) :
    Constructible K := by
  rcases hintrinsic with ⟨hlinear, hbridge, hberge⟩
  have hrunning : K.Z7g (rootedComponentPieceList K) :=
    ZF K
      hlinear hbridge hberge
  have hrestriction : Constructible
      (K.Z96 (Z9A (rootedComponentPieceList K))) :=
    K.Z3m (rootedComponentPieceList K) hrunning
  rw [Z2e K] at hrestriction
  exact Constructible.ofIso hrestriction
    (K.Z6m hnoisolated)
theorem ZP
    {X I : Type w} (K : TripleSystem X I)
    [Fintype X] [Fintype I] [DecidableEq X] [DecidableEq I]
    [DecidableRel K.levi.Adj]
    (hnoisolated : K.Z7f) :
    Constructible K ↔ K.Intrinsic := by
  constructor
  · exact Constructible.ZbC
  · intro hintrinsic
    exact ZV K
      hintrinsic hnoisolated
theorem Z1m
    {X I : Type w} (K : TripleSystem X I)
    [Fintype X] [Fintype I] [DecidableEq X] [DecidableEq I] :
    Constructible K.isolatedReduction ↔ K.isolatedReduction.Intrinsic := by
  classical
  letI : Fintype K.NonIsolatedPoint := Fintype.ofFinite _
  letI : DecidableRel K.isolatedReduction.levi.Adj := Classical.decRel _
  exact ZP
    K.isolatedReduction K.Z2A
end
end BridgeBlock
end TripleSystem
end P593
end
section
namespace P593
universe u w
namespace TripleSystem
variable {V : Type u} (G : _root_.SimpleGraph V)
inductive FiniteLiftGenerated : {X I : Type w} → TripleSystem X I → Prop
  | ofEdgeless (X : Type w) [Fintype X] :
      FiniteLiftGenerated (ZbJ X)
  | ofFactorExpansion {X : Type w} [Fintype X]
      {J : _root_.SimpleGraph X}
      (f : P593.SimpleGraph.NonInducedFactor J G) :
      FiniteLiftGenerated (Z64 J)
  | disjointUnion {X I Y J : Type w}
      {F : TripleSystem X I} {H : TripleSystem Y J}
      (hF : FiniteLiftGenerated F) (hH : FiniteLiftGenerated H) :
      FiniteLiftGenerated (F.Za7 H)
  | amalgam {X I Y J : Type w}
      {F : TripleSystem X I} {H : TripleSystem Y J}
      (hF : FiniteLiftGenerated F) (hH : FiniteLiftGenerated H)
      (x : X) (y : Y) :
      FiniteLiftGenerated (OnePointAmalgamation.amalgam F H x y)
  | ofIso {X I Y J : Type w}
      {F : TripleSystem X I} {H : TripleSystem Y J}
      (hF : FiniteLiftGenerated F) (f : Iso F H) :
      FiniteLiftGenerated H
namespace FiniteLiftGenerated
theorem Zb1 {X : Type w} [Fintype X]
    {J : _root_.SimpleGraph X}
    (f : P593.SimpleGraph.NonInducedFactor J G) :
    FiniteLiftGenerated G (Z64 J) :=
  ofFactorExpansion f
theorem Z4g
    {X I : Type w} (K : TripleSystem X I)
    (pieces : List (Set I))
    (hgeometry : BridgeBlock.RunningEdgeAssemblyGeometry K pieces)
    (hpieces : ∀ S ∈ pieces,
      FiniteLiftGenerated G (K.Z96 S)) :
    FiniteLiftGenerated G (K.Z96 (Z9A pieces)) := by
  induction pieces with
  | nil =>
      letI : IsEmpty (K.ZaR ∅) := ⟨by
        intro x
        rcases x.2 with ⟨e, he, _⟩
        exact he⟩
      letI : Fintype (K.ZaR ∅) := Fintype.ofFinite _
      exact FiniteLiftGenerated.ofIso
        (FiniteLiftGenerated.ofEdgeless (K.ZaR ∅))
        (edgelessIsoEdgeRestrictionEmpty K)
  | cons S pieces ih =>
      rcases hgeometry with ⟨hprevious, hEdges, hSupports⟩
      have hPrev :
          FiniteLiftGenerated G
            (K.Z96 (Z9A pieces)) :=
        ih hprevious (fun T hT => hpieces T (by simp [hT]))
      have hS : FiniteLiftGenerated G (K.Z96 S) :=
        hpieces S (by simp)
      rcases hSupports with hDisjoint | ⟨r, hRoot⟩
      · exact FiniteLiftGenerated.ofIso
          (FiniteLiftGenerated.disjointUnion hPrev hS)
          (K.edgeRestrictionUnionIsoDisjointUnion hEdges hDisjoint)
      · exact FiniteLiftGenerated.ofIso
          (FiniteLiftGenerated.amalgam hPrev hS
            (K.Z7m hRoot)
            (K.Z6U hRoot))
          (K.edgeRestrictionUnionIsoOnePointAmalgamation hEdges hRoot)
end FiniteLiftGenerated
end TripleSystem
end P593
end
section
namespace P593
universe u w
namespace TripleSystem
variable {V : Type u} (G : _root_.SimpleGraph V)
namespace FiniteLiftGenerated
theorem Z8z
    {X I : Type w} {K : TripleSystem X I}
    (hK : FiniteLiftGenerated G K) :
    K.BridgeAtEveryEdge := by
  induction hK with
  | ofEdgeless X =>
      exact (Z83 X).2.1
  | ofFactorExpansion f =>
      exact Z20 _
  | disjointUnion hF hH ihF ihH =>
      exact Z3L _ _ ihF ihH
  | amalgam hF hH x y ihF ihH =>
      exact OnePointAmalgamation.Z5e _ _ x y ihF ihH
  | ofIso hF f ihF =>
      exact (f.Z6A).mp ihF
end FiniteLiftGenerated
end TripleSystem
end P593
end
section
namespace P593
open scoped Cardinal Ordinal
universe u
namespace SequenceLift
abbrev Index : Type u := (ω₁ : Ordinal.{u}).ToType
noncomputable instance indexNonempty : Nonempty (Index : Type u) :=
  Ordinal.nonempty_toType_iff.mpr (Cardinal.isSuccLimit_omega 1).ne_bot
noncomputable instance indexOrderBot : OrderBot (Index : Type u) :=
  WellFoundedLT.toOrderBot (Index : Type u)
abbrev ZbG {V : Type u} (G : _root_.SimpleGraph V) : Type u := G.edgeSet
structure Node {V : Type u} (G : _root_.SimpleGraph V) where
  length : Index
  entry : Set.Iio length → ZbG G
namespace Node
variable {V : Type u} {G : _root_.SimpleGraph V}
def ExtendsBy (q : Node G) (a : ZbG G) (t : Node G) : Prop :=
  ∃ h : q.length < t.length,
    (∀ i : Set.Iio q.length,
      q.entry i = t.entry ⟨i.1, i.2.trans h⟩) ∧
    t.entry ⟨q.length, h⟩ = a
theorem Z9b {q t : Node G} {a : ZbG G}
    (h : q.ExtendsBy a t) : q ≠ t := by
  intro hqt
  rcases h with ⟨hlen, _⟩
  exact hlen.ne (congrArg Node.length hqt)
end Node
abbrev Point {V : Type u} (G : _root_.SimpleGraph V) : Type u := Node G × V
def Zb9 {V : Type u} {G : _root_.SimpleGraph V}
    {x y : V} (hxy : G.Adj x y) : ZbG G :=
  ⟨s(x, y), hxy⟩
def Zbz {V : Type u} (G : _root_.SimpleGraph V)
    (S : Set (Point G)) : Prop :=
  ∃ (q t : Node G) (x y z : V) (hxy : G.Adj x y),
    q.ExtendsBy (Zb9 hxy) t ∧
      S = {(q, x), (q, y), (t, z)}
abbrev Edge {V : Type u} (G : _root_.SimpleGraph V) : Type u :=
  {S : Set (Point G) // Zbz G S}
def mkEdge {V : Type u} {G : _root_.SimpleGraph V}
    (q t : Node G) (x y z : V) (hxy : G.Adj x y)
    (hext : q.ExtendsBy (Zb9 hxy) t) : Edge G :=
  ⟨{(q, x), (q, y), (t, z)}, ⟨q, t, x, y, z, hxy, hext, rfl⟩⟩
private theorem ZaO {α : Type u} {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Set α).ncard = 3 := by
  rw [Set.ncard_insert_of_notMem (by simp [hab, hac]), Set.ncard_pair hbc]
noncomputable def system {V : Type u} (G : _root_.SimpleGraph V) :
    TripleSystem (Point G) (Edge G) where
  Inc p e := p ∈ e.1
  edge_ncard e := by
    rcases e.2 with ⟨q, t, x, y, z, hxy, hext, hset⟩
    simp only [Set.setOf_mem_eq]
    rw [hset]
    have hqt : q ≠ t := Node.Z9b hext
    apply ZaO
    · exact fun h ↦ hxy.ne (congrArg Prod.snd h)
    · exact fun h ↦ hqt (congrArg Prod.fst h)
    · exact fun h ↦ hqt (congrArg Prod.fst h)
  simple := by
    intro e f h
    apply Subtype.ext
    simpa only [Set.setOf_mem_eq] using h
@[simp]
theorem Z9C {V : Type u} {G : _root_.SimpleGraph V}
    {p : Point G} {q t : Node G} {x y z : V} {hxy : G.Adj x y}
    {hext : q.ExtendsBy (Zb9 hxy) t} :
    (system G).Inc p (mkEdge q t x y z hxy hext) ↔
      p = (q, x) ∨ p = (q, y) ∨ p = (t, z) := by
  simp [system, mkEdge]
def Zbe {V : Type u} {G : _root_.SimpleGraph V}
    (a : Index → ZbG G) (α : Index) : Node G where
  length := α
  entry i := a i.1
theorem Z71 {V : Type u} {G : _root_.SimpleGraph V}
    (a : Index → ZbG G) {α β : Index} (hαβ : α < β) :
    (Zbe a α).ExtendsBy (a α) (Zbe a β) := by
  refine ⟨hαβ, ?_, rfl⟩
  intro i
  rfl
noncomputable def branchLetter {V : Type u} {G : _root_.SimpleGraph V}
    (pick : Node G → ZbG G) : Index → ZbG G :=
  WellFounded.fix (wellFounded_lt : WellFounded ((· < ·) : Index → Index → Prop))
    fun α earlier ↦ pick ⟨α, fun i ↦ earlier i.1 i.2⟩
theorem Z9u {V : Type u} {G : _root_.SimpleGraph V}
    (pick : Node G → ZbG G) (α : Index) :
    branchLetter pick α = pick (Zbe (branchLetter pick) α) := by
  rw [branchLetter, WellFounded.fix_eq]
  rfl
end SequenceLift
end P593
end
section
namespace P593
open scoped Cardinal Ordinal
universe u
namespace SequenceLift
variable {V : Type u} {G : _root_.SimpleGraph V}
def BasedAt (q : Node G) (e : Edge G) : Prop :=
  ∃ x y : V, x ≠ y ∧ (system G).Inc (q, x) e ∧ (system G).Inc (q, y) e
theorem Z9K
    {q t : Node G} {x y z : V} {hxy : G.Adj x y}
    {hext : q.ExtendsBy (Zb9 hxy) t} :
    BasedAt q (mkEdge q t x y z hxy hext) := by
  refine ⟨x, y, hxy.ne, ?_, ?_⟩
  · exact Z9C.mpr (Or.inl rfl)
  · exact Z9C.mpr (Or.inr (Or.inl rfl))
theorem Z5d
    {q r t : Node G} {x y z : V} {hxy : G.Adj x y}
    {hext : q.ExtendsBy (Zb9 hxy) t}
    (hr : BasedAt r (mkEdge q t x y z hxy hext)) : r = q := by
  rcases hr with ⟨u, v, huv, hu, hv⟩
  rw [Z9C] at hu hv
  by_contra hrq
  rcases hu with hu | hu | hu
  · exact hrq (congrArg Prod.fst hu)
  · exact hrq (congrArg Prod.fst hu)
  rcases hv with hv | hv | hv
  · exact hrq (congrArg Prod.fst hv)
  · exact hrq (congrArg Prod.fst hv)
  apply huv
  calc
    u = z := congrArg Prod.snd hu
    _ = v := (congrArg Prod.snd hv).symm
theorem Z9N
    {q r : Node G} {e : Edge G}
    (hq : BasedAt q e) (hr : BasedAt r e) : q = r := by
  rcases e.2 with ⟨q0, t0, x0, y0, z0, hxy0, hext0, hset⟩
  have he : e = mkEdge q0 t0 x0 y0 z0 hxy0 hext0 := by
    apply Subtype.ext
    simpa only [mkEdge] using hset
  rw [he] at hq hr
  exact (Z5d hq).trans
    (Z5d hr).symm
theorem Z9O (e : Edge G) : ∃ q : Node G, BasedAt q e := by
  rcases e.2 with ⟨q, t, x, y, z, hxy, hext, hset⟩
  have he : e = mkEdge q t x y z hxy hext := by
    apply Subtype.ext
    simpa only [mkEdge] using hset
  rw [he]
  exact ⟨q, Z9K⟩
noncomputable def baseNode (e : Edge G) : Node G :=
  Classical.choose (Z9O e)
theorem Z8P (e : Edge G) : BasedAt (baseNode e) e :=
  Classical.choose_spec (Z9O e)
theorem Z9c
    {q t : Node G} {x y z : V} {hxy : G.Adj x y}
    {hext : q.ExtendsBy (Zb9 hxy) t} :
    baseNode (mkEdge q t x y z hxy hext) = q := by
  exact Z9N (Z8P _) Z9K
end SequenceLift
end P593
end
section
namespace P593
open scoped Cardinal Ordinal
universe u
namespace SequenceLift
variable {V : Type u} {G : _root_.SimpleGraph V}
theorem Z5b (e : Edge G) :
    ∃ (t : Node G) (x y z : V) (hxy : G.Adj x y)
      (hext : (baseNode e).ExtendsBy (Zb9 hxy) t),
      e = mkEdge (baseNode e) t x y z hxy hext := by
  rcases e.2 with ⟨q, t, x, y, z, hxy, hext, hset⟩
  have he : e = mkEdge q t x y z hxy hext := by
    apply Subtype.ext
    simpa only [mkEdge] using hset
  have hq : q = baseNode e := by
    apply Z9N (e := e)
    · rw [he]
      exact Z9K
    · exact Z8P e
  subst q
  exact ⟨t, x, y, z, hxy, hext, he⟩
end SequenceLift
end P593
end
section
namespace P593
open scoped Cardinal Ordinal
universe u
namespace SequenceLift
variable {V : Type u} {G : _root_.SimpleGraph V}
namespace Node
theorem Z2Z
    {q t : Node G} {a b : ZbG G}
    (ha : q.ExtendsBy a t) (hb : q.ExtendsBy b t) : a = b := by
  rcases ha with ⟨haLength, _, haLetter⟩
  rcases hb with ⟨hbLength, _, hbLetter⟩
  have hIndex : (⟨q.length, haLength⟩ : Set.Iio t.length) =
      ⟨q.length, hbLength⟩ := Subtype.ext (by rfl)
  calc
    a = t.entry ⟨q.length, haLength⟩ := haLetter.symm
    _ = t.entry ⟨q.length, hbLength⟩ := congrArg t.entry hIndex
    _ = b := hbLetter
end Node
theorem Z5v
    {q t1 t2 : Node G} {x1 y1 x2 y2 z1 z2 : V}
    {hxy1 : G.Adj x1 y1} {hxy2 : G.Adj x2 y2}
    {hext1 : q.ExtendsBy (Zb9 hxy1) t1}
    {hext2 : q.ExtendsBy (Zb9 hxy2) t2}
    (hapex : (t1, z1) = (t2, z2)) :
    Zb9 hxy1 = Zb9 hxy2 := by
  have ht : t1 = t2 := congrArg Prod.fst hapex
  subst t2
  exact Node.Z2Z hext1 hext2
theorem Z1V
    {S : Set (Edge G)}
    (hlin : ((system G).Z96 S).Linear)
    {q t₁ t₂ : Node G} {x y z₁ z₂ : V}
    {hxy : G.Adj x y}
    {hext₁ : q.ExtendsBy (Zb9 hxy) t₁}
    {hext₂ : q.ExtendsBy (Zb9 hxy) t₂}
    (hmem₁ : mkEdge q t₁ x y z₁ hxy hext₁ ∈ S)
    (hmem₂ : mkEdge q t₂ x y z₂ hxy hext₂ ∈ S) :
    mkEdge q t₁ x y z₁ hxy hext₁ =
      mkEdge q t₂ x y z₂ hxy hext₂ := by
  let e₁ : S := ⟨mkEdge q t₁ x y z₁ hxy hext₁, hmem₁⟩
  let e₂ : S := ⟨mkEdge q t₂ x y z₂ hxy hext₂, hmem₂⟩
  let pₓ : (system G).ZaR S :=
    ⟨(q, x), ⟨mkEdge q t₁ x y z₁ hxy hext₁, hmem₁,
      (Z9C.mpr (Or.inl rfl))⟩⟩
  let pᵧ : (system G).ZaR S :=
    ⟨(q, y), ⟨mkEdge q t₁ x y z₁ hxy hext₁, hmem₁,
      (Z9C.mpr (Or.inr (Or.inl rfl)))⟩⟩
  have hpx₁ : ((system G).Z96 S).Inc pₓ e₁ := by
    change (system G).Inc (q, x) (mkEdge q t₁ x y z₁ hxy hext₁)
    exact Z9C.mpr (Or.inl rfl)
  have hpx₂ : ((system G).Z96 S).Inc pₓ e₂ := by
    change (system G).Inc (q, x) (mkEdge q t₂ x y z₂ hxy hext₂)
    exact Z9C.mpr (Or.inl rfl)
  have hpy₁ : ((system G).Z96 S).Inc pᵧ e₁ := by
    change (system G).Inc (q, y) (mkEdge q t₁ x y z₁ hxy hext₁)
    exact Z9C.mpr (Or.inr (Or.inl rfl))
  have hpy₂ : ((system G).Z96 S).Inc pᵧ e₂ := by
    change (system G).Inc (q, y) (mkEdge q t₂ x y z₂ hxy hext₂)
    exact Z9C.mpr (Or.inr (Or.inl rfl))
  have heq : e₁ = e₂ := by
    by_contra hne
    have hp : pₓ = pᵧ := hlin hne hpx₁ hpx₂ hpy₁ hpy₂
    apply hxy.ne
    exact congrArg Prod.snd (congrArg Subtype.val hp)
  simpa only [e₁, e₂] using congrArg Subtype.val heq
theorem Z1B
    {S : Set (Edge G)}
    (hlin : ((system G).Z96 S).Linear)
    {q t1 t2 : Node G} {x1 y1 x2 y2 z1 z2 : V}
    {hxy1 : G.Adj x1 y1} {hxy2 : G.Adj x2 y2}
    {hext1 : q.ExtendsBy (Zb9 hxy1) t1}
    {hext2 : q.ExtendsBy (Zb9 hxy2) t2}
    (hletter : Zb9 hxy1 = Zb9 hxy2)
    (hmem1 : mkEdge q t1 x1 y1 z1 hxy1 hext1 ∈ S)
    (hmem2 : mkEdge q t2 x2 y2 z2 hxy2 hext2 ∈ S) :
    mkEdge q t1 x1 y1 z1 hxy1 hext1 =
      mkEdge q t2 x2 y2 z2 hxy2 hext2 := by
  have hpairs : s(x1, y1) = s(x2, y2) := congrArg Subtype.val hletter
  rcases Sym2.eq_iff.mp hpairs with h | h
  · rcases h with ⟨rfl, rfl⟩
    exact Z1V hlin hmem1 hmem2
  · rcases h with ⟨hxy, hyx⟩
    subst y2
    subst x2
    have hext2' : q.ExtendsBy (Zb9 hxy1) t2 := by
      rwa [hletter]
    have hswap :
        mkEdge q t2 y1 x1 z2 hxy2 hext2 =
          mkEdge q t2 x1 y1 z2 hxy1 hext2' := by
      apply Subtype.ext
      ext p
      simp [mkEdge, or_left_comm]
    have hmem2' : mkEdge q t2 x1 y1 z2 hxy1 hext2' ∈ S := by
      rw [← hswap]
      exact hmem2
    exact (Z1V hlin hmem1 hmem2').trans
      hswap.symm
end SequenceLift
end P593
end
section
namespace P593
open scoped Cardinal Ordinal
universe u
namespace SequenceLift
variable {V : Type u} {G : _root_.SimpleGraph V}
def ZaB (e : Edge G) (a : ZbG G) : Prop :=
  ∃ (t : Node G) (x y z : V) (hxy : G.Adj x y)
      (hext : (baseNode e).ExtendsBy (Zb9 hxy) t),
    e = mkEdge (baseNode e) t x y z hxy hext ∧
      a = Zb9 hxy
theorem Z43
    {q t₁ t₂ : Node G} {x₁ y₁ z₁ x₂ y₂ z₂ : V}
    {hxy₁ : G.Adj x₁ y₁} {hxy₂ : G.Adj x₂ y₂}
    {hext₁ : q.ExtendsBy (Zb9 hxy₁) t₁}
    {hext₂ : q.ExtendsBy (Zb9 hxy₂) t₂}
    (heq :
      mkEdge q t₁ x₁ y₁ z₁ hxy₁ hext₁ =
        mkEdge q t₂ x₂ y₂ z₂ hxy₂ hext₂) :
    (t₁, z₁) = (t₂, z₂) := by
  have hinc :
      (system G).Inc (t₁, z₁) (mkEdge q t₂ x₂ y₂ z₂ hxy₂ hext₂) := by
    rw [← heq]
    exact Z9C.mpr (Or.inr (Or.inr rfl))
  rcases Z9C.mp hinc with h | h | h
  · exact
      (Node.Z9b hext₁ (congrArg Prod.fst h).symm).elim
  · exact
      (Node.Z9b hext₁ (congrArg Prod.fst h).symm).elim
  · exact h
theorem Z7s (e : Edge G) :
    ∃ a : ZbG G, ZaB e a := by
  rcases Z5b e with ⟨t, x, y, z, hxy, hext, he⟩
  exact ⟨Zb9 hxy, t, x, y, z, hxy, hext, he, rfl⟩
theorem Z7C
    {e : Edge G} {a b : ZbG G}
    (ha : ZaB e a) (hb : ZaB e b) :
    a = b := by
  rcases ha with ⟨t₁, x₁, y₁, z₁, hxy₁, hext₁, he₁, ha⟩
  rcases hb with ⟨t₂, x₂, y₂, z₂, hxy₂, hext₂, he₂, hb⟩
  have hmk :
      mkEdge (baseNode e) t₁ x₁ y₁ z₁ hxy₁ hext₁ =
        mkEdge (baseNode e) t₂ x₂ y₂ z₂ hxy₂ hext₂ :=
    he₁.symm.trans he₂
  have hapex : (t₁, z₁) = (t₂, z₂) :=
    Z43 hmk
  calc
    a = Zb9 hxy₁ := ha
    _ = Zb9 hxy₂ :=
      Z5v
        (q := baseNode e) (hext1 := hext₁) (hext2 := hext₂) hapex
    _ = b := hb.symm
noncomputable def baseLetter (e : Edge G) : ZbG G :=
  Classical.choose (Z7s e)
theorem Z5Q (e : Edge G) :
    ZaB e (baseLetter e) :=
  Classical.choose_spec (Z7s e)
theorem Z7B
    {q t : Node G} {x y z : V} {hxy : G.Adj x y}
    {hext : q.ExtendsBy (Zb9 hxy) t} :
    ZaB (mkEdge q t x y z hxy hext) (Zb9 hxy) := by
  simp only [ZaB, Z9c]
  exact ⟨t, x, y, z, hxy, hext, rfl, rfl⟩
theorem Z8k
    {q t : Node G} {x y z : V} {hxy : G.Adj x y}
    {hext : q.ExtendsBy (Zb9 hxy) t} :
    baseLetter (mkEdge q t x y z hxy hext) = Zb9 hxy := by
  exact Z7C (Z5Q _) Z7B
theorem Z10
    {S : Set (Edge G)}
    (hlin : ((system G).Z96 S).Linear)
    {e₁ e₂ : Edge G}
    (hmem₁ : e₁ ∈ S) (hmem₂ : e₂ ∈ S)
    (hbase : baseNode e₁ = baseNode e₂)
    (hletter : baseLetter e₁ = baseLetter e₂) :
    e₁ = e₂ := by
  rcases Z5b e₁ with
    ⟨t₁, x₁, y₁, z₁, hxy₁, hext₁, he₁⟩
  rcases Z5b e₂ with
    ⟨t₂, x₂, y₂, z₂, hxy₂, hext₂, he₂⟩
  have hext₂' : (baseNode e₁).ExtendsBy (Zb9 hxy₂) t₂ := by
    rw [hbase]
    exact hext₂
  have he₂' : e₂ = mkEdge (baseNode e₁) t₂ x₂ y₂ z₂ hxy₂ hext₂' := by
    simpa only [hbase] using he₂
  have hbaseLetter₁ : baseLetter e₁ = Zb9 hxy₁ := by
    rw [he₁]
    exact Z8k
  have hbaseLetter₂ : baseLetter e₂ = Zb9 hxy₂ := by
    rw [he₂']
    exact Z8k
  have hdisplayedLetter : Zb9 hxy₁ = Zb9 hxy₂ := by
    calc
      Zb9 hxy₁ = baseLetter e₁ := hbaseLetter₁.symm
      _ = baseLetter e₂ := hletter
      _ = Zb9 hxy₂ := hbaseLetter₂
  have hmem₁' : mkEdge (baseNode e₁) t₁ x₁ y₁ z₁ hxy₁ hext₁ ∈ S := by
    rw [← he₁]
    exact hmem₁
  have hmem₂' : mkEdge (baseNode e₁) t₂ x₂ y₂ z₂ hxy₂ hext₂' ∈ S := by
    rw [← he₂']
    exact hmem₂
  calc
    e₁ = mkEdge (baseNode e₁) t₁ x₁ y₁ z₁ hxy₁ hext₁ := he₁
    _ = mkEdge (baseNode e₁) t₂ x₂ y₂ z₂ hxy₂ hext₂' :=
      Z1B hlin hdisplayedLetter hmem₁' hmem₂'
    _ = e₂ := he₂'.symm
end SequenceLift
end P593
end
section
namespace P593
open scoped Cardinal
universe u v
namespace TripleSystem
variable {V W X : Type u} {E D A : Type v}
variable {F : TripleSystem V E} {G : TripleSystem X A}
variable {H : TripleSystem W D}
def Z4T (F : TripleSystem V E) :
    F.isolatedReduction.Embedding F where
  vertex := ⟨Subtype.val, Subtype.val_injective⟩
  edge := id
  map_edge := by
    intro e
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, F.Z7o hx⟩, hx, rfl⟩
theorem Appears.Z87 (i : G.Embedding F) (hF : F.Appears H) :
    G.Appears H := by
  rcases hF with ⟨f⟩
  exact ⟨i.trans f⟩
theorem IsObligatory.Z7W (i : G.Embedding F)
    (hF : F.IsObligatory) : G.IsObligatory := by
  intro Y B _ K hK
  exact (hF Y B K hK).Z87 i
theorem Z5m (H : TripleSystem W D) :
    H.IsProperColoring id := by
  intro e
  have hne : (H.edgeSet e).ncard ≠ 0 := by
    rw [H.Zaa]
    decide
  obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero hne
  obtain ⟨y, hy, hyx⟩ := H.Z6w e hx
  exact ⟨x, hx, y, hy, hyx.symm⟩
theorem Z3r (H : TripleSystem W D) :
    H.chromaticCardinal ≤ #W :=
  (H.Z4y).2 ⟨id, H.Z5m⟩
noncomputable def Embedding.extendIsolatedReduction [Fintype V] [Infinite W]
    (f : F.isolatedReduction.Embedding H) : F.Embedding H := by
  classical
  let R : Set W := Set.range f.vertex
  have hR : R.Finite := Set.finite_range f.vertex
  letI : Infinite (Rᶜ : Set W) := hR.infinite_compl.to_subtype
  let toNat : {x : V // F.IsIsolated x} ↪ ℕ :=
    Classical.choice (nonempty_embedding_nat {x : V // F.IsIsolated x})
  let unused : {x : V // F.IsIsolated x} ↪ (Rᶜ : Set W) :=
    toNat.trans (Infinite.natEmbedding (Rᶜ : Set W))
  let vertexMap : V → W := fun x ↦
    if hx : F.IsIsolated x then (unused ⟨x, hx⟩ : W)
    else f.vertex ⟨x, hx⟩
  have vertexMap_injective : Function.Injective vertexMap := by
    intro x y hxy
    by_cases hx : F.IsIsolated x
    · by_cases hy : F.IsIsolated y
      · have hu : unused ⟨x, hx⟩ = unused ⟨y, hy⟩ := by
          apply Subtype.ext
          simpa [vertexMap, hx, hy] using hxy
        exact congrArg Subtype.val (unused.injective hu)
      · have hbad : (unused ⟨x, hx⟩ : W) ∈ R := by
          refine ⟨⟨y, hy⟩, ?_⟩
          simpa [vertexMap, hx, hy] using hxy.symm
        exact False.elim ((unused ⟨x, hx⟩).property hbad)
    · by_cases hy : F.IsIsolated y
      · have hbad : (unused ⟨y, hy⟩ : W) ∈ R := by
          refine ⟨⟨x, hx⟩, ?_⟩
          simpa [vertexMap, hx, hy] using hxy
        exact False.elim ((unused ⟨y, hy⟩).property hbad)
      · have hf : f.vertex ⟨x, hx⟩ = f.vertex ⟨y, hy⟩ := by
          simpa [vertexMap, hx, hy] using hxy
        exact congrArg Subtype.val (f.vertex.injective hf)
  refine
    { vertex := ⟨vertexMap, vertexMap_injective⟩
      edge := f.edge
      map_edge := ?_ }
  intro e
  calc
    vertexMap '' F.edgeSet e =
        f.vertex '' F.isolatedReduction.edgeSet e := by
      ext w
      constructor
      · rintro ⟨x, hxe, rfl⟩
        have hx : ¬F.IsIsolated x := F.Z7o hxe
        refine ⟨⟨x, hx⟩, hxe, ?_⟩
        simp [vertexMap, hx]
      · rintro ⟨x, hxe, rfl⟩
        refine ⟨x.1, hxe, ?_⟩
        simp [vertexMap, x.2]
    _ = H.edgeSet (f.edge e) := f.map_edge e
theorem IsObligatory.Z6Z [Fintype V]
    (hF : F.isolatedReduction.IsObligatory) : F.IsObligatory := by
  intro Y B _ K hK
  obtain ⟨f⟩ := hF Y B K hK
  have hvertices : ℵ₀ ≤ #Y :=
    hK.le.trans K.Z3r
  letI : Infinite Y := Cardinal.aleph0_le_mk_iff.mp hvertices
  exact ⟨f.extendIsolatedReduction⟩
end TripleSystem
end P593
end
section
namespace P593
universe u v w x
namespace TripleSystem
namespace Embedding
variable {V : Type u} {E : Type v} {W : Type w} {D : Type x}
variable {F : TripleSystem V E} {H : TripleSystem W D}
theorem Z1Y [Fintype E]
    (f : F.Embedding H) (hlinear : F.Linear) :
    let f' := (Z4T F).trans f
    f'.Zbu.Finite ∧
      (H.Z96 f'.Zbu).Linear ∧
      Nonempty (Iso F.isolatedReduction (H.Z96 f'.Zbu)) := by
  dsimp
  have hlinear' : F.isolatedReduction.Linear :=
    F.Z5z hlinear
  refine ⟨Set.finite_range _, ?_, ?_⟩
  · exact ((Z4T F).trans f).Z4M
      F.Z2A hlinear'
  · exact ⟨((Z4T F).trans f).imageEdgeRestrictionIso
      F.Z2A⟩
end Embedding
end TripleSystem
end P593
end
section
namespace P593
open scoped Cardinal Ordinal
universe u v w
namespace SequenceLift
variable {V : Type u} {G : _root_.SimpleGraph V}
def Zbo (S : Set (Edge G)) (q : Node G) : Set (Edge G) :=
  {e | e ∈ S ∧ baseNode e = q}
@[simp]
theorem Zau {S : Set (Edge G)} {q : Node G} {e : Edge G} :
    e ∈ Zbo S q ↔ e ∈ S ∧ baseNode e = q :=
  Iff.rfl
theorem Z8O (S : Set (Edge G)) (q : Node G) :
    Zbo S q ⊆ S := by
  intro e he
  exact he.1
theorem Z2F
    {S : Set (Edge G)} (q : Node G)
    (hlin : ((system G).Z96 S).Linear) :
    Set.InjOn baseLetter (Zbo S q) := by
  intro e₁ he₁ e₂ he₂ hletter
  exact Z10
    hlin he₁.1 he₂.1 (he₁.2.trans he₂.2.symm) hletter
end SequenceLift
end P593
end
section
namespace P593
universe u
namespace SequenceLift
variable {V : Type u} {G : _root_.SimpleGraph V}
def Zbh (e : Edge G) (p : Point G) : Prop :=
  (system G).Inc p e ∧ p.1 ≠ baseNode e
theorem Z5M (e : Edge G) :
    ∃! p : Point G, Zbh e p := by
  rcases Z5b e with ⟨t, x, y, z, hxy, hext, he⟩
  rw [he]
  refine ⟨(t, z), ?_, ?_⟩
  · constructor
    · exact Z9C.mpr (Or.inr (Or.inr rfl))
    · simpa only [Z9c] using (Node.Z9b hext).symm
  · intro p hp
    rcases Z9C.mp hp.1 with h | h | h
    · exfalso
      apply hp.2
      simp only [h, Z9c]
    · exfalso
      apply hp.2
      simp only [h, Z9c]
    · exact h
noncomputable def baseApex (e : Edge G) : Point G :=
  Classical.choose (Z5M e).exists
theorem Z7i (e : Edge G) :
    Zbh e (baseApex e) :=
  Classical.choose_spec (Z5M e).exists
theorem ZaI (e : Edge G) :
    (system G).Inc (baseApex e) e :=
  (Z7i e).1
theorem Z5c (e : Edge G) :
    (baseApex e).1 ≠ baseNode e :=
  (Z7i e).2
theorem Z5g {e : Edge G} {p : Point G}
    (hp : Zbh e p) :
    p = baseApex e := by
  exact (Z5M e).unique hp (Z7i e)
theorem Z98
    {q t : Node G} {x y z : V} {hxy : G.Adj x y}
    {hext : q.ExtendsBy (Zb9 hxy) t} :
    baseApex (mkEdge q t x y z hxy hext) = (t, z) := by
  symm
  apply Z5g
  constructor
  · exact Z9C.mpr (Or.inr (Or.inr rfl))
  · simpa only [Z9c] using (Node.Z9b hext).symm
theorem Z4c
    {S : Set (Edge G)} (q : Node G)
    (hlin : ((system G).Z96 S).Linear)
    {e f : Edge G}
    (he : e ∈ Zbo S q) (hf : f ∈ Zbo S q) :
    (system G).Inc (baseApex e) f ↔ e = f := by
  constructor
  · intro hinc
    rcases Z5b e with
      ⟨t₁, x₁, y₁, z₁, hxy₁, hext₁, he₁⟩
    rcases Z5b f with
      ⟨t₂, x₂, y₂, z₂, hxy₂, hext₂, he₂⟩
    have hapex₁ : baseApex e = (t₁, z₁) := by
      rw [he₁]
      exact Z98
    have hinc' : (system G).Inc (t₁, z₁) f := by
      rw [← hapex₁]
      exact hinc
    rw [he₂, Z9C] at hinc'
    rcases hinc' with hcore | hcore | hapex
    · have hext₁' : q.ExtendsBy (Zb9 hxy₁) t₁ := by
        simpa only [he.2] using hext₁
      have htq : t₁ ≠ q := (Node.Z9b hext₁').symm
      exact (htq ((congrArg Prod.fst hcore).trans hf.2)).elim
    · have hext₁' : q.ExtendsBy (Zb9 hxy₁) t₁ := by
        simpa only [he.2] using hext₁
      have htq : t₁ ≠ q := (Node.Z9b hext₁').symm
      exact (htq ((congrArg Prod.fst hcore).trans hf.2)).elim
    · have hext₁' : q.ExtendsBy (Zb9 hxy₁) t₁ := by
        simpa only [he.2] using hext₁
      have hext₂' : q.ExtendsBy (Zb9 hxy₂) t₂ := by
        simpa only [hf.2] using hext₂
      have hletter : baseLetter e = baseLetter f := by
        calc
          baseLetter e = Zb9 hxy₁ := by
            rw [he₁]
            exact Z8k
          _ = Zb9 hxy₂ :=
            Z5v
              (q := q) (hext1 := hext₁') (hext2 := hext₂') hapex
          _ = baseLetter f := by
            rw [he₂]
            exact Z8k.symm
      exact Z10
        hlin he.1 hf.1 (he.2.trans hf.2.symm) hletter
  · rintro rfl
    exact (Z7i e).1
theorem Z35
    {S : Set (Edge G)} (q : Node G)
    (hlin : ((system G).Z96 S).Linear) :
    Set.InjOn baseApex (Zbo S q) := by
  intro e he f hf hapex
  apply (Z4c q hlin he hf).mp
  rw [hapex]
  exact (Z7i f).1
end SequenceLift
end P593
end
section
namespace P593
universe u
namespace SequenceLift
variable {V : Type u} (G : _root_.SimpleGraph V)
theorem Z28
    (e : Edge G) (p : Point G) :
    (system G).Inc p e ↔
      (p.1 = baseNode e ∧ p.2 ∈ (baseLetter e).1) ∨ p = baseApex e := by
  rcases Z5b e with ⟨t, x, y, z, hxy, hext, he⟩
  rw [he, Z9C, Z9c, Z8k, Z98]
  constructor
  · rintro (hp | hp | hp)
    · subst p
      left
      constructor
      · rfl
      · simp [Zb9]
    · subst p
      left
      constructor
      · rfl
      · simp [Zb9]
    · exact Or.inr hp
  · rintro (⟨hnode, hmem⟩ | hp)
    · change p.2 ∈ s(x, y) at hmem
      rcases Sym2.mem_iff.mp hmem with hx | hy
      · left
        exact Prod.ext hnode hx
      · right
        left
        exact Prod.ext hnode hy
    · exact Or.inr (Or.inr hp)
end SequenceLift
end P593
end
section
namespace P593
universe u
namespace SequenceLift
variable {V : Type u} {G : _root_.SimpleGraph V}
namespace Node
theorem Z3t
    {q u t : Node G} {a b : ZbG G}
    (hqt : q.ExtendsBy a t) (hut : u.ExtendsBy b t)
    (hqu : q.length < u.length) : q.ExtendsBy a u := by
  apply Exists.intro hqu
  constructor
  · intro i
    calc
      q.entry i = t.entry ⟨i.1, i.2.trans hqt.choose⟩ := hqt.choose_spec.1 i
      _ = t.entry ⟨i.1, (i.2.trans hqu).trans hut.choose⟩ := by
        exact congrArg t.entry (Subtype.ext rfl)
      _ = u.entry ⟨i.1, i.2.trans hqu⟩ :=
        (hut.choose_spec.1 ⟨i.1, i.2.trans hqu⟩).symm
  · calc
      u.entry ⟨q.length, hqu⟩ = t.entry ⟨q.length, hqu.trans hut.choose⟩ :=
        hut.choose_spec.1 ⟨q.length, hqu⟩
      _ = t.entry ⟨q.length, hqt.choose⟩ := by
        exact congrArg t.entry (Subtype.ext rfl)
      _ = a := hqt.choose_spec.2
theorem Z3s
    {q u t : Node G} {a b : ZbG G}
    (hqt : q.ExtendsBy a t) (hut : u.ExtendsBy b t)
    (hqu : q.length = u.length) : q = u := by
  cases q
  cases u
  cases hqu
  congr
  funext i
  calc
    _ = t.entry ⟨i.1, i.2.trans hqt.choose⟩ := hqt.choose_spec.1 i
    _ = t.entry ⟨i.1, i.2.trans hut.choose⟩ := by
      exact congrArg t.entry (Subtype.ext rfl)
    _ = _ := (hut.choose_spec.1 i).symm
end Node
theorem Z5s
    {S : Set (Edge G)} {q u : Node G} (hqlt : q.length < u.length)
    {p : Point G} {e f : Edge G}
    (he : e ∈ Zbo S q) (hf : f ∈ Zbo S u)
    (hpe : (system G).Inc p e) (hpf : (system G).Inc p f) :
    p = baseApex e ∧ q.ExtendsBy (baseLetter e) u := by
  rcases (Z28 G e p).mp hpe with hpcore | hpApex
  · rcases (Z28 G f p).mp hpf with hpucore | huApex
    · have hpq : p.1 = q := hpcore.1.trans he.2
      have hpu : p.1 = u := hpucore.1.trans hf.2
      have hqu : q = u := hpq.symm.trans hpu
      exact (hqlt.ne (congrArg Node.length hqu)).elim
    · rcases Z5b f with ⟨t, x, y, z, hxy, hext, hfm⟩
      have hextu : u.ExtendsBy (Zb9 hxy) t := by
        rw [hf.2] at hext
        exact hext
      have hapexf : baseApex f = (t, z) := by
        rw [hfm]
        exact Z98
      have hpq : p.1 = q := hpcore.1.trans he.2
      have hqt : q = t := by
        calc
          q = p.1 := hpq.symm
          _ = (baseApex f).1 := congrArg Prod.fst huApex
          _ = t := congrArg Prod.fst hapexf
      have huq : u.length < q.length := by
        rw [hqt]
        exact hextu.choose
      exact (lt_asymm hqlt huq).elim
  · rcases (Z28 G f p).mp hpf with hpucore | huApex
    · rcases Z5b e with ⟨t, x, y, z, hxy, hext, hem⟩
      have hextq : q.ExtendsBy (Zb9 hxy) t := by
        rw [he.2] at hext
        exact hext
      have hapexe : baseApex e = (t, z) := by
        rw [hem]
        exact Z98
      have hpu : p.1 = u := hpucore.1.trans hf.2
      have htp : t = p.1 := by
        calc
          t = (baseApex e).1 := (congrArg Prod.fst hapexe).symm
          _ = p.1 := (congrArg Prod.fst hpApex).symm
      have htu : t = u := htp.trans hpu
      have hletter : baseLetter e = Zb9 hxy := by
        rw [hem]
        exact Z8k
      refine ⟨hpApex, ?_⟩
      rw [hletter]
      rw [← htu]
      exact hextq
    · rcases Z5b e with ⟨t, x, y, z, hxy, hext, hem⟩
      rcases Z5b f with ⟨v, w, r, s, hwr, hfext, hfm⟩
      have hextq : q.ExtendsBy (Zb9 hxy) t := by
        rw [he.2] at hext
        exact hext
      have hextu : u.ExtendsBy (Zb9 hwr) v := by
        rw [hf.2] at hfext
        exact hfext
      have hapexe : baseApex e = (t, z) := by
        rw [hem]
        exact Z98
      have hapexf : baseApex f = (v, s) := by
        rw [hfm]
        exact Z98
      have htv : t = v := by
        calc
          t = (baseApex e).1 := (congrArg Prod.fst hapexe).symm
          _ = p.1 := (congrArg Prod.fst hpApex).symm
          _ = (baseApex f).1 := congrArg Prod.fst huApex
          _ = v := congrArg Prod.fst hapexf
      have hextu' : u.ExtendsBy (Zb9 hwr) t := by
        rw [htv]
        exact hextu
      have hletter : baseLetter e = Zb9 hxy := by
        rw [hem]
        exact Z8k
      refine ⟨hpApex, ?_⟩
      rw [hletter]
      exact Node.Z3t hextq hextu' hqlt
theorem Z4C
    {S : Set (Edge G)} {q u : Node G} (hqu : q.length = u.length)
    {p : Point G} {e f : Edge G}
    (he : e ∈ Zbo S q) (hf : f ∈ Zbo S u)
    (hpe : (system G).Inc p e) (hpf : (system G).Inc p f) : q = u := by
  rcases (Z28 G e p).mp hpe with hpcore | hpApex
  · rcases (Z28 G f p).mp hpf with hpucore | huApex
    · have hpq : p.1 = q := hpcore.1.trans he.2
      have hpu : p.1 = u := hpucore.1.trans hf.2
      exact hpq.symm.trans hpu
    · rcases Z5b f with ⟨t, x, y, z, hxy, hext, hfm⟩
      have hextu : u.ExtendsBy (Zb9 hxy) t := by
        rw [hf.2] at hext
        exact hext
      have hapexf : baseApex f = (t, z) := by
        rw [hfm]
        exact Z98
      have hpq : p.1 = q := hpcore.1.trans he.2
      have hqt : q = t := by
        calc
          q = p.1 := hpq.symm
          _ = (baseApex f).1 := congrArg Prod.fst huApex
          _ = t := congrArg Prod.fst hapexf
      have huq : u.length < q.length := by
        rw [hqt]
        exact hextu.choose
      rw [hqu] at huq
      exact (lt_irrefl _ huq).elim
  · rcases (Z28 G f p).mp hpf with hpucore | huApex
    · rcases Z5b e with ⟨t, x, y, z, hxy, hext, hem⟩
      have hextq : q.ExtendsBy (Zb9 hxy) t := by
        rw [he.2] at hext
        exact hext
      have hapexe : baseApex e = (t, z) := by
        rw [hem]
        exact Z98
      have hpu : p.1 = u := hpucore.1.trans hf.2
      have htp : t = p.1 := by
        calc
          t = (baseApex e).1 := (congrArg Prod.fst hapexe).symm
          _ = p.1 := (congrArg Prod.fst hpApex).symm
      have htu : t = u := htp.trans hpu
      have hqut : q.length < u.length := by
        rw [← htu]
        exact hextq.choose
      rw [hqu] at hqut
      exact (lt_irrefl _ hqut).elim
    · rcases Z5b e with ⟨t, x, y, z, hxy, hext, hem⟩
      rcases Z5b f with ⟨v, w, r, s, hwr, hfext, hfm⟩
      have hextq : q.ExtendsBy (Zb9 hxy) t := by
        rw [he.2] at hext
        exact hext
      have hextu : u.ExtendsBy (Zb9 hwr) v := by
        rw [hf.2] at hfext
        exact hfext
      have hapexe : baseApex e = (t, z) := by
        rw [hem]
        exact Z98
      have hapexf : baseApex f = (v, s) := by
        rw [hfm]
        exact Z98
      have htv : t = v := by
        calc
          t = (baseApex e).1 := (congrArg Prod.fst hapexe).symm
          _ = p.1 := (congrArg Prod.fst hpApex).symm
          _ = (baseApex f).1 := congrArg Prod.fst huApex
          _ = v := congrArg Prod.fst hapexf
      have hextu' : u.ExtendsBy (Zb9 hwr) t := by
        rw [htv]
        exact hextu
      exact Node.Z3s hextq hextu' hqu
theorem Z19
    {S : Set (Edge G)} {q u : Node G}
    (hlin : ((system G).Z96 S).Linear) (hne : q ≠ u) :
    (((system G).Z9z (Zbo S q) ∩
      (system G).Z9z (Zbo S u))).Subsingleton := by
  intro p hp r hr
  rcases hp with ⟨hpq, hpu⟩
  rcases hr with ⟨hrq, hru⟩
  rcases hpq with ⟨e, he, hpe⟩
  rcases hpu with ⟨f, hf, hpf⟩
  rcases hrq with ⟨e', he', hre⟩
  rcases hru with ⟨f', hf', hrf⟩
  rcases lt_trichotomy q.length u.length with hqlt | hqu | huqlt
  · rcases Z5s hqlt he hf hpe hpf with ⟨hpApex, hqe⟩
    rcases Z5s hqlt he' hf' hre hrf with ⟨hrApex, hqe'⟩
    have hletter : baseLetter e = baseLetter e' :=
      Node.Z2Z hqe hqe'
    have heq : e = e' :=
      Z10
        hlin he.1 he'.1 (he.2.trans he'.2.symm) hletter
    calc
      p = baseApex e := hpApex
      _ = baseApex e' := by rw [heq]
      _ = r := hrApex.symm
  · exact (hne (Z4C hqu he hf hpe hpf)).elim
  · rcases Z5s (q := u) (u := q) huqlt hf he hpf hpe with
      ⟨hpApex, huf⟩
    rcases Z5s (q := u) (u := q) huqlt hf' he' hrf hre with
      ⟨hrApex, huf'⟩
    have hletter : baseLetter f = baseLetter f' :=
      Node.Z2Z huf huf'
    have hfeq : f = f' :=
      Z10
        hlin hf.1 hf'.1 (hf.2.trans hf'.2.symm) hletter
    calc
      p = baseApex f := hpApex
      _ = baseApex f' := by rw [hfeq]
      _ = r := hrApex.symm
end SequenceLift
end P593
end
section
namespace P593
universe u
namespace SequenceLift
variable {V : Type u} {G : _root_.SimpleGraph V}
namespace Node
theorem ExtendsBy.trans
    {q u v : Node G} {a b : ZbG G}
    (hqu : q.ExtendsBy a u) (huv : u.ExtendsBy b v) :
    q.ExtendsBy a v := by
  rcases hqu with ⟨hqu, hqu_entries, hqu_letter⟩
  rcases huv with ⟨huv, huv_entries, huv_letter⟩
  refine ⟨hqu.trans huv, ?_, ?_⟩
  · intro i
    calc
      q.entry i = u.entry ⟨i.1, i.2.trans hqu⟩ := hqu_entries i
      _ = v.entry ⟨i.1, (i.2.trans hqu).trans huv⟩ :=
        huv_entries ⟨i.1, i.2.trans hqu⟩
      _ = v.entry ⟨i.1, i.2.trans (hqu.trans huv)⟩ := by
        exact congrArg v.entry (Subtype.ext rfl)
  · calc
      v.entry ⟨q.length, hqu.trans huv⟩ =
          u.entry ⟨q.length, hqu⟩ :=
        (huv_entries ⟨q.length, hqu⟩).symm
      _ = a := hqu_letter
end Node
theorem Z1g
    {S : Set (Edge G)} {q u : Node G} (hqu : q.length < u.length)
    {p : Point G}
    (hpq : p ∈ (system G).Z9z (Zbo S q))
    (hpu : p ∈ (system G).Z9z (Zbo S u)) :
    ∃ e ∈ Zbo S q,
      p = baseApex e ∧ q.ExtendsBy (baseLetter e) u := by
  rcases hpq with ⟨e, he, hpe⟩
  rcases hpu with ⟨f, hf, hpf⟩
  exact ⟨e, he, (Z5s hqu he hf hpe hpf).1,
    (Z5s hqu he hf hpe hpf).2⟩
theorem Z3d
    {S : Set (Edge G)} {q u : Node G} (hqu : q.length = u.length)
    {p : Point G}
    (hpq : p ∈ (system G).Z9z (Zbo S q))
    (hpu : p ∈ (system G).Z9z (Zbo S u)) :
    q = u := by
  rcases hpq with ⟨e, he, hpe⟩
  rcases hpu with ⟨f, hf, hpf⟩
  exact Z4C hqu he hf hpe hpf
theorem Node.Z3e
    {S : Set (Edge G)} {q u v : Node G} {a : ZbG G}
    (hqu : q.ExtendsBy a u)
    (hqvle : q.length ≤ v.length) (hqvne : q ≠ v)
    {p : Point G}
    (hpu : p ∈ (system G).Z9z (Zbo S u))
    (hpv : p ∈ (system G).Z9z (Zbo S v)) :
    q.ExtendsBy a v := by
  rcases lt_trichotomy u.length v.length with huv | huv | hvu
  · rcases Z1g huv hpu hpv with
      ⟨e, he, hp, huv'⟩
    exact hqu.trans huv'
  · have huv' : u = v := Z3d huv hpu hpv
    simpa [huv'] using hqu
  · rcases Z1g (S := S) (q := v) (u := u)
      hvu hpv hpu with ⟨e, he, hp, hvu'⟩
    have hqv : q.length < v.length := by
      rcases hqvle.eq_or_lt with hqv | hqv
      · exact (hqvne (Node.Z3s hqu hvu' hqv)).elim
      · exact hqv
    exact Node.Z3t hqu hvu' hqv
end SequenceLift
end P593
end
section
namespace P593
universe u v w
namespace SequenceLift
variable {V : Type u} {G : _root_.SimpleGraph V}
def Z9j (S : Set (Edge G)) : Set (Node G) :=
  baseNode '' S
@[simp]
theorem Z7M {S : Set (Edge G)} {q : Node G} :
    q ∈ Z9j S ↔ ∃ e ∈ S, baseNode e = q :=
  Iff.rfl
theorem Z84 {S : Set (Edge G)} {q₁ q₂ : Node G}
    (hneq : q₁ ≠ q₂) :
    Disjoint (Zbo S q₁) (Zbo S q₂) := by
  refine Set.disjoint_left.2 ?_
  intro e he₁ he₂
  exact hneq (he₁.2.symm.trans he₂.2)
theorem Z3x {S : Set (Edge G)}
    (hS : S.Finite) :
    (Z9j S).Finite := by
  exact hS.image baseNode
end SequenceLift
end P593
end
section
namespace P593
universe u v w
namespace SequenceLift
variable {V : Type u} {G : _root_.SimpleGraph V}
abbrev Z7a (S : Set (Edge G)) : Type u :=
  {q : Node G // q ∈ Z9j S}
theorem Z51 {S : Set (Edge G)}
    (hS : S.Finite) :
    Finite (Z7a S) :=
  (Z3x hS).to_subtype
noncomputable abbrev activeBaseNodeIndexFintype {S : Set (Edge G)}
    (hS : S.Finite) : Fintype (Z7a S) := by
  letI : Finite (Z7a S) := Z51 hS
  exact Fintype.ofFinite _
end SequenceLift
end P593
end
section
namespace P593
universe u
namespace SequenceLift
variable {V : Type u} {G : _root_.SimpleGraph V}
abbrev Z3n (S : Set (Edge G)) : Type u :=
  {p : Point G // p ∈ (system G).Z9z S}
theorem Z2b {S : Set (Edge G)}
    (hS : S.Finite) :
    Finite (Z3n S) :=
  ((system G).Z6M hS).to_subtype
noncomputable abbrev activeBaseFiberSupportPointIndexFintype {S : Set (Edge G)}
    (hS : S.Finite) : Fintype (Z3n S) := by
  letI : Finite (Z3n S) :=
    Z2b hS
  exact Fintype.ofFinite _
def Z3V (S : Set (Edge G)) :
    SimpleGraph
      (Z7a S ⊕ Z3n S) :=
  SimpleGraph.fromRel fun x y =>
    match x, y with
    | .inl q, .inr p =>
        p.1 ∈ (system G).Z9z (Zbo S q.1)
    | _, _ => False
@[simp]
theorem Z17
    {S : Set (Edge G)}
    {q : Z7a S}
    {p : Z3n S} :
    (Z3V S).Adj (.inl q) (.inr p) ↔
      p.1 ∈ (system G).Z9z (Zbo S q.1) := by
  simp [Z3V, SimpleGraph.fromRel_adj]
@[simp]
theorem Z18
    {S : Set (Edge G)}
    {q : Z7a S}
    {p : Z3n S} :
    (Z3V S).Adj (.inr p) (.inl q) ↔
      p.1 ∈ (system G).Z9z (Zbo S q.1) := by
  simp [Z3V, SimpleGraph.fromRel_adj]
@[simp]
theorem Z15
    {S : Set (Edge G)}
    {q r : Z7a S} :
    ¬ (Z3V S).Adj (.inl q) (.inl r) := by
  simp [Z3V, SimpleGraph.fromRel_adj]
@[simp]
theorem Z16
    {S : Set (Edge G)}
    {p r : Z3n S} :
    ¬ (Z3V S).Adj (.inr p) (.inr r) := by
  simp [Z3V, SimpleGraph.fromRel_adj]
end SequenceLift
end P593
end
section
namespace P593
universe u
namespace SequenceLift
variable {V : Type u} {G : _root_.SimpleGraph V}
private theorem Z2X
    {S : Set (Edge G)}
    {v : Z7a S ⊕ Z3n S}
    (c : (Z3V S).Walk v v)
    (hc : c.IsCycle) :
    ∃ q : Z7a S, (.inl q :
      Z7a S ⊕ Z3n S) ∈ c.support := by
  cases v with
  | inl q =>
      refine ⟨q, ?_⟩
      simpa only [c.getVert_zero] using c.getVert_mem_support 0
  | inr p =>
      have hsnd := c.adj_snd hc.not_nil
      have hlen : 1 ≤ c.length := by
        have hthree := hc.three_le_length
        omega
      cases hs : c.snd with
      | inl q =>
          refine ⟨q, ?_⟩
          apply (c.mem_support_iff_exists_getVert).mpr
          refine ⟨1, ?_, hlen⟩
          simp [hs]
      | inr p' =>
          rw [hs] at hsnd
          exact (Z16 hsnd).elim
private theorem Z3J
    {S : Set (Edge G)}
    {v : Z7a S ⊕ Z3n S}
    {q : Z7a S}
    (c : (Z3V S).Walk v v)
    (hc : c.IsCycle)
    (hq : (.inl q : Z7a S ⊕ Z3n S) ∈
      c.support) :
    ∃ r : (Z3V S).Walk (.inl q) (.inl q),
      r.IsCycle ∧
      (∀ x : Z7a S ⊕ Z3n S,
        x ∈ r.support ↔ x ∈ c.support) ∧
      ∃ pL pR : Z3n S,
      ∃ uL uR : Z7a S,
        r.snd = .inr pL ∧
        r.getVert 2 = .inl uL ∧
        r.getVert (r.length - 2) = .inl uR ∧
        r.penultimate = .inr pR ∧
        (Z3V S).Adj (.inl q) (.inr pL) ∧
        (Z3V S).Adj (.inr pL) (.inl uL) ∧
        (Z3V S).Adj (.inl uR) (.inr pR) ∧
        (Z3V S).Adj (.inr pR) (.inl q) ∧
        pL ≠ pR ∧ uL ≠ q ∧ uR ≠ q := by
  classical
  let r := c.rotate (.inl q) hq
  have hr : r.IsCycle := hc.rotate hq
  have hlen : 3 ≤ r.length := hr.three_le_length
  have hsnd : (Z3V S).Adj (.inl q) r.snd :=
    r.adj_snd hr.not_nil
  have hpen : (Z3V S).Adj r.penultimate (.inl q) :=
    r.adj_penultimate hr.not_nil
  cases hs : r.snd with
  | inl q' =>
      rw [hs] at hsnd
      exact (Z15 hsnd).elim
  | inr pL =>
      cases hp : r.penultimate with
      | inl q' =>
          rw [hp] at hpen
          exact (Z15 hpen).elim
      | inr pR =>
          have hLadj : (Z3V S).Adj (.inr pL)
              (r.getVert 2) := by
            rw [← hs]
            exact r.adj_getVert_succ (i := 1) (by omega)
          have hRadj : (Z3V S).Adj
              (r.getVert (r.length - 2)) (.inr pR) := by
            rw [← hp]
            have hindex : r.length - 2 + 1 = r.length - 1 := by omega
            change (Z3V S).Adj
              (r.getVert (r.length - 2)) (r.getVert (r.length - 1))
            rw [← hindex]
            exact r.adj_getVert_succ (i := r.length - 2) (by omega)
          cases hL : r.getVert 2 with
          | inr p =>
              rw [hL] at hLadj
              exact (Z16 hLadj).elim
          | inl uL =>
              cases hR : r.getVert (r.length - 2) with
              | inr p =>
                  rw [hR] at hRadj
                  exact (Z16 hRadj).elim
              | inl uR =>
                  refine ⟨r, hr, ?_, pL, pR, uL, uR, hs, hL, hR, hp,
                    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · intro x
                    dsimp [r]
                    exact c.mem_support_rotate_iff (.inl q) hq
                  · simpa [hs] using hsnd
                  · simpa [hL] using hLadj
                  · simpa [hR] using hRadj
                  · simpa [hp] using hpen
                  · intro hpLR
                    apply hr.snd_ne_penultimate
                    calc
                      r.snd = .inr pL := hs
                      _ = .inr pR := congrArg Sum.inr hpLR
                      _ = r.penultimate := hp.symm
                  · intro huL
                    have hEq : r.getVert 2 = (.inl q :
                        Z7a S ⊕ Z3n S) := by
                      calc
                        r.getVert 2 = .inl uL := hL
                        _ = .inl q := congrArg Sum.inl huL
                    have hEnds := (hr.getVert_endpoint_iff (i := 2) (by omega)).mp hEq
                    omega
                  · intro huR
                    have hEq : r.getVert (r.length - 2) = (.inl q :
                        Z7a S ⊕ Z3n S) := by
                      calc
                        r.getVert (r.length - 2) = .inl uR := hR
                        _ = .inl q := congrArg Sum.inl huR
                    have hEnds :=
                      (hr.getVert_endpoint_iff (i := r.length - 2) (by omega)).mp hEq
                    omega
private theorem Z42
    {S : Set (Edge G)} {q : Z7a S}
    (r : (Z3V S).Walk (.inl q) (.inl q)) :
    ∀ k : ℕ, 2 * k ≤ r.length →
      ∃ u : Z7a S, r.getVert (2 * k) = .inl u := by
  intro k
  induction k with
  | zero =>
      intro _
      exact ⟨q, by simp⟩
  | succ k ih =>
      intro hk
      have hbound : 2 * k + 2 ≤ r.length := by
        convert hk using 1
        all_goals omega
      rcases ih (by omega) with ⟨u, hu⟩
      have hmid : (Z3V S).Adj
          (.inl u) (r.getVert (2 * k + 1)) := by
        have hadj := r.adj_getVert_succ (i := 2 * k) (by omega)
        simpa [hu] using hadj
      cases hm : r.getVert (2 * k + 1) with
      | inl w =>
          rw [hm] at hmid
          exact (Z15 hmid).elim
      | inr p =>
          have hnext : (Z3V S).Adj
              (.inr p) (r.getVert (2 * (k + 1))) := by
            rw [← hm]
            have hsuc : 2 * k + 1 < r.length := by omega
            have hadj := r.adj_getVert_succ (i := 2 * k + 1) hsuc
            have hindex : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
            rw [hindex] at hadj
            exact hadj
          cases hn : r.getVert (2 * (k + 1)) with
          | inl w => exact ⟨w, rfl⟩
          | inr p' =>
              rw [hn] at hnext
              exact (Z16 hnext).elim
private theorem Z4R
    {S : Set (Edge G)} {q : Z7a S}
    (r : (Z3V S).Walk (.inl q) (.inl q)) :
    ∃ n : ℕ, r.length = 2 * n := by
  rcases Nat.even_or_odd' r.length with ⟨n, hn | hn⟩
  · exact ⟨n, hn⟩
  · have hle : 2 * n ≤ r.length := by omega
    rcases Z42 r n hle with ⟨u, hu⟩
    have hadj := r.adj_getVert_succ (i := 2 * n) (by omega)
    have hend : r.getVert (2 * n + 1) = (.inl q :
        Z7a S ⊕ Z3n S) := by
      rw [← hn]
      exact r.getVert_length
    rw [hu, hend] at hadj
    exact (Z15 hadj).elim
private theorem Z4q
    {S : Set (Edge G)} {q : Z7a S}
    (r : (Z3V S).Walk (.inl q) (.inl q))
    (hr : r.IsCycle) {i : ℕ} {u : Z7a S}
    (hi : 0 < i) (hil : i < r.length)
    (hu : r.getVert i = .inl u) :
    q ≠ u := by
  intro hqu
  have hEq : r.getVert i = (.inl q :
      Z7a S ⊕ Z3n S) := by
    calc
      r.getVert i = .inl u := hu
      _ = .inl q := congrArg Sum.inl hqu.symm
  have hEnds := (hr.getVert_endpoint_iff (i := i) (by omega)).mp hEq
  omega
private theorem Z3U
    {S : Set (Edge G)} {q : Z7a S}
    (r : (Z3V S).Walk (.inl q) (.inl q))
    (hr : r.IsCycle) {n : ℕ} (hlen : r.length = 2 * n)
    (hmin : ∀ u : Z7a S,
      (.inl u : Z7a S ⊕ Z3n S) ∈
        r.support → q.1.length ≤ u.1.length)
    {a : ZbG G} {u1 : Z7a S}
    (hu1 : r.getVert 2 = .inl u1)
    (hqu1 : q.1.ExtendsBy a u1.1) :
    ∀ k : ℕ, ∀ u : Z7a S,
      1 ≤ k → k < n → r.getVert (2 * k) = .inl u → q.1.ExtendsBy a u.1 := by
  intro k
  induction k with
  | zero =>
      intro u hk
      omega
  | succ k ih =>
      intro u hk hkn hu
      cases k with
      | zero =>
          have htwo : 2 * Nat.succ 0 = 2 := by omega
          have hu' : r.getVert 2 = (.inl u :
              Z7a S ⊕ Z3n S) := by
            rw [← htwo]
            exact hu
          have hEq : u = u1 := Sum.inl.inj (hu'.symm.trans hu1)
          subst u
          exact hqu1
      | succ k =>
          have hprev_le : 2 * Nat.succ k ≤ r.length := by
            rw [hlen]
            omega
          rcases Z42 r (Nat.succ k) hprev_le with
            ⟨w, hw⟩
          have hprev : q.1.ExtendsBy a w.1 :=
            ih w (by omega) (by omega) hw
          have hmid_raw := r.adj_getVert_succ (i := 2 * Nat.succ k) (by
            rw [hlen]
            omega)
          cases hm : r.getVert (2 * Nat.succ k + 1) with
          | inl z =>
              rw [hw, hm] at hmid_raw
              exact (Z15 hmid_raw).elim
          | inr p =>
              have hmid : (Z3V S).Adj (.inl w) (.inr p) := by
                simpa [hw, hm] using hmid_raw
              have hnext_raw := r.adj_getVert_succ (i := 2 * Nat.succ k + 1) (by
                rw [hlen]
                omega)
              have hindex : 2 * Nat.succ k + 1 + 1 =
                  2 * Nat.succ (Nat.succ k) := by omega
              rw [hindex, hm, hu] at hnext_raw
              have hnext : (Z3V S).Adj (.inr p) (.inl u) :=
                hnext_raw
              apply Node.Z3e hprev
              · apply hmin u
                rw [← hu]
                exact r.getVert_mem_support _
              · intro hqu
                have hne : q ≠ u := Z4q r hr
                  (i := 2 * Nat.succ (Nat.succ k)) (u := u)
                  (by omega) (by rw [hlen]; omega) hu
                exact hne (Subtype.ext hqu)
              · exact Z17.mp hmid
              · exact Z18.mp hnext
theorem Zv
    {S : Set (Edge G)} (_hS : S.Finite)
    (hlinear : ((system G).Z96 S).Linear) :
    (Z3V S).IsAcyclic := by
  classical
  intro v c hc
  rcases Z2X c hc with ⟨q0, hq0⟩
  let Q : Set (Z7a S) :=
    {q | (.inl q : Z7a S ⊕ Z3n S) ∈
      c.support}
  have hQ : Q.Nonempty := by
    refine ⟨q0, ?_⟩
    simpa only [Q, Set.mem_setOf_eq] using hq0
  let q : Z7a S :=
    Function.argminOn (fun q : Z7a S => q.1.length) Q hQ
  have hq : (.inl q : Z7a S ⊕ Z3n S) ∈
      c.support := by
    change q ∈ Q
    exact Function.argminOn_mem _ Q hQ
  have hmin : ∀ u : Z7a S,
      (.inl u : Z7a S ⊕ Z3n S) ∈
        c.support → q.1.length ≤ u.1.length := by
    intro u hu
    dsimp only [q]
    exact Function.argminOn_le
      (fun q : Z7a S => q.1.length) Q hu
  rcases Z3J c hc hq with
    ⟨r, hr, hrsupp, pL, pR, uL, uR, hs, hL, hR, hp,
      hqL, hpLuL, huRpR, hpRq, hpLR, huLq, huRq⟩
  have hminR : ∀ u : Z7a S,
      (.inl u : Z7a S ⊕ Z3n S) ∈
        r.support → q.1.length ≤ u.1.length := by
    intro u hu
    exact hmin u ((hrsupp _).mp hu)
  have hpLq : pL.1 ∈ (system G).Z9z (Zbo S q.1) :=
    Z17.mp hqL
  have hpLuL : pL.1 ∈ (system G).Z9z (Zbo S uL.1) :=
    Z18.mp hpLuL
  have huLmem : (.inl uL : Z7a S ⊕ Z3n S) ∈
      r.support := by
    rw [← hL]
    exact r.getVert_mem_support 2
  have hqlt : q.1.length < uL.1.length := by
    rcases (hminR uL huLmem).eq_or_lt with hEq | hlt
    · exfalso
      apply huLq
      apply Subtype.ext
      exact (Z3d hEq hpLq hpLuL).symm
    · exact hlt
  rcases Z1g hqlt hpLq hpLuL with
    ⟨eL, heL, hpL, hquL⟩
  rcases Z4R r with ⟨n, hlen⟩
  have hn2 : 2 ≤ n := by
    have hthree := hr.three_le_length
    rw [hlen] at hthree
    omega
  have hbranch := Z3U r hr hlen hminR hL hquL
  have hquR : q.1.ExtendsBy (baseLetter eL) uR.1 := by
    apply hbranch (n - 1) uR
    · omega
    · omega
    · have hindex : 2 * (n - 1) = r.length - 2 := by
        rw [hlen]
        omega
      calc
        r.getVert (2 * (n - 1)) = r.getVert (r.length - 2) := by
          rw [hindex]
        _ = .inl uR := hR
  have hpRq' : pR.1 ∈ (system G).Z9z (Zbo S q.1) :=
    Z18.mp hpRq
  have hpRuR : pR.1 ∈ (system G).Z9z (Zbo S uR.1) :=
    Z17.mp huRpR
  rcases Z1g hquR.choose hpRq' hpRuR with
    ⟨eR, heR, hpR, hquR'⟩
  have hletter : baseLetter eL = baseLetter eR :=
    Node.Z2Z hquR hquR'
  have heq : eL = eR :=
    Z2F q.1 hlinear heL heR hletter
  apply hpLR
  apply Subtype.ext
  calc
    pL.1 = baseApex eL := hpL
    _ = baseApex eR := congrArg baseApex heq
    _ = pR.1 := hpR.symm
end SequenceLift
end P593
end
section
namespace SimpleGraph
universe u
variable {V : Type u}
theorem IsAcyclic.exists_vertex_adj_unique
    {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] [Nonempty V]
    (hG : G.IsAcyclic) :
    ∃ q : V, ∀ ⦃u w : V⦄, G.Adj q u → G.Adj q w → u = w := by
  classical
  let x : V := Classical.choice (inferInstance : Nonempty V)
  by_cases hx : G.degree x = 0
  · refine ⟨x, ?_⟩
    intro u w hxu _
    have hpos : 0 < G.degree x := (G.degree_pos_iff_exists_adj x).mpr ⟨u, hxu⟩
    omega
  · have hpos : 0 < G.degree x := Nat.pos_of_ne_zero hx
    obtain ⟨y, hxy⟩ := (G.degree_pos_iff_exists_adj x).mp hpos
    let c : G.ConnectedComponent := G.connectedComponentMk x
    have hxc : x ∈ c := by
      exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := G)
    have hyc : y ∈ c := c.mem_supp_of_adj_mem_supp hxc hxy
    have hne : (⟨x, hxc⟩ : c) ≠ ⟨y, hyc⟩ := by
      intro h
      exact hxy.ne (congrArg Subtype.val h)
    letI : Nontrivial c := ⟨⟨x, hxc⟩, ⟨y, hyc⟩, hne⟩
    obtain ⟨q, hq⟩ := (hG.isTree_connectedComponent c).exists_vert_degree_one_of_nontrivial
    have huniq : ∃! z : c, c.toSimpleGraph.Adj q z :=
      (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mp hq
    refine ⟨q, ?_⟩
    intro u w hqu hqw
    have huc : u ∈ c := c.mem_supp_of_adj_mem_supp q.property hqu
    have hwc : w ∈ c := c.mem_supp_of_adj_mem_supp q.property hqw
    have hqu' : c.toSimpleGraph.Adj q ⟨u, huc⟩ :=
      (c.toSimpleGraph_adj q.property huc).mpr hqu
    have hqw' : c.toSimpleGraph.Adj q ⟨w, hwc⟩ :=
      (c.toSimpleGraph_adj q.property hwc).mpr hqw
    exact congrArg Subtype.val (huniq.unique hqu' hqw')
end SimpleGraph
end
section
namespace SimpleGraph
universe u v
variable {A : Type u} {P : Type v}
def bipartiteIncidenceGraph (r : A → P → Prop) : SimpleGraph (A ⊕ P) :=
  SimpleGraph.fromRel fun x y =>
    match x, y with
    | .inl a, .inr p => r a p
    | _, _ => False
@[simp]
theorem bipartiteIncidenceGraph_adj_inl_inr_iff
    (r : A → P → Prop) (a : A) (p : P) :
    (bipartiteIncidenceGraph r).Adj (.inl a) (.inr p) ↔ r a p := by
  simp [bipartiteIncidenceGraph]
@[simp]
theorem bipartiteIncidenceGraph_adj_inr_inl_iff
    (r : A → P → Prop) (a : A) (p : P) :
    (bipartiteIncidenceGraph r).Adj (.inr p) (.inl a) ↔ r a p := by
  simp [bipartiteIncidenceGraph]
def sharedRightPoints (r : A → P → Prop)
    [Fintype P] [DecidableEq P] [DecidableRel r]
    (t : Finset A) : Finset P :=
  Finset.univ.filter fun p => 2 ≤ (t.filter fun a => r a p).card
def bipartitePruneVertices (r : A → P → Prop)
    [Fintype P] [DecidableEq A] [DecidableEq P] [DecidableRel r]
    (t : Finset A) : Finset (A ⊕ P) :=
  (t.image Sum.inl) ∪ ((sharedRightPoints r t).image Sum.inr)
@[simp]
theorem mem_sharedRightPoints
    (r : A → P → Prop) [Fintype P] [DecidableEq P] [DecidableRel r]
    (t : Finset A) (p : P) :
    p ∈ sharedRightPoints r t ↔ 2 ≤ (t.filter fun a => r a p).card := by
  simp [sharedRightPoints]
@[simp]
theorem mem_bipartitePruneVertices_inl
    (r : A → P → Prop) [Fintype P]
    [DecidableEq A] [DecidableEq P] [DecidableRel r]
    (t : Finset A) (a : A) :
    .inl a ∈ bipartitePruneVertices r t ↔ a ∈ t := by
  simp [bipartitePruneVertices]
@[simp]
theorem mem_bipartitePruneVertices_inr
    (r : A → P → Prop) [Fintype P]
    [DecidableEq A] [DecidableEq P] [DecidableRel r]
    (t : Finset A) (p : P) :
    .inr p ∈ bipartitePruneVertices r t ↔ p ∈ sharedRightPoints r t := by
  simp [bipartitePruneVertices]
def bipartiteTailPointSubsingleton (r : A → P → Prop) : List A → Prop
  | [] => True
  | a :: tail =>
      bipartiteTailPointSubsingleton r tail ∧
        ∀ p p', r a p → r a p' →
          (∃ b ∈ tail, r b p) →
          (∃ c ∈ tail, r c p') → p = p'
theorem IsAcyclic.exists_bipartiteLeftVertex_adj_unique
    (r : A → P → Prop) [Fintype P] [DecidableEq A] [DecidableEq P]
    [DecidableRel r] (hG : (bipartiteIncidenceGraph r).IsAcyclic)
    {t : Finset A} (ht : t.Nonempty) :
    ∃ a ∈ t, ∀ ⦃z w : A ⊕ P⦄,
      z ∈ bipartitePruneVertices r t →
      w ∈ bipartitePruneVertices r t →
      (bipartiteIncidenceGraph r).Adj (.inl a) z →
      (bipartiteIncidenceGraph r).Adj (.inl a) w → z = w := by
  classical
  let s : Finset (A ⊕ P) := bipartitePruneVertices r t
  have hs : s.Nonempty := by
    obtain ⟨a, ha⟩ := ht
    exact ⟨.inl a, (mem_bipartitePruneVertices_inl r t a).mpr ha⟩
  letI : Nonempty s := hs.to_subtype
  obtain ⟨q, hq⟩ :=
    SimpleGraph.IsAcyclic.exists_vertex_adj_unique
      (hG.induce (↑s : Set (A ⊕ P)))
  rcases q with ⟨q, hqmem⟩
  rcases q with a | p
  · have ha : a ∈ t := (mem_bipartitePruneVertices_inl r t a).mp hqmem
    refine ⟨a, ha, ?_⟩
    intro z w hz hw haz haw
    let qa : ↑(↑s : Set (A ⊕ P)) := ⟨.inl a, hqmem⟩
    let z' : ↑(↑s : Set (A ⊕ P)) := ⟨z, hz⟩
    let w' : ↑(↑s : Set (A ⊕ P)) := ⟨w, hw⟩
    have haz' :
        (SimpleGraph.induce (↑s : Set (A ⊕ P))
          (bipartiteIncidenceGraph r)).Adj qa z' := by
      rw [SimpleGraph.induce_adj]
      change (bipartiteIncidenceGraph r).Adj (.inl a) z
      exact haz
    have haw' :
        (SimpleGraph.induce (↑s : Set (A ⊕ P))
          (bipartiteIncidenceGraph r)).Adj qa w' := by
      rw [SimpleGraph.induce_adj]
      change (bipartiteIncidenceGraph r).Adj (.inl a) w
      exact haw
    have heq : z' = w' := hq haz' haw'
    simpa [z', w'] using congrArg Subtype.val heq
  · have hp : p ∈ sharedRightPoints r t :=
      (mem_bipartitePruneVertices_inr r t p).mp hqmem
    have hcard : 2 ≤ (t.filter fun a => r a p).card :=
      (mem_sharedRightPoints r t p).mp hp
    have htwo : 1 < (t.filter fun a => r a p).card := by
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp htwo
    rcases Finset.mem_filter.mp ha with ⟨ha, hap⟩
    rcases Finset.mem_filter.mp hb with ⟨hb, hbp⟩
    have hma : (.inl a : A ⊕ P) ∈ s :=
      (mem_bipartitePruneVertices_inl r t a).mpr ha
    have hmb : (.inl b : A ⊕ P) ∈ s :=
      (mem_bipartitePruneVertices_inl r t b).mpr hb
    let qa : ↑(↑s : Set (A ⊕ P)) := ⟨.inr p, hqmem⟩
    let za : ↑(↑s : Set (A ⊕ P)) := ⟨.inl a, hma⟩
    let zb : ↑(↑s : Set (A ⊕ P)) := ⟨.inl b, hmb⟩
    have hqza :
        (SimpleGraph.induce (↑s : Set (A ⊕ P))
          (bipartiteIncidenceGraph r)).Adj qa za := by
      rw [SimpleGraph.induce_adj]
      change (bipartiteIncidenceGraph r).Adj (.inr p) (.inl a)
      exact (bipartiteIncidenceGraph_adj_inr_inl_iff r a p).mpr hap
    have hqzb :
        (SimpleGraph.induce (↑s : Set (A ⊕ P))
          (bipartiteIncidenceGraph r)).Adj qa zb := by
      rw [SimpleGraph.induce_adj]
      change (bipartiteIncidenceGraph r).Adj (.inr p) (.inl b)
      exact (bipartiteIncidenceGraph_adj_inr_inl_iff r b p).mpr hbp
    have heq : za = zb := hq hqza hqzb
    have heq' : (.inl a : A ⊕ P) = .inl b := by
      simpa [za, zb] using congrArg Subtype.val heq
    exact False.elim (hab (Sum.inl.inj heq'))
theorem IsAcyclic.exists_finset_bipartiteTailPointSubsingletonOrder
    (r : A → P → Prop) [Fintype P] [DecidableEq A] [DecidableEq P]
    [DecidableRel r] (hG : (bipartiteIncidenceGraph r).IsAcyclic)
    (t : Finset A) :
    ∃ l : List A,
      l.Nodup ∧ l.toFinset = t ∧ bipartiteTailPointSubsingleton r l := by
  classical
  induction t using Finset.strongInduction with
  | H t ih =>
    by_cases ht : t.Nonempty
    · obtain ⟨a, ha, hleaf⟩ := hG.exists_bipartiteLeftVertex_adj_unique r ht
      obtain ⟨l, hlnd, hlt, hlcoh⟩ :=
        ih (t.erase a) (Finset.erase_ssubset ha)
      refine ⟨a :: l, ?_, ?_, ?_⟩
      · rw [List.nodup_cons]
        refine ⟨?_, hlnd⟩
        intro hal
        have hae : a ∈ t.erase a := by
          rw [← hlt]
          exact List.mem_toFinset.mpr hal
        exact (Finset.mem_erase.mp hae).1 rfl
      · rw [List.toFinset_cons, hlt, Finset.insert_erase ha]
      · change bipartiteTailPointSubsingleton r l ∧
          ∀ p p', r a p → r a p' →
            (∃ b ∈ l, r b p) →
            (∃ c ∈ l, r c p') → p = p'
        refine ⟨hlcoh, ?_⟩
        intro p p' hap hap' hpt hp't
        rcases hpt with ⟨b, hb, hbp⟩
        rcases hp't with ⟨c, hc, hcp'⟩
        have hbe : b ∈ t.erase a := by
          rw [← hlt]
          exact List.mem_toFinset.mpr hb
        have hce : c ∈ t.erase a := by
          rw [← hlt]
          exact List.mem_toFinset.mpr hc
        have hbT : b ∈ t := (Finset.mem_erase.mp hbe).2
        have hcT : c ∈ t := (Finset.mem_erase.mp hce).2
        have hab : a ≠ b := by
          intro hab
          subst b
          exact (Finset.mem_erase.mp hbe).1 rfl
        have hac : a ≠ c := by
          intro hac
          subst c
          exact (Finset.mem_erase.mp hce).1 rfl
        have hpactive : (.inr p : A ⊕ P) ∈ bipartitePruneVertices r t := by
          rw [mem_bipartitePruneVertices_inr]
          rw [mem_sharedRightPoints]
          have hcard : 1 < (t.filter fun x => r x p).card :=
            Finset.one_lt_card.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hap⟩,
              b, Finset.mem_filter.mpr ⟨hbT, hbp⟩, hab⟩
          omega
        have hp'active : (.inr p' : A ⊕ P) ∈ bipartitePruneVertices r t := by
          rw [mem_bipartitePruneVertices_inr]
          rw [mem_sharedRightPoints]
          have hcard : 1 < (t.filter fun x => r x p').card :=
            Finset.one_lt_card.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hap'⟩,
              c, Finset.mem_filter.mpr ⟨hcT, hcp'⟩, hac⟩
          omega
        exact Sum.inr.inj (hleaf hpactive hp'active
          ((bipartiteIncidenceGraph_adj_inl_inr_iff r a p).mpr hap)
          ((bipartiteIncidenceGraph_adj_inl_inr_iff r a p').mpr hap'))
    · have htempty : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
      subst t
      exact ⟨[], by simp, by simp, trivial⟩
end SimpleGraph
end
section
namespace P593
universe u
namespace SequenceLift
variable {V : Type u} (G : _root_.SimpleGraph V)
noncomputable def baseLetterSubgraph (A : Set (ZbG G)) : G.Subgraph :=
  { verts := {x : V | ∃ a : ZbG G, a ∈ A ∧ x ∈ (a.1 : Sym2 V)}
    Adj := fun x y => s(x, y) ∈ ((fun a : ZbG G => a.1) '' A)
    adj_sub := by
      intro v w h
      rcases h with ⟨a, ha, hEq⟩
      rw [← G.mem_edgeSet, ← hEq]
      exact a.property
    edge_vert := by
      intro v w h
      rcases h with ⟨a, ha, hEq⟩
      exact ⟨a, ha, by simp [hEq]⟩
    symm := ⟨by
      intro v w h
      rcases h with ⟨a, ha, hEq⟩
      refine ⟨a, ha, ?_⟩
      rw [hEq]
      exact Sym2.eq_swap⟩ }
theorem Z4W (A : Set (ZbG G)) :
    (baseLetterSubgraph G A).edgeSet = ((fun a : ZbG G => a.1) '' A) := by
  ext z
  induction z using Sym2.ind with
  | h x y => rfl
theorem Z3M
    {A : Set (ZbG G)} (hA : A.Finite) :
    (baseLetterSubgraph G A).verts.Finite := by
  classical
  rw [show (baseLetterSubgraph G A).verts =
      ⋃ a ∈ A, {x : V | x ∈ (a.1 : Sym2 V)} by
    ext x
    simp [baseLetterSubgraph]]
  apply hA.biUnion
  intro a ha
  rw [show ({x : V | x ∈ (a.1 : Sym2 V)}) = ↑a.1.toFinset by
    ext x
    simp]
  exact Finset.finite_toSet _
noncomputable def baseLetterSubgraphEdgeEquiv (A : Set (ZbG G)) :
    (baseLetterSubgraph G A).coe.edgeSet ≃ A := by
  let K := baseLetterSubgraph G A
  let f : K.coe.edgeSet → A := fun j =>
    let hjK : Sym2.map (fun x : K.verts => (x : V)) j.1 ∈ K.edgeSet := by
      simpa [SimpleGraph.Subgraph.edgeSet_coe] using j.2
    let e0 : ZbG G :=
      ⟨Sym2.map (fun x : K.verts => (x : V)) j.1, K.edgeSet_subset hjK⟩
    ⟨e0, by
      rw [Z4W] at hjK
      rcases hjK with ⟨a, ha, hEq⟩
      rw [show e0 = a by
        apply Subtype.ext
        exact hEq.symm]
      exact ha⟩
  exact Equiv.ofBijective f (by
    constructor
    · intro j k hjk
      apply Subtype.ext
      apply Sym2.map.injective Subtype.val_injective
      simpa [f] using congrArg (fun a : A => a.1.1) hjk
    · intro a
      have hK : a.1.1 ∈ K.edgeSet := by
        rw [Z4W]
        exact ⟨a.1, a.2, rfl⟩
      rw [← SimpleGraph.Subgraph.image_coe_edgeSet_coe K] at hK
      rcases hK with ⟨j, hj, hmap⟩
      refine ⟨⟨j, hj⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      simpa [f] using hmap)
end SequenceLift
end P593
end
section
namespace P593
universe u
namespace SequenceLift
variable {V : Type u} {G : _root_.SimpleGraph V}
noncomputable def baseFiberEquivBaseLetterImage_of_linear
    {S : Set (Edge G)} (q : Node G)
    (hlinear : ((system G).Z96 S).Linear) :
    Zbo S q ≃ (baseLetter '' Zbo S q) :=
  Equiv.ofBijective
    (fun e => ⟨baseLetter e.1, ⟨e.1, e.2, rfl⟩⟩)
    (by
      constructor
      · intro e₁ e₂ h
        apply Subtype.ext
        exact Z2F q hlinear e₁.2 e₂.2
          (congrArg Subtype.val h)
      · rintro ⟨letter, e, he, rfl⟩
        exact ⟨⟨e, he⟩, rfl⟩)
end SequenceLift
end P593
end
section
namespace P593
universe u
namespace SequenceLift
variable {V : Type u} {G : _root_.SimpleGraph V}
noncomputable def baseFiberLetterSubgraphFactor
    (S : Set (Edge G)) (q : Node G) :
    P593.SimpleGraph.NonInducedFactor
      (baseLetterSubgraph G (baseLetter '' Zbo S q)).coe G :=
  P593.SimpleGraph.NonInducedFactor.ofCopy
    (baseLetterSubgraph G (baseLetter '' Zbo S q)).coeCopy
noncomputable def baseFiberLetterSubgraphEdgeEquiv_of_linear
    {S : Set (Edge G)} (q : Node G)
    (hlinear : ((system G).Z96 S).Linear) :
    (baseLetterSubgraph G (baseLetter '' Zbo S q)).coe.edgeSet ≃
      Zbo S q :=
  (baseLetterSubgraphEdgeEquiv G (baseLetter '' Zbo S q)).trans
    (baseFiberEquivBaseLetterImage_of_linear q hlinear).symm
end SequenceLift
end P593
end
section
namespace P593
universe u
namespace SequenceLift
variable {V : Type u} {G : _root_.SimpleGraph V}
private noncomputable def baseFiberExpansionEdgeEquiv_of_linear
    {S : Set (Edge G)} (q : Node G)
    (hlinear : ((system G).Z96 S).Linear) :
    (baseLetterSubgraph G (baseLetter '' Zbo S q)).coe.edgeSet ≃
      Zbo S q :=
  baseFiberLetterSubgraphEdgeEquiv_of_linear q hlinear
private theorem Z2x
    {S : Set (Edge G)} (q : Node G)
    (hlinear : ((system G).Z96 S).Linear)
    (j : (baseLetterSubgraph G (baseLetter '' Zbo S q)).coe.edgeSet) :
    baseLetter ((baseFiberExpansionEdgeEquiv_of_linear q hlinear j).1) =
      (baseLetterSubgraphEdgeEquiv G (baseLetter '' Zbo S q) j).1 := by
  let psi := baseFiberEquivBaseLetterImage_of_linear q hlinear
  let theta := baseLetterSubgraphEdgeEquiv G (baseLetter '' Zbo S q)
  change baseLetter ((psi.symm (theta j)).1) = (theta j).1
  exact congrArg Subtype.val (psi.apply_symm_apply (theta j))
private theorem Z21
    {S : Set (Edge G)} (q : Node G)
    (hlinear : ((system G).Z96 S).Linear)
    (x : (baseLetterSubgraph G (baseLetter '' Zbo S q)).verts)
    (j : (baseLetterSubgraph G (baseLetter '' Zbo S q)).coe.edgeSet) :
    x ∈ (j.1 : Sym2 (baseLetterSubgraph G (baseLetter '' Zbo S q)).verts) ↔
      (x : V) ∈
        (baseLetter ((baseFiberExpansionEdgeEquiv_of_linear q hlinear j).1)).1 := by
  rw [Z2x q hlinear j]
  change x ∈ j.1 ↔ (x : V) ∈
    Sym2.map (fun y : (baseLetterSubgraph G (baseLetter '' Zbo S q)).verts =>
      (y : V)) j.1
  constructor
  · intro hx
    exact Sym2.mem_map.mpr ⟨x, hx, rfl⟩
  · intro hx
    rcases Sym2.mem_map.mp hx with ⟨y, hy, hxy⟩
    have hxy' : x = y := Subtype.ext hxy.symm
    simpa [hxy'] using hy
private noncomputable def baseFiberExpansionPointEquiv_of_linear
    {S : Set (Edge G)} (q : Node G)
    (hlinear : ((system G).Z96 S).Linear) :
    TripleSystem.PrivateVertexExpansion.Point
      (baseLetterSubgraph G (baseLetter '' Zbo S q)).coe ≃
      (system G).ZaR (Zbo S q) := by
  classical
  let K := baseLetterSubgraph G (baseLetter '' Zbo S q)
  let edgeEquiv : K.coe.edgeSet ≃ Zbo S q :=
    baseFiberExpansionEdgeEquiv_of_linear q hlinear
  let f : TripleSystem.PrivateVertexExpansion.Point K.coe →
      (system G).ZaR (Zbo S q) := fun p =>
    match p with
    | .inl x =>
        ⟨(q, (x : V)), by
          rcases x.2 with ⟨a, ha, hx⟩
          rcases ha with ⟨e, he, hletter⟩
          refine ⟨e, he,
            (Z28 G e (q, (x : V))).2 (Or.inl ?_)⟩
          constructor
          · exact he.2.symm
          · simpa [hletter] using hx⟩
    | .inr j =>
        let e := edgeEquiv j
        ⟨baseApex e.1, ⟨e.1, e.2, ZaI e.1⟩⟩
  exact Equiv.ofBijective f (by
    constructor
    · intro a b hab
      rcases a with x | j <;> rcases b with y | k
      · apply congrArg Sum.inl
        apply Subtype.ext
        exact congrArg (fun z => z.2) (congrArg Subtype.val hab)
      · exfalso
        have hnode := congrArg (fun z => z.1) (congrArg Subtype.val hab)
        change q = (baseApex (edgeEquiv k).1).1 at hnode
        exact Z5c (edgeEquiv k).1
          (hnode.symm.trans (edgeEquiv k).2.2.symm)
      · exfalso
        have hnode := congrArg (fun z => z.1) (congrArg Subtype.val hab)
        change (baseApex (edgeEquiv j).1).1 = q at hnode
        exact Z5c (edgeEquiv j).1
          (hnode.trans (edgeEquiv j).2.2.symm)
      · apply congrArg Sum.inr
        apply edgeEquiv.injective
        apply Subtype.ext
        apply Z35 q hlinear (edgeEquiv j).2 (edgeEquiv k).2
        exact congrArg Subtype.val hab
    · intro p
      rcases p with ⟨p, hp⟩
      change (∃ e : Edge G, e ∈ Zbo S q ∧ (system G).Inc p e) at hp
      rcases hp with ⟨e, he, hInc⟩
      rcases (Z28 G e p).1 hInc with hcore | hapex
      · let x : K.verts := ⟨p.2, ⟨baseLetter e, ⟨e, he, rfl⟩, hcore.2⟩⟩
        refine ⟨.inl x, ?_⟩
        apply Subtype.ext
        exact Prod.ext (hcore.1.trans he.2).symm rfl
      · let j : K.coe.edgeSet := edgeEquiv.symm ⟨e, he⟩
        refine ⟨.inr j, ?_⟩
        apply Subtype.ext
        change baseApex (edgeEquiv j).1 = p
        rw [show edgeEquiv j = ⟨e, he⟩ by simp [j]]
        exact hapex.symm)
noncomputable def baseFiber_privateVertexExpansionIso_of_linear
    {S : Set (Edge G)} (q : Node G)
    (hlinear : ((system G).Z96 S).Linear) :
    TripleSystem.Iso
      (TripleSystem.Z64
        (baseLetterSubgraph G (baseLetter '' Zbo S q)).coe)
      ((system G).Z96 (Zbo S q)) where
  vertexEquiv := baseFiberExpansionPointEquiv_of_linear q hlinear
  edgeEquiv := baseFiberExpansionEdgeEquiv_of_linear q hlinear
  map_inc_iff := by
    intro p j
    rcases p with x | k
    · change x ∈ (j.1 : Sym2 (baseLetterSubgraph G (baseLetter '' Zbo S q)).verts) ↔
        (system G).Inc (q, (x : V))
          ((baseFiberExpansionEdgeEquiv_of_linear q hlinear j).1)
      constructor
      · intro hx
        apply (Z28 G
          ((baseFiberExpansionEdgeEquiv_of_linear q hlinear j).1) (q, (x : V))).2
        exact Or.inl ⟨(baseFiberExpansionEdgeEquiv_of_linear q hlinear j).2.2.symm,
          (Z21 q hlinear x j).1 hx⟩
      · intro hInc
        rcases (Z28 G
          ((baseFiberExpansionEdgeEquiv_of_linear q hlinear j).1) (q, (x : V))).1 hInc with
          hcore | hapex
        · exact (Z21 q hlinear x j).2 hcore.2
        · exfalso
          have hnode := congrArg Prod.fst hapex
          exact Z5c
            ((baseFiberExpansionEdgeEquiv_of_linear q hlinear j).1)
            (hnode.symm.trans
              (baseFiberExpansionEdgeEquiv_of_linear q hlinear j).2.2.symm)
    · change k = j ↔
        (system G).Inc
          (baseApex ((baseFiberExpansionEdgeEquiv_of_linear q hlinear k).1))
          ((baseFiberExpansionEdgeEquiv_of_linear q hlinear j).1)
      rw [Z4c q hlinear
        (baseFiberExpansionEdgeEquiv_of_linear q hlinear k).2
        (baseFiberExpansionEdgeEquiv_of_linear q hlinear j).2]
      constructor
      · intro h
        simp [h]
      · intro h
        apply (baseFiberExpansionEdgeEquiv_of_linear q hlinear).injective
        apply Subtype.ext
        exact h
theorem Zb
    {S : Set (Edge G)} (hS : S.Finite) (q : Node G)
    (hlinear : ((system G).Z96 S).Linear) :
    Exists (fun _ : Fintype
      (baseLetterSubgraph G (baseLetter '' Zbo S q)).verts =>
      And
        (Nonempty (P593.SimpleGraph.NonInducedFactor
          (baseLetterSubgraph G (baseLetter '' Zbo S q)).coe G))
        (Nonempty (TripleSystem.Iso
          (TripleSystem.Z64
            (baseLetterSubgraph G (baseLetter '' Zbo S q)).coe)
          ((system G).Z96 (Zbo S q))))) := by
  classical
  letI : Finite (baseLetterSubgraph G (baseLetter '' Zbo S q)).verts :=
    Set.finite_coe_iff.mpr <|
      Z3M G <|
        (hS.subset (Z8O S q)).image baseLetter
  letI : Fintype (baseLetterSubgraph G (baseLetter '' Zbo S q)).verts :=
    Fintype.ofFinite _
  apply Exists.intro (inferInstance : Fintype
    (baseLetterSubgraph G (baseLetter '' Zbo S q)).verts)
  exact And.intro
    (Nonempty.intro (baseFiberLetterSubgraphFactor S q))
    (Nonempty.intro (baseFiber_privateVertexExpansionIso_of_linear q hlinear))
end SequenceLift
end P593
end
section
namespace P593
universe u
abbrev Z7c (n : ℕ) := ULift.{u} (Fin n)
abbrev Z7b (n : ℕ) :
    _root_.SimpleGraph
      (Z7c.{u} n ⊕ Z7c.{u} n) :=
  _root_.completeBipartiteGraph
    (Z7c.{u} n) (Z7c.{u} n)
end P593
end
section
namespace P593
universe u v
namespace TripleSystem
structure ThirdVertexWitness {W : Type u} {D : Type v}
    (H : TripleSystem W D) (x y z : W) where
  edge : D
  edgeSet_eq : H.edgeSet edge = {x, y, z}
private theorem Z31
    {W : Type u} {x y z : W} (hdup : x = y ∨ x = z ∨ y = z) :
    ({x, y, z} : Set W).ncard < 3 := by
  rcases hdup with hxy | hxz | hyz
  · subst y
    have hle : ({x, x, z} : Set W).ncard ≤ 2 := by
      calc
        ({x, x, z} : Set W).ncard = ({x, z} : Set W).ncard := by simp
        _ ≤ ({z} : Set W).ncard + 1 := Set.ncard_insert_le x {z}
        _ = 2 := by simp
    exact Nat.lt_succ_iff.mpr hle
  · subst z
    have hle : ({x, y, x} : Set W).ncard ≤ 2 := by
      calc
        ({x, y, x} : Set W).ncard = ({y, x} : Set W).ncard := by simp
        _ = ({x, y} : Set W).ncard := by rw [Set.pair_comm y x]
        _ ≤ ({y} : Set W).ncard + 1 := Set.ncard_insert_le x {y}
        _ = 2 := by simp
    exact Nat.lt_succ_iff.mpr hle
  · subst z
    have hle : ({x, y, y} : Set W).ncard ≤ 2 := by
      calc
        ({x, y, y} : Set W).ncard = ({x, y} : Set W).ncard := by simp
        _ ≤ ({y} : Set W).ncard + 1 := Set.ncard_insert_le x {y}
        _ = 2 := by simp
    exact Nat.lt_succ_iff.mpr hle
theorem Z3G
    {W : Type u} {D : Type v} {H : TripleSystem W D} {e : D} {x y z : W}
    (he : H.edgeSet e = {x, y, z}) : x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  have hcard : ({x, y, z} : Set W).ncard = 3 := by
    rw [← he]
    exact H.Zaa e
  constructor
  · intro hxy
    exact (Nat.ne_of_lt
      (Z31 (Or.inl hxy))) hcard
  constructor
  · intro hxz
    exact (Nat.ne_of_lt
      (Z31 (Or.inr (Or.inl hxz)))) hcard
  · intro hyz
    exact (Nat.ne_of_lt
      (Z31 (Or.inr (Or.inr hyz)))) hcard
namespace ThirdVertexWitness
variable {W : Type u} {D : Type v} {H : TripleSystem W D} {x y : W}
def swap {z : W} (p : ThirdVertexWitness H x y z) :
    ThirdVertexWitness H y x z where
  edge := p.edge
  edgeSet_eq := p.edgeSet_eq.trans (Set.insert_comm x y {z})
def rotate {z : W} (p : ThirdVertexWitness H x y z) :
    ThirdVertexWitness H x z y where
  edge := p.edge
  edgeSet_eq := p.edgeSet_eq.trans
    (congrArg (Set.insert x) (Set.pair_comm y z))
theorem Zae {z : W} (p : ThirdVertexWitness H x y z) : x ≠ y :=
  (Z3G p.edgeSet_eq).1
end ThirdVertexWitness
structure PairCodegreeWitness {W : Type u} {D : Type v}
    (H : TripleSystem W D) (x y : W) (t : Nat) where
  third : Fin t ↪ W
  edge : Fin t → D
  edgeSet_eq : ∀ k, H.edgeSet (edge k) = {x, y, third k}
def Z66 (H : TripleSystem W D) (x y : W) (t : Nat) : Prop :=
  Nonempty (PairCodegreeWitness H x y t)
namespace PairCodegreeWitness
variable {W : Type u} {D : Type v} {H : TripleSystem W D}
  {x y : W} {t : Nat}
def ZaM (p : PairCodegreeWitness H x y t) (k : Fin t) :
    ThirdVertexWitness H x y (p.third k) where
  edge := p.edge k
  edgeSet_eq := p.edgeSet_eq k
def Z69 (third : Fin t ↪ W)
    (witness : ∀ k, ThirdVertexWitness H x y (third k)) :
    PairCodegreeWitness H x y t where
  third := third
  edge := fun k => (witness k).edge
  edgeSet_eq := fun k => (witness k).edgeSet_eq
def swap (p : PairCodegreeWitness H x y t) : PairCodegreeWitness H y x t where
  third := p.third
  edge := p.edge
  edgeSet_eq k := (p.edgeSet_eq k).trans (Set.insert_comm x y {p.third k})
theorem Zaq (p : PairCodegreeWitness H x y t) (ht : 0 < t) : x ≠ y :=
  ThirdVertexWitness.Zae (ZaM p ⟨0, ht⟩)
end PairCodegreeWitness
theorem Z4A {W : Type u} {D : Type v}
    (H : TripleSystem W D) (x y : W) (t : Nat) :
    Z66 H x y t ↔ Z66 H y x t := by
  constructor
  · rintro ⟨p⟩
    exact ⟨p.swap⟩
  · rintro ⟨p⟩
    exact ⟨p.swap⟩
end TripleSystem
end P593
end
section
namespace P593
universe u
namespace CompleteBipartiteEdges
abbrev Part (n : Nat) := Z7c.{u} n
abbrev Graph (n : Nat) := Z7b.{u} n
def edge (n : Nat) (a b : Part n) : (Graph n).edgeSet :=
  ⟨s(Sum.inl a, Sum.inr b), by simp [Graph, Z7b]⟩
noncomputable def coords (n : Nat) (e : (Graph n).edgeSet) : Part n × Part n := by
  classical
  let eVal : Sym2 (Part n ⊕ Part n) := e.1
  have he : eVal ∈ (_root_.completeBipartiteGraph (Part n) (Part n)).edgeSet := by
    exact e.2
  rw [SimpleGraph.edgeSet_completeBipartiteGraph] at he
  exact Classical.choose he
theorem ZaX (n : Nat) (e : (Graph n).edgeSet) :
    s(Sum.inl (coords n e).1, Sum.inr (coords n e).2) = e.1 := by
  classical
  let eVal : Sym2 (Part n ⊕ Part n) := e.1
  have he : eVal ∈ Set.range
      (fun x : Part n × Part n => s(Sum.inl x.1, Sum.inr x.2)) := by
    have he' : eVal ∈ (_root_.completeBipartiteGraph (Part n) (Part n)).edgeSet := by
      exact e.2
    rw [SimpleGraph.edgeSet_completeBipartiteGraph] at he'
    exact he'
  change s(Sum.inl (coords n e).1, Sum.inr (coords n e).2) = eVal
  unfold coords
  exact Classical.choose_spec he
theorem ZaZ (n : Nat) (e : (Graph n).edgeSet) :
    edge n (coords n e).1 (coords n e).2 = e := by
  apply Subtype.ext
  exact ZaX n e
theorem Z8S (n : Nat) : Function.Injective (coords n) := by
  intro e f hef
  apply Subtype.ext
  calc
    e.1 = s(Sum.inl (coords n e).1, Sum.inr (coords n e).2) :=
      (ZaX n e).symm
    _ = s(Sum.inl (coords n f).1, Sum.inr (coords n f).2) := by rw [hef]
    _ = f.1 := ZaX n f
theorem Z9W (n : Nat) :
    Function.Injective (fun ab : Part n × Part n => edge n ab.1 ab.2) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h' := congrArg Subtype.val h
  rcases Sym2.eq_iff.mp h' with h' | h'
  · exact Prod.ext (Sum.inl.inj h'.1) (Sum.inr.inj h'.2)
  · simp at h'
theorem Zb0 (n : Nat) (a b : Part n) :
    coords n (edge n a b) = (a, b) := by
  apply Z9W n
  change edge n (coords n (edge n a b)).1 (coords n (edge n a b)).2 =
    edge n a b
  exact ZaZ n (edge n a b)
end CompleteBipartiteEdges
end P593
end
section
open Function
namespace P593
namespace RainbowBipartite
universe u
namespace Counting
universe v w
theorem Z3w
    {Omega : Type v} {Iota : Type w} [Fintype Omega] [Fintype Iota]
    (bad : Iota → Omega → Prop) [∀ i, DecidablePred (bad i)]
    (bound : ℕ)
    (hbad : ∀ i, Fintype.card {sample : Omega // bad i sample} ≤ bound)
    (hsmall : Fintype.card Iota * bound < Fintype.card Omega) :
    ∃ sample : Omega, ∀ i, ¬ bad i sample := by
  classical
  by_contra hcover
  push Not at hcover
  let forget : (Σ i, {sample : Omega // bad i sample}) → Omega := fun z ↦ z.2.1
  have hsurj : Function.Surjective forget := by
    intro sample
    obtain ⟨i, hi⟩ := hcover sample
    exact ⟨⟨i, ⟨sample, hi⟩⟩, rfl⟩
  have hcard : Fintype.card Omega ≤ Fintype.card (Σ i, {sample : Omega // bad i sample}) :=
    Fintype.card_le_of_surjective forget hsurj
  have hlt : Fintype.card Omega < Fintype.card Omega := by
    calc
      Fintype.card Omega
          ≤ Fintype.card (Σ i, {sample : Omega // bad i sample}) := hcard
      _ = ∑ i, Fintype.card {sample : Omega // bad i sample} := Fintype.card_sigma
      _ ≤ ∑ _i : Iota, bound := by
        gcongr with i
        exact hbad i
      _ = Fintype.card Iota * bound := by simp
      _ < Fintype.card Omega := hsmall
  exact (Nat.lt_irrefl _ hlt)
theorem Z2Y
    {Iota : Type v} {Alpha : Type w} [Fintype Iota] [DecidableEq Iota]
    [Fintype Alpha] (k : Iota) (P : (Iota → Alpha) → Prop) [DecidablePred P]
    (d : ℕ)
    (hfiber : ∀ rest : ({j : Iota // j ≠ k} → Alpha),
      Fintype.card {a : Alpha // P ((Equiv.funSplitAt k Alpha).symm (a, rest))} ≤ d) :
    Fintype.card {f : Iota → Alpha // P f} ≤
      d * Fintype.card Alpha ^ (Fintype.card Iota - 1) := by
  classical
  let R := ({j : Iota // j ≠ k} → Alpha)
  let split : (Iota → Alpha) ≃ R × Alpha :=
    (Equiv.funSplitAt k Alpha).trans (Equiv.prodComm Alpha R)
  let p : R → Alpha → Prop := fun rest a ↦ P (split.symm (rest, a))
  let eventEquiv : {f : Iota → Alpha // P f} ≃ {z : R × Alpha // p z.1 z.2} :=
    split.subtypeEquiv (by
      intro f
      simp [p])
  have hremaining : Fintype.card {j : Iota // j ≠ k} = Fintype.card Iota - 1 := by
    simp
  calc
    Fintype.card {f : Iota → Alpha // P f}
        = Fintype.card {z : R × Alpha // p z.1 z.2} :=
          Fintype.card_congr eventEquiv
    _ = Fintype.card (Σ rest : R, {a : Alpha // p rest a}) :=
      Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype p)
    _ = ∑ rest : R, Fintype.card {a : Alpha // p rest a} := Fintype.card_sigma
    _ ≤ ∑ _rest : R, d := by
      gcongr with rest
      have heq :
          Fintype.card {a : Alpha // p rest a} =
            Fintype.card {a : Alpha //
              P ((Equiv.funSplitAt k Alpha).symm (a, rest))} := by
        apply Fintype.card_congr
        apply Equiv.subtypeEquivRight
        intro a
        rfl
      exact heq.trans_le (hfiber rest)
    _ = Fintype.card R * d := by simp
    _ = d * Fintype.card Alpha ^ (Fintype.card Iota - 1) := by
      simp [R, hremaining, Nat.mul_comm]
end Counting
def Z9E {q : ℕ} {Gamma : Type u} (t : ℕ)
    (color : Fin q → Fin q → Gamma) : Prop :=
  (∀ x a, Nat.card {y : Fin q // color x y = a} < t) ∧
    (∀ y a, Nat.card {x : Fin q // color x y = a} < t)
def Zbv {n q : ℕ} {Gamma : Type u} (color : Fin q → Fin q → Gamma)
    (left : Fin n ↪ Fin q) (right : Fin n ↪ Fin q) : Prop :=
  Injective fun ij : Fin n × Fin n ↦ color (left ij.1) (right ij.2)
private abbrev Zba (n : ℕ) := Fin n ⊕ Fin n
private abbrev ZaE (n : ℕ) := Fin n × Fin n
private abbrev ZbL (n : ℕ) :=
  ZaE n ⊕ (ZaE n ⊕ (ZaE n × ZaE n))
private def Bad {n q : ℕ} {Gamma : Type u} (color : Fin q → Fin q → Gamma) :
    ZbL n → (Zba n → Fin q) → Prop
  | Sum.inl (i, i'), sample =>
      i ≠ i' ∧ sample (Sum.inl i) = sample (Sum.inl i')
  | Sum.inr (Sum.inl (j, j')), sample =>
      j ≠ j' ∧ sample (Sum.inr j) = sample (Sum.inr j')
  | Sum.inr (Sum.inr (e, e')), sample =>
      e ≠ e' ∧
        color (sample (Sum.inl e.1)) (sample (Sum.inr e.2)) =
          color (sample (Sum.inl e'.1)) (sample (Sum.inr e'.2))
private theorem Z4V
    {Iota Alpha : Type*} [DecidableEq Iota] (k : Iota) (a : Alpha)
    (rest : {j : Iota // j ≠ k} → Alpha) :
    (Equiv.funSplitAt k Alpha).symm (a, rest) k = a := by
  simp [Equiv.funSplitAt_symm_apply]
private theorem Z4x
    {Iota Alpha : Type*} [DecidableEq Iota] (k j : Iota) (hjk : j ≠ k)
    (a : Alpha) (rest : {j : Iota // j ≠ k} → Alpha) :
    (Equiv.funSplitAt k Alpha).symm (a, rest) j = rest ⟨j, hjk⟩ := by
  simp [Equiv.funSplitAt_symm_apply, hjk]
theorem Z34 (n t : ℕ) (hn : 0 < n) (ht : 0 < t) :
    ∃ q : ℕ, ∀ (Gamma : Type u) (color : Fin q → Fin q → Gamma),
      Z9E t color →
        ∃ (left : Fin n ↪ Fin q) (right : Fin n ↪ Fin q),
          Zbv color left right := by
  classical
  let q := Fintype.card (ZbL n) * t + 1
  refine ⟨q, ?_⟩
  intro Gamma color hlocal
  have hq : 0 < q := by simp [q]
  have hbad : ∀ index : ZbL n,
      Fintype.card {sample : Zba n → Fin q // Bad color index sample} ≤
        t * q ^ (Fintype.card (Zba n) - 1) := by
    intro index
    rcases index with leftIndex | rightOrColor
    · rcases leftIndex with ⟨i, i'⟩
      by_cases hii : i = i'
      · simp [Bad, hii]
      · have hcount := Counting.Z2Y
          (Iota := Zba n) (Alpha := Fin q)
          (k := Sum.inl i') (P := Bad color (Sum.inl (i, i'))) t (by
            intro rest
            have hne : (Sum.inl i : Zba n) ≠ Sum.inl i' := by simp [hii]
            have hpred : ∀ a : Fin q,
                Bad color (Sum.inl (i, i'))
                    ((Equiv.funSplitAt (Sum.inl i') (Fin q)).symm (a, rest)) ↔
                  rest ⟨Sum.inl i, hne⟩ = a := by
              intro a
              simp only [Bad]
              rw [Z4x _ _ hne,
                Z4V]
              simp [hii]
            calc
              Fintype.card {a : Fin q //
                  Bad color (Sum.inl (i, i'))
                    ((Equiv.funSplitAt (Sum.inl i') (Fin q)).symm (a, rest))} =
                  Fintype.card {a : Fin q // rest ⟨Sum.inl i, hne⟩ = a} :=
                Fintype.card_congr (Equiv.subtypeEquivRight hpred)
              _ = 1 := by simp
              _ ≤ t := by omega)
        simpa using hcount
    · rcases rightOrColor with rightIndex | colorIndex
      · rcases rightIndex with ⟨j, j'⟩
        by_cases hjj : j = j'
        · simp [Bad, hjj]
        · have hcount := Counting.Z2Y
            (Iota := Zba n) (Alpha := Fin q)
            (k := Sum.inr j') (P := Bad color (Sum.inr (Sum.inl (j, j')))) t (by
              intro rest
              have hne : (Sum.inr j : Zba n) ≠ Sum.inr j' := by simp [hjj]
              have hpred : ∀ a : Fin q,
                  Bad color (Sum.inr (Sum.inl (j, j')))
                      ((Equiv.funSplitAt (Sum.inr j') (Fin q)).symm (a, rest)) ↔
                    rest ⟨Sum.inr j, hne⟩ = a := by
                intro a
                simp only [Bad]
                rw [Z4x _ _ hne,
                  Z4V]
                simp [hjj]
              calc
                Fintype.card {a : Fin q //
                    Bad color (Sum.inr (Sum.inl (j, j')))
                      ((Equiv.funSplitAt (Sum.inr j') (Fin q)).symm (a, rest))} =
                    Fintype.card {a : Fin q // rest ⟨Sum.inr j, hne⟩ = a} :=
                  Fintype.card_congr (Equiv.subtypeEquivRight hpred)
                _ = 1 := by simp
                _ ≤ t := by omega)
          simpa using hcount
      · rcases colorIndex with ⟨e, e'⟩
        by_cases heq : e = e'
        · simp [Bad, heq]
        · by_cases hright : e.2 = e'.2
          · have hleft : e.1 ≠ e'.1 := by
              intro h
              apply heq
              exact Prod.ext h hright
            have hcount := Counting.Z2Y
              (Iota := Zba n) (Alpha := Fin q)
              (k := Sum.inl e'.1)
              (P := Bad color (Sum.inr (Sum.inr (e, e')))) t (by
                intro rest
                have hL : (Sum.inl e.1 : Zba n) ≠ Sum.inl e'.1 := by
                  simp [hleft]
                have hR : (Sum.inr e.2 : Zba n) ≠ Sum.inl e'.1 := by simp
                have hR' : (Sum.inr e'.2 : Zba n) ≠ Sum.inl e'.1 := by simp
                let x : Fin q := rest ⟨Sum.inl e.1, hL⟩
                let y : Fin q := rest ⟨Sum.inr e.2, hR⟩
                let target : Gamma := color x y
                have hy : rest ⟨Sum.inr e'.2, hR'⟩ = y := by
                  dsimp only [y]
                  congr 1
                  apply Subtype.ext
                  simp [hright]
                have hpred : ∀ a : Fin q,
                    Bad color (Sum.inr (Sum.inr (e, e')))
                        ((Equiv.funSplitAt (Sum.inl e'.1) (Fin q)).symm (a, rest)) ↔
                      color a y = target := by
                  intro a
                  simp only [Bad]
                  rw [Z4x _ _ hL,
                    Z4x _ _ hR,
                    Z4V,
                    Z4x _ _ hR', hy]
                  simp only [x, y, target, eq_comm]
                  exact and_iff_right heq
                have hlocalCard :
                    Fintype.card {a : Fin q // color a y = target} < t := by
                  simpa only [Nat.card_eq_fintype_card] using hlocal.2 y target
                calc
                  Fintype.card {a : Fin q //
                      Bad color (Sum.inr (Sum.inr (e, e')))
                        ((Equiv.funSplitAt (Sum.inl e'.1) (Fin q)).symm (a, rest))} =
                      Fintype.card {a : Fin q // color a y = target} :=
                    Fintype.card_congr (Equiv.subtypeEquivRight hpred)
                  _ ≤ t := hlocalCard.le)
            simpa using hcount
          · have hcount := Counting.Z2Y
              (Iota := Zba n) (Alpha := Fin q)
              (k := Sum.inr e'.2)
              (P := Bad color (Sum.inr (Sum.inr (e, e')))) t (by
                intro rest
                have hL : (Sum.inl e.1 : Zba n) ≠ Sum.inr e'.2 := by simp
                have hL' : (Sum.inl e'.1 : Zba n) ≠ Sum.inr e'.2 := by simp
                have hR : (Sum.inr e.2 : Zba n) ≠ Sum.inr e'.2 := by
                  simp [hright]
                let x : Fin q := rest ⟨Sum.inl e.1, hL⟩
                let x' : Fin q := rest ⟨Sum.inl e'.1, hL'⟩
                let y : Fin q := rest ⟨Sum.inr e.2, hR⟩
                let target : Gamma := color x y
                have hpred : ∀ a : Fin q,
                    Bad color (Sum.inr (Sum.inr (e, e')))
                        ((Equiv.funSplitAt (Sum.inr e'.2) (Fin q)).symm (a, rest)) ↔
                      color x' a = target := by
                  intro a
                  simp only [Bad]
                  rw [Z4x _ _ hL,
                    Z4x _ _ hR,
                    Z4x _ _ hL',
                    Z4V]
                  simp only [x, x', y, target, eq_comm]
                  exact and_iff_right heq
                have hlocalCard :
                    Fintype.card {a : Fin q // color x' a = target} < t := by
                  simpa only [Nat.card_eq_fintype_card] using hlocal.1 x' target
                calc
                  Fintype.card {a : Fin q //
                      Bad color (Sum.inr (Sum.inr (e, e')))
                        ((Equiv.funSplitAt (Sum.inr e'.2) (Fin q)).symm (a, rest))} =
                      Fintype.card {a : Fin q // color x' a = target} :=
                    Fintype.card_congr (Equiv.subtypeEquivRight hpred)
                  _ ≤ t := hlocalCard.le)
            simpa using hcount
  have hcoord : 0 < Fintype.card (Zba n) :=
    Fintype.card_pos_iff.mpr ⟨Sum.inl ⟨0, hn⟩⟩
  have hsmall :
      Fintype.card (ZbL n) *
          (t * q ^ (Fintype.card (Zba n) - 1)) <
        Fintype.card (Zba n → Fin q) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    have hcoeff : Fintype.card (ZbL n) * t < q := by simp [q]
    have hmul :
        (Fintype.card (ZbL n) * t) *
            q ^ (Fintype.card (Zba n) - 1) <
          q * q ^ (Fintype.card (Zba n) - 1) := by
      exact Nat.mul_lt_mul_of_pos_right hcoeff (pow_pos hq _)
    calc
      Fintype.card (ZbL n) *
          (t * q ^ (Fintype.card (Zba n) - 1)) =
        (Fintype.card (ZbL n) * t) *
          q ^ (Fintype.card (Zba n) - 1) := by ring
      _ < q * q ^ (Fintype.card (Zba n) - 1) := hmul
      _ = q ^ (Fintype.card (Zba n) - 1 + 1) := by
        rw [pow_succ]
        ring
      _ = q ^ Fintype.card (Zba n) := by
        have hcard : Fintype.card (Zba n) - 1 + 1 =
            Fintype.card (Zba n) := by omega
        rw [hcard]
  obtain ⟨sample, hsample⟩ :=
    Counting.Z3w
      (bad := Bad color)
      (bound := t * q ^ (Fintype.card (Zba n) - 1)) hbad hsmall
  have hleftInjective : Injective (fun i : Fin n ↦ sample (Sum.inl i)) := by
    intro i i' hii
    by_contra hne
    exact hsample (Sum.inl (i, i')) ⟨hne, hii⟩
  have hrightInjective : Injective (fun j : Fin n ↦ sample (Sum.inr j)) := by
    intro j j' hjj
    by_contra hne
    exact hsample (Sum.inr (Sum.inl (j, j'))) ⟨hne, hjj⟩
  let left : Fin n ↪ Fin q := ⟨fun i ↦ sample (Sum.inl i), hleftInjective⟩
  let right : Fin n ↪ Fin q := ⟨fun j ↦ sample (Sum.inr j), hrightInjective⟩
  refine ⟨left, right, ?_⟩
  intro e e' he
  by_contra hne
  exact hsample (Sum.inr (Sum.inr (e, e'))) ⟨hne, he⟩
end RainbowBipartite
end P593
end
section
namespace P593
universe u v
namespace TripleSystem
structure WitnessedBipartiteMatrix {W : Type u} {D : Type v}
    (H : TripleSystem W D) (q t : Nat) where
  left : Fin q ↪ W
  right : Fin q ↪ W
  apex : Fin q → Fin q → W
  edge : Fin q → Fin q → D
  core_disjoint : ∀ i j, left i ≠ right j
  apex_ne_left : ∀ i j k, apex i j ≠ left k
  apex_ne_right : ∀ i j k, apex i j ≠ right k
  edgeSet_eq : ∀ i j,
    H.edgeSet (edge i j) = {left i, right j, apex i j}
  locallyBounded : RainbowBipartite.Z9E t apex
def WitnessedBipartiteMatrix.Z6k
    {W : Type u} {D : Type v} {H : TripleSystem W D} {q t : Nat}
    (left right : Fin q ↪ W) (apex : Fin q → Fin q → W)
    (cell : ∀ i j, ThirdVertexWitness H (left i) (right j) (apex i j))
    (core_disjoint : ∀ i j, left i ≠ right j)
    (apex_ne_left : ∀ i j k, apex i j ≠ left k)
    (apex_ne_right : ∀ i j k, apex i j ≠ right k)
    (locallyBounded : RainbowBipartite.Z9E t apex) :
    WitnessedBipartiteMatrix H q t where
  left := left
  right := right
  apex := apex
  edge := fun i j => (cell i j).edge
  core_disjoint := core_disjoint
  apex_ne_left := apex_ne_left
  apex_ne_right := apex_ne_right
  edgeSet_eq := fun i j => (cell i j).edgeSet_eq
  locallyBounded := locallyBounded
noncomputable def WitnessedBipartiteMatrix.rainbowEmbedding
    {W : Type u} {D : Type v} {H : TripleSystem W D} {n q t : Nat}
    (M : WitnessedBipartiteMatrix H q t)
    (row column : Fin n ↪ Fin q)
    (hrainbow : RainbowBipartite.Zbv M.apex row column) :
    (Z64 (Z7b.{u} n)).Embedding H := by
  let G := Z7b.{u} n
  let vertexMap : PrivateVertexExpansion.Point G → W
    | .inl (.inl a) => M.left (row a.down)
    | .inl (.inr b) => M.right (column b.down)
    | .inr e => M.apex (row (CompleteBipartiteEdges.coords n e).1.down)
        (column (CompleteBipartiteEdges.coords n e).2.down)
  let edgeMap : G.edgeSet → D := fun e =>
    M.edge (row (CompleteBipartiteEdges.coords n e).1.down)
      (column (CompleteBipartiteEdges.coords n e).2.down)
  have hvertexMap : Function.Injective vertexMap := by
    intro p q hpq
    rcases p with p | e <;> rcases q with q | f
    · rcases p with a | b <;> rcases q with c | d
      · have h : row a.down = row c.down := M.left.injective (by
          simpa [vertexMap] using hpq)
        have hac : a.down = c.down := row.injective h
        have hac' : a = c := ULift.ext a c hac
        exact congrArg (fun z => Sum.inl (Sum.inl z)) hac'
      · exfalso
        exact M.core_disjoint (row a.down) (column d.down) (by
          simpa [vertexMap] using hpq)
      · exfalso
        exact (M.core_disjoint (row c.down) (column b.down)).symm (by
          simpa [vertexMap] using hpq)
      · have h : column b.down = column d.down := M.right.injective (by
          simpa [vertexMap] using hpq)
        have hbd : b.down = d.down := column.injective h
        have hbd' : b = d := ULift.ext b d hbd
        exact congrArg (fun z => Sum.inl (Sum.inr z)) hbd'
    · rcases p with a | b
      · exfalso
        exact M.apex_ne_left
          (row (CompleteBipartiteEdges.coords n f).1.down)
          (column (CompleteBipartiteEdges.coords n f).2.down)
          (row a.down) (by simpa [vertexMap] using hpq.symm)
      · exfalso
        exact M.apex_ne_right
          (row (CompleteBipartiteEdges.coords n f).1.down)
          (column (CompleteBipartiteEdges.coords n f).2.down)
          (column b.down) (by simpa [vertexMap] using hpq.symm)
    · rcases q with a | b
      · exfalso
        exact M.apex_ne_left
          (row (CompleteBipartiteEdges.coords n e).1.down)
          (column (CompleteBipartiteEdges.coords n e).2.down)
          (row a.down) (by simpa [vertexMap] using hpq)
      · exfalso
        exact M.apex_ne_right
          (row (CompleteBipartiteEdges.coords n e).1.down)
          (column (CompleteBipartiteEdges.coords n e).2.down)
          (column b.down) (by simpa [vertexMap] using hpq)
    · have hcoord :
          ((CompleteBipartiteEdges.coords n e).1.down,
            (CompleteBipartiteEdges.coords n e).2.down) =
          ((CompleteBipartiteEdges.coords n f).1.down,
            (CompleteBipartiteEdges.coords n f).2.down) :=
        hrainbow (by simpa [vertexMap] using hpq)
      have hcoords : CompleteBipartiteEdges.coords n e =
          CompleteBipartiteEdges.coords n f := by
        apply Prod.ext
        · apply ULift.ext
          exact congrArg Prod.fst hcoord
        · apply ULift.ext
          exact congrArg Prod.snd hcoord
      exact congrArg Sum.inr (CompleteBipartiteEdges.Z8S n hcoords)
  let vertexEmbedding : PrivateVertexExpansion.Point G ↪ W :=
    { toFun := vertexMap
      inj' := hvertexMap }
  exact
    { vertex := vertexEmbedding
      edge := edgeMap
      map_edge := by
        intro e
        change vertexMap '' {p | PrivateVertexExpansion.Inc G p e} =
          H.edgeSet (edgeMap e)
        rw [← CompleteBipartiteEdges.ZaZ n e]
        have hInc :
            {p | PrivateVertexExpansion.Inc G p
              (CompleteBipartiteEdges.edge n
                (CompleteBipartiteEdges.coords n e).1
                (CompleteBipartiteEdges.coords n e).2)} =
              {PrivateVertexExpansion.core G
                (Sum.inl (CompleteBipartiteEdges.coords n e).1),
               PrivateVertexExpansion.core G
                (Sum.inr (CompleteBipartiteEdges.coords n e).2),
               PrivateVertexExpansion.Za6 G
                (CompleteBipartiteEdges.edge n
                  (CompleteBipartiteEdges.coords n e).1
                  (CompleteBipartiteEdges.coords n e).2)} := by
          change {p | PrivateVertexExpansion.Inc G p
            (⟨s(Sum.inl (CompleteBipartiteEdges.coords n e).1,
                Sum.inr (CompleteBipartiteEdges.coords n e).2), by
                simp [G, Z7b]⟩ : G.edgeSet)} = _
          exact PrivateVertexExpansion.Z9k G (by
            simp [G, Z7b])
        rw [hInc]
        rw [M.edgeSet_eq]
        ext z
        simp [vertexMap, PrivateVertexExpansion.core,
          PrivateVertexExpansion.Za6,
          CompleteBipartiteEdges.Zb0, eq_comm] }
end TripleSystem
end P593
end
section
namespace P593
open scoped Cardinal
universe u
namespace TripleSystem
abbrev Z3W (n : ℕ) :=
  Z64 (Z7b.{u} n)
theorem ZX :
    (Z3W.{u} 0).IsObligatory := by
  intro W D _ H _
  apply Nonempty.intro
  exact
    { vertex :=
        { toFun := fun x => isEmptyElim x
          inj' := fun x => isEmptyElim x }
      edge := fun e => isEmptyElim e
      map_edge := fun e => isEmptyElim e }
end TripleSystem
end P593
end
section
namespace P593
universe u
structure FiniteClosureLayering {V : Type u} (r : ℕ)
    (Φ : {s : Finset V // s.card = r} → Finset V)
    (I : Type u) [LinearOrder I] where
  rank : V → I
  fiber_lt : ∀ i, Cardinal.mk {x : V // rank x = i} < Cardinal.mk V
  earlier_closed : ∀ (v : V) (s : Finset V) (hs : s.card = r),
    (∀ x ∈ s, rank x < rank v) →
    ∀ y ∈ Φ ⟨s, hs⟩, rank y < rank v
namespace FiniteClosureLayering
variable {V : Type u} {r : ℕ}
variable {Φ : {s : Finset V // s.card = r} → Finset V}
variable {I : Type u} [LinearOrder I]
theorem Z6c
    (L : FiniteClosureLayering r Φ I) (v : V) (s : Finset V)
    (hs : s.card = r) (hsmaller : ∀ x ∈ s, L.rank x < L.rank v) :
    v ∉ Φ ⟨s, hs⟩ := by
  intro hv
  exact (lt_irrefl _ (L.earlier_closed v s hs hsmaller v hv))
end FiniteClosureLayering
end P593
end
section
namespace P593
namespace FiniteClosureCardinality
open Set
universe u
variable {V : Type u}
def Zbr (f : Set V → Set V) (S : Set V) : Set V :=
  ⋃ n : Nat, (f^[n]) S
def Zbb (r : Nat) (S : Set V) : Type u :=
  {s : Finset V // s.card = r ∧ ∀ x ∈ s, x ∈ S}
def output (r : Nat) (Φ : {s : Finset V // s.card = r} → Finset V)
    {S : Set V} (s : Zbb r S) : Set V :=
  ((Φ ⟨s.1, s.2.1⟩ : Finset V) : Set V)
def ZaS (r : Nat) (Φ : {s : Finset V // s.card = r} → Finset V)
    (S : Set V) : Set V :=
  S ∪ ⋃ s : Zbb r S, output r Φ s
theorem Z7h
    (r : Nat) (Φ : {s : Finset V // s.card = r} → Finset V)
    (S : Set V) (x : V) :
    x ∈ ZaS r Φ S ↔ x ∈ S ∨
      ∃ s : {s : Finset V // s.card = r},
        (∀ z ∈ s.1, z ∈ S) ∧ x ∈ Φ s := by
  simp only [ZaS, Set.mem_union, Set.mem_iUnion]
  constructor
  · rintro (hx | ⟨⟨a, ha, hinside⟩, hx⟩)
    · exact Or.inl hx
    · refine Or.inr ⟨⟨a, ha⟩, hinside, ?_⟩
      simpa [output] using hx
  · rintro (hx | ⟨s, hinside, hx⟩)
    · exact Or.inl hx
    · refine Or.inr ⟨⟨s.1, s.2, hinside⟩, ?_⟩
      simpa [output] using hx
theorem Z8T
    (r : Nat) (Φ : {s : Finset V // s.card = r} → Finset V) :
    Monotone (ZaS r Φ) := by
  intro S T hST x hx
  rw [Z7h] at hx
  rw [Z7h]
  rcases hx with hx | ⟨s, hinside, hx⟩
  · exact Or.inl (hST hx)
  · exact Or.inr ⟨s, fun z hz => hST (hinside z hz), hx⟩
theorem Z5P (r : Nat) (S : Set V) :
    Cardinal.mk (Zbb r S) ≤ Cardinal.mk (Finset S) := by
  classical
  calc
    Cardinal.mk (Zbb r S) ≤
        Cardinal.mk {s : Finset V // ∀ x ∈ s, x ∈ S} :=
      Cardinal.mk_subtype_le_of_subset fun _ hs => hs.2
    _ = Cardinal.mk (Finset S) :=
      (Cardinal.mk_congr (Equiv.finsetSubtypeComm fun x : V => x ∈ S)).symm
theorem Z8U
    (r : Nat) (S : Set V) (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (hS : Cardinal.mk S ≤ c) :
    Cardinal.mk (Zbb r S) ≤ c := by
  classical
  calc
    Cardinal.mk (Zbb r S) ≤ Cardinal.mk (Finset S) :=
      Z5P r S
    _ ≤ Cardinal.mk (List S) :=
      Cardinal.mk_le_of_surjective List.toFinset_surjective
    _ ≤ max Cardinal.aleph0 (Cardinal.mk S) := Cardinal.mk_list_le_max S
    _ ≤ c := max_le hc hS
theorem Z8x
    (r : Nat) (Φ : {s : Finset V // s.card = r} → Finset V)
    (S : Set V) (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (hS : Cardinal.mk S ≤ c) :
    Cardinal.mk (ZaS r Φ S) ≤ c := by
  classical
  have houtputOne (s : Zbb r S) : Cardinal.mk (output r Φ s) ≤ c := by
    change Cardinal.mk ((Φ ⟨s.1, s.2.1⟩ : Finset V) : Set V) ≤ c
    exact (Cardinal.finset_card_lt_aleph0 (Φ ⟨s.1, s.2.1⟩)).le.trans hc
  have houtput :
      Cardinal.mk (⋃ s : Zbb r S, output r Φ s) ≤ c := by
    calc
      Cardinal.mk (⋃ s : Zbb r S, output r Φ s) ≤
          Cardinal.mk (Zbb r S) *
            ⨆ s : Zbb r S,
              Cardinal.mk (output r Φ s) := by
        exact Cardinal.mk_iUnion_le (output r Φ)
      _ ≤ c * c := by
        exact mul_le_mul' (Z8U r S c hc hS) (ciSup_le' houtputOne)
      _ = c := Cardinal.mul_eq_self hc
  calc
    Cardinal.mk (ZaS r Φ S) ≤
        Cardinal.mk S + Cardinal.mk (⋃ s : Zbb r S, output r Φ s) :=
      Cardinal.mk_union_le _ _
    _ ≤ c + c := add_le_add hS houtput
    _ = c := Cardinal.add_eq_self hc
def closure (r : Nat) (Φ : {s : Finset V // s.card = r} → Finset V)
    (S : Set V) : Set V :=
  Zbr (ZaS r Φ) S
theorem Z6E
    (r : Nat) (Φ : {s : Finset V // s.card = r} → Finset V) (S : Set V) :
    S ⊆ ZaS r Φ S := fun _ hx => Or.inl hx
theorem Z8q
    (f : Set V → Set V) (S : Set V) (x : V) :
    x ∈ Zbr f S ↔ ∃ n : Nat, x ∈ (f^[n]) S := by
  simp [Zbr]
theorem Z5f
    (f : Set V → Set V) (hExt : ∀ T : Set V, T ⊆ f T)
    (S : Set V) (n : Nat) :
    (f^[n]) S ⊆ (f^[n + 1]) S := by
  simpa [Function.iterate_succ_apply'] using hExt ((f^[n]) S)
theorem Z7V
    (f : Set V → Set V) (hExt : ∀ T : Set V, T ⊆ f T)
    (S : Set V) {n m : Nat} (hnm : n ≤ m) :
    (f^[n]) S ⊆ (f^[m]) S := by
  obtain ⟨d, rfl⟩ := Nat.le.dest hnm
  induction d with
  | zero => simp
  | succ d ih =>
      exact (ih (Nat.le_add_right _ _)).trans (by
        simpa [Nat.add_assoc] using Z5f f hExt S (n + d))
theorem Z4H
    (f : Set V → Set V) (hExt : ∀ T : Set V, T ⊆ f T)
    (S : Set V) (s : Finset V) :
    (∀ x ∈ s, x ∈ Zbr f S) →
      ∃ n : Nat, ∀ x ∈ s, x ∈ (f^[n]) S := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro _
      exact ⟨0, by simp⟩
  | @insert a s ha ih =>
      intro hs
      have haUnion : a ∈ Zbr f S := hs a (by simp)
      rcases (Z8q f S a).mp haUnion with ⟨na, hna⟩
      have hsUnion : ∀ x ∈ s, x ∈ Zbr f S := by
        intro x hx
        exact hs x (by simp [hx])
      rcases ih hsUnion with ⟨ns, hns⟩
      refine ⟨max na ns, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Z7V f hExt S (Nat.le_max_left _ _) hna
      · exact Z7V f hExt S (Nat.le_max_right _ _) (hns x hx)
theorem Z9X
    (r : Nat) (Φ : {s : Finset V // s.card = r} → Finset V)
    (S : Set V) :
    S ⊆ closure r Φ S := by
  intro x hx
  apply (Z8q (ZaS r Φ) S x).mpr
  exact ⟨0, by simpa using hx⟩
theorem Z50
    (r : Nat) (Φ : {s : Finset V // s.card = r} → Finset V)
    (S : Set V) :
    ZaS r Φ (closure r Φ S) ⊆ closure r Φ S := by
  intro x hx
  rw [Z7h] at hx
  rcases hx with hx | ⟨s, hinside, hxout⟩
  · exact hx
  · have hExt : ∀ T : Set V, T ⊆ ZaS r Φ T :=
      Z6E r Φ
    obtain ⟨n, hn⟩ :=
      Z4H (ZaS r Φ) hExt S s.1 hinside
    apply (Z8q (ZaS r Φ) S x).mpr
    refine ⟨n + 1, ?_⟩
    have hnext : x ∈ ZaS r Φ ((ZaS r Φ)^[n] S) := by
      rw [Z7h]
      exact Or.inr ⟨s, hn, hxout⟩
    simpa [Function.iterate_succ_apply'] using hnext
theorem ZaH
    (r : Nat) (Φ : {s : Finset V // s.card = r} → Finset V) :
    Monotone (closure r Φ) := by
  intro S T hST x hx
  simp only [closure, Zbr, Set.mem_iUnion] at hx ⊢
  rcases hx with ⟨n, hx⟩
  have hiter : Monotone ((ZaS r Φ)^[n]) :=
    (Z8T r Φ).iterate n
  exact ⟨n, hiter hST hx⟩
theorem Z9t
    (f : Set V → Set V) (S : Set V) (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c)
    (hstep : ∀ T : Set V, Cardinal.mk T ≤ c → Cardinal.mk (f T) ≤ c)
    (hS : Cardinal.mk S ≤ c) :
    Cardinal.mk (Zbr f S) ≤ c := by
  have hiter : ∀ n : Nat, Cardinal.mk ((f^[n]) S) ≤ c := by
    intro n
    induction n with
    | zero => simpa using hS
    | succ n ih =>
        simpa [Function.iterate_succ_apply'] using hstep ((f^[n]) S) ih
  calc
    Cardinal.mk (Zbr f S) ≤
        Cardinal.lift.{u} (Cardinal.mk Nat) *
          ⨆ n : Nat, Cardinal.lift.{0} (Cardinal.mk ((f^[n]) S)) := by
      simpa [Zbr] using
        (Cardinal.mk_iUnion_le_lift (fun n : Nat => (f^[n]) S))
    _ ≤ c * c := by
      exact mul_le_mul' (by simpa using hc) (ciSup_le fun n => by simpa using hiter n)
    _ = c := Cardinal.mul_eq_self hc
theorem Zaj
    (r : Nat) (Φ : {s : Finset V // s.card = r} → Finset V)
    (S : Set V) (c : Cardinal.{u})
    (hc : Cardinal.aleph0 ≤ c) (hS : Cardinal.mk S ≤ c) :
    Cardinal.mk (closure r Φ S) ≤ c := by
  apply Z9t (ZaS r Φ) S c hc
  · intro T hT
    exact Z8x r Φ T c hc hT
  · exact hS
theorem Zak
    (r : Nat) (Φ : {s : Finset V // s.card = r} → Finset V)
    (S : Set V) (κ : Cardinal.{u})
    (hκ : Cardinal.aleph0 < κ) (hS : Cardinal.mk S < κ) :
    Cardinal.mk (closure r Φ S) < κ := by
  let c : Cardinal.{u} := max Cardinal.aleph0 (Cardinal.mk S)
  have hc : Cardinal.aleph0 ≤ c := le_max_left _ _
  have hSc : Cardinal.mk S ≤ c := le_max_right _ _
  have hcκ : c < κ := max_lt hκ hS
  exact (Zaj r Φ S c hc hSc).trans_lt hcκ
end FiniteClosureCardinality
end P593
end
section
namespace P593
namespace FiniteClosureLayeringConstruction
open Set
open scoped Ordinal
universe u
variable {V I : Type u}
noncomputable def firstRank [LinearOrder I] [WellFoundedLT I]
    (C : I → Set V) (hcover : ∀ x : V, ∃ i : I, x ∈ C i) (x : V) : I :=
  wellFounded_lt.min {i | x ∈ C i} (by
    rcases hcover x with ⟨i, hi⟩
    exact ⟨i, hi⟩)
theorem Zag [LinearOrder I] [WellFoundedLT I]
    (C : I → Set V) (hcover : ∀ x : V, ∃ i : I, x ∈ C i) (x : V) :
    x ∈ C (firstRank C hcover x) := by
  unfold firstRank
  exact wellFounded_lt.min_mem {i : I | x ∈ C i} _
theorem Z7A [LinearOrder I] [WellFoundedLT I]
    (C : I → Set V) (hcover : ∀ x : V, ∃ i : I, x ∈ C i)
    {x : V} {i : I} (hx : x ∈ C i) :
    firstRank C hcover x ≤ i := by
  apply le_of_not_gt
  unfold firstRank
  exact wellFounded_lt.not_lt_min {j : I | x ∈ C j} hx
theorem Z1o
    [LinearOrder I] [WellFoundedLT I]
    {r : Nat} (Φ : {s : Finset V // s.card = r} → Finset V)
    (C : I → Set V)
    (hcover : ∀ x : V, ∃ i : I, x ∈ C i)
    (hmono : Monotone C)
    (hsmall : ∀ i : I, Cardinal.mk (C i) < Cardinal.mk V)
    (hclosed : ∀ (i : I) (s : Finset V) (hs : s.card = r),
      (∀ x ∈ s, x ∈ C i) → ∀ y ∈ Φ ⟨s, hs⟩, y ∈ C i)
    (hr : 0 < r) :
    ∃ L : FiniteClosureLayering r Φ I, L.rank = firstRank C hcover := by
  classical
  refine ⟨{ rank := firstRank C hcover
            fiber_lt := ?_
            earlier_closed := ?_ }, rfl⟩
  · intro i
    apply (Cardinal.mk_subtype_le_of_subset ?_).trans_lt (hsmall i)
    intro x hx
    change firstRank C hcover x = i at hx
    rw [← hx]
    exact Zag C hcover x
  · intro v s hs hlt
    have hspos : 0 < s.card := by
      simpa only [hs] using hr
    obtain ⟨m, hm, hmax⟩ :=
      Finset.exists_max_image s (firstRank C hcover) (Finset.card_pos.mp hspos)
    intro y hy
    have hsC : ∀ x ∈ s, x ∈ C (firstRank C hcover m) := by
      intro x hx
      exact hmono (hmax x hx) (Zag C hcover x)
    have hyC : y ∈ C (firstRank C hcover m) :=
      hclosed _ s hs hsC y hy
    exact (Z7A C hcover hyC).trans_lt (hlt m hm)
theorem Z1O
    {κ : Cardinal.{u}}
    {r : Nat} (Φ : {s : Finset V // s.card = r} → Finset V)
    (hκ : Cardinal.aleph0 ≤ κ) (hV : Cardinal.mk V = κ)
    (Hull : Set V → Set V)
    (hHull_mono : Monotone Hull)
    (hHull_contains : ∀ S : Set V, S ⊆ Hull S)
    (hHull_small : ∀ S : Set V, Cardinal.mk S < κ → Cardinal.mk (Hull S) < κ)
    (hHull_closed : ∀ (S : Set V) (s : Finset V) (hs : s.card = r),
      (∀ x ∈ s, x ∈ Hull S) → ∀ y ∈ Φ ⟨s, hs⟩, y ∈ Hull S)
    (hr : 0 < r) :
    Nonempty (FiniteClosureLayering r Φ κ.ord.ToType) := by
  classical
  have hκtype : Cardinal.mk κ.ord.ToType = κ := by
    simp
  let e : V ≃ κ.ord.ToType :=
    Classical.choice (Cardinal.eq.mp (hV.trans hκtype.symm))
  refine ⟨(Z1o Φ
      (fun i : κ.ord.ToType => Hull (e.symm '' Set.Iic i)) ?_ ?_ ?_ ?_ hr).choose⟩
  · intro x
    refine ⟨e x, hHull_contains _ ?_⟩
    refine ⟨e x, ?_, e.symm_apply_apply x⟩
    change e x ≤ e x
    exact le_rfl
  · intro i j hij
    apply hHull_mono
    rintro x ⟨a, ha, rfl⟩
    exact ⟨a, ha.trans hij, rfl⟩
  · intro i
    rw [hV]
    apply hHull_small
    rw [Cardinal.mk_image_eq e.symm.injective]
    have horder : Cardinal.ord (Cardinal.mk κ.ord.ToType) = typeLT κ.ord.ToType := by
      rw [hκtype]
      exact (Ordinal.type_toType κ.ord).symm
    have htype : Cardinal.aleph0 ≤ Cardinal.mk κ.ord.ToType := by
      rwa [hκtype]
    exact (Cardinal.mk_Iic_lt i horder htype).trans_eq hκtype
  · intro i s hs hsC y hy
    exact hHull_closed _ s hs hsC y hy
theorem Z1z
    {r : Nat} (Φ : {s : Finset V // s.card = r} → Finset V)
    (hV : Cardinal.aleph0 < Cardinal.mk V) (hr : 0 < r) :
    Nonempty (FiniteClosureLayering r Φ (Cardinal.mk V).ord.ToType) := by
  refine Z1O Φ hV.le rfl
    (FiniteClosureCardinality.closure r Φ) ?_ ?_ ?_ ?_ hr
  · exact FiniteClosureCardinality.ZaH r Φ
  · exact FiniteClosureCardinality.Z9X r Φ
  · intro S hS
    exact FiniteClosureCardinality.Zak r Φ S (Cardinal.mk V) hV hS
  · intro S s hs hinside y hy
    apply FiniteClosureCardinality.Z50 r Φ S
    rw [FiniteClosureCardinality.Z7h]
    exact Or.inr ⟨⟨s, hs⟩, hinside, hy⟩
end FiniteClosureLayeringConstruction
end P593
end
section
namespace P593
universe u v
namespace TripleSystem
def ZbH {W : Type u} {D : Type v}
    (H : TripleSystem W D) (t : Nat) (x y : W) : Prop :=
  x ≠ y ∧ Z66 H x y t
def Zac {W : Type u} {D : Type v}
    (H : TripleSystem W D) (t : Nat) : _root_.SimpleGraph W where
  Adj x y := ZbH H t x y
  symm := ⟨by
    rintro x y ⟨hxy, hcodeg⟩
    exact ⟨hxy.symm, (Z4A H x y t).mp hcodeg⟩⟩
  loopless := ⟨by
    intro x hx
    exact hx.1 rfl⟩
@[simp]
theorem Z8w {W : Type u} {D : Type v}
    (H : TripleSystem W D) (t : Nat) (x y : W) :
    (Zac H t).Adj x y ↔ ZbH H t x y :=
  Iff.rfl
theorem Z7y {W : Type u} {D : Type v}
    {H : TripleSystem W D} {x y : W} {t : Nat}
    (p : PairCodegreeWitness H x y t) (ht : 0 < t) : ZbH H t x y :=
  ⟨PairCodegreeWitness.Zaq p ht, ⟨p⟩⟩
end TripleSystem
end P593
end
section
namespace P593
universe u v
namespace TripleSystem
variable {W : Type u} {D : Type v}
def Z9J (H : TripleSystem W D) (x y : W) : Set W :=
  {z | Nonempty (ThirdVertexWitness H x y z)}
@[simp]
theorem Z6p {H : TripleSystem W D} {x y z : W} :
    z ∈ Z9J H x y ↔ Nonempty (ThirdVertexWitness H x y z) :=
  Iff.rfl
theorem ZG
    {H : TripleSystem W D} {x y : W} {s : Finset W} {t : Nat}
    (hcard : s.card = t)
    (hsubset : (s : Set W) ⊆ Z9J H x y) :
    Z66 H x y t := by
  classical
  let e : (↑s : Type u) ≃ Fin t := s.equivFinOfCardEq hcard
  let third : Fin t ↪ W :=
    { toFun := fun k => (e.symm k).1
      inj' := by
        intro i j hij
        apply e.symm.injective
        apply Subtype.ext
        exact hij }
  refine ⟨PairCodegreeWitness.Z69 third ?_⟩
  intro k
  change ThirdVertexWitness H x y ((e.symm k).1)
  exact Classical.choice (hsubset (e.symm k).property)
theorem ZN
    {H : TripleSystem W D} {x y : W} {t : Nat}
    (h : ¬ Z66 H x y t) :
    (Z9J H x y).Finite := by
  by_contra hinfinite
  have hinfinite' : (Z9J H x y).Infinite := hinfinite
  obtain ⟨s, hs, hcard⟩ := hinfinite'.exists_subset_card_eq t
  exact h (ZG hcard hs)
noncomputable def thirdVertexFinset
    {H : TripleSystem W D} {x y : W} {t : Nat}
    (h : ¬ Z66 H x y t) : Finset W :=
  (ZN h).toFinset
theorem Z5n
    {H : TripleSystem W D} {x y z : W} {t : Nat}
    (h : ¬ Z66 H x y t) :
    z ∈ thirdVertexFinset h ↔ Nonempty (ThirdVertexWitness H x y z) := by
  change z ∈ (ZN h).toFinset ↔ _
  rw [(ZN h).mem_toFinset]
  rfl
noncomputable def lowCompletionFinset
    (H : TripleSystem W D) (t : Nat) (x y : W) : Finset W := by
  classical
  exact if h : Z66 H x y t then ∅ else thirdVertexFinset h
theorem Z4
    {H : TripleSystem W D} {x y : W} {t : Nat}
    (h : ¬ Z66 H x y t) :
    lowCompletionFinset H t x y = thirdVertexFinset h := by
  rw [lowCompletionFinset, dif_neg h]
theorem Zy
    {H : TripleSystem W D} {x y z : W} {t : Nat}
    (h : ¬ Z66 H x y t) :
    z ∈ lowCompletionFinset H t x y ↔ Nonempty (ThirdVertexWitness H x y z) := by
  rw [Z4 h]
  exact Z5n h
theorem Z2k
    {H : TripleSystem W D} {x y z : W} {t : Nat}
    (hxy : x ≠ y) (h : ¬ ZbH H t x y)
    (hz : Nonempty (ThirdVertexWitness H x y z)) :
    z ∈ lowCompletionFinset H t x y := by
  have hlow : ¬ Z66 H x y t := by
    intro hcodeg
    exact h ⟨hxy, hcodeg⟩
  exact (Zy hlow).mpr hz
theorem Zas
    (H : TripleSystem W D) (t : Nat) (x y : W) :
    ZbH H t x y ↔ ZbH H t y x := by
  constructor
  · rintro ⟨hxy, hcodeg⟩
    exact ⟨hxy.symm, (Z4A H x y t).mp hcodeg⟩
  · rintro ⟨hyx, hcodeg⟩
    exact ⟨hyx.symm, (Z4A H y x t).mp hcodeg⟩
structure PairEndpoints (s : Finset W) where
  left : W
  right : W
  ne : left ≠ right
  eq_pair : (s : Set W) = {left, right}
noncomputable def choosePairEndpoints
    (s : {s : Finset W // s.card = 2}) : PairEndpoints s.1 :=
  Classical.choice (by
  classical
  obtain ⟨x, y, hxy, hs⟩ := Finset.card_eq_two.mp s.2
  exact ⟨⟨x, y, hxy, by simp [hs]⟩⟩)
theorem Z6l
    (s : {s : Finset W // s.card = 2}) :
    (choosePairEndpoints s).left ≠ (choosePairEndpoints s).right :=
  (choosePairEndpoints s).ne
theorem Z4P
    (s : {s : Finset W // s.card = 2}) :
    (s.1 : Set W) = {(choosePairEndpoints s).left, (choosePairEndpoints s).right} :=
  (choosePairEndpoints s).eq_pair
theorem Z3i
    (s : {s : Finset W // s.card = 2}) {x y : W}
    (hs : (s.1 : Set W) = {x, y}) :
    ((choosePairEndpoints s).left = x ∧ (choosePairEndpoints s).right = y) ∨
      ((choosePairEndpoints s).left = y ∧ (choosePairEndpoints s).right = x) := by
  have hpairs : ({x, y} : Set W) =
      {(choosePairEndpoints s).left, (choosePairEndpoints s).right} :=
    hs.symm.trans (Z4P s)
  rcases Set.pair_eq_pair_iff.mp hpairs with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · exact Or.inl ⟨hleft.symm, hright.symm⟩
  · exact Or.inr ⟨hright.symm, hleft.symm⟩
noncomputable def lowPairClosureFinset
    (H : TripleSystem W D) (t : Nat) :
    {s : Finset W // s.card = 2} → Finset W :=
  fun s => lowCompletionFinset H t (choosePairEndpoints s).left
    (choosePairEndpoints s).right
theorem Z1Z
    {H : TripleSystem W D} {t : Nat}
    (s : {s : Finset W // s.card = 2}) {z : W}
    (h : ¬ ZbH H t (choosePairEndpoints s).left (choosePairEndpoints s).right)
    (hz : Nonempty (ThirdVertexWitness H (choosePairEndpoints s).left
      (choosePairEndpoints s).right z)) :
    z ∈ lowPairClosureFinset H t s := by
  change z ∈ lowCompletionFinset H t (choosePairEndpoints s).left
    (choosePairEndpoints s).right
  exact Z2k (Z6l s) h hz
theorem ZZ
    {H : TripleSystem W D} {t : Nat}
    (s : {s : Finset W // s.card = 2}) {x y z : W}
    (hs : (s.1 : Set W) = {x, y})
    (h : ¬ ZbH H t x y)
    (hz : Nonempty (ThirdVertexWitness H x y z)) :
    z ∈ lowPairClosureFinset H t s := by
  rcases Z3i s hs with hdirect | hswap
  · apply Z1Z s
      (by simpa [hdirect.1, hdirect.2] using h)
    simpa [hdirect.1, hdirect.2] using hz
  · have hlowSwap : ¬ ZbH H t y x := by
      intro hyx
      exact h ((Zas H t x y).mpr hyx)
    have hzSwap : Nonempty (ThirdVertexWitness H y x z) := by
      rcases hz with ⟨p⟩
      exact ⟨p.swap⟩
    apply Z1Z s
      (by simpa [hswap.1, hswap.2] using hlowSwap)
    simpa [hswap.1, hswap.2] using hzSwap
end TripleSystem
end P593
end
section
namespace P593
universe u v
namespace TripleSystem
variable {W : Type u} {D : Type v}
theorem Z1w
    (H : TripleSystem W D) (t : Nat)
    (hW : Cardinal.aleph0 < Cardinal.mk W) :
    Nonempty (FiniteClosureLayering 2 (lowPairClosureFinset H t)
      (Cardinal.mk W).ord.ToType) := by
  exact _root_.P593.FiniteClosureLayeringConstruction.Z1z
    (lowPairClosureFinset H t) hW (by decide)
theorem ZC
    {I : Type u} [LinearOrder I]
    {H : TripleSystem W D} {t : Nat} {x y z : W}
    (L : FiniteClosureLayering 2 (lowPairClosureFinset H t) I)
    (p : ThirdVertexWitness H x y z)
    (hxy : Not (ZbH H t x y)) :
    Not (And (L.rank x < L.rank z) (L.rank y < L.rank z)) := by
  classical
  intro hboth
  have hxz : L.rank x < L.rank z := hboth.1
  have hyz : L.rank y < L.rank z := hboth.2
  let s : {q : Finset W // q.card = 2} := by
    exact Subtype.mk ({x, y} : Finset W) (Finset.card_pair p.Zae)
  have hs : (s.1 : Set W) = {x, y} := by
    dsimp only [s]
    ext w
    simp
  have hz : Membership.mem (lowPairClosureFinset H t s) z :=
    ZZ (H := H) (t := t)
      s hs hxy (Nonempty.intro p)
  have hnot : Not (Membership.mem (lowPairClosureFinset H t s) z) := by
    apply FiniteClosureLayering.Z6c L z s.1 s.2
    intro w hw
    have hwset : Membership.mem (s.1 : Set W) w := by
      exact hw
    rw [hs] at hwset
    have hw' : Or (w = x) (w = y) := by
      simpa using hwset
    cases hw' with
    | inl hwx =>
        subst w
        exact hxz
    | inr hwy =>
        subst w
        exact hyz
  exact hnot hz
end TripleSystem
end P593
end
section
namespace P593
open scoped Cardinal
universe u v
namespace TripleSystem
def Z3o
    {A : Type u} {E : Type v} (F : TripleSystem A E) (κ : Cardinal.{u}) : Prop :=
  ∃ (W : Type u) (D : Type v) (H : TripleSystem W D),
    Cardinal.mk W = κ ∧
      ℵ₀ < H.chromaticCardinal ∧
        ¬ F.Appears H
theorem Z1f
    {A : Type u} {E : Type v} (F : TripleSystem A E)
    (h : ∃ κ : Cardinal.{u}, Z3o F κ) :
    ∃ κ : Cardinal.{u},
      Z3o F κ ∧
        ∀ κ' : Cardinal.{u}, κ' < κ →
          ¬ Z3o F κ' := by
  rcases h with ⟨κ₀, hκ₀⟩
  let B : Set Cardinal.{u} := fun κ => Z3o F κ
  have hB : B.Nonempty := ⟨κ₀, hκ₀⟩
  let κ := Cardinal.lt_wf.min B hB
  refine ⟨κ, Cardinal.lt_wf.min_mem B hB, ?_⟩
  intro κ' hκ' hbad
  exact (Cardinal.lt_wf.not_lt_min B hbad) hκ'
def Z3X {W : Type u} {D : Type v}
    (H : TripleSystem W D) : Prop :=
  ∀ S : Set W, Cardinal.mk S < Cardinal.mk W →
    (H.Z8j S).chromaticCardinal ≤ ℵ₀
theorem Z1y
    {A : Type u} {E : Type v} (F : TripleSystem A E)
    {W : Type u} {D : Type v} (H : TripleSystem W D)
    {κ : Cardinal.{u}}
    (hcard : Cardinal.mk W = κ)
    (hfree : ¬ F.Appears H)
    (hmin : ∀ κ' : Cardinal.{u}, κ' < κ →
      ¬ Z3o F κ') :
    Z3X H := by
  intro S hS
  apply le_of_not_gt
  intro hunc
  apply hmin (Cardinal.mk S) (by simpa [hcard] using hS)
  unfold Z3o
  refine ⟨(S : Type u), H.Z9D S, H.Z8j S, rfl, hunc, ?_⟩
  intro happ
  exact hfree (Appears.trans F happ
    (Nonempty.intro (H.Z4U S)))
end TripleSystem
end P593
end
section
namespace P593
universe u
namespace SimpleGraph
variable {V : Type u} (G : _root_.SimpleGraph V)
noncomputable def finiteBipartitePartEquivFinset (s : Finset V) {n : ℕ}
    (hcard : s.card = n) : Z7c.{u} n ≃ s :=
  Equiv.ulift.{u, 0}.trans <|
    (finCongr hcard.symm).trans
      ((finCongr (Fintype.card_coe s).symm).trans (Fintype.equivFin s).symm)
noncomputable def finiteBipartitePartEmbeddingFinset (s : Finset V) {n : ℕ}
    (hcard : s.card = n) : Z7c.{u} n ↪ V :=
  (finiteBipartitePartEquivFinset s hcard).toEmbedding.trans
    (Function.Embedding.subtype _)
theorem Z2q (s : Finset V) {n : ℕ}
    (hcard : s.card = n) (i : Z7c.{u} n) :
    finiteBipartitePartEmbeddingFinset s hcard i ∈ s := by
  classical
  change ((finiteBipartitePartEquivFinset s hcard i : s) : V) ∈ s
  exact (finiteBipartitePartEquivFinset s hcard i).property
def Z2R (n : ℕ)
    (left right : Z7c.{u} n ↪ V)
    (hdisjoint : ∀ a b, left a ≠ right b)
    (hadj : ∀ a b, G.Adj (left a) (right b)) :
    _root_.SimpleGraph.Copy (Z7b.{u} n) G where
  toHom :=
    { toFun := Sum.elim left right
      map_rel' := by
        intro x y hxy
        rcases x with x | x <;> rcases y with y | y
        · simp at hxy
        · exact hadj x y
        · exact (hadj y x).symm
        · simp at hxy }
  injective' := by
    intro x y hxy
    rcases x with x | x <;> rcases y with y | y
    · exact congrArg Sum.inl (left.injective hxy)
    · exact (hdisjoint x y hxy).elim
    · exact (hdisjoint y x hxy.symm).elim
    · exact congrArg Sum.inr (right.injective hxy)
def Z8m {n : ℕ}
    (left : Z7c.{u} n ↪ V) : Set V :=
  {v | ∀ i, G.Adj (left i) v}
def Z22 {n : ℕ}
    (left : Z7c.{u} n ↪ V)
    (right : Z7c.{u} n ↪ Z8m G left) :
    _root_.SimpleGraph.Copy (Z7b.{u} n) G := by
  let rightV : Z7c.{u} n ↪ V :=
    right.trans (Function.Embedding.subtype _)
  apply Z2R G n left rightV
  · intro a b hab
    have hAdj : G.Adj (left a) (rightV b) := (right b).property a
    exact G.loopless.irrefl (left a) (hab ▸ hAdj)
  · intro a b
    exact (right b).property a
theorem Zr {n : ℕ}
    (hfree : IsEmpty
      (_root_.SimpleGraph.Copy (Z7b.{u} n) G))
    (left : Z7c.{u} n ↪ V) :
    IsEmpty (Z7c.{u} n ↪ Z8m G left) :=
  ⟨fun right ↦ hfree.false
    (Z22 G left right)⟩
theorem ZD {n : ℕ}
    (hfree : IsEmpty
      (_root_.SimpleGraph.Copy (Z7b.{u} n) G))
    (left : Z7c.{u} n ↪ V) :
    Set.Finite (Z8m G left) := by
  classical
  let S := Z8m G left
  have hno := Zr G hfree left
  by_contra hfinite
  letI : Infinite S := Set.infinite_coe_iff.mpr hfinite
  let finToNat : Z7c.{u} n ↪ ℕ :=
    (Equiv.ulift.{u, 0}.toEmbedding).trans Fin.valEmbedding
  let right : Z7c.{u} n ↪ S :=
    finToNat.trans (Infinite.natEmbedding S)
  exact hno.false right
theorem Z11 {q : Nat}
    (f : _root_.SimpleGraph.Copy (Z7b.{u} q) G) :
    ∃ left right : Fin q ↪ V,
      (∀ i j, left i ≠ right j) ∧ ∀ i j, G.Adj (left i) (right j) := by
  let left : Fin q ↪ V :=
    { toFun := fun i => f (Sum.inl (ULift.up i))
      inj' := by
        intro i j hij
        have h := f.injective hij
        simpa using h }
  let right : Fin q ↪ V :=
    { toFun := fun j => f (Sum.inr (ULift.up j))
      inj' := by
        intro i j hij
        have h := f.injective hij
        simpa using h }
  refine ⟨left, right, ?_, ?_⟩
  · intro i j h
    have hsrc : (Z7b.{u} q).Adj
        (Sum.inl (ULift.up i)) (Sum.inr (ULift.up j)) := by
      simp [Z7b]
    have htgt : G.Adj (left i) (right j) := by
      exact f.toHom.map_adj hsrc
    exact G.loopless.irrefl (left i) (h ▸ htgt)
  · intro i j
    have hsrc : (Z7b.{u} q).Adj
        (Sum.inl (ULift.up i)) (Sum.inr (ULift.up j)) := by
      simp [Z7b]
    exact f.toHom.map_adj hsrc
end SimpleGraph
end P593
end
section
namespace P593
open scoped BigOperators
universe u
namespace FiniteOutdegreeColoring
variable {α : Type u}
section Finite
variable [DecidableEq α]
def Zbq (targets : α → Finset α) (s : Finset α) (x : α) : Finset α :=
  s.filter fun y => y ≠ x ∧ (y ∈ targets x ∨ x ∈ targets y)
private def ZbK (targets : α → Finset α) (s : Finset α) (x : α) : Finset α :=
  (targets x).filter fun y => y ∈ s
private def ZbM (targets : α → Finset α) (s : Finset α) (x : α) : Finset α :=
  s.filter fun y => x ∈ targets y
private theorem Z6n (targets : α → Finset α)
    (s : Finset α) (x : α) :
    Zbq targets s x ⊆ ZbK targets s x ∪ ZbM targets s x := by
  intro y hy
  simp only [Zbq, Finset.mem_filter] at hy
  rcases hy.2.2 with hyout | hyin
  · exact Finset.mem_union_left _ (by simp [ZbK, hy.1, hyout])
  · exact Finset.mem_union_right _ (by simp [ZbM, hy.1, hyin])
private theorem Z4w (targets : α → Finset α)
    (s : Finset α) :
    (∑ x ∈ s, (ZbM targets s x).card) =
      ∑ x ∈ s, (ZbK targets s x).card := by
  rw [show (∑ x ∈ s, (ZbM targets s x).card) =
      ∑ x ∈ s, ∑ y ∈ s, if x ∈ targets y then 1 else 0 by
        simp only [ZbM, Finset.card_filter]]
  rw [Finset.sum_comm]
  simp only [ZbK, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← Finset.card_filter, ← Finset.card_filter]
  congr 1
  ext z
  simp [and_comm]
theorem Z8V (targets : α → Finset α) (d : ℕ)
    (hcard : ∀ x, (targets x).card ≤ d) (s : Finset α) :
    (∑ x ∈ s, (Zbq targets s x).card) ≤ 2 * s.card * d := by
  calc
    (∑ x ∈ s, (Zbq targets s x).card) ≤
        ∑ x ∈ s, ((ZbK targets s x).card + (ZbM targets s x).card) := by
      gcongr with x hx
      exact (Finset.card_le_card (Z6n targets s x)).trans
        (Finset.card_union_le _ _)
    _ = (∑ x ∈ s, (ZbK targets s x).card) +
        ∑ x ∈ s, (ZbM targets s x).card := by
      simp only [Finset.sum_add_distrib]
    _ = 2 * (∑ x ∈ s, (ZbK targets s x).card) := by
      rw [Z4w]
      rw [two_mul]
    _ ≤ 2 * (s.card * d) := by
      gcongr
      calc
        (∑ x ∈ s, (ZbK targets s x).card) ≤ ∑ _x ∈ s, d := by
          gcongr with x hx
          exact (Finset.card_filter_le _ _).trans (hcard x)
        _ = s.card * d := by simp
    _ = 2 * s.card * d := by ac_rfl
theorem Z5C (targets : α → Finset α) (d : ℕ)
    (hcard : ∀ x, (targets x).card ≤ d) {s : Finset α} (hs : s.Nonempty) :
    ∃ x ∈ s, (Zbq targets s x).card ≤ 2 * d := by
  by_contra h
  push Not at h
  have hlower : s.card * (2 * d + 1) ≤
      ∑ x ∈ s, (Zbq targets s x).card := by
    calc
      s.card * (2 * d + 1) = ∑ _x ∈ s, (2 * d + 1) := by simp
      _ ≤ ∑ x ∈ s, (Zbq targets s x).card := by
        gcongr with x hx
        exact Nat.succ_le_iff.mpr (h x hx)
  have hupper := Z8V targets d hcard s
  have hpos : 0 < s.card := Finset.card_pos.mpr hs
  nlinarith
def ZbO (targets : α → Finset α) (s : Finset α)
    {C : Type*} (color : α → C) : Prop :=
  ∀ ⦃x y : α⦄, x ∈ s → y ∈ s → x ≠ y →
    (y ∈ targets x ∨ x ∈ targets y) → color x ≠ color y
theorem Z6x (targets : α → Finset α) (d : ℕ)
    (hcard : ∀ x, (targets x).card ≤ d) (s : Finset α) :
    ∃ color : α → Fin (2 * d + 1), ZbO targets s color := by
  classical
  induction hsize : s.card using Nat.strong_induction_on generalizing s with
  | h n ih =>
      by_cases hs : s.Nonempty
      · obtain ⟨x, hx, hxdeg⟩ := Z5C targets d hcard hs
        have herase_card : (s.erase x).card < n := by
          rw [← hsize]
          exact Finset.card_erase_lt_of_mem hx
        obtain ⟨color, hcolor⟩ := ih (s.erase x).card herase_card (s.erase x) rfl
        let used : Finset (Fin (2 * d + 1)) :=
          (Zbq targets s x).image color
        have hused : used.card < Fintype.card (Fin (2 * d + 1)) := by
          calc
            used.card ≤ (Zbq targets s x).card := Finset.card_image_le
            _ ≤ 2 * d := hxdeg
            _ < 2 * d + 1 := Nat.lt_succ_self _
            _ = Fintype.card (Fin (2 * d + 1)) := by simp
        obtain ⟨fresh, hfresh⟩ : ∃ fresh : Fin (2 * d + 1), fresh ∉ used := by
          by_contra hall
          push Not at hall
          have huniv : used = Finset.univ := Finset.eq_univ_of_forall hall
          rw [huniv, Finset.card_univ] at hused
          exact (Nat.lt_irrefl _ hused)
        let color' : α → Fin (2 * d + 1) := fun y =>
          if y = x then fresh else color y
        refine ⟨color', ?_⟩
        intro y z hy hz hyz hadj
        by_cases hyx : y = x
        · subst y
          have hzmem : z ∈ Zbq targets s x := by
            exact Finset.mem_filter.mpr ⟨hz, hyz.symm, hadj⟩
          have hcz : color z ∈ used := by
            exact Finset.mem_image.mpr ⟨z, hzmem, rfl⟩
          simp only [color', if_pos rfl, if_neg hyz.symm]
          intro heq
          apply hfresh
          rw [heq]
          exact hcz
        · by_cases hzx : z = x
          · subst z
            have hymem : y ∈ Zbq targets s x := by
              exact Finset.mem_filter.mpr ⟨hy, hyx, hadj.elim Or.inr Or.inl⟩
            have hcy : color y ∈ used := by
              exact Finset.mem_image.mpr ⟨y, hymem, rfl⟩
            simp only [color', if_neg hyx, if_pos rfl]
            intro heq
            apply hfresh
            rw [← heq]
            exact hcy
          · simp only [color', if_neg hyx, if_neg hzx]
            apply hcolor
            · simpa [Finset.mem_erase, hyx] using hy
            · simpa [Finset.mem_erase, hzx] using hz
            · exact hyz
            · exact hadj
      · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        exact ⟨fun _ => 0, by simp [ZbO, hempty]⟩
end Finite
section Infinite
theorem Z9o (targets : α → Finset α) (d : ℕ)
    (hcard : ∀ x, (targets x).card ≤ d) :
    ∃ color : α → Fin (2 * d + 1),
      ∀ ⦃x y : α⦄, x ≠ y → (y ∈ targets x ∨ x ∈ targets y) →
        color x ≠ color y := by
  classical
  let localColor : Finset α → α → Fin (2 * d + 1) := fun s =>
    Classical.choose (Z6x targets d hcard s)
  have hlocal (s : Finset α) : ZbO targets s (localColor s) :=
    Classical.choose_spec (Z6x targets d hcard s)
  obtain ⟨color, hcolor⟩ := Finset.rado_selection localColor
  refine ⟨color, ?_⟩
  intro x y hxy hadj
  obtain ⟨t, hsub, hagree⟩ := hcolor {x, y}
  have hxt : x ∈ t := hsub (by simp)
  have hyt : y ∈ t := hsub (by simp)
  rw [hagree x (by simp), hagree y (by simp)]
  exact hlocal t hxt hyt hxy hadj
end Infinite
end FiniteOutdegreeColoring
end P593
end
section
namespace P593
universe u v
namespace SimpleGraph
variable {V : Type u}
def Z7R (G : _root_.SimpleGraph V) : Prop :=
  Nonempty (G.Coloring ℕ)
theorem Z53 (G : _root_.SimpleGraph V)
    (targets : V → Finset V) (d : ℕ)
    (hcard : ∀ x, (targets x).card ≤ d)
    (hcover : ∀ {x y : V}, G.Adj x y →
      y ∈ targets x ∨ x ∈ targets y) :
    Nonempty (G.Coloring (Fin (2 * d + 1))) := by
  classical
  obtain ⟨color, hcolor⟩ :=
    FiniteOutdegreeColoring.Z9o targets d hcard
  refine ⟨_root_.SimpleGraph.Coloring.mk color ?_⟩
  intro x y hxy
  exact hcolor (G.ne_of_adj hxy) (hcover hxy)
theorem Z2p
    (G : _root_.SimpleGraph V) {I : Type v} (rank : V → I)
    (within : V → ℕ) {k : ℕ} (cross : V → Fin k)
    (hwithin : ∀ {x y : V}, G.Adj x y → rank x = rank y →
      within x ≠ within y)
    (hcross : ∀ {x y : V}, G.Adj x y → rank x ≠ rank y →
      cross x ≠ cross y) :
    Z7R G := by
  refine ⟨_root_.SimpleGraph.Coloring.mk
    (fun x ↦ Nat.pair (within x) (cross x).val) ?_⟩
  intro x y hxy hEq
  have hp := Nat.pair_eq_pair.mp hEq
  by_cases hrank : rank x = rank y
  · exact hwithin hxy hrank hp.1
  · exact hcross hxy hrank (Fin.ext hp.2)
theorem Z1C
    (G : _root_.SimpleGraph V) {I : Type v} [LinearOrder I]
    (rank : V → I) (d : ℕ)
    (hfinite : ∀ x : V,
      Set.Finite {y : V | G.Adj x y ∧ rank y < rank x})
    (hcard : ∀ x : V,
      (hfinite x).toFinset.card ≤ d)
    (hfiber : ∀ i : I,
      Z7R (G.induce {x : V | rank x = i})) :
    Z7R G := by
  classical
  let targets : V → Finset V := fun x ↦ (hfinite x).toFinset
  have htargets_card : ∀ x, (targets x).card ≤ d := by
    intro x
    exact hcard x
  have htargets_cover : ∀ {x y : V}, G.Adj x y → rank x ≠ rank y →
      y ∈ targets x ∨ x ∈ targets y := by
    intro x y hxy hne
    rcases lt_or_gt_of_ne hne with hxyRank | hyxRank
    · right
      simp only [targets, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact ⟨hxy.symm, hxyRank⟩
    · left
      simp only [targets, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact ⟨hxy, hyxRank⟩
  let crossGraph : _root_.SimpleGraph V :=
    _root_.SimpleGraph.fromRel fun x y ↦ G.Adj x y ∧ rank x ≠ rank y
  have hcross_cover : ∀ {x y : V}, crossGraph.Adj x y →
      y ∈ targets x ∨ x ∈ targets y := by
    intro x y hxy
    rcases hxy.2 with h | h
    · exact htargets_cover h.1 h.2
    · exact htargets_cover h.1.symm h.2.symm
  obtain ⟨cross⟩ :=
    Z53 crossGraph targets d htargets_card hcross_cover
  let layerColor : ∀ i : I,
      (G.induce {x : V | rank x = i}).Coloring ℕ := fun i ↦
    Classical.choice (hfiber i)
  let fiberColor : I → V → ℕ := fun i x ↦
    if hx : rank x = i then layerColor i ⟨x, hx⟩ else 0
  have hfiberColor (i : I) {x y : V} (hxy : G.Adj x y)
      (hx : rank x = i) (hy : rank y = i) :
      fiberColor i x ≠ fiberColor i y := by
    simp only [fiberColor, dif_pos hx, dif_pos hy]
    exact (layerColor i).valid hxy
  let within : V → ℕ := fun x ↦ fiberColor (rank x) x
  have hwithin : ∀ {x y : V}, G.Adj x y → rank x = rank y →
      within x ≠ within y := by
    intro x y hxy hrank
    change fiberColor (rank x) x ≠ fiberColor (rank y) y
    rw [hrank]
    exact hfiberColor (rank y) hxy hrank rfl
  apply Z2p G rank within cross hwithin
  intro x y hxy hne
  exact cross.valid ⟨G.ne_of_adj hxy, Or.inl ⟨hxy, hne⟩⟩
end SimpleGraph
end P593
end
section
namespace P593
universe u
namespace SimpleGraph
variable {V : Type u} (G : _root_.SimpleGraph V)
theorem Z1I {n : Nat} (S : Set V)
    (hno : IsEmpty (Z7c.{u} n ↪ S)) :
    Set.Finite S := by
  classical
  by_contra hfinite
  letI : Infinite S := Set.infinite_coe_iff.mpr hfinite
  let finToNat : Z7c.{u} n ↪ Nat :=
    (Equiv.ulift.{u, 0}.toEmbedding).trans Fin.valEmbedding
  let right : Z7c.{u} n ↪ S :=
    finToNat.trans (Infinite.natEmbedding S)
  exact hno.false right
theorem ZK {n : Nat}
    (S : Set V) (hno : IsEmpty (Z7c.{u} n ↪ S)) :
    (Z1I S hno).toFinset.card < n := by
  classical
  let hS : Set.Finite S := Z1I S hno
  by_contra hlt
  have hle : n ≤ hS.toFinset.card := Nat.le_of_not_gt hlt
  let finIncl : Fin n ↪ Fin hS.toFinset.card :=
    { toFun := fun i ↦ ⟨i, i.isLt.trans_le hle⟩
      inj' := fun _ _ h ↦
        Fin.ext (congrArg (fun z : Fin hS.toFinset.card ↦ z.val) h) }
  let cardEquiv : Fin hS.toFinset.card ≃ hS.toFinset :=
    (finCongr (Fintype.card_coe hS.toFinset).symm).trans
      (Fintype.equivFin hS.toFinset).symm
  let finsetToSet : hS.toFinset ↪ S :=
    { toFun := fun x ↦
        ⟨x, by simpa only [Set.Finite.mem_toFinset] using x.property⟩
      inj' := by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun z : S ↦ z.val) h }
  let right : Z7c.{u} n ↪ S :=
    (Equiv.ulift.{u, 0}.toEmbedding).trans
      (finIncl.trans (cardEquiv.toEmbedding.trans finsetToSet))
  exact hno.false right
noncomputable def commonNeighborClosure {n : Nat}
    (hfree : IsEmpty (_root_.SimpleGraph.Copy (Z7b.{u} n) G)) :
    {s : Finset V // s.card = n} → Finset V :=
  fun s ↦
    (ZD G hfree
      (finiteBipartitePartEmbeddingFinset s.1 s.2)).toFinset
theorem Z4e {n : Nat}
    (hfree : IsEmpty (_root_.SimpleGraph.Copy (Z7b.{u} n) G))
    (s : {s : Finset V // s.card = n}) (v : V) :
    v ∈ commonNeighborClosure G hfree s ↔ ∀ x ∈ s.1, G.Adj x v := by
  classical
  constructor
  · intro hv x hx
    have hv' : v ∈ Z8m G
        (finiteBipartitePartEmbeddingFinset s.1 s.2) := by
      simpa only [commonNeighborClosure, Set.Finite.mem_toFinset] using hv
    let i : Z7c.{u} n :=
      (finiteBipartitePartEquivFinset s.1 s.2).symm ⟨x, hx⟩
    have hi : finiteBipartitePartEmbeddingFinset s.1 s.2 i = x := by
      change ((finiteBipartitePartEquivFinset s.1 s.2 i : s.1) : V) = x
      exact congrArg Subtype.val
        ((finiteBipartitePartEquivFinset s.1 s.2).apply_symm_apply ⟨x, hx⟩)
    rw [← hi]
    exact hv' i
  · intro hv
    simp only [commonNeighborClosure, Set.Finite.mem_toFinset, Z8m,
      Set.mem_setOf_eq]
    intro i
    exact hv _ (Z2q s.1 s.2 i)
theorem ZJ
    {n : Nat} {I : Type u} [LinearOrder I]
    (hfree : IsEmpty (_root_.SimpleGraph.Copy (Z7b.{u} n) G))
    (L : FiniteClosureLayering n (commonNeighborClosure G hfree) I) (v : V) :
    IsEmpty (Z7c.{u} n ↪
      {x : V | G.Adj v x ∧ L.rank x < L.rank v}) := by
  classical
  refine ⟨?_⟩
  intro e
  let eV : Z7c.{u} n ↪ V :=
    e.trans (Function.Embedding.subtype _)
  let s : Finset V := Finset.univ.image eV
  have hs : s.card = n := by
    dsimp [s]
    rw [Finset.card_image_iff.mpr ?_]
    · simp
    · intro a _ b _ hab
      exact eV.injective hab
  have hsmaller : ∀ x ∈ s, L.rank x < L.rank v := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, -, hix⟩
    subst x
    change L.rank (e i).val < L.rank v
    exact (e i).property.2
  have hv : v ∈ commonNeighborClosure G hfree ⟨s, hs⟩ := by
    apply (Z4e G hfree ⟨s, hs⟩ v).2
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, -, hix⟩
    subst x
    change G.Adj (e i).val v
    exact (e i).property.1.symm
  exact lt_irrefl _ (L.earlier_closed v s hs hsmaller v hv)
theorem Z1a
    {n : Nat} {I : Type u} [LinearOrder I]
    (hfree : IsEmpty (_root_.SimpleGraph.Copy (Z7b.{u} n) G))
    (L : FiniteClosureLayering n (commonNeighborClosure G hfree) I) (v : V) :
    Set.Finite {x : V | G.Adj v x ∧ L.rank x < L.rank v} :=
  Z1I _
    (ZJ G hfree L v)
theorem ZA
    {n : Nat} {I : Type u} [LinearOrder I]
    (hfree : IsEmpty (_root_.SimpleGraph.Copy (Z7b.{u} n) G))
    (L : FiniteClosureLayering n (commonNeighborClosure G hfree) I) (v : V) :
    (Z1a G hfree L v).toFinset.card < n :=
  ZK _
    (ZJ G hfree L v)
theorem Z1p
    {n : Nat} {I : Type u} [LinearOrder I]
    (hfree : IsEmpty (_root_.SimpleGraph.Copy (Z7b.{u} n) G))
    (L : FiniteClosureLayering n (commonNeighborClosure G hfree) I)
    (hfiber : ∀ i : I,
      Z7R (G.induce {x : V | L.rank x = i})) :
    Z7R G := by
  refine Z1C G L.rank (n - 1) ?_ ?_ hfiber
  · intro v
    exact Z1a G hfree L v
  · intro v
    exact Nat.le_pred_of_lt
      (ZA G hfree L v)
end SimpleGraph
end P593
end
section
namespace P593
universe u
namespace SimpleGraph
variable {V : Type u}
def Zbc (n : Nat) (kappa : Cardinal.{u}) : Prop :=
  Exists fun (W : Type u) => Exists fun (H : _root_.SimpleGraph W) =>
    Cardinal.mk W = kappa ∧
      ¬ Z7R H ∧
        IsEmpty (_root_.SimpleGraph.Copy (Z7b.{u} n) H)
theorem Z5F {n : Nat}
    (h : Exists fun kappa : Cardinal.{u} => Zbc n kappa) :
    Exists fun kappa : Cardinal.{u} =>
      Zbc n kappa ∧
        ((kappa' : Cardinal.{u}) -> kappa' < kappa -> ¬ Zbc n kappa') := by
  rcases h with ⟨kappa0, hkappa0⟩
  let B : Set Cardinal.{u} := fun kappa => Zbc n kappa
  have hB : B.Nonempty := ⟨kappa0, hkappa0⟩
  let kappa := Cardinal.lt_wf.min B hB
  refine ⟨kappa, Cardinal.lt_wf.min_mem B hB, ?_⟩
  intro kappa' hkappa' hbad
  exact (Cardinal.lt_wf.not_lt_min B hbad) hkappa'
theorem Z9Y {n : Nat} (G : _root_.SimpleGraph V)
    (hfree : IsEmpty (_root_.SimpleGraph.Copy (Z7b.{u} n) G))
    (s : Set V) :
    IsEmpty (_root_.SimpleGraph.Copy (Z7b.{u} n) (G.induce s)) := by
  constructor
  intro f
  exact (isEmpty_iff.mp hfree) ((_root_.SimpleGraph.Copy.induce G s).comp f)
def Z3Y (G : _root_.SimpleGraph V) : Prop :=
  (s : Set V) -> Cardinal.mk s < Cardinal.mk V -> Z7R (G.induce s)
theorem Z1q
    {n : Nat} {kappa : Cardinal.{u}} (G : _root_.SimpleGraph V)
    (hcard : Cardinal.mk V = kappa)
    (hfree : IsEmpty (_root_.SimpleGraph.Copy (Z7b.{u} n) G))
    (hmin : (kappa' : Cardinal.{u}) -> kappa' < kappa -> ¬ Zbc n kappa') :
    Z3Y G := by
  classical
  intro s hs
  by_contra hscolor
  apply hmin (Cardinal.mk s) (by simpa [hcard] using hs)
  exact ⟨s, G.induce s, rfl, hscolor, Z9Y G hfree s⟩
theorem Z3O (G : _root_.SimpleGraph V) [Countable V] :
    Z7R G := by
  letI : Encodable V := Encodable.ofCountable V
  apply Nonempty.intro
  apply _root_.SimpleGraph.Coloring.mk Encodable.encode
  intro x y hxy heq
  exact G.ne_of_adj hxy (Encodable.encode_injective heq)
theorem Z2o
    (G : _root_.SimpleGraph V) (hG : ¬ Z7R G) :
    Cardinal.aleph0 < Cardinal.mk V := by
  apply lt_of_not_ge
  intro hle
  have hcount : Countable V := Cardinal.mk_le_aleph0_iff.mp hle
  exact hG (Z3O G)
theorem Zq
    (G : _root_.SimpleGraph V) {n : Nat} {I : Type u} [LinearOrder I]
    (hfree : IsEmpty (_root_.SimpleGraph.Copy (Z7b.{u} n) G))
    (L : FiniteClosureLayering n (commonNeighborClosure G hfree) I)
    (hsmall : Z3Y G) :
    Z7R G := by
  apply Z1p G hfree L
  intro i
  exact hsmall {x : V | L.rank x = i} (L.fiber_lt i)
theorem Z1k
    {n : Nat} {kappa : Cardinal.{u}} (G : _root_.SimpleGraph V)
    (hcard : Cardinal.mk V = kappa)
    (hfree : IsEmpty (_root_.SimpleGraph.Copy (Z7b.{u} n) G))
    (hbad : ¬ Z7R G)
    (hmin : (kappa' : Cardinal.{u}) -> kappa' < kappa -> ¬ Zbc n kappa')
    {I : Type u} [LinearOrder I]
    (L : FiniteClosureLayering n (commonNeighborClosure G hfree) I) : False := by
  apply hbad
  apply Zq G hfree L
  exact Z1q G hcard hfree hmin
theorem ZW
    {n : Nat} (G : _root_.SimpleGraph V) (hn : 0 < n)
    (hfree : IsEmpty (_root_.SimpleGraph.Copy (Z7b.{u} n) G)) :
    Z7R G := by
  classical
  by_contra hbad
  obtain ⟨κ, hκbad, hmin⟩ :=
    Z5F (n := n)
      ⟨Cardinal.mk V, ⟨V, G, rfl, hbad, hfree⟩⟩
  rcases hκbad with ⟨W, H, hcard, hHbad, hHfree⟩
  let L : FiniteClosureLayering n (commonNeighborClosure H hHfree)
      (Cardinal.mk W).ord.ToType :=
    (FiniteClosureLayeringConstruction.Z1z
      (commonNeighborClosure H hHfree)
      (Z2o H hHbad) hn).some
  exact Z1k H hcard hHfree hHbad hmin L
end SimpleGraph
end P593
end
section
namespace P593
universe u v
namespace TripleSystem
theorem Z1e
    {ι : Type v} {W : Type u} [Fintype ι] [DecidableEq W] {T : Nat}
    (C : Finset W) (reservoir : ι → Fin T ↪ W)
    (hcap : C.card + Fintype.card ι ≤ T) :
    ∃ choose : ι → Fin T,
      Function.Injective (fun i => reservoir i (choose i)) ∧
      ∀ i, reservoir i (choose i) ∉ C := by
  classical
  let A : ι → Finset W := fun i => Finset.univ.map (reservoir i) \ C
  have hlarge : ∀ i : ι, Fintype.card ι ≤ (A i).card := by
    intro i
    have hsub : T - C.card ≤ (A i).card := by
      simpa [A, Finset.card_map] using
        (Finset.le_card_sdiff C (Finset.univ.map (reservoir i)))
    exact (Nat.le_sub_of_add_le' hcap).trans hsub
  have hhall : ∀ s : Finset ι, s.card ≤ (s.biUnion A).card := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    · obtain ⟨i, hi⟩ := hs
      calc
        s.card ≤ Fintype.card ι := Finset.card_le_univ s
        _ ≤ (A i).card := hlarge i
        _ ≤ (s.biUnion A).card := Finset.card_le_card (by
          intro x hx
          exact Finset.mem_biUnion.mpr ⟨i, hi, hx⟩)
  obtain ⟨f, hf_inj, hf_mem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective A).mp hhall
  choose choose hchoose using fun i =>
    (Finset.mem_map.mp (Finset.mem_sdiff.mp (hf_mem i)).1)
  refine ⟨choose, ?_, ?_⟩
  · intro i j hij
    apply hf_inj
    calc
      f i = reservoir i (choose i) := (hchoose i).2.symm
      _ = reservoir j (choose j) := hij
      _ = f j := (hchoose j).2
  · intro i
    rw [(hchoose i).2]
    exact (Finset.mem_sdiff.mp (hf_mem i)).2
end TripleSystem
end P593
end
section
namespace P593
universe u v
namespace TripleSystem
theorem Z3S
    {W : Type u} {q : Nat} (apex : Fin q → Fin q → W)
    (hinj : Function.Injective
      (fun ij : Fin q × Fin q => apex ij.1 ij.2)) :
    RainbowBipartite.Z9E 2 apex := by
  constructor
  · intro x a
    apply Nat.lt_succ_iff.mpr
    apply Finite.card_le_one_iff_subsingleton.mpr
    constructor
    intro y z
    apply Subtype.ext
    have hp : (x, y.1) = (x, z.1) := hinj (by
      change apex x y.1 = apex x z.1
      exact y.2.trans z.2.symm)
    exact congrArg Prod.snd hp
  · intro y a
    apply Nat.lt_succ_iff.mpr
    apply Finite.card_le_one_iff_subsingleton.mpr
    constructor
    intro x z
    apply Subtype.ext
    have hp : (x.1, y) = (z.1, y) := hinj (by
      change apex x.1 y = apex z.1 y
      exact x.2.trans z.2.symm)
    exact congrArg Prod.fst hp
theorem Zi
    {W : Type u} {D : Type v} [DecidableEq W]
    {H : TripleSystem W D} {n : Nat}
    (left right : Fin n ↪ W)
    (hhigh : ∀ i j,
      ZbH H (2 * n + n * n) (left i) (right j)) :
    ∃ M : WitnessedBipartiteMatrix H n 2,
      M.left = left ∧ M.right = right ∧
        Function.Injective (fun ij : Fin n × Fin n => M.apex ij.1 ij.2) := by
  classical
  let core : Finset W := Finset.univ.map left ∪ Finset.univ.map right
  have hcap : core.card + Fintype.card (Fin n × Fin n) ≤ 2 * n + n * n := by
    have hcore : core.card ≤ 2 * n := by
      calc
        core.card ≤ (Finset.univ.map left).card + (Finset.univ.map right).card :=
          Finset.card_union_le _ _
        _ = 2 * n := by simp [two_mul]
    simpa using Nat.add_le_add_right hcore (n * n)
  let completion : ∀ ij : Fin n × Fin n,
      PairCodegreeWitness H (left ij.1) (right ij.2) (2 * n + n * n) :=
    fun ij => Classical.choice (hhigh ij.1 ij.2).2
  obtain ⟨choose, hchoose_inj, hchoose_avoid⟩ :=
    Z1e
      (ι := Fin n × Fin n) (W := W) core
      (fun ij => (completion ij).third) hcap
  let apex : Fin n → Fin n → W :=
    fun i j => (completion (i, j)).third (choose (i, j))
  have hapex_inj : Function.Injective
      (fun ij : Fin n × Fin n => apex ij.1 ij.2) := by
    intro ij kl h
    apply hchoose_inj
    simpa [apex] using h
  have hapex_avoid : ∀ i j, apex i j ∉ core := by
    intro i j
    simpa [apex] using hchoose_avoid (i, j)
  refine ⟨{
    left := left
    right := right
    apex := apex
    edge := fun i j => (completion (i, j)).edge (choose (i, j))
    core_disjoint := fun i j => (hhigh i j).1
    apex_ne_left := fun i j k h =>
      hapex_avoid i j (h.symm ▸ Finset.mem_union_left _
        (Finset.mem_map.mpr ⟨k, Finset.mem_univ _, rfl⟩))
    apex_ne_right := fun i j k h =>
      hapex_avoid i j (h.symm ▸ Finset.mem_union_right _
        (Finset.mem_map.mpr ⟨k, Finset.mem_univ _, rfl⟩))
    edgeSet_eq := fun i j => by
      simpa [apex] using (completion (i, j)).edgeSet_eq (choose (i, j))
    locallyBounded := Z3S apex hapex_inj
  }, rfl, rfl, hapex_inj⟩
end TripleSystem
end P593
end
section
namespace P593
universe u v
namespace TripleSystem
open _root_.SimpleGraph
theorem Z2i
    {W : Type u} {D : Type v} {H : TripleSystem W D} {n t : Nat}
    (f : Copy (Z7b.{u} n) (Zac H t)) :
    ∃ left right : Fin n ↪ W,
      (∀ i j, left i ≠ right j) ∧
        ∀ i j, ZbH H t (left i) (right j) := by
  let left : Fin n ↪ W :=
    { toFun := fun i => f (Sum.inl (ULift.up i))
      inj' := by
        intro i j hij
        have h := f.injective hij
        simpa using h }
  let right : Fin n ↪ W :=
    { toFun := fun j => f (Sum.inr (ULift.up j))
      inj' := by
        intro i j hij
        have h := f.injective hij
        simpa using h }
  refine ⟨left, right, ?_, ?_⟩
  · intro i j h
    have hsrc : (Z7b.{u} n).Adj
        (Sum.inl (ULift.up i)) (Sum.inr (ULift.up j)) := by
      simp [Z7b]
    have htgt : (Zac H t).Adj (left i) (right j) := by
      exact f.toHom.map_adj hsrc
    exact (Z8w H t (left i) (right j)).mp htgt |>.1 h
  · intro i j
    have hsrc : (Z7b.{u} n).Adj
        (Sum.inl (ULift.up i)) (Sum.inr (ULift.up j)) := by
      simp [Z7b]
    have htgt : (Zac H t).Adj (left i) (right j) := by
      exact f.toHom.map_adj hsrc
    exact (Z8w H t (left i) (right j)).mp htgt
theorem Zc
    {W : Type u} {D : Type v} [DecidableEq W]
    {H : TripleSystem W D} {n : Nat}
    (left right : Fin n ↪ W)
    (hhigh : ∀ i j,
      ZbH H (2 * n + n * n) (left i) (right j)) :
    Nonempty ((Z3W.{u} n).Embedding H) := by
  obtain ⟨M, _, _, hapex_inj⟩ :=
    Zi
      left right hhigh
  let row : Fin n ↪ Fin n := Function.Embedding.refl _
  let column : Fin n ↪ Fin n := Function.Embedding.refl _
  have hrainbow : RainbowBipartite.Zbv M.apex row column := by
    intro ij kl h
    apply hapex_inj
    simpa [row, column] using h
  exact ⟨M.rainbowEmbedding row column hrainbow⟩
theorem Zx
    {W : Type u} {D : Type u} [DecidableEq W]
    {H : TripleSystem W D} {n : Nat}
    (hatomFree : ¬ (Z3W.{u} n).Appears H) :
    IsEmpty (Copy (Z7b.{u} n)
      (Zac H (2 * n + n * n))) := by
  refine ⟨?_⟩
  intro f
  obtain ⟨left, right, _, hhigh⟩ :=
    Z2i f
  exact hatomFree ⟨
    (Zc
      left right hhigh).some⟩
theorem Z1v
    {W : Type u} {D : Type u} [DecidableEq W]
    {H : TripleSystem W D} {n : Nat} (hn : 0 < n)
    (hatomFree : ¬ (Z3W.{u} n).Appears H) :
    P593.SimpleGraph.Z7R
      (Zac H (2 * n + n * n)) :=
  P593.SimpleGraph.ZW
    (Zac H (2 * n + n * n)) hn
    (Zx hatomFree)
end TripleSystem
end P593
end
section
namespace P593
universe u v w x
namespace TripleSystem
variable {W : Type u} {D : Type v} (H : TripleSystem W D)
def Z7X {C : Type w} (P : D → Prop) (c : W → C) : Prop :=
  ∀ e : D, P e → ∃ x : W, H.Inc x e ∧ ∃ y : W, H.Inc y e ∧ c x ≠ c y
def CountablyColorableOn (P : D → Prop) : Prop :=
  ∃ c : W → ℕ, H.Z7X P c
def Z6u (G : _root_.SimpleGraph W) : D → Prop := fun e =>
  ∃ x y : W, H.Inc x e ∧ H.Inc y e ∧ G.Adj x y
theorem CountablyColorableOn.union {P Q : D → Prop}
    (hP : H.CountablyColorableOn P) (hQ : H.CountablyColorableOn Q) :
    H.CountablyColorableOn (fun e => P e ∨ Q e) := by
  rcases hP with ⟨cP, hcP⟩
  rcases hQ with ⟨cQ, hcQ⟩
  refine ⟨fun z => Nat.pair (cP z) (cQ z), ?_⟩
  intro e he
  rcases he with he | he
  · rcases hcP e he with ⟨a, hae, b, hbe, hab⟩
    refine ⟨a, hae, b, hbe, ?_⟩
    intro hEq
    exact hab (Nat.pair_eq_pair.mp hEq).1
  · rcases hcQ e he with ⟨a, hae, b, hbe, hab⟩
    refine ⟨a, hae, b, hbe, ?_⟩
    intro hEq
    exact hab (Nat.pair_eq_pair.mp hEq).2
theorem Z26
    {G : _root_.SimpleGraph W} {C : Type w} (c : G.Coloring C) :
    H.Z7X (H.Z6u G) (fun z => c z) := by
  intro e he
  rcases he with ⟨a, b, hae, hbe, hab⟩
  exact ⟨a, hae, b, hbe, c.valid hab⟩
theorem Z1M
    {G : _root_.SimpleGraph W} (hG : P593.SimpleGraph.Z7R G) :
    H.CountablyColorableOn (H.Z6u G) := by
  rcases hG with ⟨c⟩
  exact ⟨fun z => c z, H.Z26 c⟩
end TripleSystem
end P593
end
section
namespace P593
universe u v w
namespace TripleSystem
variable {W : Type u} {D : Type v} (H : TripleSystem W D)
def ZaA (t : Nat) : D → Prop :=
  H.Z6u (Zac H t)
def ZaT (t : Nat) : D → Prop := fun e => ¬ H.ZaA t e
theorem Z3l {t : Nat} {e : D} {x y : W}
    (hxe : H.Inc x e) (hye : H.Inc y e) (hxy : ZbH H t x y) :
    H.ZaA t e :=
  ⟨x, y, hxe, hye, hxy⟩
theorem Z4z {t : Nat} {e : D} {x y : W}
    (he : H.ZaT t e) (hxe : H.Inc x e) (hye : H.Inc y e) :
    ¬ ZbH H t x y := by
  intro hxy
  exact he (H.Z3l hxe hye hxy)
theorem Z4Q (t : Nat) (e : D) :
    H.ZaA t e ∨ H.ZaT t e := by
  exact Classical.em _
theorem Z3j {t : Nat}
    (hG : P593.SimpleGraph.Z7R (Zac H t)) :
    H.CountablyColorableOn (H.ZaA t) := by
  simpa only [ZaA] using
    H.Z1M hG
end TripleSystem
end P593
end
section
namespace P593
namespace RainbowBipartite
universe u
theorem Z2n (n t : Nat) (hn : 0 < n) (ht : 0 < t) :
    ∃ q : Nat, 0 < q ∧
      ∀ (Gamma : Type u) (color : Fin q → Fin q → Gamma),
        Z9E t color →
          ∃ (left : Fin n ↪ Fin q) (right : Fin n ↪ Fin q),
            Zbv color left right := by
  obtain ⟨q, hextract⟩ := Z34 n t hn ht
  refine ⟨q, ?_, hextract⟩
  by_contra hq
  have hqzero : q = 0 := Nat.eq_zero_of_not_pos hq
  subst q
  let color : Fin 0 → Fin 0 → PUnit := fun x _ => Fin.elim0 x
  have hlocal : Z9E t color := by
    constructor <;> intro x <;> exact Fin.elim0 x
  obtain ⟨left, _, _⟩ := hextract PUnit color hlocal
  exact Fin.elim0 (left ⟨0, hn⟩)
end RainbowBipartite
end P593
end
section
namespace P593
universe u v
namespace TripleSystem
theorem Z2j
    {W : Type u} {D : Type v} {H : TripleSystem W D}
    {q t : Nat} (ht : 0 < t)
    (left right : Fin q ↪ W) (apex : Fin q → Fin q → W)
    (cell : ∀ i j, ThirdVertexWitness H (left i) (right j) (apex i j))
    (hleft : ∀ i j, ¬ ZbH H t (left i) (apex i j))
    (hright : ∀ i j, ¬ ZbH H t (right j) (apex i j)) :
    RainbowBipartite.Z9E t apex := by
  classical
  constructor
  · intro i a
    by_contra hlt
    have hle : t ≤ Nat.card {j : Fin q // apex i j = a} :=
      Nat.le_of_not_gt hlt
    let S := {j : Fin q // apex i j = a}
    letI : Fintype S := Fintype.ofFinite S
    have hle' : Fintype.card (Fin t) ≤ Fintype.card S := by
      simpa [S, Nat.card_eq_fintype_card] using hle
    obtain ⟨select⟩ := Function.Embedding.nonempty_of_card_le hle'
    let third : Fin t ↪ W :=
      select.trans ((Function.Embedding.subtype _).trans right)
    have hcell : ∀ k, ThirdVertexWitness H (left i) a (third k) := by
      intro k
      change ThirdVertexWitness H (left i) a (right (select k).1)
      simpa [(select k).property] using (cell i (select k).1).rotate
    let p : PairCodegreeWitness H (left i) a t :=
      PairCodegreeWitness.Z69 third hcell
    let k0 : Fin t := ⟨0, ht⟩
    have hhigh : ZbH H t (left i) a := Z7y p ht
    exact hleft i (select k0).1 (by
      simpa [(select k0).property] using hhigh)
  · intro j a
    by_contra hlt
    have hle : t ≤ Nat.card {i : Fin q // apex i j = a} :=
      Nat.le_of_not_gt hlt
    let S := {i : Fin q // apex i j = a}
    letI : Fintype S := Fintype.ofFinite S
    have hle' : Fintype.card (Fin t) ≤ Fintype.card S := by
      simpa [S, Nat.card_eq_fintype_card] using hle
    obtain ⟨select⟩ := Function.Embedding.nonempty_of_card_le hle'
    let third : Fin t ↪ W :=
      select.trans ((Function.Embedding.subtype _).trans left)
    have hcell : ∀ k, ThirdVertexWitness H (right j) a (third k) := by
      intro k
      change ThirdVertexWitness H (right j) a (left (select k).1)
      simpa [(select k).property] using (cell (select k).1 j).swap.rotate
    let p : PairCodegreeWitness H (right j) a t :=
      PairCodegreeWitness.Z69 third hcell
    let k0 : Fin t := ⟨0, ht⟩
    have hhigh : ZbH H t (right j) a := Z7y p ht
    exact hright (select k0).1 j (by
      simpa [(select k0).property] using hhigh)
end TripleSystem
end P593
end
section
namespace P593
universe u v w
namespace TripleSystem
open _root_.SimpleGraph
def Z8G {W : Type u} {D : Type v} {I : Type w}
    [LinearOrder I] (H : TripleSystem W D) (rank : W → I) (t : Nat) :
    _root_.SimpleGraph W where
  Adj x y :=
    ∃ z : W, rank z < rank x ∧ rank x = rank y ∧
      ∃ p : ThirdVertexWitness H x y z, H.ZaT t p.edge
  symm := ⟨by
    rintro x y ⟨z, hzx, hxy, p, hlow⟩
    refine ⟨z, ?_, hxy.symm, p.swap, hlow⟩
    simpa [hxy] using hzx⟩
  loopless := ⟨by
    intro x hx
    rcases hx with ⟨z, _, _, p, _⟩
    exact p.Zae rfl⟩
@[simp]
theorem Z6W {W : Type u} {D : Type v} {I : Type w}
    [LinearOrder I] (H : TripleSystem W D) (rank : W → I) (t : Nat)
    (x y : W) :
    (Z8G H rank t).Adj x y ↔
      ∃ z : W, rank z < rank x ∧ rank x = rank y ∧
        ∃ p : ThirdVertexWitness H x y z, H.ZaT t p.edge :=
  Iff.rfl
theorem Zg
    {W : Type u} {D : Type v} {I : Type w} [LinearOrder I]
    {H : TripleSystem W D} {rank : W → I} {n q t : Nat}
    (ht : 0 < t)
    (hq : ∀ (Gamma : Type u) (color : Fin q → Fin q → Gamma),
      RainbowBipartite.Z9E t color →
        ∃ row column : Fin n ↪ Fin q,
          RainbowBipartite.Zbv color row column)
    (f : Copy (Z7b.{u} q) (Z8G H rank t)) :
    Nonempty ((Z3W.{u} n).Embedding H) := by
  classical
  obtain ⟨left, right, hcore, hadj⟩ :=
    P593.SimpleGraph.Z11
      (Z8G H rank t) f
  have hdata : ∀ i j : Fin q,
      ∃ z : W, rank z < rank (left i) ∧ rank (left i) = rank (right j) ∧
        ∃ p : ThirdVertexWitness H (left i) (right j) z,
          H.ZaT t p.edge := by
    intro i j
    exact (Z6W H rank t (left i) (right j)).mp (hadj i j)
  let apex : Fin q → Fin q → W :=
    fun i j => Classical.choose (hdata i j)
  have hapex_lt : ∀ i j, rank (apex i j) < rank (left i) := by
    intro i j
    simpa [apex] using (Classical.choose_spec (hdata i j)).1
  have hsame : ∀ i j, rank (left i) = rank (right j) := by
    intro i j
    simpa [apex] using (Classical.choose_spec (hdata i j)).2.1
  let cell : ∀ i j, ThirdVertexWitness H (left i) (right j) (apex i j) :=
    fun i j => Classical.choose ((Classical.choose_spec (hdata i j)).2.2)
  have hlow : ∀ i j, H.ZaT t (cell i j).edge := by
    intro i j
    exact Classical.choose_spec ((Classical.choose_spec (hdata i j)).2.2)
  have hleft_inc : ∀ i j, H.Inc (left i) (cell i j).edge := by
    intro i j
    change left i ∈ H.edgeSet (cell i j).edge
    rw [(cell i j).edgeSet_eq]
    simp
  have hright_inc : ∀ i j, H.Inc (right j) (cell i j).edge := by
    intro i j
    change right j ∈ H.edgeSet (cell i j).edge
    rw [(cell i j).edgeSet_eq]
    simp
  have hapex_inc : ∀ i j, H.Inc (apex i j) (cell i j).edge := by
    intro i j
    change apex i j ∈ H.edgeSet (cell i j).edge
    rw [(cell i j).edgeSet_eq]
    simp
  have hnot_high_left : ∀ i j, ¬ ZbH H t (left i) (apex i j) := by
    intro i j
    exact H.Z4z (hlow i j)
      (hleft_inc i j) (hapex_inc i j)
  have hnot_high_right : ∀ i j, ¬ ZbH H t (right j) (apex i j) := by
    intro i j
    exact H.Z4z (hlow i j)
      (hright_inc i j) (hapex_inc i j)
  have hapex_ne_left : ∀ i j k, apex i j ≠ left k := by
    intro i j k h
    have hrank : rank (left k) = rank (left i) :=
      (hsame k j).trans (hsame i j).symm
    have hlt := hapex_lt i j
    rw [h, hrank] at hlt
    exact (lt_irrefl _ hlt)
  have hapex_ne_right : ∀ i j k, apex i j ≠ right k := by
    intro i j k h
    have hrank : rank (right k) = rank (left i) :=
      (hsame i k).symm
    have hlt := hapex_lt i j
    rw [h, hrank] at hlt
    exact (lt_irrefl _ hlt)
  let M : WitnessedBipartiteMatrix H q t :=
    WitnessedBipartiteMatrix.Z6k left right apex cell hcore
      hapex_ne_left hapex_ne_right
      (Z2j ht left right apex cell
        hnot_high_left hnot_high_right)
  obtain ⟨row, column, hrainbow⟩ := hq W M.apex M.locallyBounded
  exact ⟨M.rainbowEmbedding row column hrainbow⟩
theorem Zm
    {W : Type u} {D : Type u} {I : Type w} [LinearOrder I]
    {H : TripleSystem W D} {rank : W → I} {n q t : Nat}
    (ht : 0 < t)
    (hq : ∀ (Gamma : Type u) (color : Fin q → Fin q → Gamma),
      RainbowBipartite.Z9E t color →
        ∃ row column : Fin n ↪ Fin q,
          RainbowBipartite.Zbv color row column)
    (hatomFree : ¬ (Z3W.{u} n).Appears H) :
    IsEmpty (Copy (Z7b.{u} q) (Z8G H rank t)) := by
  refine ⟨?_⟩
  intro f
  exact hatomFree ⟨
    (Zg
      (n := n) ht hq f).some⟩
end TripleSystem
end P593
end
section
namespace P593
universe u w
namespace TripleSystem
open _root_.SimpleGraph
theorem Z13
    {W : Type u} {D : Type u} {I : Type w} [LinearOrder I]
    {H : TripleSystem W D} {rank : W -> I} {n t : Nat}
    (hn : 0 < n) (ht : 0 < t)
    (hatomFree : ¬ (Z3W.{u} n).Appears H) :
    P593.SimpleGraph.Z7R (Z8G H rank t) := by
  obtain ⟨q, hqpos, hqrainbow⟩ :=
    RainbowBipartite.Z2n n t hn ht
  apply P593.SimpleGraph.ZW
    (Z8G H rank t) hqpos
  exact Zm
    (n := n) ht hqrainbow hatomFree
end TripleSystem
end P593
end
section
namespace P593
universe u v
namespace TripleSystem
def AllSameRank {W : Type u} {I : Type u}
    (rank : W → I) (x y z : W) : Prop :=
  rank x = rank y ∧ rank y = rank z
def Z8N {W : Type u} {I : Type u} [LT I]
    (rank : W → I) (x y z : W) : Prop :=
  rank x = rank y ∧ rank z < rank x
theorem Z8g
    {W : Type u} {D : Type v} {I : Type u} [LinearOrder I]
    {H : TripleSystem W D} {t : Nat} {x y z : W}
    (L : FiniteClosureLayering 2 (lowPairClosureFinset H t) I)
    (p : ThirdVertexWitness H x y z)
    (hlow : H.ZaT t p.edge) :
    AllSameRank L.rank x y z ∨
      Z8N L.rank x y z ∨
        Z8N L.rank x z y ∨
          Z8N L.rank y z x := by
  have hx : H.Inc x p.edge := by
    change x ∈ H.edgeSet p.edge
    rw [p.edgeSet_eq]
    simp
  have hy : H.Inc y p.edge := by
    change y ∈ H.edgeSet p.edge
    rw [p.edgeSet_eq]
    simp
  have hz : H.Inc z p.edge := by
    change z ∈ H.edgeSet p.edge
    rw [p.edgeSet_eq]
    simp
  have hnot_xy : ¬ ZbH H t x y :=
    H.Z4z hlow hx hy
  have hnot_xz : ¬ ZbH H t x z :=
    H.Z4z hlow hx hz
  have hnot_yz : ¬ ZbH H t y z :=
    H.Z4z hlow hy hz
  have hnot_top_z : ¬ (L.rank x < L.rank z ∧ L.rank y < L.rank z) :=
    ZC L p hnot_xy
  have hnot_top_y : ¬ (L.rank x < L.rank y ∧ L.rank z < L.rank y) :=
    ZC L p.rotate hnot_xz
  have hnot_top_x : ¬ (L.rank y < L.rank x ∧ L.rank z < L.rank x) :=
    ZC L p.swap.rotate hnot_yz
  rcases lt_trichotomy (L.rank x) (L.rank y) with hrxy | hrxy | hryx
  · rcases lt_trichotomy (L.rank z) (L.rank y) with hrzy | hrzy | hryz
    · exact False.elim (hnot_top_y ⟨hrxy, hrzy⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨hrzy.symm, hrxy⟩))
    · exact False.elim (hnot_top_z ⟨lt_trans hrxy hryz, hryz⟩)
  · rcases lt_trichotomy (L.rank z) (L.rank x) with hrzx | hrzx | hrxz
    · exact Or.inr (Or.inl ⟨hrxy, hrzx⟩)
    · exact Or.inl ⟨hrxy, hrxy.symm.trans hrzx.symm⟩
    · exact False.elim
        (hnot_top_z ⟨hrxz, by simpa [hrxy] using hrxz⟩)
  · rcases lt_trichotomy (L.rank z) (L.rank x) with hrzx | hrzx | hrxz
    · exact False.elim (hnot_top_x ⟨hryx, hrzx⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hrzx.symm, hryx⟩))
    · exact False.elim (hnot_top_z ⟨hrxz, lt_trans hryx hrxz⟩)
theorem Z2M
    {W : Type u} {D : Type v} {I : Type u} [LinearOrder I]
    {H : TripleSystem W D} {t : Nat} {x y z : W}
    (L : FiniteClosureLayering 2 (lowPairClosureFinset H t) I)
    (p : ThirdVertexWitness H x y z)
    (hlow : H.ZaT t p.edge) :
    AllSameRank L.rank x y z ∨
      (Z8G H L.rank t).Adj x y ∨
        (Z8G H L.rank t).Adj x z ∨
          (Z8G H L.rank t).Adj y z := by
  rcases Z8g L p hlow with hall | hxy | hxz | hyz
  · exact Or.inl hall
  · refine Or.inr (Or.inl ?_)
    exact (Z6W H L.rank t x y).mpr
      ⟨z, hxy.2, hxy.1, p, hlow⟩
  · refine Or.inr (Or.inr (Or.inl ?_))
    apply (Z6W H L.rank t x z).mpr
    refine ⟨y, hxz.2, hxz.1, p.rotate, ?_⟩
    exact hlow
  · refine Or.inr (Or.inr (Or.inr ?_))
    apply (Z6W H L.rank t y z).mpr
    refine ⟨x, hyz.2, hyz.1, p.swap.rotate, ?_⟩
    exact hlow
theorem Z1H
    {W : Type u} {D : Type v} {I : Type u} [LinearOrder I]
    {H : TripleSystem W D} {t : Nat} {e : D}
    (L : FiniteClosureLayering 2 (lowPairClosureFinset H t) I)
    (hlow : H.ZaT t e) :
    ∃ x y z : W, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      H.edgeSet e = {x, y, z} ∧
        (AllSameRank L.rank x y z ∨
          (Z8G H L.rank t).Adj x y ∨
            (Z8G H L.rank t).Adj x z ∨
              (Z8G H L.rank t).Adj y z) := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hedge⟩ :=
    Set.ncard_eq_three.mp (H.Zaa e)
  let p : ThirdVertexWitness H x y z := ⟨e, hedge⟩
  have hlow' : H.ZaT t p.edge := by
    simpa [p] using hlow
  refine ⟨x, y, z, hxy, hxz, hyz, hedge, ?_⟩
  exact Z2M L p hlow'
end TripleSystem
end P593
end
section
namespace P593
open scoped Cardinal
universe u v
namespace TripleSystem
variable {V W X : Type u} {E D A : Type v}
abbrev CountableColor := ULift.{u} ℕ
structure RootedEmbedding (F : TripleSystem V E) (r : V)
    (H : TripleSystem W D) (root : W) where
  embedding : F.Embedding H
  map_root : embedding.vertex r = root
namespace RootedEmbedding
variable {F : TripleSystem V E} {r : V} {H : TripleSystem W D} {root : W}
def atImage (f : F.Embedding H) (r : V) : RootedEmbedding F r H (f.vertex r) where
  embedding := f
  map_root := rfl
def trans {Y : Type u} {B : Type v} {K : TripleSystem Y B}
    (f : RootedEmbedding F r H root) (g : H.Embedding K) :
    RootedEmbedding F r K (g.vertex root) where
  embedding := f.embedding.trans g
  map_root := congrArg g.vertex f.map_root
def Za8 [Fintype V] [DecidableEq V] [DecidableEq W]
    (f : RootedEmbedding F r H root) : Finset W :=
  (Finset.univ.erase r).image f.embedding.vertex
@[simp]
theorem Z8p [Fintype V] [DecidableEq V] [DecidableEq W]
    (f : RootedEmbedding F r H root) (x : W) :
    x ∈ f.Za8 ↔ ∃ y : V, y ≠ r ∧ f.embedding.vertex y = x := by
  simp [Za8]
theorem Z7Z [Fintype V] [DecidableEq V] [DecidableEq W]
    (f : RootedEmbedding F r H root) :
    f.Za8.card = Fintype.card V - 1 := by
  rw [Za8, Finset.card_image_of_injective _ f.embedding.vertex.injective]
  exact Finset.card_erase_of_mem (Finset.mem_univ r)
@[simp]
theorem Z4Z [Fintype V] [DecidableEq V] [DecidableEq W]
    (f : RootedEmbedding F r H root) : root ∉ f.Za8 := by
  rw [Z8p]
  rintro ⟨y, hyr, hy⟩
  apply hyr
  apply f.embedding.vertex.injective
  exact hy.trans f.map_root.symm
end RootedEmbedding
def RootedEmbedding.amalgam
    {F₀ : TripleSystem V E} {F₁ : TripleSystem X A}
    {H : TripleSystem W D} {r₀ : V} {r₁ : X} {root : W}
    (f₀ : RootedEmbedding F₀ r₀ H root)
    (f₁ : RootedEmbedding F₁ r₁ H root)
    (hcross : ∀ x y,
      f₀.embedding.vertex x = f₁.embedding.vertex y ↔ x = r₀ ∧ y = r₁) :
    (OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁).Embedding H where
  vertex :=
    { toFun := OnePointAmalgamation.lift r₀ r₁
        f₀.embedding.vertex f₁.embedding.vertex (f₀.map_root.trans f₁.map_root.symm)
      inj' := OnePointAmalgamation.Z9Q r₀ r₁
        f₀.embedding.vertex f₁.embedding.vertex
        (f₀.map_root.trans f₁.map_root.symm)
        f₀.embedding.vertex.injective f₁.embedding.vertex.injective hcross }
  edge := Sum.elim f₀.embedding.edge f₁.embedding.edge
  map_edge := by
    intro e
    cases e with
    | inl e =>
        change (OnePointAmalgamation.lift r₀ r₁
          f₀.embedding.vertex f₁.embedding.vertex
            (f₀.map_root.trans f₁.map_root.symm) ''
            (OnePointAmalgamation.left r₀ r₁ '' F₀.edgeSet e)) =
          H.edgeSet (f₀.embedding.edge e)
        rw [Set.image_image]
        change f₀.embedding.vertex '' F₀.edgeSet e = _
        exact f₀.embedding.map_edge e
    | inr e =>
        change (OnePointAmalgamation.lift r₀ r₁
          f₀.embedding.vertex f₁.embedding.vertex
            (f₀.map_root.trans f₁.map_root.symm) ''
            (OnePointAmalgamation.right r₀ r₁ '' F₁.edgeSet e)) =
          H.edgeSet (f₁.embedding.edge e)
        rw [Set.image_image]
        change f₁.embedding.vertex '' F₁.edgeSet e = _
        exact f₁.embedding.map_edge e
structure RootedPacking (F : TripleSystem V E) (r : V)
    (H : TripleSystem W D) (root : W) (m : ℕ) [Fintype V]
    [DecidableEq V] [DecidableEq W] where
  copy : Fin m → RootedEmbedding F r H root
  offRoot_disjoint : ∀ ⦃i j : Fin m⦄, i ≠ j →
    Disjoint (copy i).Za8 (copy j).Za8
namespace RootedPacking
variable {F : TripleSystem V E} {r : V} {H : TripleSystem W D} {root : W}
variable [Fintype V] [DecidableEq V] [DecidableEq W]
def zero : RootedPacking F r H root 0 where
  copy := Fin.elim0
  offRoot_disjoint := by intro i; exact Fin.elim0 i
def snoc {m : ℕ} (p : RootedPacking F r H root m)
    (g : RootedEmbedding F r H root)
    (hdisj : ∀ i, Disjoint (p.copy i).Za8 g.Za8) :
    RootedPacking F r H root (m + 1) where
  copy i := Sum.elim p.copy (fun _ : Fin 1 => g) (finSumFinEquiv.symm i)
  offRoot_disjoint := by
    intro i j hij
    generalize hi : finSumFinEquiv.symm i = si
    generalize hj : finSumFinEquiv.symm j = sj
    cases si with
    | inl a =>
        cases sj with
        | inl b =>
            apply p.offRoot_disjoint
            intro hab
            apply hij
            apply finSumFinEquiv.symm.injective
            simp [hi, hj, hab]
        | inr b =>
            simpa [hi, hj] using hdisj a
    | inr a =>
        cases sj with
        | inl b =>
            simpa [hi, hj] using (hdisj b).symm
        | inr b =>
            exfalso
            apply hij
            apply finSumFinEquiv.symm.injective
            have hab : a = b := Subsingleton.elim _ _
            simp [hi, hj, hab]
end RootedPacking
def Z6S [Fintype V] [DecidableEq V] [DecidableEq W]
    (F : TripleSystem V E) (r : V) (H : TripleSystem W D)
    (m : ℕ) (root : W) : Prop :=
  Nonempty (RootedPacking F r H root m)
def Z9i [Fintype V] [DecidableEq V] [DecidableEq W]
    (F : TripleSystem V E) (r : V) (H : TripleSystem W D) (m : ℕ) : Set W :=
  {root | Z6S F r H m root}
@[simp]
theorem Z5p [Fintype V] [DecidableEq V] [DecidableEq W]
    (F : TripleSystem V E) (r : V) (H : TripleSystem W D) (root : W) :
    Z6S F r H 0 root :=
  ⟨RootedPacking.zero⟩
theorem Z3F
    [DecidableEq W] {m : ℕ} (pieces : Fin m → Finset W)
    (hpair : ∀ ⦃i j⦄, i ≠ j → Disjoint (pieces i) (pieces j))
    (t : Finset W) (hcard : t.card < m) :
    ∃ i, Disjoint (pieces i) t := by
  classical
  by_contra h
  push Not at h
  have hmeet : ∀ i, ∃ x, x ∈ pieces i ∧ x ∈ t := by
    intro i
    exact Finset.not_disjoint_iff.mp (h i)
  let point : Fin m → W := fun i => Classical.choose (hmeet i)
  have hpoint_piece (i : Fin m) : point i ∈ pieces i :=
    (Classical.choose_spec (hmeet i)).1
  have hpoint_t (i : Fin m) : point i ∈ t :=
    (Classical.choose_spec (hmeet i)).2
  let pointInT : Fin m → t := fun i => ⟨point i, hpoint_t i⟩
  have hinj : Function.Injective pointInT := by
    intro i j hij
    by_contra hij'
    have hdisj := hpair hij'
    apply (Finset.disjoint_left.mp hdisj (hpoint_piece i))
    have hp : point i = point j := congrArg Subtype.val hij
    simpa [hp] using hpoint_piece j
  have hle : m ≤ t.card := by
    simpa using Fintype.card_le_of_injective pointInT hinj
  omega
section CountableColoring
variable (H : TripleSystem W D)
theorem ZR
    (hH : H.chromaticCardinal ≤ ℵ₀) :
    ∃ c : W → CountableColor.{u}, H.IsProperColoring c := by
  apply (H.Z4y (C := CountableColor.{u})).mp
  simpa [CountableColor] using hH
theorem Z1L
    (hH : ∃ c : W → CountableColor.{u}, H.IsProperColoring c) :
    H.chromaticCardinal ≤ ℵ₀ := by
  have hle : H.chromaticCardinal ≤ #CountableColor.{u} :=
    (H.Z4y (C := CountableColor.{u})).mpr hH
  simpa [CountableColor] using hle
theorem Z1x
    (S : Set W) {C₀ C₁ : Type u}
    (c₀ : S → C₀) (hc₀ : (H.Z8j S).IsProperColoring c₀)
    (c₁ : (Sᶜ : Set W) → C₁)
    (hc₁ : (H.Z8j (Sᶜ : Set W)).IsProperColoring c₁) :
    ∃ c : W → C₀ ⊕ C₁, H.IsProperColoring c := by
  classical
  let c : W → C₀ ⊕ C₁ := fun x =>
    if hx : x ∈ S then Sum.inl (c₀ ⟨x, hx⟩) else Sum.inr (c₁ ⟨x, hx⟩)
  refine ⟨c, ?_⟩
  intro e
  by_cases hin : ∃ x : W, H.Inc x e ∧ x ∈ S
  · obtain ⟨x, hxe, hxS⟩ := hin
    by_cases hout : ∃ y : W, H.Inc y e ∧ y ∉ S
    · obtain ⟨y, hye, hyS⟩ := hout
      refine ⟨x, hxe, y, hye, ?_⟩
      simp [c, hxS, hyS]
    · push Not at hout
      let d : H.Z9D S := ⟨e, fun z hze => hout z hze⟩
      obtain ⟨x₀, hx₀, y₀, hy₀, hxy⟩ := hc₀ d
      refine ⟨x₀.1, hx₀, y₀.1, hy₀, ?_⟩
      rw [show c x₀.1 = Sum.inl (c₀ x₀) by simp [c, x₀.2],
        show c y₀.1 = Sum.inl (c₀ y₀) by simp [c, y₀.2]]
      exact Sum.inl_injective.ne hxy
  · push Not at hin
    let d : H.Z9D (Sᶜ : Set W) := ⟨e, fun z hze => hin z hze⟩
    obtain ⟨x₁, hx₁, y₁, hy₁, hxy⟩ := hc₁ d
    refine ⟨x₁.1, hx₁, y₁.1, hy₁, ?_⟩
    have hxS : x₁.1 ∉ S := x₁.2
    have hyS : y₁.1 ∉ S := y₁.2
    rw [show c x₁.1 = Sum.inr (c₁ x₁) by simp [c, hxS],
      show c y₁.1 = Sum.inr (c₁ y₁) by simp [c, hyS]]
    exact Sum.inr_injective.ne hxy
end CountableColoring
section Blocking
variable [Fintype V] [DecidableEq V] [DecidableEq W]
variable (F : TripleSystem V E) (r : V) (H : TripleSystem W D)
noncomputable def maximalRootedPackingSize (m : ℕ) (root : W) : ℕ :=
  by
    classical
    exact Nat.findGreatest (fun k => Z6S F r H k root) (m - 1)
theorem Z4F (m : ℕ) (root : W) :
    maximalRootedPackingSize (F := F) (r := r) (H := H) m root ≤ m - 1 :=
  by
    classical
    unfold maximalRootedPackingSize
    exact Nat.findGreatest_le _
theorem Z3I (m : ℕ) (root : W) :
    Z6S F r H
      (maximalRootedPackingSize (F := F) (r := r) (H := H) m root) root := by
  classical
  unfold maximalRootedPackingSize
  exact Nat.findGreatest_spec
    (P := fun k => Z6S F r H k root)
    (m := 0) (n := m - 1) (Nat.zero_le _)
    (Z5p F r H root)
noncomputable def maximalRootedPacking (m : ℕ) (root : W) :
    RootedPacking F r H root
      (maximalRootedPackingSize (F := F) (r := r) (H := H) m root) :=
  Classical.choice (Z3I F r H m root)
noncomputable def rootedBlockingFinset (m : ℕ) (root : W) : Finset W :=
  Finset.univ.biUnion fun i : Fin
      (maximalRootedPackingSize (F := F) (r := r) (H := H) m root) =>
    ((maximalRootedPacking (F := F) (r := r) (H := H) m root).copy i).Za8
theorem Z4v (m : ℕ) (root : W) :
    (rootedBlockingFinset (F := F) (r := r) (H := H) m root).card ≤
      (m - 1) * (Fintype.card V - 1) := by
  classical
  calc
    (rootedBlockingFinset (F := F) (r := r) (H := H) m root).card ≤
        ∑ i : Fin (maximalRootedPackingSize (F := F) (r := r) (H := H) m root),
          (((maximalRootedPacking (F := F) (r := r) (H := H) m root).copy i).Za8.card) := by
      simpa [rootedBlockingFinset] using
        (Finset.card_biUnion_le (s :=
          (Finset.univ : Finset (Fin (maximalRootedPackingSize
            (F := F) (r := r) (H := H) m root))))
          (t := fun i => ((maximalRootedPacking
            (F := F) (r := r) (H := H) m root).copy i).Za8))
    _ = maximalRootedPackingSize (F := F) (r := r) (H := H) m root *
        (Fintype.card V - 1) := by
      simp [RootedEmbedding.Z7Z]
    _ ≤ (m - 1) * (Fintype.card V - 1) := by
      gcongr
      exact Z4F (F := F) (r := r) (H := H) m root
theorem Z5o (m : ℕ) (hm : 0 < m) (root : W)
    (hbad : ¬Z6S F r H m root)
    (g : RootedEmbedding F r H root) :
    ∃ x, x ∈ g.Za8 ∧
      x ∈ rootedBlockingFinset (F := F) (r := r) (H := H) m root := by
  classical
  rw [← Finset.not_disjoint_iff]
  intro hdisj
  let p := maximalRootedPacking (F := F) (r := r) (H := H) m root
  have hpieces : ∀ i, Disjoint (p.copy i).Za8 g.Za8 := by
    intro i
    apply Finset.disjoint_left.mpr
    intro x hxi hxg
    apply (Finset.disjoint_left.mp hdisj hxg)
    simp only [rootedBlockingFinset, Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, hxi⟩
  have hnext : Z6S F r H
      (maximalRootedPackingSize (F := F) (r := r) (H := H) m root + 1) root :=
    ⟨p.snoc g hpieces⟩
  have hklt : maximalRootedPackingSize (F := F) (r := r) (H := H) m root < m := by
    have hk := Z4F (F := F) (r := r) (H := H) m root
    omega
  by_cases heq : maximalRootedPackingSize (F := F) (r := r) (H := H) m root + 1 = m
  · exact hbad (heq ▸ hnext)
  · have hnext_lt : maximalRootedPackingSize (F := F) (r := r) (H := H) m root + 1 < m := by omega
    have hbound : maximalRootedPackingSize (F := F) (r := r) (H := H) m root + 1 ≤ m - 1 := by omega
    exact (Nat.findGreatest_is_greatest
      (P := fun k => Z6S F r H k root)
      (Nat.lt_succ_self _) hbound) hnext
end Blocking
section RootedAbundance
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq W]
variable (F : TripleSystem V E) (r : V)
theorem IsObligatory.Z9w
    (hF : F.IsObligatory) (m : ℕ) (hm : 0 < m)
    (H : TripleSystem W D) (hH : ℵ₀ < H.chromaticCardinal) :
    ℵ₀ < (H.Z8j
      (P593.TripleSystem.Z9i F r H m)).chromaticCardinal := by
  classical
  let R : Set W := P593.TripleSystem.Z9i F r H m
  let B : Set W := Rᶜ
  let bound : ℕ := (m - 1) * (Fintype.card V - 1)
  let targets : W → Finset W := fun x =>
    if hx : x ∈ B then
      rootedBlockingFinset (F := F) (r := r) (H := H) m x
    else ∅
  have htargets_card (x : W) : (targets x).card ≤ bound := by
    by_cases hx : x ∈ B
    · simpa [targets, hx, bound] using
        Z4v (F := F) (r := r) (H := H) m x
    · simp [targets, hx, bound]
  obtain ⟨aux, haux⟩ :=
    FiniteOutdegreeColoring.Z9o targets bound htargets_card
  let ColorClass (i : Fin (2 * bound + 1)) : Set W :=
    {x | x ∈ B ∧ aux x = i}
  have hclass_free (i : Fin (2 * bound + 1)) :
      ¬F.Appears (H.Z8j (ColorClass i)) := by
    rintro ⟨f⟩
    let root : W := (f.vertex r).1
    have hroot_class : root ∈ ColorClass i := (f.vertex r).2
    have hroot_bad : ¬Z6S F r H m root := by
      have hnotR : root ∉ R := hroot_class.1
      simpa [R, P593.TripleSystem.Z9i] using hnotR
    let fr : RootedEmbedding F r H root :=
      (RootedEmbedding.atImage f r).trans
        (H.Z4U (ColorClass i))
    obtain ⟨x, hxoff, hxblock⟩ :=
      Z5o (F := F) (r := r) (H := H)
        m hm root hroot_bad fr
    obtain ⟨y, hyr, hyx⟩ := (RootedEmbedding.Z8p fr x).mp hxoff
    have hxclass : x ∈ ColorClass i := by
      have hyclass : (f.vertex y).1 ∈ ColorClass i := (f.vertex y).2
      simpa [fr, RootedEmbedding.trans, RootedEmbedding.atImage] using hyx ▸ hyclass
    have hroot_target : x ∈ targets root := by
      simp [targets, hroot_class.1, hxblock]
    have hxr : x ≠ root := by
      intro hxr
      apply fr.Z4Z
      simpa [hxr] using hxoff
    have hne := haux hxr.symm (Or.inl hroot_target)
    exact hne (hroot_class.2.trans hxclass.2.symm)
  have hclass_count (i : Fin (2 * bound + 1)) :
      (H.Z8j (ColorClass i)).chromaticCardinal ≤ ℵ₀ := by
    by_contra hnot
    have hunc : ℵ₀ < (H.Z8j (ColorClass i)).chromaticCardinal :=
      lt_of_not_ge hnot
    exact hclass_free i
      (hF (ColorClass i) (H.Z9D (ColorClass i))
        (H.Z8j (ColorClass i)) hunc)
  have hclass_coloring (i : Fin (2 * bound + 1)) :
      ∃ c : ColorClass i → CountableColor.{u},
        (H.Z8j (ColorClass i)).IsProperColoring c :=
    (H.Z8j (ColorClass i)).ZR
      (hclass_count i)
  let inner : ∀ i : Fin (2 * bound + 1), ColorClass i → CountableColor.{u} :=
    fun i => Classical.choose (hclass_coloring i)
  have hinner (i : Fin (2 * bound + 1)) :
      (H.Z8j (ColorClass i)).IsProperColoring (inner i) :=
    Classical.choose_spec (hclass_coloring i)
  let innerFull (i : Fin (2 * bound + 1)) (x : W) : CountableColor.{u} :=
    if hx : x ∈ ColorClass i then inner i ⟨x, hx⟩ else default
  let cB : B → CountableColor.{u} := fun x =>
    ⟨Nat.pair (aux x.1).val (innerFull (aux x.1) x.1).down⟩
  have hcB : (H.Z8j B).IsProperColoring cB := by
    intro d
    by_cases hdiff : ∃ x : B, (H.Z8j B).Inc x d ∧
        ∃ y : B, (H.Z8j B).Inc y d ∧ aux x.1 ≠ aux y.1
    · obtain ⟨x, hx, y, hy, hxy⟩ := hdiff
      refine ⟨x, hx, y, hy, ?_⟩
      intro hc
      have hp := congrArg ULift.down hc
      have hfirst := (Nat.pair_eq_pair.mp hp).1
      exact hxy (Fin.ext hfirst)
    · push Not at hdiff
      have hne : ((H.Z8j B).edgeSet d).ncard ≠ 0 := by
        rw [(H.Z8j B).Zaa d]
        decide
      obtain ⟨x₀, hx₀⟩ := Set.nonempty_of_ncard_ne_zero hne
      let i : Fin (2 * bound + 1) := aux x₀.1
      have hall (z : B) (hz : (H.Z8j B).Inc z d) : aux z.1 = i := by
        exact (hdiff x₀ hx₀ z hz).symm
      let dclass : H.Z9D (ColorClass i) :=
        ⟨d.1, fun z hz => by
          have hzB : z ∈ B := d.2 hz
          have hzi : aux z = i := hall ⟨z, hzB⟩ hz
          exact ⟨hzB, hzi⟩⟩
      obtain ⟨x, hx, y, hy, hxy⟩ := hinner i dclass
      let xB : B := ⟨x.1, x.2.1⟩
      let yB : B := ⟨y.1, y.2.1⟩
      refine ⟨xB, hx, yB, hy, ?_⟩
      have hcx : cB xB =
          ⟨Nat.pair i.val (inner i x).down⟩ := by
        change (⟨Nat.pair (aux x.1).val
          (innerFull (aux x.1) x.1).down⟩ : CountableColor.{u}) = _
        rw [x.2.2]
        simp [innerFull, x.2]
      have hcy : cB yB =
          ⟨Nat.pair i.val (inner i y).down⟩ := by
        change (⟨Nat.pair (aux y.1).val
          (innerFull (aux y.1) y.1).down⟩ : CountableColor.{u}) = _
        rw [y.2.2]
        simp [innerFull, y.2]
      rw [hcx, hcy]
      intro hc
      have hp := congrArg ULift.down hc
      exact hxy (ULift.down_injective ((Nat.pair_eq_pair.mp hp).2))
  have hBcount : (H.Z8j B).chromaticCardinal ≤ ℵ₀ :=
    (H.Z8j B).Z1L ⟨cB, hcB⟩
  by_contra hRnot
  have hRnot' : ¬ℵ₀ < (H.Z8j R).chromaticCardinal := by
    simpa [R] using hRnot
  have hRcount : (H.Z8j R).chromaticCardinal ≤ ℵ₀ :=
    le_of_not_gt hRnot'
  obtain ⟨cR, hcR⟩ :=
    (H.Z8j R).ZR hRcount
  obtain ⟨cB₀, hcB₀⟩ :=
    (H.Z8j B).ZR hBcount
  obtain ⟨cSum, hcSum⟩ :=
    H.Z1x R cR hcR cB₀ hcB₀
  let encode : CountableColor.{u} ⊕ CountableColor.{u} → CountableColor.{u}
    | .inl a => ⟨Nat.pair 0 a.down⟩
    | .inr b => ⟨Nat.pair 1 b.down⟩
  have hencode : Function.Injective encode := by
    intro a b hab
    cases a with
    | inl a =>
        cases b with
        | inl b =>
            simp only [encode] at hab
            congr
            apply ULift.down_injective
            exact (Nat.pair_eq_pair.mp (congrArg ULift.down hab)).2
        | inr b =>
            simp only [encode] at hab
            have := (Nat.pair_eq_pair.mp (congrArg ULift.down hab)).1
            omega
    | inr a =>
        cases b with
        | inl b =>
            simp only [encode] at hab
            have := (Nat.pair_eq_pair.mp (congrArg ULift.down hab)).1
            omega
        | inr b =>
            simp only [encode] at hab
            congr
            apply ULift.down_injective
            exact (Nat.pair_eq_pair.mp (congrArg ULift.down hab)).2
  let c : W → CountableColor.{u} := encode ∘ cSum
  have hc : H.IsProperColoring c := by
    intro e
    obtain ⟨x, hx, y, hy, hxy⟩ := hcSum e
    exact ⟨x, hx, y, hy, hencode.ne hxy⟩
  have hHcount : H.chromaticCardinal ≤ ℵ₀ :=
    H.Z1L ⟨c, hc⟩
  exact hH.2 hHcount
end RootedAbundance
section ObligatoryAmalgamation
variable {F₀ : TripleSystem V E} {F₁ : TripleSystem X A}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype A]
variable [DecidableEq V] [DecidableEq X]
theorem IsObligatory.Z72
    (h₀ : F₀.IsObligatory) (h₁ : F₁.IsObligatory) (r₀ : V) (r₁ : X) :
    (OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁).IsObligatory := by
  classical
  intro W D _ H hH
  let m := Fintype.card X
  have hm : 0 < m := by
    exact Fintype.card_pos_iff.mpr ⟨r₁⟩
  let R : Set W := P593.TripleSystem.Z9i F₀ r₀ H m
  have hR : ℵ₀ < (H.Z8j R).chromaticCardinal := by
    simpa [R] using
      IsObligatory.Z9w (F := F₀) (r := r₀) h₀ m hm H hH
  obtain ⟨g₁⟩ := h₁ R (H.Z9D R) (H.Z8j R) hR
  let root : W := (g₁.vertex r₁).1
  let f₁ : RootedEmbedding F₁ r₁ H root :=
    (RootedEmbedding.atImage g₁ r₁).trans (H.Z4U R)
  have hrootR : root ∈ R := (g₁.vertex r₁).2
  have hsupp : Z6S F₀ r₀ H m root := by
    change Z6S F₀ r₀ H m root at hrootR
    exact hrootR
  obtain ⟨p⟩ := hsupp
  have htcard : f₁.Za8.card < m := by
    rw [f₁.Z7Z]
    simp [m, hm]
  obtain ⟨i, hdisj⟩ := Z3F
    (fun i => (p.copy i).Za8) p.offRoot_disjoint
    f₁.Za8 htcard
  refine ⟨RootedEmbedding.amalgam (p.copy i) f₁ ?_⟩
  intro x y
  constructor
  · intro hxy
    have hx : x = r₀ := by
      by_contra hxr
      have hxmem : (p.copy i).embedding.vertex x ∈
          (p.copy i).Za8 :=
        ((p.copy i).Z8p _).2 ⟨x, hxr, rfl⟩
      by_cases hyr : y = r₁
      · subst y
        have hxeqroot : (p.copy i).embedding.vertex x = root :=
          hxy.trans f₁.map_root
        exact (p.copy i).Z4Z
          (by simpa only [hxeqroot] using hxmem)
      · have hymem : f₁.embedding.vertex y ∈ f₁.Za8 :=
          (f₁.Z8p _).2 ⟨y, hyr, rfl⟩
        exact (Finset.disjoint_left.mp hdisj hxmem) (hxy ▸ hymem)
    have hy : y = r₁ := by
      apply f₁.embedding.vertex.injective
      calc
        f₁.embedding.vertex y = (p.copy i).embedding.vertex x := hxy.symm
        _ = (p.copy i).embedding.vertex r₀ := congrArg _ hx
        _ = root := (p.copy i).map_root
        _ = f₁.embedding.vertex r₁ := f₁.map_root.symm
    exact ⟨hx, hy⟩
  · rintro ⟨rfl, rfl⟩
    exact (p.copy i).map_root.trans f₁.map_root.symm
end ObligatoryAmalgamation
end TripleSystem
end P593
end
section
namespace P593
open scoped Cardinal
universe u v
namespace TripleSystem
variable {W : Type u} {D : Type v}
def ZaD {I : Type u} (H : TripleSystem W D) (rank : W → I) : D → Prop :=
  fun e => ∃ i : I, ∀ x : W, H.Inc x e → rank x = i
theorem Z9
    {I : Type u} (H : TripleSystem W D) (rank : W → I)
    (hlocal : H.Z3X)
    (hfiber : ∀ i : I,
      Cardinal.mk {x : W // rank x = i} < Cardinal.mk W) :
    H.CountablyColorableOn (ZaD H rank) := by
  classical
  let fiber : I → Set W := fun i => {x | rank x = i}
  have fiberEquiv (i : I) : fiber i ≃ {x : W // rank x = i} :=
    Equiv.subtypeEquivRight fun x => by simp [fiber]
  have hsmall (i : I) : Cardinal.mk (fiber i) < Cardinal.mk W := by
    calc
      Cardinal.mk (fiber i) = Cardinal.mk {x : W // rank x = i} :=
        Cardinal.mk_congr (fiberEquiv i)
      _ < Cardinal.mk W := hfiber i
  have hfiberColor (i : I) :
      ∃ c : fiber i → CountableColor.{u},
        (H.Z8j (fiber i)).IsProperColoring c :=
    (H.Z8j (fiber i)).ZR
      (hlocal (fiber i) (hsmall i))
  let inner : ∀ i : I, fiber i → CountableColor.{u} :=
    fun i => Classical.choose (hfiberColor i)
  have hinner (i : I) :
      (H.Z8j (fiber i)).IsProperColoring (inner i) :=
    Classical.choose_spec (hfiberColor i)
  let c : W → ℕ := fun x => (inner (rank x) ⟨x, rfl⟩).down
  refine ⟨c, ?_⟩
  intro e he
  rcases he with ⟨i, hi⟩
  let d : H.Z9D (fiber i) := ⟨e, fun x hx => hi x hx⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := hinner i d
  refine ⟨x.1, hx, y.1, hy, ?_⟩
  have hcx : c x.1 = (inner i x).down := by
    clear hx
    rcases x with ⟨x, hxmem⟩
    change rank x = i at hxmem
    cases hxmem
    rfl
  have hcy : c y.1 = (inner i y).down := by
    clear hy
    rcases y with ⟨y, hymem⟩
    change rank y = i at hymem
    cases hymem
    rfl
  rw [hcx, hcy]
  intro hEq
  exact hxy (ULift.down_injective hEq)
theorem Zs
    {r : ℕ} {Φ : {s : Finset W // s.card = r} → Finset W}
    {I : Type u} [LinearOrder I] (H : TripleSystem W D)
    (L : FiniteClosureLayering r Φ I)
    (hlocal : H.Z3X) :
    H.CountablyColorableOn (ZaD H L.rank) :=
  Z9 H L.rank
    hlocal L.fiber_lt
end TripleSystem
end P593
end
section
namespace P593
universe u
namespace TripleSystem
theorem Z14
    {W : Type u} {D : Type u} {I : Type u} [LinearOrder I]
    {H : TripleSystem W D} {t : Nat} {e : D}
    (L : FiniteClosureLayering 2 (lowPairClosureFinset H t) I) :
    H.ZaA t e \/ ZaD H L.rank e \/
      H.Z6u (Z8G H L.rank t) e := by
  rcases H.Z4Q t e with hhigh | hlow
  · exact Or.inl hhigh
  · obtain ⟨x, y, z, hxy, hxz, hyz, hedge, hshape⟩ :=
      Z1H L hlow
    rcases hshape with hall | hadj | hadj | hadj
    · refine Or.inr (Or.inl ⟨L.rank x, ?_⟩)
      intro w hw
      change w ∈ H.edgeSet e at hw
      rw [hedge] at hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl
      · rfl
      · exact hall.1.symm
      · exact (hall.1.trans hall.2).symm
    · refine Or.inr (Or.inr ⟨x, y, ?_, ?_, hadj⟩)
      · change x ∈ H.edgeSet e
        rw [hedge]
        simp
      · change y ∈ H.edgeSet e
        rw [hedge]
        simp
    · refine Or.inr (Or.inr ⟨x, z, ?_, ?_, hadj⟩)
      · change x ∈ H.edgeSet e
        rw [hedge]
        simp
      · change z ∈ H.edgeSet e
        rw [hedge]
        simp
    · refine Or.inr (Or.inr ⟨y, z, ?_, ?_, hadj⟩)
      · change y ∈ H.edgeSet e
        rw [hedge]
        simp
      · change z ∈ H.edgeSet e
        rw [hedge]
        simp
theorem Zj
    {W : Type u} {D : Type u} {I : Type u}
    [DecidableEq W] [LinearOrder I]
    {H : TripleSystem W D} {n : Nat}
    (hn : 0 < n)
    (hatomFree : ¬ (Z3W.{u} n).Appears H)
    (L : FiniteClosureLayering 2
      (lowPairClosureFinset H (2 * n + n * n)) I)
    (hlocal : H.Z3X) :
    ∃ c : W → Nat, H.IsProperColoring c := by
  have ht : 0 < 2 * n + n * n := by
    omega
  have hhigh : H.CountablyColorableOn (H.ZaA (2 * n + n * n)) :=
    H.Z3j
      (Z1v hn hatomFree)
  have hsame : H.CountablyColorableOn (ZaD H L.rank) :=
    Zs H L hlocal
  have hcrossGraph : P593.SimpleGraph.Z7R
      (Z8G H L.rank (2 * n + n * n)) :=
    Z13
      (rank := L.rank) hn ht hatomFree
  have hcross : H.CountablyColorableOn
      (H.Z6u (Z8G H L.rank (2 * n + n * n))) :=
    H.Z1M hcrossGraph
  have hrest : H.CountablyColorableOn
      (fun e => ZaD H L.rank e \/
        H.Z6u (Z8G H L.rank (2 * n + n * n)) e) :=
    CountablyColorableOn.union H hsame hcross
  have hparts : H.CountablyColorableOn
      (fun e => H.ZaA (2 * n + n * n) e \/
        ZaD H L.rank e \/
          H.Z6u
            (Z8G H L.rank (2 * n + n * n)) e) :=
    CountablyColorableOn.union H hhigh hrest
  rcases hparts with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro e
  exact hc e (Z14 L)
end TripleSystem
end P593
end
section
namespace P593
open scoped Cardinal
universe u
namespace TripleSystem
theorem ZM
    (n : Nat) (hn : 0 < n) :
    (Z3W.{u} n).IsObligatory := by
  intro W D _ H hunc
  classical
  by_contra hatomFree
  have hbad : exists kappa : Cardinal.{u},
      Z3o
        (Z3W.{u} n) kappa := by
    refine ⟨Cardinal.mk W, W, D, H, rfl, hunc, hatomFree⟩
  obtain ⟨kappa, hkappa, hminimal⟩ :=
    Z1f
      (Z3W.{u} n) hbad
  rcases hkappa with ⟨W0, D0, H0, hcard, hunc0, hfree0⟩
  letI : DecidableEq W0 := Classical.decEq W0
  have hlocal : H0.Z3X :=
    Z1y
      (Z3W.{u} n) H0 hcard hfree0 hminimal
  have hW0 : Cardinal.aleph0 < Cardinal.mk W0 :=
    lt_of_lt_of_le hunc0 H0.Z3r
  obtain ⟨L⟩ := Z1w H0
    (2 * n + n * n) hW0
  obtain ⟨c, hc⟩ :=
    Zj
      hn hfree0 L hlocal
  let cCountable : W0 -> CountableColor.{u} := fun x => ULift.up (c x)
  have hcCountable : H0.IsProperColoring cCountable := by
    intro e
    obtain ⟨x, hx, y, hy, hxy⟩ := hc e
    refine ⟨x, hx, y, hy, ?_⟩
    intro hEq
    apply hxy
    simpa [cCountable] using congrArg ULift.down hEq
  have hcount : H0.chromaticCardinal <= Cardinal.aleph0 :=
    H0.Z1L ⟨cCountable, hcCountable⟩
  exact (not_lt_of_ge hcount) hunc0
end TripleSystem
end P593
end
section
namespace P593
universe u
namespace TripleSystem
theorem Z1G (n : Nat) :
    (Z3W.{u} n).IsObligatory := by
  cases n with
  | zero => exact ZX
  | succ n =>
      exact ZM n.succ n.succ_pos
end TripleSystem
end P593
end
section
namespace P593
universe u
namespace TripleSystem
abbrev Z7t (n : ℕ) := P593.Z7c.{u} n
abbrev Z7l (n : ℕ) := P593.Z7b.{u} n
namespace SimpleGraph
variable {V W : Type u}
variable (G : _root_.SimpleGraph V) (H : _root_.SimpleGraph W)
noncomputable def copyCompleteBipartiteNN [Fintype V]
    (C : G.Coloring (Fin 2)) :
    _root_.SimpleGraph.Copy G
      (Z7l.{u} (Fintype.card V)) := by
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let vertexMap : V →
      Z7t.{u} (Fintype.card V) ⊕
        Z7t.{u} (Fintype.card V) := fun x ↦
    if C x = 0 then Sum.inl (ULift.up (e x))
    else Sum.inr (ULift.up (e x))
  have hinjective : Function.Injective vertexMap := by
    intro x y hxy
    have h := congrArg
      (Sum.elim (fun z ↦ z.down) (fun z ↦ z.down)) hxy
    have he : e x = e y := by
      simpa only [vertexMap, apply_ite, Sum.elim_inl, Sum.elim_inr,
        ULift.down_up, ite_self] using h
    exact e.injective he
  refine
    { toHom :=
        { toFun := vertexMap
          map_rel' := ?_ }
      injective' := hinjective }
  intro x y hxy
  have hcolors : C x ≠ C y := C.valid hxy
  by_cases hx : C x = 0
  · have hy : C y ≠ 0 := by
      intro hy
      exact hcolors (hx.trans hy.symm)
    simp [vertexMap, hx, hy]
  · have hcx : C x = 1 := Fin.eq_one_of_ne_zero (C x) hx
    have hy : C y = 0 := by
      by_contra hy
      have hcy : C y = 1 := Fin.eq_one_of_ne_zero (C y) hy
      exact hcolors (hcx.trans hcy.symm)
    simp [vertexMap, hx, hy]
end SimpleGraph
variable {V W : Type u}
variable {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
def Z2D
    (f : _root_.SimpleGraph.Copy G H) :
    (Z64 G).Embedding (Z64 H) where
  vertex := Function.Embedding.sumMap f.toEmbedding f.mapEdgeSet
  edge := f.mapEdgeSet
  map_edge := by
    intro e
    rcases e with ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | _ x y =>
        change
          f.toEmbedding.sumMap f.mapEdgeSet ''
              {p | PrivateVertexExpansion.Inc G p ⟨s(x, y), he⟩} =
            {p | PrivateVertexExpansion.Inc H p
              (f.mapEdgeSet ⟨s(x, y), he⟩)}
        rw [PrivateVertexExpansion.Z9k G he]
        ext p
        rcases p with p | p
        · simp [Function.Embedding.sumMap, PrivateVertexExpansion.core,
            PrivateVertexExpansion.Inc,
            PrivateVertexExpansion.Za6,
            _root_.SimpleGraph.Copy.mapEdgeSet,
            _root_.SimpleGraph.Hom.mapEdgeSet]
          constructor
          · rintro (h | h)
            · exact Or.inl h.symm
            · exact Or.inr h.symm
          · rintro (h | h)
            · exact Or.inl h.symm
            · exact Or.inr h.symm
        · simp [Function.Embedding.sumMap, PrivateVertexExpansion.core,
            PrivateVertexExpansion.Inc,
            PrivateVertexExpansion.Za6,
            _root_.SimpleGraph.Copy.mapEdgeSet,
            _root_.SimpleGraph.Hom.mapEdgeSet]
          constructor <;> intro h <;> exact h.symm
noncomputable def isolatedExpansionEmbeddingCompleteBipartiteNN
    [Fintype V] (C : G.Coloring (Fin 2)) :
    (Z64 G).isolatedReduction.Embedding
      (Z64
        (Z7l.{u} (Fintype.card V))) :=
  (Z4T (Z64 G)).trans
    (Z2D
      (SimpleGraph.copyCompleteBipartiteNN G C))
theorem Zt
    [Fintype V] (hG : G.Colorable 2)
    (hAtoms : ∀ n : ℕ,
      (Z64 (Z7l.{u} n)).IsObligatory) :
    (Z64 G).IsObligatory := by
  classical
  obtain ⟨C⟩ := hG
  apply IsObligatory.Z6Z
  exact (hAtoms (Fintype.card V)).Z7W
    (isolatedExpansionEmbeddingCompleteBipartiteNN C)
end TripleSystem
end P593
end
section
namespace P593
open scoped Cardinal
universe w
namespace TripleSystem
namespace Iso
variable {V E V' E' : Type w}
variable {F : TripleSystem V E} {F' : TripleSystem V' E'}
def Zb2 (f : Iso F F') : F.Embedding F' where
  vertex := f.vertexEquiv.toEmbedding
  edge := f.edgeEquiv
  map_edge := by
    intro e
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (f.map_inc_iff x e).mp hx
    · intro hy
      refine ⟨f.vertexEquiv.symm y, ?_, f.vertexEquiv.apply_symm_apply y⟩
      exact (f.map_inc_iff _ e).mpr (by simpa using hy)
end Iso
theorem IsObligatory.ofIso {V E V' E' : Type w}
    {F : TripleSystem V E} {F' : TripleSystem V' E'}
    (hF : F.IsObligatory) (f : Iso F F') : F'.IsObligatory :=
  hF.Z7W f.symm.Zb2
theorem Constructible.ZaU {V E : Type w} {F : TripleSystem V E}
    (hF : Constructible F) : Finite V ∧ Finite E := by
  induction hF with
  | ofEdgeless V =>
      exact ⟨inferInstance, inferInstance⟩
  | ofExpansion G hG =>
      classical
      letI : Finite G.edgeSet :=
        Finite.of_injective Subtype.val Subtype.val_injective
      letI : Fintype G.edgeSet := Fintype.ofFinite G.edgeSet
      exact ⟨inferInstance, inferInstance⟩
  | @disjointUnion V E W D F G hF hG ihF ihG =>
      classical
      letI : Finite V := ihF.1
      letI : Finite E := ihF.2
      letI : Finite W := ihG.1
      letI : Finite D := ihG.2
      letI : Fintype V := Fintype.ofFinite V
      letI : Fintype E := Fintype.ofFinite E
      letI : Fintype W := Fintype.ofFinite W
      letI : Fintype D := Fintype.ofFinite D
      exact ⟨inferInstance, inferInstance⟩
  | @amalgam V₀ E₀ V₁ E₁ F₀ F₁ h₀ h₁ r₀ r₁ ih₀ ih₁ =>
      classical
      letI : Finite V₀ := ih₀.1
      letI : Finite E₀ := ih₀.2
      letI : Finite V₁ := ih₁.1
      letI : Finite E₁ := ih₁.2
      letI : Fintype V₀ := Fintype.ofFinite V₀
      letI : Fintype E₀ := Fintype.ofFinite E₀
      letI : Fintype V₁ := Fintype.ofFinite V₁
      letI : Fintype E₁ := Fintype.ofFinite E₁
      letI : Fintype (OnePointAmalgamation.Vertex r₀ r₁) :=
        OnePointAmalgamation.vertexFintype r₀ r₁
      exact ⟨inferInstance, inferInstance⟩
  | @ofIso V E V' E' F F' hF f ihF =>
      letI : Finite V := ihF.1
      letI : Finite E := ihF.2
      exact ⟨Finite.of_equiv V f.vertexEquiv,
        Finite.of_equiv E f.edgeEquiv⟩
theorem Z6N (V : Type w) [Fintype V] :
    (ZbJ V).IsObligatory := by
  classical
  intro W D _ H hH
  have hvertices : ℵ₀ ≤ #W :=
    hH.le.trans H.Z3r
  letI : Infinite W := Cardinal.aleph0_le_mk_iff.mp hvertices
  let vertexEmbedding : V ↪ W :=
    (Fintype.equivFin V).toEmbedding.trans
      (Fin.valEmbedding.trans (Infinite.natEmbedding W))
  refine ⟨{ vertex := vertexEmbedding, edge := ?_, map_edge := ?_ }⟩
  · intro e
    exact Empty.elim e.down
  · intro e
    exact Empty.elim e.down
theorem Constructible.Z54
    (hExpansion : ∀ {X : Type w} [Fintype X] (G : _root_.SimpleGraph X),
      G.Colorable 2 → (Z64 G).IsObligatory)
    {V E : Type w} {F : TripleSystem V E} (hF : Constructible F) :
    F.IsObligatory := by
  induction hF with
  | ofEdgeless V =>
      exact Z6N V
  | ofExpansion G hG =>
      exact hExpansion G hG
  | @disjointUnion V E W D F G hF hG ihF ihG =>
      classical
      letI : Finite V := hF.ZaU.1
      letI : Finite E := hF.ZaU.2
      letI : Finite W := hG.ZaU.1
      letI : Finite D := hG.ZaU.2
      letI : Fintype V := Fintype.ofFinite V
      letI : Fintype E := Fintype.ofFinite E
      letI : Fintype W := Fintype.ofFinite W
      letI : Fintype D := Fintype.ofFinite D
      exact IsObligatory.Zao F G ihF ihG
  | @amalgam V₀ E₀ V₁ E₁ F₀ F₁ h₀ h₁ r₀ r₁ ih₀ ih₁ =>
      classical
      letI : Finite V₀ := h₀.ZaU.1
      letI : Finite E₀ := h₀.ZaU.2
      letI : Finite V₁ := h₁.ZaU.1
      letI : Finite E₁ := h₁.ZaU.2
      letI : Fintype V₀ := Fintype.ofFinite V₀
      letI : Fintype E₀ := Fintype.ofFinite E₀
      letI : Fintype V₁ := Fintype.ofFinite V₁
      letI : Fintype E₁ := Fintype.ofFinite E₁
      exact IsObligatory.Z72 ih₀ ih₁ r₀ r₁
  | ofIso hF f ihF =>
      exact ihF.ofIso f
theorem Constructible.Z2T
    (hAtoms : ∀ n : ℕ,
      (Z64 (Z7l.{w} n)).IsObligatory)
    {V E : Type w} {F : TripleSystem V E} (hF : Constructible F) :
    F.IsObligatory := by
  apply hF.Z54
  intro X _ G hG
  exact Zt hG hAtoms
theorem Constructible.Z1t
    (hAtoms : ∀ n : Nat, 0 < n →
      (Z64 (Z7l.{w} n)).IsObligatory)
    {V E : Type w} {F : TripleSystem V E} (hF : Constructible F) :
    F.IsObligatory := by
  apply hF.Z2T
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ZX
  · exact hAtoms n hn
end TripleSystem
end P593
end
section
namespace P593
universe u
namespace TripleSystem
theorem Constructible.ZaK
    {V E : Type u} {F : TripleSystem V E} (hF : Constructible F) :
    F.IsObligatory := by
  apply hF.Z1t
  intro n _
  simpa only [Z3W] using
    (Z1G.{u} n)
theorem Z25
    {V E : Type u} (F : TripleSystem V E) [Finite V] [Finite E]
    (hF : F.isolatedReduction.Intrinsic) : F.IsObligatory := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype E := Fintype.ofFinite E
  letI : DecidableEq V := Classical.decEq V
  letI : DecidableEq E := Classical.decEq E
  apply IsObligatory.Z6Z
  apply Constructible.ZaK
  exact (BridgeBlock.Z1m F).mpr hF
end TripleSystem
end P593
end
section
namespace P593
universe u
namespace SequenceLift
variable {V : Type u} {G : _root_.SimpleGraph V}
def baseFiberAssemblyCompatible (S : Set (Edge G)) : List (Node G) → Prop
  | [] => True
  | q :: nodes =>
      baseFiberAssemblyCompatible S nodes ∧
      Disjoint
        (TripleSystem.Z9A (nodes.map (Zbo S)))
        (Zbo S q) ∧
      (Disjoint
          ((system G).Z9z
            (TripleSystem.Z9A (nodes.map (Zbo S))))
          ((system G).Z9z (Zbo S q)) ∨
        ∃ r : Point G,
          (system G).Z9z
              (TripleSystem.Z9A (nodes.map (Zbo S))) ∩
            (system G).Z9z (Zbo S q) = {r})
theorem Z3p
    (S : Set (Edge G)) (nodes : List (Node G)) {e : Edge G} :
    e ∈ TripleSystem.Z9A (nodes.map (Zbo S)) ↔
      ∃ q, q ∈ nodes ∧ e ∈ Zbo S q := by
  induction nodes with
  | nil =>
      simp [TripleSystem.Z9A]
  | cons q nodes ih =>
      change
        (e ∈ TripleSystem.Z9A (nodes.map (Zbo S)) ∨
          e ∈ Zbo S q) ↔ _
      constructor
      · rintro (he | he)
        · rcases ih.mp he with ⟨q', hq', heq'⟩
          exact ⟨q', List.mem_cons.mpr (Or.inr hq'), heq'⟩
        · exact ⟨q, List.mem_cons.mpr (Or.inl rfl), he⟩
      · rintro ⟨q', hq', he⟩
        rcases List.mem_cons.mp hq' with rfl | hq'
        · exact Or.inr he
        · exact Or.inl (ih.mpr ⟨q', hq', he⟩)
theorem Z1A
    {S : Set (Edge G)} (nodes : List (Node G))
    (hcover : ∀ e, e ∈ S → baseNode e ∈ nodes) :
    TripleSystem.Z9A (nodes.map (Zbo S)) = S := by
  ext e
  rw [Z3p]
  constructor
  · rintro ⟨q, hq, he⟩
    exact he.1
  · intro he
    exact ⟨baseNode e, hcover e he, ⟨he, rfl⟩⟩
end SequenceLift
end P593
end
section
namespace P593
universe u
namespace SequenceLift
variable {V : Type u} {G : _root_.SimpleGraph V}
def Z2N
    (S : Set (Edge G)) : List (Node G) → Prop
  | [] => True
  | q :: nodes =>
      Z2N S nodes ∧
      ∀ u ∈ nodes, ∀ v ∈ nodes,
        (((system G).Z9z (Zbo S q) ∩
          (system G).Z9z (Zbo S u)).Nonempty) →
        (((system G).Z9z (Zbo S q) ∩
          (system G).Z9z (Zbo S v)).Nonempty) →
        ((system G).Z9z (Zbo S q) ∩
          (system G).Z9z (Zbo S u)) =
          ((system G).Z9z (Zbo S q) ∩
            (system G).Z9z (Zbo S v))
theorem Z2
    {S : Set (Edge G)} {nodes : List (Node G)}
    (hlinear : ((system G).Z96 S).Linear)
    (hnodup : nodes.Nodup)
    (hcoherent : Z2N S nodes) :
    baseFiberAssemblyCompatible S nodes := by
  induction nodes with
  | nil =>
      trivial
  | cons q nodes ih =>
      rw [List.nodup_cons] at hnodup
      change Z2N S nodes ∧ _ at hcoherent
      rcases hcoherent with ⟨hcoherentTail, hcoherentHead⟩
      refine ⟨ih hnodup.2 hcoherentTail, ?_, ?_⟩
      · rw [Set.disjoint_left]
        intro e hePrevious heQ
        rcases (Z3p S nodes).mp hePrevious with
          ⟨u, hu, heU⟩
        have hqu : q ≠ u := by
          intro hq
          exact hnodup.1 (hq.symm ▸ hu)
        exact (Set.disjoint_left.mp (Z84 hqu)) heQ heU
      · by_cases hdisjoint : Disjoint
            ((system G).Z9z
              (TripleSystem.Z9A (nodes.map (Zbo S))))
            ((system G).Z9z (Zbo S q))
        · exact Or.inl hdisjoint
        · right
          rcases Set.not_disjoint_iff.mp hdisjoint with
            ⟨r, hrPrevious, hrQ⟩
          refine ⟨r, Set.Subset.antisymm ?_ ?_⟩
          · intro x hx
            rcases hx.1 with ⟨e, hePrevious, hxe⟩
            rcases (Z3p S nodes).mp hePrevious with
              ⟨u, hu, heU⟩
            have hxU :
                x ∈ (system G).Z9z (Zbo S u) :=
              ⟨e, heU, hxe⟩
            rcases hrPrevious with ⟨f, hfPrevious, hrf⟩
            rcases (Z3p S nodes).mp hfPrevious with
              ⟨v, hv, hfV⟩
            have hrV :
                r ∈ (system G).Z9z (Zbo S v) :=
              ⟨f, hfV, hrf⟩
            have hintersections :=
              hcoherentHead u hu v hv
                ⟨x, hx.2, hxU⟩ ⟨r, hrQ, hrV⟩
            have hqv : q ≠ v := by
              intro hqv
              exact hnodup.1 (hqv.symm ▸ hv)
            have hsubsingleton :=
              Z19 hlinear hqv
            have hxV :
                x ∈ (system G).Z9z (Zbo S q) ∩
                  (system G).Z9z (Zbo S v) := by
              rw [← hintersections]
              exact ⟨hx.2, hxU⟩
            have hrV' :
                r ∈ (system G).Z9z (Zbo S q) ∩
                  (system G).Z9z (Zbo S v) :=
              ⟨hrQ, hrV⟩
            exact Set.mem_singleton_iff.mpr (hsubsingleton hxV hrV')
          · intro x hx
            have hxr : x = r := Set.mem_singleton_iff.mp hx
            simpa [hxr] using And.intro hrPrevious hrQ
end SequenceLift
end P593
end
section
namespace P593
universe u
namespace SequenceLift
variable {V : Type u} {G : _root_.SimpleGraph V}
theorem Z3N
    (S : Set (Edge G)) (q : Node G) :
    (system G).Z9z (Zbo S q) ⊆
      (system G).Z9z S := by
  rintro p ⟨e, he, hp⟩
  exact ⟨e, (Z8O S q) he, hp⟩
def Zz
    {S : Set (Edge G)} {q : Node G} {p : Point G}
    (hp : p ∈ (system G).Z9z (Zbo S q)) :
    Z3n S :=
  ⟨p, Z3N S q hp⟩
@[simp]
theorem Zn
    {S : Set (Edge G)} {q : Node G} {p : Point G}
    (hp : p ∈ (system G).Z9z (Zbo S q)) :
    (Zz hp).1 = p := rfl
theorem ZT
    {S : Set (Edge G)} {q u v : Node G}
    (hlin : ((system G).Z96 S).Linear)
    (hqu : q ≠ u) (hqv : q ≠ v)
    {p : Point G}
    (hpq : p ∈ (system G).Z9z (Zbo S q))
    (hpu : p ∈ (system G).Z9z (Zbo S u))
    (hpv : p ∈ (system G).Z9z (Zbo S v)) :
    ((system G).Z9z (Zbo S q) ∩
      (system G).Z9z (Zbo S u)) =
      ((system G).Z9z (Zbo S q) ∩
        (system G).Z9z (Zbo S v)) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxp : x = p :=
      Z19 hlin hqu hx ⟨hpq, hpu⟩
    subst x
    exact ⟨hpq, hpv⟩
  · intro x hx
    have hxp : x = p :=
      Z19 hlin hqv hx ⟨hpq, hpv⟩
    subst x
    exact ⟨hpq, hpu⟩
theorem Z5
    {S : Set (Edge G)} {qs : List (Z7a S)}
    (hlin : ((system G).Z96 S).Linear)
    (hnodup : qs.Nodup)
    (htail : SimpleGraph.bipartiteTailPointSubsingleton
      (fun (q : Z7a S)
          (p : Z3n S) =>
        p.1 ∈ (system G).Z9z (Zbo S q.1)) qs) :
    Z2N S (qs.map Subtype.val) := by
  induction qs with
  | nil =>
      simp [Z2N]
  | cons q qs ih =>
      rw [List.nodup_cons] at hnodup
      rcases htail with ⟨htail, hpoints⟩
      change Z2N S (qs.map Subtype.val) ∧
        ∀ u ∈ qs.map Subtype.val, ∀ v ∈ qs.map Subtype.val,
          (((system G).Z9z (Zbo S q.1) ∩
            (system G).Z9z (Zbo S u)).Nonempty) →
          (((system G).Z9z (Zbo S q.1) ∩
            (system G).Z9z (Zbo S v)).Nonempty) →
          ((system G).Z9z (Zbo S q.1) ∩
            (system G).Z9z (Zbo S u)) =
            ((system G).Z9z (Zbo S q.1) ∩
              (system G).Z9z (Zbo S v))
      refine ⟨ih hnodup.2 htail, ?_⟩
      intro u hu v hv hqu hqv
      obtain ⟨u', hu', rfl⟩ := List.mem_map.1 hu
      obtain ⟨v', hv', rfl⟩ := List.mem_map.1 hv
      rcases hqu with ⟨p, hpq, hpu⟩
      rcases hqv with ⟨p', hpq', hpv⟩
      let pI : Z3n S :=
        Zz hpq
      let pI' : Z3n S :=
        Zz hpq'
      have hpIeq : pI = pI' := hpoints pI pI'
        (by simpa [pI] using hpq)
        (by simpa [pI'] using hpq')
        ⟨u', hu', by simpa [pI] using hpu⟩
        ⟨v', hv', by simpa [pI'] using hpv⟩
      have hpp' : p = p' := by
        simpa [pI, pI'] using congrArg Subtype.val hpIeq
      have hqu' : q.1 ≠ u'.1 := by
        intro hqeu
        apply hnodup.1
        have hqe : q = u' := Subtype.ext hqeu
        simpa [hqe] using hu'
      have hqv' : q.1 ≠ v'.1 := by
        intro hqev
        apply hnodup.1
        have hqe : q = v' := Subtype.ext hqev
        simpa [hqe] using hv'
      subst p'
      exact ZT hlin hqu' hqv'
        hpq hpu hpv
theorem Zu
    (S : Set (Edge G)) :
    Z3V S =
      SimpleGraph.bipartiteIncidenceGraph
        (fun (q : Z7a S)
            (p : Z3n S) =>
          p.1 ∈ (system G).Z9z (Zbo S q.1)) := by
  ext x y
  rcases x with q | p <;> rcases y with r | s <;>
    simp [Z3V, SimpleGraph.bipartiteIncidenceGraph,
      SimpleGraph.fromRel_adj]
theorem Z8
    {S : Set (Edge G)} (hS : S.Finite)
    (hlin : ((system G).Z96 S).Linear)
    (hacyclic : (Z3V S).IsAcyclic) :
    ∃ nodes : List (Node G),
      nodes.Nodup ∧
        (∀ e, e ∈ S → baseNode e ∈ nodes) ∧
        Z2N S nodes := by
  classical
  letI : Fintype (Z7a S) := activeBaseNodeIndexFintype hS
  letI : Fintype (Z3n S) :=
    activeBaseFiberSupportPointIndexFintype hS
  have hG :
      (SimpleGraph.bipartiteIncidenceGraph
        (fun (q : Z7a S)
            (p : Z3n S) =>
          p.1 ∈ (system G).Z9z (Zbo S q.1))).IsAcyclic := by
    rw [← Zu]
    exact hacyclic
  obtain ⟨qs, hnodup, hqs, htail⟩ :=
    hG.exists_finset_bipartiteTailPointSubsingletonOrder
      (fun (q : Z7a S)
          (p : Z3n S) =>
        p.1 ∈ (system G).Z9z (Zbo S q.1)) Finset.univ
  refine ⟨qs.map Subtype.val, hnodup.map Subtype.val_injective, ?_, ?_⟩
  · intro e he
    let q : Z7a S := ⟨baseNode e, ⟨e, he, rfl⟩⟩
    have hqmemFinset : q ∈ qs.toFinset := by
      rw [hqs]
      exact Finset.mem_univ q
    have hqmem : q ∈ qs := List.mem_toFinset.mp hqmemFinset
    change q.1 ∈ qs.map Subtype.val
    exact List.mem_map_of_mem hqmem
  · exact Z5
      hlin hnodup htail
theorem Z3
    {S : Set (Edge G)} (hS : S.Finite)
    (hlin : ((system G).Z96 S).Linear)
    (hacyclic : (Z3V S).IsAcyclic) :
    ∃ nodes : List (Node G),
      nodes.Nodup ∧
        (∀ e, e ∈ S → baseNode e ∈ nodes) ∧
        baseFiberAssemblyCompatible S nodes := by
  obtain ⟨nodes, hnodup, hcover, hcoherent⟩ :=
    Z8
      hS hlin hacyclic
  exact ⟨nodes, hnodup, hcover,
    Z2
      hlin hnodup hcoherent⟩
end SequenceLift
end P593
end
section
namespace P593
universe u
namespace SequenceLift
variable {V : Type u} {G : _root_.SimpleGraph V}
theorem baseFiberAssemblyCompatible.Z4I
    {S : Set (Edge G)} :
    ∀ nodes : List (Node G),
      baseFiberAssemblyCompatible S nodes →
        TripleSystem.BridgeBlock.RunningEdgeAssemblyGeometry (system G)
          (nodes.map (Zbo S)) := by
  intro nodes hcompatible
  induction nodes with
  | nil =>
      trivial
  | cons q nodes ih =>
      rcases hcompatible with ⟨htail, hEdges, hSupports⟩
      refine ⟨ih htail, ?_, ?_⟩
      · simpa [TripleSystem.Z9A] using hEdges
      · simpa [TripleSystem.Z9A] using hSupports
theorem Z2a
    {S : Set (Edge G)} (hS : S.Finite) (q : Node G)
    (hlinear : ((system G).Z96 S).Linear) :
    TripleSystem.FiniteLiftGenerated G
      ((system G).Z96 (Zbo S q)) := by
  classical
  obtain ⟨inst, hfactor, hiso⟩ :=
    Zb
      hS q hlinear
  letI : Fintype
      (baseLetterSubgraph G (baseLetter '' Zbo S q)).verts := inst
  rcases hfactor with ⟨factor⟩
  rcases hiso with ⟨iso⟩
  exact TripleSystem.FiniteLiftGenerated.ofIso
    (TripleSystem.FiniteLiftGenerated.Zb1 G factor) iso
theorem Za
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).Z96 S).Linear)
    (nodes : List (Node G))
    (hcover : TripleSystem.Z9A (nodes.map (Zbo S)) = S)
    (hcompatible : baseFiberAssemblyCompatible S nodes) :
    TripleSystem.FiniteLiftGenerated G ((system G).Z96 S) := by
  have hgeometry :
      TripleSystem.BridgeBlock.RunningEdgeAssemblyGeometry (system G)
        (nodes.map (Zbo S)) :=
    baseFiberAssemblyCompatible.Z4I nodes hcompatible
  have hgenerated :
      TripleSystem.FiniteLiftGenerated G
        ((system G).Z96
          (TripleSystem.Z9A (nodes.map (Zbo S)))) :=
    TripleSystem.FiniteLiftGenerated.Z4g
      G (system G) (nodes.map (Zbo S)) hgeometry (by
        intro T hT
        rw [List.mem_map] at hT
        rcases hT with ⟨q, _, rfl⟩
        exact Z2a hS q hlinear)
  rw [hcover] at hgenerated
  exact hgenerated
end SequenceLift
end P593
end
section
namespace P593
universe u
namespace SequenceLift
variable {V : Type u} {G : _root_.SimpleGraph V}
theorem Zd
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).Z96 S).Linear)
    (hacyclic : (Z3V S).IsAcyclic) :
    TripleSystem.FiniteLiftGenerated G ((system G).Z96 S) := by
  obtain ⟨nodes, _, hcover, hcompatible⟩ :=
    Z3
      hS hlinear hacyclic
  exact Za
    hS hlinear nodes
    (Z1A nodes hcover)
    hcompatible
end SequenceLift
end P593
end
section
namespace P593
universe u
namespace SequenceLift
variable {V : Type u} {G : _root_.SimpleGraph V}
theorem Z1j
    {S : Set (Edge G)} (hS : S.Finite)
    (hlinear : ((system G).Z96 S).Linear) :
    TripleSystem.FiniteLiftGenerated G ((system G).Z96 S) := by
  exact Zd
    hS hlinear
    (Zv hS hlinear)
end SequenceLift
end P593
end
section
namespace P593
namespace SimpleGraph
universe u
variable {V : Type u}
theorem Z2L
    (G : _root_.SimpleGraph V) (m : ℕ)
    (hcycle : ∀ ⦃v : V⦄ (c : G.Walk v v),
      c.IsCycle → c.length ≤ m → Even c.length) :
    ∀ ⦃v : V⦄ (w : G.Walk v v), w.length ≤ m → Even w.length := by
  intro v w hw
  induction hn : w.length using Nat.strongRec generalizing v with
  | ind n ih =>
    by_cases hc : w.IsCycle
    · simpa only [hn] using hcycle w hc hw
    by_cases hs : 3 ≤ w.length
    · have hnp : ¬ w.tail.IsPath := by
        intro hp
        exact hc
          (_root_.SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
            ⟨hp, hs⟩)
      cases w with
      | nil => simp at hs
      | @cons _ x _ hadj p =>
        have hnp' : ¬ p.IsPath := by
          simpa using hnp
        rw [_root_.SimpleGraph.Walk.isPath_iff_isSubwalk_imp_nil] at hnp'
        push Not at hnp'
        obtain ⟨z, q, hqsub, hqnil⟩ := hnp'
        obtain ⟨r₁, r₂, hp⟩ := hqsub
        let r : G.Walk v v := (r₁.append r₂).cons hadj
        have hlen :
            (_root_.SimpleGraph.Walk.cons hadj p).length =
              q.length + r.length := by
          simp [r, hp, _root_.SimpleGraph.Walk.length_append]
          omega
        have hq_lt :
            q.length < (_root_.SimpleGraph.Walk.cons hadj p).length := by
          simp only [_root_.SimpleGraph.Walk.length_cons]
          simp [hp, _root_.SimpleGraph.Walk.length_append]
          omega
        have hr_lt :
            r.length < (_root_.SimpleGraph.Walk.cons hadj p).length := by
          have hqpos : 0 < q.length :=
            Nat.pos_of_ne_zero
              (fun hzero =>
                hqnil
                  (_root_.SimpleGraph.Walk.length_eq_zero_iff.mp hzero))
          omega
        have hq_le : q.length ≤ m := by omega
        have hr_le : r.length ≤ m := by omega
        have hqeven : Even q.length :=
          ih q.length (by simpa only [hn] using hq_lt) q hq_le rfl
        have hreven : Even r.length :=
          ih r.length (by simpa only [hn] using hr_lt) r hr_le rfl
        rw [← hn, hlen]
        exact hqeven.add hreven
    · have hne1 : w.length ≠ 1 := by
        intro hwlen
        exact G.loopless.irrefl v (w.adj_of_length_eq_one hwlen)
      have hnsmall : n = 0 ∨ n = 2 := by omega
      rcases hnsmall with rfl | rfl <;> simp
theorem Z1h
    (G : _root_.SimpleGraph V) (m : ℕ)
    (hcycle : ∀ ⦃v : V⦄ (c : G.Walk v v),
      c.IsCycle → c.length ≤ m → ¬ Odd c.length) :
    ∀ ⦃v : V⦄ (w : G.Walk v v), w.length ≤ m → ¬ Odd w.length := by
  intro v w hw hodd
  have heven : Even w.length :=
    Z2L G m
      (fun _ c hc hcm => Nat.not_odd_iff_even.mp (hcycle c hc hcm)) w hw
  exact Nat.not_even_iff_odd.mpr hodd heven
end SimpleGraph
end P593
end
section
namespace P593
universe u w
namespace TripleSystem
variable {V : Type u}
def BergeCycleTraceTo (G : _root_.SimpleGraph V) (K : TripleSystem X I) : Prop :=
  ∀ ⦃z : X ⊕ I⦄ (c : K.levi.Walk z z), c.IsCycle →
    ∃ (v : V) (q : G.Walk v v), c.length = 2 * q.length
namespace BergeCycleTraceTo
theorem Z6G
    (G : _root_.SimpleGraph V) {K : TripleSystem X I}
    (htrace : BergeCycleTraceTo G K) (m : ℕ)
    (hodd : ∀ ⦃v : V⦄ (q : G.Walk v v), q.length ≤ m → ¬ Odd q.length) :
    ∀ ⦃z : X ⊕ I⦄ (c : K.levi.Walk z z), c.IsCycle →
      c.length ≤ 2 * m → 4 ∣ c.length := by
  intro z c hc hclen
  obtain ⟨v, q, hlen⟩ := htrace c hc
  have hqle : q.length ≤ m := by omega
  have hqeven : Even q.length := Nat.not_odd_iff_even.mp (hodd q hqle)
  obtain ⟨k, hk⟩ := hqeven
  use k
  omega
theorem ZbP (G : _root_.SimpleGraph V) (X : Type w) :
    BergeCycleTraceTo G (TripleSystem.ZbJ X) := by
  intro z c hc
  cases c with
  | nil => exact (hc.not_nil (by simp)).elim
  | @cons _ y _ h p =>
      rcases z with x | e
      · rcases y with y | e
        · exact (TripleSystem.Z5r
            (TripleSystem.ZbJ X) h).elim
        · exact e.down.elim
      · exact e.down.elim
theorem Z1P
    (G : _root_.SimpleGraph V) {X : Type w}
    {J : _root_.SimpleGraph X}
    (f : P593.SimpleGraph.NonInducedFactor J G) :
    BergeCycleTraceTo G (Z64 J) := by
  classical
  intro z c hc
  obtain ⟨x, hx⟩ : ∃ x : X,
      Sum.inl (PrivateVertexExpansion.core J x) ∈ c.support := by
    rcases z with (x | e) | e
    · exact ⟨x, c.start_mem_support⟩
    · exact (Z2O J c hc e
        c.start_mem_support).elim
    · obtain ⟨y, hy, hey⟩ :=
        _root_.SimpleGraph.adj_of_mem_walk_support c hc.not_nil
          c.start_mem_support
      rcases y with (x | d) | d
      · exact ⟨x, hy⟩
      · exact (Z2O J c hc d hy).elim
      · exact (Z65 (Z64 J) hey).elim
  let d := c.rotate (Sum.inl (PrivateVertexExpansion.core J x)) hx
  have hdcycle : d.IsCycle := hc.rotate hx
  have hdprivate : ∀ e : PrivateVertexExpansion.Edge J,
      Sum.inl (PrivateVertexExpansion.Za6 J e) ∉ d.support := by
    intro e he
    apply Z2O J c hc e
    exact (c.mem_support_rotate_iff
      (Sum.inl (PrivateVertexExpansion.core J x)) hx).mp he
  obtain ⟨q, hq⟩ :=
    ZY J d hdcycle.isTrail
      hdprivate
  refine ⟨f.vertex x, f.mapWalk q, ?_⟩
  dsimp only [d] at hq
  simp only [_root_.SimpleGraph.Walk.length_rotate] at hq
  simpa using hq
theorem Zam
    (G : _root_.SimpleGraph V)
    (F : TripleSystem X I) (H : TripleSystem Y J)
    (hF : BergeCycleTraceTo G F) (hH : BergeCycleTraceTo G H) :
    BergeCycleTraceTo G (F.Za7 H) := by
  intro z c hc
  let e := Z6T F H
  let c' := c.map e.toHom
  have hc' : c'.IsCycle := hc.map e.injective
  have hlength : c'.length = c.length :=
    _root_.SimpleGraph.Walk.length_map e.toHom c
  have left
      {z' : X ⊕ I}
      (d : (F.levi ⊕g H.levi).Walk (.inl z') (.inl z'))
      (hd : d.IsCycle) :
      ∃ (v : V) (q : G.Walk v v), d.length = 2 * q.length := by
    obtain ⟨zF, dF, hdF, hdlength⟩ :=
      Z5O F.levi H.levi d hd
    obtain ⟨v, q, hq⟩ := hF dF hdF
    exact ⟨v, q, hdlength.trans hq⟩
  have right
      {z' : Y ⊕ J}
      (d : (F.levi ⊕g H.levi).Walk (.inr z') (.inr z'))
      (hd : d.IsCycle) :
      ∃ (v : V) (q : G.Walk v v), d.length = 2 * q.length := by
    obtain ⟨zH, dH, hdH, hdlength⟩ :=
      Z61 F.levi H.levi d hd
    obtain ⟨v, q, hq⟩ := hH dH hdH
    exact ⟨v, q, hdlength.trans hq⟩
  rcases z with (x | y) | (i | j)
  · obtain ⟨v, q, hq⟩ := left c' hc'
    exact ⟨v, q, hlength.symm.trans hq⟩
  · obtain ⟨v, q, hq⟩ := right c' hc'
    exact ⟨v, q, hlength.symm.trans hq⟩
  · obtain ⟨v, q, hq⟩ := left c' hc'
    exact ⟨v, q, hlength.symm.trans hq⟩
  · obtain ⟨v, q, hq⟩ := right c' hc'
    exact ⟨v, q, hlength.symm.trans hq⟩
theorem amalgam
    (G : _root_.SimpleGraph V)
    (F₀ : TripleSystem X₀ I₀) (F₁ : TripleSystem X₁ I₁)
    (r₀ : X₀) (r₁ : X₁)
    (h₀ : BergeCycleTraceTo G F₀) (h₁ : BergeCycleTraceTo G F₁) :
    BergeCycleTraceTo G (OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁) := by
  intro z c hc
  let f₀ := OnePointAmalgamation.Z8t F₀ F₁ r₀ r₁
  let f₁ := OnePointAmalgamation.Z7Y F₀ F₁ r₀ r₁
  let A : Set (OnePointAmalgamation.Vertex r₀ r₁ ⊕
      OnePointAmalgamation.Edge I₀ I₁) := Set.range f₀
  let B : Set (OnePointAmalgamation.Vertex r₀ r₁ ⊕
      OnePointAmalgamation.Edge I₀ I₁) := Set.range f₁
  let root : OnePointAmalgamation.Vertex r₀ r₁ ⊕
      OnePointAmalgamation.Edge I₀ I₁ :=
    .inl (OnePointAmalgamation.left r₀ r₁ r₀)
  have hrootA : root ∈ A := by
    exact ⟨.inl r₀, rfl⟩
  have hrootB : root ∈ B := by
    refine ⟨.inl r₁, ?_⟩
    exact congrArg Sum.inl (OnePointAmalgamation.root_eq r₀ r₁).symm
  have hinter : A ∩ B ⊆ {root} := by
    rintro w ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
    rcases a with x | e <;> rcases b with y | f
    · change Sum.inl (OnePointAmalgamation.right r₀ r₁ y) = Sum.inl (OnePointAmalgamation.left r₀ r₁ x) at hb
      have hx := (OnePointAmalgamation.Z8u r₀ r₁ y x).mp (Sum.inl.inj hb)
      change Sum.inl (OnePointAmalgamation.left r₀ r₁ x) = Sum.inl (OnePointAmalgamation.left r₀ r₁ r₀)
      rw [hx.2]
    · change Sum.inr (Sum.inr f) = Sum.inl (OnePointAmalgamation.left r₀ r₁ x) at hb
      cases hb
    · change Sum.inl (OnePointAmalgamation.right r₀ r₁ y) = Sum.inr (Sum.inl e) at hb
      cases hb
    · change Sum.inr (Sum.inr f) = Sum.inr (Sum.inl e) at hb
      cases Sum.inr.inj hb
  have hadj : ∀ ⦃a b⦄,
      (OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁).levi.Adj a b →
      (a ∈ A ∧ b ∈ A) ∨ (a ∈ B ∧ b ∈ B) := by
    intro a b hab
    rcases a with q | (e | e)
    · rcases b with q' | (f | f)
      · exact ((OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁).Z5r
          hab).elim
      · have hi := (OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁).Z7d.mp
          hab
        change q ∈ OnePointAmalgamation.left r₀ r₁ '' F₀.edgeSet f at hi
        rcases hi with ⟨x, hx, rfl⟩
        exact Or.inl ⟨⟨.inl x, rfl⟩, ⟨.inr f, rfl⟩⟩
      · have hi := (OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁).Z7d.mp
          hab
        change q ∈ OnePointAmalgamation.right r₀ r₁ '' F₁.edgeSet f at hi
        rcases hi with ⟨y, hy, rfl⟩
        exact Or.inr ⟨⟨.inl y, rfl⟩, ⟨.inr f, rfl⟩⟩
    · rcases b with q' | (f | f)
      · have hi := (OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁).Z7n.mp
          hab
        change q' ∈ OnePointAmalgamation.left r₀ r₁ '' F₀.edgeSet e at hi
        rcases hi with ⟨x, hx, rfl⟩
        exact Or.inl ⟨⟨.inr e, rfl⟩, ⟨.inl x, rfl⟩⟩
      · exact ((OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁).Z65
          hab).elim
      · exact ((OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁).Z65
          hab).elim
    · rcases b with q' | (f | f)
      · have hi := (OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁).Z7n.mp
          hab
        change q' ∈ OnePointAmalgamation.right r₀ r₁ '' F₁.edgeSet e at hi
        rcases hi with ⟨y, hy, rfl⟩
        exact Or.inr ⟨⟨.inr e, rfl⟩, ⟨.inl y, rfl⟩⟩
      · exact ((OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁).Z65
          hab).elim
      · exact ((OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁).Z65
          hab).elim
  rcases OnePointAmalgamation.Z3u
      (OnePointAmalgamation.amalgam F₀ F₁ r₀ r₁).levi A B root
      hrootA hrootB hinter hadj c hc with hsupp | hsupp
  · obtain ⟨x, d, hd, hlength⟩ :=
      OnePointAmalgamation.Z4a f₀ c hc hsupp
    obtain ⟨v, q, hq⟩ := h₀ d hd
    exact ⟨v, q, hlength.trans hq⟩
  · obtain ⟨y, d, hd, hlength⟩ :=
      OnePointAmalgamation.Z4a f₁ c hc hsupp
    obtain ⟨v, q, hq⟩ := h₁ d hd
    exact ⟨v, q, hlength.trans hq⟩
theorem ofIso
    (G : _root_.SimpleGraph V)
    {F : TripleSystem X I} {H : TripleSystem Y J}
    (hF : BergeCycleTraceTo G F) (f : TripleSystem.Iso F H) :
    BergeCycleTraceTo G H := by
  intro z c hc
  let e := TripleSystem.Iso.leviIso f
  let d := c.map e.symm.toHom
  have hd : d.IsCycle := hc.map e.symm.injective
  obtain ⟨v, q, hq⟩ := hF d hd
  refine ⟨v, q, ?_⟩
  have hlength : d.length = c.length :=
    _root_.SimpleGraph.Walk.length_map e.symm.toHom c
  exact hlength.symm.trans hq
end BergeCycleTraceTo
namespace FiniteLiftGenerated
theorem Z8y
    (G : _root_.SimpleGraph V)
    {X I : Type w} {K : TripleSystem X I}
    (hK : FiniteLiftGenerated G K) :
    BergeCycleTraceTo G K := by
  induction hK with
  | ofEdgeless X =>
      exact BergeCycleTraceTo.ZbP G X
  | ofFactorExpansion f =>
      exact BergeCycleTraceTo.Z1P G f
  | disjointUnion hF hH ihF ihH =>
      exact BergeCycleTraceTo.Zam G _ _ ihF ihH
  | amalgam hF hH x y ihF ihH =>
      exact BergeCycleTraceTo.amalgam G _ _ x y ihF ihH
  | ofIso hF f ihF =>
      exact BergeCycleTraceTo.ofIso G ihF f
end FiniteLiftGenerated
end TripleSystem
end P593
end
section
namespace P593
universe u
namespace SequenceLift
variable {V : Type u} {G : _root_.SimpleGraph V}
variable {X I : Type u} {F : TripleSystem X I}
theorem Zl
    [Fintype I]
    (f : F.Embedding (system G)) (hlinear : F.Linear) :
    TripleSystem.FiniteLiftGenerated G F.isolatedReduction := by
  have htrace :=
    TripleSystem.Embedding.Z1Y f hlinear
  exact TripleSystem.FiniteLiftGenerated.ofIso
    (Z1j htrace.1 htrace.2.1)
    (Classical.choice htrace.2.2).symm
end SequenceLift
end P593
end
section
namespace P593
universe u
namespace SequenceLift
variable {V : Type u} {G : _root_.SimpleGraph V}
variable {X I : Type u} {F : TripleSystem X I}
theorem Zp
    [Fintype I]
    (f : F.Embedding (system G)) (hlinear : F.Linear) :
    F.isolatedReduction.BridgeAtEveryEdge := by
  exact TripleSystem.FiniteLiftGenerated.Z8z G
    (Zl f hlinear)
theorem Ze
    [Fintype I]
    (hlinear : F.Linear)
    (hno : Not F.isolatedReduction.BridgeAtEveryEdge) :
    Not (Nonempty (F.Embedding (system G))) := by
  intro h
  cases h with
  | intro f =>
      exact hno (Zp f hlinear)
end SequenceLift
end P593
end
section
namespace P593
open scoped Cardinal Ordinal
universe u
namespace SequenceLift
variable {V : Type u} {G : _root_.SimpleGraph V}
structure MonoEdgeAt (c : Point G → ℕ) (q : Node G) where
  x : V
  y : V
  adj : G.Adj x y
  color_eq : c (q, x) = c (q, y)
theorem Z7D
    (hG : ¬ Nonempty (G.Coloring ℕ))
    (c : Point G → ℕ) (q : Node G) :
    Nonempty (MonoEdgeAt c q) := by
  by_contra hmono
  apply hG
  refine ⟨_root_.SimpleGraph.Coloring.mk (fun x ↦ c (q, x)) ?_⟩
  intro x y hxy hcolor
  exact hmono ⟨⟨x, y, hxy, hcolor⟩⟩
noncomputable def chosenMonoEdge
    (hG : ¬ Nonempty (G.Coloring ℕ))
    (c : Point G → ℕ) (q : Node G) : MonoEdgeAt c q :=
  Classical.choice (Z7D hG c q)
theorem Z5D
    (hG : ¬ Nonempty (G.Coloring ℕ))
    (c : Point G → ℕ) :
    ¬ (system G).IsProperColoring c := by
  intro hc
  let M : (q : Node G) → MonoEdgeAt c q :=
    fun q ↦ chosenMonoEdge hG c q
  let pick : Node G → ZbG G := fun q ↦ Zb9 (M q).adj
  let a : Index → ZbG G := branchLetter pick
  let q : Index → Node G := Zbe a
  let k : Index → ℕ := fun α ↦ c (q α, (M (q α)).x)
  have hk_lt : ∀ {α β : Index}, α < β → k α ≠ k β := by
    intro α β hαβ hk
    have ha : a α = Zb9 (M (q α)).adj := by
      simpa [a, q, pick] using Z9u pick α
    have hext : (q α).ExtendsBy (Zb9 (M (q α)).adj) (q β) := by
      rw [← ha]
      exact Z71 a hαβ
    let e : Edge G :=
      mkEdge (q α) (q β) (M (q α)).x (M (q α)).y
        (M (q β)).x (M (q α)).adj hext
    rcases hc e with ⟨p, hp, p', hp', hne⟩
    have hmono : ∀ {w : Point G}, (system G).Inc w e → c w = k α := by
      intro w hw
      change (system G).Inc w
        (mkEdge (q α) (q β) (M (q α)).x (M (q α)).y
          (M (q β)).x (M (q α)).adj hext) at hw
      rcases Z9C.mp hw with h | h | h
      · subst w
        rfl
      · subst w
        exact (M (q α)).color_eq.symm
      · subst w
        exact hk.symm
    exact hne ((hmono hp).trans (hmono hp').symm)
  have hk_injective : Function.Injective k := by
    intro α β hab
    rcases lt_trichotomy α β with hlt | heq | hgt
    · exact (hk_lt hlt hab).elim
    · exact heq
    · exact (hk_lt hgt hab.symm).elim
  let ku : Index → ULift.{u} ℕ := fun α ↦ ULift.up (k α)
  have hku_injective : Function.Injective ku :=
    fun α β h ↦ hk_injective (congrArg ULift.down h)
  have hcard : #(Index : Type u) ≤ #(ULift.{u} ℕ) :=
    Cardinal.mk_le_of_injective hku_injective
  have haleph : (ℵ₁ : Cardinal.{u}) ≤ (ℵ₀ : Cardinal.{u}) := by
    simp [Index] at hcard
  exact Cardinal.aleph0_lt_aleph_one.2 haleph
theorem Z4B
    (hG : ¬ Nonempty (G.Coloring ℕ)) :
    ℵ₀ < (system G).chromaticCardinal := by
  by_contra hnot
  have hle : (system G).chromaticCardinal ≤ ℵ₀ := le_of_not_gt hnot
  have hle' : (system G).chromaticCardinal ≤ #(ULift.{u} ℕ) := by
    simpa using hle
  obtain ⟨c, hc⟩ :=
    ((system G).Z4y (C := ULift.{u} ℕ)).mp hle'
  let d : Point G → ℕ := fun p ↦ (c p).down
  apply Z5D hG d
  intro e
  rcases hc e with ⟨x, hx, y, hy, hxy⟩
  refine ⟨x, hx, y, hy, ?_⟩
  intro hdown
  apply hxy
  exact ULift.ext _ _ hdown
end SequenceLift
end P593
end
section
namespace P593
universe u
namespace SequenceLift
variable {V : Type u} {G : _root_.SimpleGraph V}
variable {X I : Type u} {F : TripleSystem X I}
theorem Z6
    [Fintype I]
    (hG : ¬ Nonempty (G.Coloring ℕ))
    (hlinear : F.Linear)
    (hno : ¬ F.isolatedReduction.BridgeAtEveryEdge) :
    ¬ F.IsObligatory := by
  classical
  intro hF
  exact Ze
    hlinear hno
    (hF _ _ (system G) (Z4B hG))
end SequenceLift
end P593
end
section
namespace P593
open scoped Cardinal
universe u
namespace SequenceLift
abbrev MissingBridgeHostVertex : Type u :=
  ULift.{u} TripleSystem.TriangleHost.ErdosRadoCarrier
abbrev missingBridgeHost : _root_.SimpleGraph MissingBridgeHostVertex.{u} :=
  _root_.SimpleGraph.completeGraph MissingBridgeHostVertex.{u}
theorem not_nonempty_coloring_missingBridgeHost :
    ¬ Nonempty (missingBridgeHost.{u}.Coloring ℕ) := by
  rintro ⟨C⟩
  have hC : Function.Injective C := by
    simpa only [Function.comp_id] using
      C.injective_comp_of_pairwise_adj (f := id) (by
        intro x y hxy
        simpa using hxy)
  let colorLift : MissingBridgeHostVertex.{u} → ULift.{u} ℕ :=
    fun x ↦ ULift.up (C x)
  have hcolorLift : Function.Injective colorLift := by
    intro x y hxy
    exact hC (congrArg ULift.down hxy)
  have hcard : Cardinal.mk MissingBridgeHostVertex.{u} ≤
      Cardinal.mk (ULift.{u} ℕ) :=
    Cardinal.mk_le_of_injective hcolorLift
  have hcard' : Order.succ (Cardinal.continuum : Cardinal.{u}) ≤ ℵ₀ := by
    simpa [MissingBridgeHostVertex,
      TripleSystem.TriangleHost.Z7x, Cardinal.mk_nat] using hcard
  have hsucc_le_continuum :
      Order.succ (Cardinal.continuum : Cardinal.{u}) ≤ Cardinal.continuum :=
    hcard'.trans Cardinal.aleph0_le_continuum
  exact (Order.lt_succ (Cardinal.continuum : Cardinal.{u})).2
    hsucc_le_continuum
end SequenceLift
namespace TripleSystem
variable {X I : Type u}
theorem Z7
    (F : TripleSystem X I) [Fintype I]
    (hlinear : F.Linear)
    (hno : ¬ F.isolatedReduction.BridgeAtEveryEdge) :
    ¬ F.IsObligatory := by
  exact SequenceLift.Z6
    (G := SequenceLift.missingBridgeHost.{u})
    SequenceLift.not_nonempty_coloring_missingBridgeHost.{u} hlinear hno
end TripleSystem
end P593
end
section
namespace P593
universe u
namespace ShiftGraph
variable (κ : Type u) [LinearOrder κ]
abbrev Tuple (r : ℕ) := {f : Fin r → κ // StrictMono f}
def Shift {r : ℕ} (x y : Tuple κ r) : Prop :=
  ∃ z : Tuple κ (r + 1),
    (∀ i : Fin r, x.1 i = z.1 i.castSucc) ∧
    (∀ i : Fin r, y.1 i = z.1 i.succ)
def graph (r : ℕ) : _root_.SimpleGraph (Tuple κ r) :=
  _root_.SimpleGraph.fromRel (Shift κ)
theorem ZaY {r : ℕ} (hr : 0 < r) {x y : Tuple κ r}
    (h : Shift κ x y) : x ≠ y := by
  obtain ⟨ z, hx, hy ⟩ := h;
  contrapose! hr;
  rcases r with ( _ | r ) <;> simp_all +decide [ Fin.forall_fin_succ, StrictMono ];
  exact absurd hx.1 ( ne_of_gt ( z.2 ( by simp +decide ) ) )
theorem ZaJ {r : ℕ} (hr : 0 < r) {x y : Tuple κ r}
    (h : Shift κ x y) : (graph κ r).Adj x y := by
  apply (ZaY κ hr h) |> fun h_ne => by tauto;
theorem Z67 {r : ℕ} (hr : 0 < r) {x y : Tuple κ r} :
    (graph κ r).Adj x y ↔ Shift κ x y ∨ Shift κ y x := by
  simp +decide [ graph ];
  rintro ( h | h ) <;> [ exact ZaY κ hr h; exact ZaY κ hr h |> Ne.symm ]
theorem Z52 :
    graph κ 1 = _root_.SimpleGraph.completeGraph (Tuple κ 1) := by
  ext x y;
  simp +decide [ graph, SimpleGraph.fromRel_adj ];
  intro hxy; cases lt_or_gt_of_ne ( show x.1 0 ≠ y.1 0 from by contrapose! hxy; ext i; fin_cases i; aesop ) <;> [ left; right ] <;> use ⟨ Fin.cons ( if x.1 0 < y.1 0 then x.1 0 else y.1 0 ) ( if x.1 0 < y.1 0 then y.1 else x.1 ), ?_ ⟩ <;> simp +decide [ *, Fin.forall_fin_succ ] ;
  · simp +decide [ StrictMono, Fin.forall_fin_succ ];
    assumption;
  · grind;
  · simp +decide [ *, StrictMono, Fin.forall_fin_succ ];
    split_ifs <;> simp_all +decide [ lt_asymm ]
end ShiftGraph
end P593
end
section
namespace P593
open scoped Cardinal
universe u v
namespace ShiftGraph
variable {κ : Type u} [LinearOrder κ]
def init {r : ℕ} (z : Tuple κ (r + 1)) : Tuple κ r :=
  ⟨fun i ↦ z.1 i.castSucc, z.2.comp Fin.strictMono_castSucc⟩
def tail {r : ℕ} (z : Tuple κ (r + 1)) : Tuple κ r :=
  ⟨fun i ↦ z.1 i.succ, z.2.comp Fin.strictMono_succ⟩
@[simp]
theorem Zbl {r : ℕ} (z : Tuple κ (r + 1)) (i : Fin r) :
    (init z).1 i = z.1 i.castSucc := rfl
@[simp]
theorem Zbm {r : ℕ} (z : Tuple κ (r + 1)) (i : Fin r) :
    (tail z).1 i = z.1 i.succ := rfl
theorem Z4X {r : ℕ} {x y : Tuple κ r} :
    Shift κ x y ↔ ∃ z : Tuple κ (r + 1), init z = x ∧ tail z = y := by
  constructor
  · rintro ⟨z, hx, hy⟩
    refine ⟨z, Subtype.ext ?_, Subtype.ext ?_⟩
    · funext i
      exact (hx i).symm
    · funext i
      exact (hy i).symm
  · rintro ⟨z, rfl, rfl⟩
    exact ⟨z, fun _ ↦ rfl, fun _ ↦ rfl⟩
def glue {r : ℕ} (hr : 0 < r) (z w : Tuple κ (r + 1))
    (h : tail z = init w) : Tuple κ (r + 2) :=
  ⟨Fin.cons (z.1 0) w.1, by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · have hz := (Fin.strictMono_iff_lt_succ.mp z.2) (⟨0, hr⟩ : Fin r)
      have hover := congrArg (fun q : Tuple κ r ↦ q.1 (⟨0, hr⟩ : Fin r)) h
      simpa [tail, init] using hz.trans_eq hover
    · simpa using (Fin.strictMono_iff_lt_succ.mp w.2) j⟩
@[simp]
theorem ZbA {r : ℕ} (hr : 0 < r) (z w : Tuple κ (r + 1))
    (h : tail z = init w) : init (glue hr z w h) = z := by
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rfl
  · have hover := congrArg (fun q : Tuple κ r ↦ q.1 j) h
    simpa [glue, tail, init] using hover.symm
@[simp]
theorem ZbB {r : ℕ} (hr : 0 < r) (z w : Tuple κ (r + 1))
    (h : tail z = init w) : tail (glue hr z w h) = w := by
  apply Subtype.ext
  funext i
  rfl
theorem Z6F {r : ℕ} (hr : 0 < r) {z w : Tuple κ (r + 1)}
    (h : tail z = init w) : Shift κ z w := by
  exact (Z4X).2 ⟨glue hr z w h, ZbA hr z w h, ZbB hr z w h⟩
def Z9g {C : Type v} {r : ℕ}
    (c : (graph κ (r + 1)).Coloring C) (x : Tuple κ r) : Set C :=
  {a | ∃ z : Tuple κ (r + 1), init z = x ∧ c z = a}
theorem Z4D {C : Type v} {r : ℕ} (hr : 0 < r)
    (c : (graph κ (r + 1)).Coloring C) {x y : Tuple κ r} (hxy : Shift κ x y) :
    Z9g c x ≠ Z9g c y := by
  obtain ⟨z, hz_init, hz_tail⟩ := (Z4X).1 hxy
  intro heq
  have hz_mem : c z ∈ Z9g c x := ⟨z, hz_init, rfl⟩
  rw [heq] at hz_mem
  obtain ⟨w, hw_init, hcw⟩ := hz_mem
  have hzw : Shift κ z w := Z6F hr (hz_tail.trans hw_init.symm)
  exact c.valid (ZaJ κ (Nat.succ_pos r) hzw) hcw.symm
noncomputable def lowerColoring {C : Type v} {r : ℕ} (hr : 0 < r)
    (c : (graph κ (r + 1)).Coloring C) : (graph κ r).Coloring (Set C) :=
  SimpleGraph.Coloring.mk (Z9g c) fun {x y} hxy ↦ by
    rw [Z67 κ hr] at hxy
    rcases hxy with hxy | hyx
    · exact Z4D hr c hxy
    · exact (Z4D hr c hyx).symm
theorem Z6d {C : Type v}
    (c : (graph κ 1).Coloring C) : Function.Injective c := by
  intro x y hxy
  by_contra hne
  exact c.valid (by rw [Z52]; simpa) hxy
def ZaV (C : Type v) : ℕ → Type v
  | 0 => C
  | n + 1 => ZaV (Set C) n
noncomputable def lowerToOne {C : Type v} :
    ∀ n : ℕ, (graph κ (n + 1)).Coloring C →
      (graph κ 1).Coloring (ZaV C n)
  | 0, c => c
  | n + 1, c => lowerToOne n (lowerColoring (Nat.succ_pos n) c)
theorem Z8W (C : Type v) (n : ℕ) :
    ZaV C (n + 1) = Set (ZaV C n) := by
  induction n generalizing C with
  | zero => rfl
  | succ n ih => simpa only [ZaV] using ih (Set C)
theorem Z85 (n : ℕ) :
    #(ZaV ℕ n) = ℶ_ (n : Ordinal) := by
  induction n with
  | zero => simp [ZaV, Cardinal.beth_zero]
  | succ n ih =>
    rw [Z8W, Cardinal.mk_set, ih, ← Cardinal.beth_succ]
    change ℶ_ ((n : Ordinal) + 1) = ℶ_ (((n + 1 : ℕ) : Ordinal))
    rw [Nat.cast_add_one]
def Zal : Tuple κ 1 ≃ κ where
  toFun x := x.1 0
  invFun x := ⟨fun _ => x, by simp [StrictMono]⟩
  left_inv x := by ext i; fin_cases i; rfl
  right_inv _ := rfl
theorem Z2J {r : ℕ} (hr : 0 < r)
    (hκ : ℶ_ ((r - 1 : ℕ) : Ordinal) < #κ) :
    ¬ Nonempty ((graph κ r).Coloring ℕ) := by
  rintro ⟨c⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have hinj : Function.Injective (lowerToOne n c) := Z6d _
  have hle0 := Cardinal.lift_mk_le_lift_mk_of_injective hinj
  have hle : #κ ≤ ℶ_ (n : Ordinal) := by
    rw [Z85, Cardinal.lift_beth, Ordinal.lift_natCast] at hle0
    simpa only [Cardinal.lift_uzero, Cardinal.mk_congr Zal] using hle0
  rw [Nat.succ_sub_one] at hκ
  exact (not_lt_of_ge hle) hκ
end ShiftGraph
end P593
end
section
namespace P593
universe u
namespace ShiftGraph
variable (κ : Type u) [LinearOrder κ]
def Zbt {r : ℕ} (x : Tuple κ (r + 1)) : Tuple κ r :=
  ⟨fun i => x.1 i.castSucc, fun _ _ hij => x.2 (Fin.castSucc_lt_castSucc_iff.mpr hij)⟩
theorem Z5N {r : ℕ} {x y : Tuple κ (r + 1)}
    (h : Shift κ x y) : x.1 0 < y.1 0 := by
  obtain ⟨z, hx, hy⟩ := h
  rw [hx 0, hy 0]
  exact z.2 (by simp)
theorem ZaG {r : ℕ} (_hr : 0 < r) {x y : Tuple κ (r + 1)}
    (h : Shift κ x y) : Shift κ (Zbt κ x) (Zbt κ y) := by
  obtain ⟨z, hx, hy⟩ := h
  refine ⟨x, ?_, ?_⟩
  · intro i
    rfl
  · intro i
    change y.1 i.castSucc = x.1 i.succ
    rw [hy i.castSucc, hx i.succ]
    rfl
def Zby {r : ℕ} (hr : 0 < r) : graph κ (r + 1) →g graph κ r where
  toFun := Zbt κ
  map_rel' := by
    intro x y hxy
    rw [Z67 κ (Nat.succ_pos r)] at hxy
    rw [Z67 κ hr]
    exact hxy.imp (ZaG κ hr) (ZaG κ hr)
theorem Z4J {r : ℕ} {x y z : Tuple κ (r + 1)}
    (hxy : Shift κ x y) (hxz : Shift κ x z) : Zbt κ y = Zbt κ z := by
  obtain ⟨w, hxw, hyw⟩ := hxy
  obtain ⟨w', hxw', hzw'⟩ := hxz
  ext i
  change y.1 i.castSucc = z.1 i.castSucc
  rw [hyw i.castSucc, hzw' i.castSucc]
  have hi : i.castSucc.succ = i.succ.castSucc := Fin.ext rfl
  rw [hi, ← hxw i.succ, ← hxw' i.succ]
theorem Z7E :
    ∀ (r : ℕ) {v : Tuple κ r} (c : (graph κ r).Walk v v),
      c.IsCycle → Odd c.length → 2 * r + 1 ≤ c.length := by
  intro r
  induction r with
  | zero =>
      intro v c hc _
      exact Nat.le_trans (by omega) hc.three_le_length
  | succ r ih =>
      intro v c hc hodd
      by_cases hr : r = 0
      · subst r
        exact hc.three_le_length
      · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
        by_contra hbound
        have hclt : c.length < 2 * (r + 1) + 1 := by omega
        classical
        obtain ⟨x, hxc, hxmin⟩ :=
          Finset.exists_min_image c.support.toFinset (fun t => t.1 0)
            (by simp)
        have hxsupp : x ∈ c.support := by simpa using hxc
        let d := c.rotate x hxsupp
        have hdcycle : d.IsCycle := hc.rotate hxsupp
        have hdlen : d.length = c.length := c.length_rotate x hxsupp
        have hmin : ∀ y ∈ d.support, x.1 0 ≤ y.1 0 := by
          intro y hy
          apply hxmin y
          simpa [d, c.mem_support_rotate_iff x hxsupp] using hy
        have hdnotnil : ¬ d.Nil := hdcycle.not_nil
        let y := d.snd
        let p := d.tail
        have hpnotnil : ¬ p.Nil := by
          intro hp
          have hpzero : p.length = 0 :=
            SimpleGraph.Walk.length_eq_zero_iff.mpr hp
          have htail := d.length_tail_add_one hdnotnil
          have hthree := hdcycle.three_le_length
          simp only [p] at hpzero
          omega
        have hadj : (graph κ (r + 1)).Adj x y := by
          simpa [y, d] using d.adj_snd hdnotnil
        have hxy : Shift κ x y := by
          rw [Z67 κ (Nat.succ_pos r)] at hadj
          rcases hadj with hxy | hyx
          · exact hxy
          · have hylt := Z5N κ hyx
            have hy_mem : y ∈ d.support := by
              exact List.mem_of_mem_tail (by simpa [y, p] using d.snd_mem_tail_support hdnotnil)
            have hymin : x.1 0 ≤ y.1 0 := hmin y hy_mem
            exact (not_lt_of_ge hymin hylt).elim
        have hxp : Shift κ x p.penultimate := by
          have hadj' := p.adj_penultimate hpnotnil
          rw [Z67 κ (Nat.succ_pos r)] at hadj'
          rcases hadj' with hpx | hxp
          · have hplt := Z5N κ hpx
            have hp_mem_p : p.penultimate ∈ p.support :=
              List.mem_of_mem_dropLast (p.penultimate_mem_dropLast_support hpnotnil)
            have hp_mem_d : p.penultimate ∈ d.support := by
              apply List.mem_of_mem_tail
              rw [← d.support_tail_of_not_nil hdnotnil]
              simpa [p] using hp_mem_p
            have hpmin : x.1 0 ≤ p.penultimate.1 0 := hmin _ hp_mem_d
            exact (not_lt_of_ge hpmin hplt).elim
          · exact hxp
        have hpref : Zbt κ y = Zbt κ p.penultimate :=
          Z4J κ hxy hxp
        let q : (graph κ r).Walk (Zbt κ y) (Zbt κ y) :=
          (p.dropLast.map (Zby κ hrpos)).copy rfl hpref.symm
        have hqlen : q.length = c.length - 2 := by
          have htail := d.length_tail_add_one hdnotnil
          calc
            q.length = (p.dropLast.map (Zby κ hrpos)).length :=
              SimpleGraph.Walk.length_copy _ _ _
            _ = p.dropLast.length := SimpleGraph.Walk.length_map _ _
            _ = c.length - 2 := by
              rw [SimpleGraph.Walk.length_dropLast]
              simp only [p] at htail ⊢
              omega
        have hqodd : Odd q.length := by
          obtain ⟨k, hk⟩ := hodd
          refine ⟨k - 1, ?_⟩
          rw [hqlen]
          have := hc.three_le_length
          omega
        exact (P593.SimpleGraph.Z1h
          (graph κ r) (2 * r)
          (fun {_} e he hle heodd => by
            have := ih e he heodd
            omega)
          q (by rw [hqlen]; omega)) hqodd
theorem Z86 {r m : ℕ} (hm : m < 2 * r + 1) :
    ∀ ⦃v : Tuple κ r⦄ (c : (graph κ r).Walk v v),
      c.IsCycle → c.length ≤ m → ¬ Odd c.length := by
  intro v c hc hcm hodd
  have := Z7E κ r c hc hodd
  omega
theorem Z5R {r m : ℕ} (hm : m < 2 * r + 1) :
    ∀ ⦃v : Tuple κ r⦄ (w : (graph κ r).Walk v v),
      w.length ≤ m → ¬ Odd w.length :=
  P593.SimpleGraph.Z1h
    (graph κ r) m (Z86 κ hm)
end ShiftGraph
end P593
end
section
namespace P593
open scoped Cardinal
namespace ShiftGraph
universe u
def Zbw (r : ℕ) : Type u :=
  (Order.succ (ℶ_ ((r - 1 : ℕ) : Ordinal.{u}))).ord.ToType
noncomputable instance (r : ℕ) : LinearOrder (Zbw r) :=
  linearOrder_toType _
noncomputable def hostGraph (m : ℕ) : SimpleGraph (Tuple (Zbw (m + 1)) (m + 1)) :=
  graph (Zbw (m + 1)) (m + 1)
theorem Z3f (m : ℕ) :
    ∀ ⦃v⦄ (w : (hostGraph m).Walk v v), w.length ≤ m → ¬ Odd w.length := by
  exact Z5R (Zbw (m + 1)) (by omega)
theorem Z2Q (m : ℕ) :
    ¬ Nonempty ((hostGraph m).Coloring ℕ) := by
  apply Z2J (Nat.succ_pos m)
  simp only [Zbw, Cardinal.mk_ord_toType]
  exact Order.lt_succ _
end ShiftGraph
end P593
end
section
namespace P593
universe u
namespace SequenceLift
variable {X I : Type u} {F : TripleSystem X I}
theorem ZU
    [Fintype I] (hlinear : F.Linear)
    {z : F.NonIsolatedPoint ⊕ I}
    (c : F.isolatedReduction.levi.Walk z z) (hc : c.IsCycle)
    (hodd : ¬ 4 ∣ c.length) :
    ¬ Nonempty (F.Embedding (system (ShiftGraph.hostGraph.{u} c.length))) := by
  rintro ⟨f⟩
  have hgenerated :=
    Zl f hlinear
  have htrace := TripleSystem.FiniteLiftGenerated.Z8y
    (ShiftGraph.hostGraph.{u} c.length) hgenerated
  have heven := TripleSystem.BergeCycleTraceTo.Z6G
    (ShiftGraph.hostGraph.{u} c.length) htrace c.length
    (ShiftGraph.Z3f c.length)
    c hc (by omega)
  exact hodd heven
theorem Z1
    (F : TripleSystem X I) [Fintype I]
    (hlinear : F.Linear)
    (hno : ¬ F.isolatedReduction.EvenBergeCycles) :
    ¬ F.IsObligatory := by
  classical
  rw [TripleSystem.EvenBergeCycles] at hno
  push Not at hno
  obtain ⟨z, c, hc, hodd⟩ := hno
  intro hF
  have hembedding := hF _ _
    (system (ShiftGraph.hostGraph.{u} c.length))
    (Z4B
      (ShiftGraph.Z2Q c.length))
  exact ZU hlinear c hc hodd
    hembedding
end SequenceLift
end P593
end
section
namespace P593
universe u
namespace TripleSystem
theorem isObligatory_iff_isolatedReduction_intrinsic
    {V E : Type u} (F : TripleSystem V E) [Fintype V] [Fintype E] :
    F.IsObligatory ↔ F.isolatedReduction.Intrinsic := by
  constructor
  · intro hF
    have hlinear : F.Linear := by
      by_contra hn
      exact (Z49 F hn) hF
    refine ⟨F.Z5z hlinear, ?_, ?_⟩
    · by_contra hbridge
      exact (Z7
        F hlinear hbridge) hF
    · by_contra hberge
      exact (SequenceLift.Z1
        F hlinear hberge) hF
  · exact Z25 F
end TripleSystem
end P593
end
namespace P593
open Cardinal
universe u v w
noncomputable section

def fromUniform {V : Type u} (H : UniformHypergraph V 3) :
    TripleSystem V H.edgeSet where
  Inc x e := x ∈ e.val
  edge_ncard e := by
    have h := H.uniform e.val e.property
    change e.val.ncard = 3
    simp [Set.ncard_def, h]
  simple := by
    intro e f h
    exact Subtype.ext h

def toUniform {V : Type u} {E : Type v} (F : TripleSystem V E) :
    UniformHypergraph V 3 where
  toHypergraph :=
    { vertexSet := Set.univ
      edgeSet := Set.range F.edgeSet
      subset_vertexSet_of_mem_edgeSet' := fun {_} _ => Set.subset_univ _ }
  vertexSet_eq_univ := rfl
  uniform := by
    rintro _ ⟨e, rfl⟩
    have he := F.Zaa e
    have hf : (F.edgeSet e).Finite := Set.finite_of_ncard_ne_zero (by simp [he])
    simp only [← hf.cast_ncard_eq, he]

theorem coloring {V : Type u} {E : Type v} (F : TripleSystem V E)
    {C : Type w} (c : V → C) :
    (toUniform F).IsProperColoring c ↔ F.IsProperColoring c := by
  constructor
  · intro h e
    exact h (F.edgeSet e) ⟨e, rfl⟩
  · rintro h _ ⟨e, rfl⟩
    exact h e

theorem nColorable {V : Type u} {E : Type v} (F : TripleSystem V E) :
    (toUniform F).IsNColorable 2 ↔ F.IsTwoColorable := by
  change (∃ c : V → Fin 2, (toUniform F).IsProperColoring c) ↔
    ∃ c : V → Fin 2, F.IsProperColoring c
  exact exists_congr (coloring F)

theorem chromatic {V : Type u} {E : Type v} (F : TripleSystem V E) :
    (toUniform F).chromaticCardinal = F.chromaticCardinal := by
  unfold UniformHypergraph.chromaticCardinal TripleSystem.chromaticCardinal
  simp only [coloring]

theorem appears {V W : Type u} {E D : Type v}
    (F : TripleSystem V E) (H : TripleSystem W D) :
    (toUniform F).Appears (toUniform H) ↔ F.Appears H := by
  classical
  constructor
  · rintro ⟨f, hf, hm⟩
    have he (e : E) : ∃ d : D, H.edgeSet d = f '' F.edgeSet e :=
      hm ⟨F.edgeSet e, ⟨e, rfl⟩, rfl⟩
    choose g hg using he
    exact ⟨⟨⟨f, hf⟩, g, fun e => (hg e).symm⟩⟩
  · rintro ⟨f⟩
    refine ⟨f.vertex, f.vertex.injective, ?_⟩
    rintro _ ⟨_, ⟨e, rfl⟩, rfl⟩
    exact ⟨f.edge e, (f.map_edge e).symm⟩

theorem uniform_ext {V : Type u} (H K : UniformHypergraph V 3)
    (he : H.edgeSet = K.edgeSet) : H = K := by
  have hv : H.vertexSet = K.vertexSet := H.vertexSet_eq_univ.trans K.vertexSet_eq_univ.symm
  rcases H with ⟨⟨hv₁, he₁, hs₁⟩, _, _⟩
  rcases K with ⟨⟨hv₂, he₂, hs₂⟩, _, _⟩
  change hv₁ = hv₂ at hv
  change he₁ = he₂ at he
  subst hv₂
  subst he₂
  rfl

theorem roundtrip {V : Type u} (H : UniformHypergraph V 3) :
    toUniform (fromUniform H) = H := by
  apply uniform_ext
  change Set.range (fromUniform H).edgeSet = H.edgeSet
  ext e
  constructor
  · rintro ⟨f, rfl⟩
    exact f.property
  · exact fun h => ⟨⟨e, h⟩, rfl⟩

theorem obligatory {V : Type} [Fintype V] (F : UniformHypergraph V 3) :
    F.IsObligatory ↔ (fromUniform F).IsObligatory := by
  constructor
  · intro h W D _ H hH
    apply (appears _ _).mp
    rw [roundtrip]
    apply h W
    rwa [chromatic]
  · intro h W _ H hH
    have happ : (fromUniform F).Appears (fromUniform H) :=
      h W H.edgeSet (fromUniform H) (by rwa [← chromatic, roundtrip])
    have happ' := (appears _ _).mpr happ
    rwa [roundtrip, roundtrip] at happ'

end
end P593

def OMA.answer : Set ((n : ℕ) × UniformHypergraph (Fin n) 3) :=
  {p | (P593.fromUniform p.2).isolatedReduction.Intrinsic}

theorem OMA.solution : Erdos593.erdos_593.answer = OMA.answer →
    type_of% @Erdos593.erdos_593 := by
  intro h
  rw [h]
  ext p
  classical
  letI : Fintype p.2.edgeSet := Fintype.ofFinite _
  exact (P593.obligatory p.2).trans
    (P593.TripleSystem.isObligatory_iff_isolatedReduction_intrinsic _)
