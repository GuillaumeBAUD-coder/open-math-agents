import FormalConjectures.Wikipedia.SumnerUniversalTournamentConjecture
import Mathlib.Data.List.Permutation
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-
Ported from an existing public Lean proof; the mathematics and the Lean proof are the original author's.
Original: https://github.com/ChironTheCentaur/rh-lab-sumner-el-sahili/blob/a41c4affce63499d7af29595f9d294de8d870c86/SumnerFC/Statement.lean  (theorem sumner_conjecture.variants.el_sahili)
Original author: Sky (GitHub: ChironTheCentaur)   Licence: Apache-2.0 (LICENSE)
Submitted to lefttosolve.com by @senamakel; ported to Lean v4.33.1 / formal-conjectures 9097e2f.
Changes: flattened SumnerFC/{MedianOrder,Branching,Oriented,Corollary2,TreeGlue}.lean into one file under namespace
OMAPort_Sumner; dropped SumnerFC/Defs.lean and the copied IsOrientedTree/Embeds (taken from the imported
formal-conjectures module instead); renamed the core lemmas ite_eq_left/ite_eq_right to if_pos/if_neg (older Lean);
the final theorem is stated as OMA.solution with the original proof body.
-/

/-
NOTICE of the original package (retained as required by Apache-2.0, section 4(d)):

SumnerElSahili (standalone package)
Copyright 2026 Sky (GitHub: ChironTheCentaur)

The original work in this package (SumnerFC/, SumnerElSahili.lean, check.py, AxiomAudit.lean, PlantedSorry.lean,
controls/) is licensed under the Apache License, Version 2.0 (see LICENSE).

Digraph.IsTournament, IsOrientation, Hom and their notation in SumnerFC/Defs.lean, IsOrientedTree and
Embeds in SumnerFC/Statement.lean, and the statement of sumner_conjecture.variants.el_sahili are copied verbatim
from google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/SumnerUniversalTournamentConjecture.lean and the
files it imports, commit ea8e3e19), Copyright The Formal Conjectures Authors, licensed under the Apache License,
Version 2.0.
-/

namespace OMAPort_Sumner

/- ===== SumnerFC/MedianOrder.lean ===== -/

/-!
# Median orders of tournaments and the feedback property

A median order of a tournament is an ordering `v₀, …, v_{m-1}` of its vertices with the most forward arcs. Moving
`vᵢ` behind `vᵢ₊₁, …, vⱼ`, or `vⱼ` in front of `vᵢ, …, vⱼ₋₁`, cannot gain arcs, so (Havet–Thomassé 2000, property
(M2)):

* `vᵢ` beats at least half of `vᵢ₊₁, …, vⱼ`;
* `vⱼ` is beaten by at least half of `vᵢ, …, vⱼ₋₁`.

`IsLocalMedian G σ a b` states (M2) for a position map `σ : ℕ → V` on the window `[a, b)`; it passes to every
sub-window (`IsLocalMedian.mono`). `exists_localMedian` gives, for every finite tournament, an injective `σ` whose
window `[0, card V)` is a local median order and covers every vertex.

The list part (`fwd`, `fwd_append_perm`, `fwd_move`) is the one of `GraphClassics.SecondNeighbourhood`.
-/

open Finset

namespace SumnerFC

section Lists

variable {V : Type*} (R : V → V → Prop) [DecidableRel R]

/-- The number of forward arcs of an ordering. -/
def fwd : List V → ℕ
  | [] => 0
  | a :: l => l.countP (fun z => R a z) + fwd l

variable {R}

lemma fwd_append_perm (A : List V) {L₁ L₂ : List V} (h : L₁.Perm L₂) :
    fwd R (A ++ L₁) + fwd R L₂ = fwd R (A ++ L₂) + fwd R L₁ := by
  induction A with
  | nil => simp only [List.nil_append]; omega
  | cons a A ih =>
    simp only [List.cons_append, fwd, List.countP_append, h.countP_eq]
    omega

lemma fwd_move (m C : List V) (y : V) :
    fwd R (m ++ y :: C) = fwd R (m ++ C) + C.countP (fun z => R y z) +
      m.countP (fun z => R z y) := by
  induction m with
  | nil => simp [fwd]; omega
  | cons a m ih =>
    simp only [List.cons_append, fwd, List.countP_append, List.countP_cons, ih]
    split_ifs <;> simp_all <;> omega

/-- In an ordering with the most forward arcs, `y` is beaten by at least as many vertices of a block `m` just in
front of it as it beats. -/
lemma feedback_left {l : List V} (hmax : ∀ l' : List V, l'.Perm l → fwd R l' ≤ fwd R l)
    (A m : List V) (y : V) (C : List V) (hl : l = A ++ m ++ y :: C) :
    m.countP (fun z => R y z) ≤ m.countP (fun z => R z y) := by
  have hperm : (A ++ y :: (m ++ C)).Perm l := by
    rw [hl, List.append_assoc]
    exact List.Perm.append_left A (List.perm_middle.symm.trans (by simp))
  have h1 := hmax _ hperm
  have h2 := fwd_append_perm (R := R) A (L₁ := m ++ y :: C) (L₂ := y :: (m ++ C))
    List.perm_middle
  rw [hl, List.append_assoc] at h1
  have h3 := fwd_move (R := R) m C y
  simp only [fwd, List.countP_append] at h2
  omega

/-- In an ordering with the most forward arcs, `y` beats at least as many vertices of a block `m` just behind it as
it is beaten by. -/
lemma feedback_right {l : List V} (hmax : ∀ l' : List V, l'.Perm l → fwd R l' ≤ fwd R l)
    (A : List V) (y : V) (m C : List V) (hl : l = A ++ y :: (m ++ C)) :
    m.countP (fun z => R z y) ≤ m.countP (fun z => R y z) := by
  have hperm : (A ++ (m ++ y :: C)).Perm l := by
    rw [hl]
    exact List.Perm.append_left A List.perm_middle
  have h1 := hmax _ hperm
  have h2 := fwd_append_perm (R := R) A (L₁ := m ++ y :: C) (L₂ := y :: (m ++ C))
    List.perm_middle
  rw [hl] at h1
  have h3 := fwd_move (R := R) m C y
  simp only [fwd, List.countP_append] at h2
  omega

end Lists

section Window

variable {V : Type*} [Inhabited V]

lemma getD_eq {l : List V} {k : ℕ} (hk : k < l.length) : l.getD k default = l[k] := by
  simp [List.getD_eq_getElem?_getD, hk]

/-- The count of a predicate over the block `l[i], …, l[j-1]` is the count over the positions `[i, j)`. -/
lemma countP_drop_take (l : List V) (p : V → Bool) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ l.length) :
    ((l.take j).drop i).countP p = #((Ico i j).filter (fun k => p (l.getD k default) = true)) := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    have hjl : j < l.length := by omega
    rw [List.take_add_one, List.getElem?_eq_getElem hjl, Option.toList_some,
      List.drop_append_of_le_length (by simp; omega), List.countP_append, ih (by omega),
      Nat.Ico_succ_right_eq_insert_Ico hij, Finset.filter_insert]
    have hjn : j ∉ (Ico i j).filter (fun k => p (l.getD k default) = true) := by simp
    simp only [getD_eq hjl, List.countP_singleton]
    split_ifs with h <;> simp [h, Finset.card_insert_of_notMem hjn]

end Window

variable {V : Type*} (G : Digraph V) [DecidableRel G.Adj]

/-- Property (M2) of Havet and Thomassé on the window `[a, b)` of a position map `σ`. -/
def IsLocalMedian (σ : ℕ → V) (a b : ℕ) : Prop :=
  ∀ i j, a ≤ i → i < j → j < b →
    j - i ≤ 2 * #((Ioc i j).filter (fun k => G.Adj (σ i) (σ k))) ∧
    j - i ≤ 2 * #((Ico i j).filter (fun k => G.Adj (σ k) (σ j)))

variable {G}

lemma IsLocalMedian.mono {σ : ℕ → V} {a b a' b' : ℕ} (h : IsLocalMedian G σ a b) (ha : a ≤ a')
    (hb : b' ≤ b) : IsLocalMedian G σ a' b' :=
  fun i j hi hij hj => h i j (ha.trans hi) hij (lt_of_lt_of_le hj hb)

/-- Every finite tournament has a local median order covering all its vertices. -/
theorem exists_localMedian [Fintype V] [DecidableEq V] [Inhabited V] (hG : G.IsTournament) :
    ∃ σ : ℕ → V, Set.InjOn σ (Set.Iio (Fintype.card V)) ∧
      (∀ v, ∃ k < Fintype.card V, σ k = v) ∧ IsLocalMedian G σ 0 (Fintype.card V) := by
  classical
  let R : V → V → Prop := fun x y => G.Adj x y
  let P := (univ : Finset V).toList.permutations.toFinset
  have hP : P.Nonempty := ⟨_, List.mem_toFinset.2 (List.mem_permutations.2 (List.Perm.refl _))⟩
  obtain ⟨l, hl, hmax⟩ := exists_max_image P (fwd R) hP
  have hperm : l.Perm (univ : Finset V).toList := List.mem_permutations.1 (List.mem_toFinset.1 hl)
  have hmax' : ∀ l' : List V, l'.Perm l → fwd R l' ≤ fwd R l := fun l' hl' =>
    hmax l' (List.mem_toFinset.2 (List.mem_permutations.2 (hl'.trans hperm)))
  have hnd : l.Nodup := hperm.nodup_iff.2 (Finset.nodup_toList _)
  have hlen : l.length = Fintype.card V := by
    rw [hperm.length_eq, Finset.length_toList, Finset.card_univ]
  refine ⟨fun k => l.getD k default, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Set.mem_Iio] at hx hy
    rw [← hlen] at hx hy
    simp only [getD_eq hx, getD_eq hy] at hxy
    exact (hnd.getElem_inj_iff).1 hxy
  · intro v
    have hv : v ∈ l := hperm.mem_iff.2 (Finset.mem_toList.2 (mem_univ v))
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
    exact ⟨k, hlen ▸ hk, getD_eq hk⟩
  · intro i j _ hij hj
    rw [← hlen] at hj
    have hi : i < l.length := hij.trans hj
    -- the two blocks, and the tournament identity `beats + beaten = length` on each
    have hsplit_left : l = l.take i ++ (l.take j).drop i ++ l[j] :: l.drop (j + 1) := by
      conv_lhs => rw [← List.take_append_drop (j + 1) l]
      rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some]
      conv_lhs => rw [← List.take_append_drop i (l.take j)]
      rw [List.take_take, min_eq_left hij.le]
      simp
    have hsplit_right : l = l.take i ++ l[i] :: (((l.take (j + 1)).drop (i + 1)) ++ l.drop (j + 1)) := by
      conv_lhs => rw [← List.take_append_drop (j + 1) l]
      conv_lhs => rw [← List.take_append_drop i (l.take (j + 1))]
      rw [List.take_take, min_eq_left (by omega), List.drop_eq_getElem_cons (by simp; omega)]
      simp [List.getElem_take]
    have hsum : ∀ (y : V) (m : List V), y ∉ m →
        m.countP (fun z => R y z) + m.countP (fun z => R z y) = m.length := by
      intro y m hym
      induction m with
      | nil => simp
      | cons a m ih =>
        have hay : a ≠ y := fun h => hym (h ▸ List.mem_cons_self)
        have := ih (fun h => hym (List.mem_cons_of_mem _ h))
        have htour := hG.2 y a (Ne.symm hay)
        rw [List.countP_cons, List.countP_cons, List.length_cons]
        by_cases hya : R y a
        · have hay' : ¬ R a y := htour.1 hya
          simp only [hya, hay', decide_true, decide_false, ite_true]
          simp only [Bool.false_eq_true, ite_false]
          omega
        · have hay' : R a y := by by_contra h; exact hya (htour.2 h)
          simp only [hya, hay', decide_true, decide_false, ite_true]
          simp only [Bool.false_eq_true, ite_false]
          omega
    constructor
    · -- `l[i]` beats at least half of the positions `(i, j]`
      set m := (l.take (j + 1)).drop (i + 1)
      have hfb := feedback_right hmax' _ _ m _ hsplit_right
      have hym : l[i] ∉ m := by
        intro hm
        have hnd' := hsplit_right ▸ hnd
        rw [List.nodup_append] at hnd'
        exact (List.nodup_cons.1 hnd'.2.1).1 (List.mem_append_left _ hm)
      have hs := hsum _ _ hym
      have hmlen : m.length = j - i := by simp [m]; omega
      have hc := countP_drop_take l (fun z => decide (R l[i] z)) (i := i + 1) (j := j + 1) (by omega)
        (by omega)
      have hIoc : Ioc i j = Ico (i + 1) (j + 1) := by ext; simp only [mem_Ioc, mem_Ico]; omega
      rw [hIoc]
      have hσi : l.getD i default = l[i] := getD_eq hi
      simp only [hσi]
      simp only [m] at hc hfb hs hmlen
      have : #((Ico (i + 1) (j + 1)).filter (fun k => G.Adj l[i] (l.getD k default))) =
          ((l.take (j + 1)).drop (i + 1)).countP (fun z => R l[i] z) := by
        rw [hc]; simp [R]
      omega
    · -- `l[j]` is beaten by at least half of the positions `[i, j)`
      set m := (l.take j).drop i
      have hfb := feedback_left hmax' _ m _ _ hsplit_left
      have hym : l[j] ∉ m := by
        intro hm
        have hnd' := hsplit_left ▸ hnd
        rw [List.nodup_append] at hnd'
        exact hnd'.2.2 _ (List.mem_append_right _ hm) _ List.mem_cons_self rfl
      have hs := hsum _ _ hym
      have hmlen : m.length = j - i := by simp [m]; omega
      have hc := countP_drop_take l (fun z => decide (R z l[j])) (i := i) (j := j) hij.le hj.le
      have hσj : l.getD j default = l[j] := getD_eq hj
      simp only [hσj]
      simp only [m] at hc hfb hs hmlen
      have : #((Ico i j).filter (fun k => G.Adj (l.getD k default) l[j])) =
          ((l.take j).drop i).countP (fun z => R z l[j]) := by
        rw [hc]; simp [R]
      omega

end SumnerFC

/- ===== SumnerFC/Branching.lean ===== -/

/-!
# El Sahili's Proposition 1 and Corollary 1: branchings in median orders

El Sahili, *Trees in tournaments*, JCTB 92 (2004) 183–187, Section 2.

Positions `0, …, m-1` of a position map `σ : ℕ → V` stand for the vertices `v₁, …, v_m` of a median order. A set
`P` of positions is an *M-set* of the window `[0, m)` (`IsMSet P m`) when every final section `[k, m)` with `k ≥ 1`
holds fewer than `|[k, m)|/2 + 1` points of `P`; an *M-embedding* is an embedding whose image is an M-set.

* `IsMSet.leaf_step` is Proposition 1: an M-set of `[0, m)` gains an out-neighbour of any of its points inside
  `[0, m + 2)` and stays an M-set there. `IsMSet.leaves_step` repeats it `k` times.
* `OutTree.exists_mEmbedding` is Corollary 1 for out-branchings: an out-branching on `n ≥ 2` nodes has an
  M-embedding in every window of length `≥ 2n − 2`.
* `OutTree.exists_inEmbedding_of_finset` is Corollary 1 for in-branchings, as Theorem 1 uses it: an in-branching on
  `n ≥ 2` nodes embeds into every set of `≥ 2n − 2` vertices on which the digraph is a tournament (through a median
  order of that set, read backwards).

Only the first half of property (M2) is used (`IsOutMedian`).
-/

open Finset

namespace SumnerFC

variable {V : Type*}

section Median

variable (G : Digraph V) [DecidableRel G.Adj]

/-- The first half of (M2) on the window `[0, m)`: `σ i` beats at least half of the positions `(i, j]`. -/
def IsOutMedian (σ : ℕ → V) (m : ℕ) : Prop :=
  ∀ i j, i < j → j < m → j - i ≤ 2 * #((Ioc i j).filter (fun k => G.Adj (σ i) (σ k)))

variable {G}

lemma IsLocalMedian.toOut {σ : ℕ → V} {m : ℕ} (h : IsLocalMedian G σ 0 m) : IsOutMedian G σ m :=
  fun i j hij hj => (h i j (Nat.zero_le _) hij hj).1

lemma IsOutMedian.mono {σ : ℕ → V} {m m' : ℕ} (h : IsOutMedian G σ m) (hm : m' ≤ m) :
    IsOutMedian G σ m' :=
  fun i j hij hj => h i j hij (lt_of_lt_of_le hj hm)

end Median

/-! ### M-sets and Proposition 1 -/

/-- `P` is an M-set of the window `[0, m)`: its points lie in the window and every final section `[k, m)`,
`k ≥ 1`, holds fewer than half its length plus one of them. -/
def IsMSet (P : Finset ℕ) (m : ℕ) : Prop :=
  (∀ p ∈ P, p < m) ∧ ∀ k, 1 ≤ k → 2 * #(P.filter (fun q => k ≤ q)) < m - k + 2

lemma IsMSet.mono {P : Finset ℕ} {m m' : ℕ} (h : IsMSet P m) (hm : m ≤ m') : IsMSet P m' := by
  refine ⟨fun p hp => lt_of_lt_of_le (h.1 p hp) hm, fun k hk => ?_⟩
  have := h.2 k hk
  omega

lemma IsMSet.subset {P Q : Finset ℕ} {m : ℕ} (h : IsMSet P m) (hQ : Q ⊆ P) : IsMSet Q m := by
  refine ⟨fun p hp => h.1 p (hQ hp), fun k hk => ?_⟩
  have h1 := h.2 k hk
  have h2 : #(Q.filter (fun q => k ≤ q)) ≤ #(P.filter (fun q => k ≤ q)) :=
    card_le_card (filter_subset_filter _ hQ)
  omega

variable {G : Digraph V} [DecidableRel G.Adj] {σ : ℕ → V}

/-- **Proposition 1** (El Sahili). An M-set `P` of `[0, m)` and a point `i ∈ P`: the window `[0, m + 2)` has a
position `p > i` outside `P` with `σ i → σ p`, and `P ∪ {p}` is an M-set of `[0, m + 2)`. -/
theorem IsMSet.leaf_step {P : Finset ℕ} {m i : ℕ} (hσ : IsOutMedian G σ (m + 2)) (hP : IsMSet P m)
    (hi : i ∈ P) :
    ∃ p, i < p ∧ p < m + 2 ∧ p ∉ P ∧ G.Adj (σ i) (σ p) ∧ IsMSet (insert p P) (m + 2) := by
  have him : i < m := hP.1 i hi
  have hmed := hσ i (m + 1) (by omega) (by omega)
  have hPQ := hP.2 (i + 1) (by omega)
  have hlt : #(P.filter (fun q => i + 1 ≤ q)) <
      #((Ioc i (m + 1)).filter (fun k => G.Adj (σ i) (σ k))) := by omega
  obtain ⟨p, hpO, hpQ⟩ := exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨hpI, hadj⟩ := mem_filter.1 hpO
  obtain ⟨hip, hpm⟩ := mem_Ioc.1 hpI
  have hpP : p ∉ P := fun h => hpQ (mem_filter.2 ⟨h, by omega⟩)
  refine ⟨p, hip, by omega, hpP, hadj, ?_, fun k hk => ?_⟩
  · intro q hq
    rcases mem_insert.1 hq with rfl | hq
    · omega
    · exact lt_of_lt_of_le (hP.1 q hq) (by omega)
  · have h1 := hP.2 k hk
    have h2 : #((insert p P).filter (fun q => k ≤ q)) ≤ #(P.filter (fun q => k ≤ q)) + 1 := by
      rw [filter_insert]
      split_ifs
      · exact card_insert_le _ _
      · omega
    have h3 : p < k → #((insert p P).filter (fun q => k ≤ q)) = #(P.filter (fun q => k ≤ q)) := by
      intro hpk
      rw [filter_insert, if_neg (by omega)]
    have h4 : m < k → #(P.filter (fun q => k ≤ q)) = 0 := by
      intro hmk
      rw [card_eq_zero, filter_eq_empty_iff]
      intro q hq
      have := hP.1 q hq
      omega
    by_cases hkm : k ≤ m
    · omega
    · by_cases hpk : p < k
      · have := h3 hpk; have := h4 (by omega); omega
      · have := h4 (by omega); omega

/-- Proposition 1 applied `k` times at the same point: `k` fresh out-neighbours of `σ i` in `[0, m + 2k)`. -/
theorem IsMSet.leaves_step {P : Finset ℕ} {m i : ℕ} (hP : IsMSet P m) (hi : i ∈ P) :
    ∀ k, IsOutMedian G σ (m + 2 * k) →
      ∃ S : Finset ℕ, #S = k ∧ Disjoint S P ∧ (∀ p ∈ S, i < p ∧ G.Adj (σ i) (σ p)) ∧
        IsMSet (P ∪ S) (m + 2 * k) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨∅, rfl, disjoint_empty_left _, by simp, by simpa using hP⟩
  | succ k ih =>
    intro hσ
    obtain ⟨S, hS, hSP, hSi, hPS⟩ := ih (hσ.mono (by omega))
    have hσ' : IsOutMedian G σ (m + 2 * k + 2) := by
      have : m + 2 * k + 2 = m + 2 * (k + 1) := by omega
      rw [this]; exact hσ
    obtain ⟨p, hip, _, hpPS, hadj, hM⟩ := hPS.leaf_step hσ' (mem_union_left _ hi)
    refine ⟨insert p S, ?_, ?_, ?_, ?_⟩
    · rw [card_insert_of_notMem (fun h => hpPS (mem_union_right _ h)), hS]
    · exact disjoint_insert_left.2 ⟨fun h => hpPS (mem_union_left _ h), hSP⟩
    · intro q hq
      rcases mem_insert.1 hq with rfl | hq
      · exact ⟨hip, hadj⟩
      · exact hSi q hq
    · have : P ∪ insert p S = insert p (P ∪ S) := by
        ext; simp only [mem_union, mem_insert]; tauto
      rw [this, show m + 2 * (k + 1) = m + 2 * k + 2 by omega]
      exact hM

/-! ### Rooted trees given by parent pointers -/

/-- A finite rooted tree on node set `T`, given by parent pointers and a rank that grows away from the root
(which rules out cycles). As an out-branching its arcs are `par x → x`; as an in-branching, `x → par x`. -/
structure OutTree (α : Type*) where
  T : Finset α
  r : α
  par : α → α
  rk : α → ℕ
  root_mem : r ∈ T
  par_root : par r = r
  par_mem : ∀ x ∈ T, par x ∈ T
  rk_lt : ∀ x ∈ T, x ≠ r → rk (par x) < rk x

namespace OutTree

variable {α : Type*} [DecidableEq α]

/-- A tree with at least two nodes has a non-root node with no children (one of maximal rank). -/
lemma exists_leaf (A : OutTree α) (h : 2 ≤ #A.T) :
    ∃ y ∈ A.T, y ≠ A.r ∧ ∀ x ∈ A.T, x ≠ A.r → A.par x ≠ y := by
  have hne : (A.T.erase A.r).Nonempty := by
    rw [← card_pos, card_erase_of_mem A.root_mem]; omega
  obtain ⟨y, hy, hmax⟩ := exists_max_image (A.T.erase A.r) A.rk hne
  obtain ⟨hyr, hyT⟩ := mem_erase.1 hy
  refine ⟨y, hyT, hyr, fun x hx hxr hxy => ?_⟩
  have h1 := A.rk_lt x hx hxr
  have h2 := hmax x (mem_erase.2 ⟨hxr, hx⟩)
  rw [hxy] at h1
  omega

/-- The tree with a childless non-root node `y` removed. -/
def eraseLeaf (A : OutTree α) (y : α) (hyr : y ≠ A.r) (hy : ∀ x ∈ A.T, x ≠ A.r → A.par x ≠ y) :
    OutTree α where
  T := A.T.erase y
  r := A.r
  par := A.par
  rk := A.rk
  root_mem := mem_erase.2 ⟨Ne.symm hyr, A.root_mem⟩
  par_root := A.par_root
  par_mem := by
    intro x hx
    obtain ⟨hxy, hxT⟩ := mem_erase.1 hx
    refine mem_erase.2 ⟨?_, A.par_mem x hxT⟩
    by_cases hxr : x = A.r
    · rw [hxr, A.par_root]; exact Ne.symm hyr
    · exact hy x hxT hxr
  rk_lt := fun x hx hxr => A.rk_lt x (mem_of_mem_erase hx) hxr

/-- **Corollary 1** (El Sahili) for out-branchings: an out-branching on `n ≥ 2` nodes has an M-embedding in every
window of length `2n − 2` of a position map satisfying the first half of (M2). -/
theorem exists_mEmbedding :
    ∀ (n : ℕ) (A : OutTree α), #A.T = n → 2 ≤ n → IsOutMedian G σ (2 * n - 2) →
      ∃ f : α → ℕ, Set.InjOn f A.T ∧ (∀ x ∈ A.T, x ≠ A.r → G.Adj (σ (f (A.par x))) (σ (f x))) ∧
        IsMSet (A.T.image f) (2 * n - 2) := by
  intro n
  induction n with
  | zero => intro _ _ h; omega
  | succ n ih =>
    intro A hcard hn hσ
    obtain ⟨y, hyT, hyr, hleaf⟩ := A.exists_leaf (by omega)
    by_cases h2 : n = 1
    · -- two nodes: the root at position 0, the other node at position 1
      subst h2
      have hT : A.T = {A.r, y} := by
        symm
        apply eq_of_subset_of_card_le
        · intro z hz
          rcases mem_insert.1 hz with rfl | hz
          · exact A.root_mem
          · rw [mem_singleton.1 hz]; exact hyT
        · rw [hcard, card_pair (Ne.symm hyr)]
      have hpy : A.par y = A.r := by
        have := A.par_mem y hyT
        rw [hT] at this
        rcases mem_insert.1 this with h | h
        · exact h
        · exact absurd (mem_singleton.1 h) (hleaf y hyT hyr)
      refine ⟨fun z => if z = A.r then 0 else 1, ?_, ?_, ?_⟩
      · intro a ha b hb hab
        simp only [mem_coe, hT, mem_insert, mem_singleton] at ha hb
        simp only at hab
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all
      · intro z hz hzr
        rw [hT] at hz
        rcases mem_insert.1 hz with h | h
        · exact absurd h hzr
        · rw [mem_singleton.1 h] at hzr ⊢
          simp only [hpy, if_neg hzr]
          have := (hσ 0 1 (by omega) (by omega))
          by_contra hadj
          have h0 : (Ioc 0 1).filter (fun k => G.Adj (σ 0) (σ k)) = ∅ := by
            rw [filter_eq_empty_iff]
            intro k hk
            rw [show k = 1 by simpa using hk]
            exact hadj
          rw [h0] at this
          simp at this
      · refine ⟨?_, fun k hk => ?_⟩
        · intro p hp
          rw [hT, image_insert, image_singleton, if_pos rfl, if_neg hyr] at hp
          simp only [mem_insert, mem_singleton] at hp
          omega
        · rw [hT, image_insert, image_singleton, if_pos rfl, if_neg hyr]
          rcases Nat.lt_or_ge k 2 with hk2 | hk2
          · obtain rfl : k = 1 := by omega
            decide
          · have h0 : ({0, 1} : Finset ℕ).filter (fun q => k ≤ q) = ∅ := by
              rw [filter_eq_empty_iff]
              intro q hq
              simp only [mem_insert, mem_singleton] at hq
              omega
            rw [h0, card_empty]
            omega
    · -- remove the leaf `y`, embed the rest, put `y` back with Proposition 1
      set A' := A.eraseLeaf y hyr hleaf
      have hcard' : #A'.T = n := by
        show #(A.T.erase y) = n
        rw [card_erase_of_mem hyT, hcard]; rfl
      have hσ' : IsOutMedian G σ (2 * n - 2) := hσ.mono (by omega)
      obtain ⟨f, hinj, harc, hM⟩ := ih A' hcard' (by omega) hσ'
      set x := A.par y
      have hxy : x ≠ y := fun h => hleaf y hyT hyr h
      have hxT' : x ∈ A'.T := mem_erase.2 ⟨hxy, A.par_mem y hyT⟩
      have hσ'' : IsOutMedian G σ (2 * n - 2 + 2) := by
        rw [show 2 * n - 2 + 2 = 2 * (n + 1) - 2 by omega]; exact hσ
      obtain ⟨p, _, _, hpP, hadj, hMp⟩ := hM.leaf_step hσ'' (mem_image_of_mem f hxT')
      refine ⟨Function.update f y p, ?_, ?_, ?_⟩
      · intro a ha b hb hab
        simp only [mem_coe] at ha hb
        by_cases hay : a = y <;> by_cases hby : b = y
        · rw [hay, hby]
        · subst hay
          rw [Function.update_self, Function.update_of_ne hby] at hab
          exact absurd (hab ▸ mem_image_of_mem f (mem_erase.2 ⟨hby, hb⟩)) hpP
        · subst hby
          rw [Function.update_self, Function.update_of_ne hay] at hab
          exact absurd (hab.symm ▸ mem_image_of_mem f (mem_erase.2 ⟨hay, ha⟩)) hpP
        · rw [Function.update_of_ne hay, Function.update_of_ne hby] at hab
          exact hinj (mem_erase.2 ⟨hay, ha⟩) (mem_erase.2 ⟨hby, hb⟩) hab
      · intro z hz hzr
        by_cases hzy : z = y
        · subst hzy
          rw [Function.update_self, Function.update_of_ne hxy]
          exact hadj
        · have hpz : A.par z ≠ y := hleaf z hz hzr
          rw [Function.update_of_ne hzy, Function.update_of_ne hpz]
          exact harc z (mem_erase.2 ⟨hzy, hz⟩) hzr
      · have himg : A.T.image (Function.update f y p) = insert p (A'.T.image f) := by
          ext q
          simp only [mem_image, mem_insert]
          constructor
          · rintro ⟨z, hz, rfl⟩
            by_cases hzy : z = y
            · left; rw [hzy, Function.update_self]
            · right; exact ⟨z, mem_erase.2 ⟨hzy, hz⟩, (Function.update_of_ne hzy _ _).symm⟩
          · rintro (rfl | ⟨z, hz, rfl⟩)
            · exact ⟨y, hyT, Function.update_self _ _ _⟩
            · obtain ⟨hzy, hzT⟩ := mem_erase.1 hz
              exact ⟨z, hzT, Function.update_of_ne hzy _ _⟩
        rw [himg, show 2 * (n + 1) - 2 = 2 * n - 2 + 2 by omega]
        exact hMp

end OutTree

/-! ### In-branchings, through a median order read backwards -/

/-- The converse digraph. -/
def rev (G : Digraph V) : Digraph V := ⟨fun u v => G.Adj v u⟩

instance (G : Digraph V) [DecidableRel G.Adj] : DecidableRel (rev G).Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj v u))

/-- Reading a local median order backwards gives the first half of (M2) for the converse digraph (it is the second
half of (M2) for the original one). -/
lemma IsLocalMedian.rev_out {m : ℕ} (h : IsLocalMedian G σ 0 m) :
    IsOutMedian (rev G) (fun k => σ (m - 1 - k)) m := by
  intro i j hij hj
  have h2 := (h (m - 1 - j) (m - 1 - i) (Nat.zero_le _) (by omega) (by omega)).2
  have hcard : #((Ioc i j).filter (fun k => (rev G).Adj (σ (m - 1 - i)) (σ (m - 1 - k)))) =
      #((Ico (m - 1 - j) (m - 1 - i)).filter (fun k => G.Adj (σ k) (σ (m - 1 - i)))) := by
    apply card_nbij' (fun k => m - 1 - k) (fun k => m - 1 - k)
    · intro k hk
      simp only [coe_filter, mem_Ioc, Set.mem_ofPred_eq] at hk
      simp only [coe_filter, mem_Ico, Set.mem_ofPred_eq]
      exact ⟨by omega, hk.2⟩
    · intro k hk
      simp only [coe_filter, mem_Ico, Set.mem_ofPred_eq] at hk
      simp only [coe_filter, mem_Ioc, Set.mem_ofPred_eq]
      refine ⟨by omega, ?_⟩
      show G.Adj (σ (m - 1 - (m - 1 - k))) (σ (m - 1 - i))
      rw [show m - 1 - (m - 1 - k) = k by omega]; exact hk.2
    · intro k hk
      simp only [coe_filter, mem_Ioc, Set.mem_ofPred_eq] at hk
      show m - 1 - (m - 1 - k) = k
      omega
    · intro k hk
      simp only [coe_filter, mem_Ico, Set.mem_ofPred_eq] at hk
      show m - 1 - (m - 1 - k) = k
      omega
  rw [hcard]
  have : m - 1 - i - (m - 1 - j) = j - i := by omega
  omega

/-- A finite set of vertices on which `G` is a tournament has a local median order. -/
theorem exists_localMedian_finset [DecidableEq V] (S : Finset V) (hS : S.Nonempty)
    (hirr : ∀ v ∈ S, ¬ G.Adj v v) (htour : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → (G.Adj u v ↔ ¬ G.Adj v u)) :
    ∃ τ : ℕ → V, Set.InjOn τ (Set.Iio #S) ∧ (∀ k < #S, τ k ∈ S) ∧ IsLocalMedian G τ 0 #S := by
  let H : Digraph S := ⟨fun a b => G.Adj a.1 b.1⟩
  let _ : DecidableRel H.Adj := fun a b => inferInstanceAs (Decidable (G.Adj a.1 b.1))
  let _ : Inhabited S := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  have hH : H.IsTournament := by
    refine ⟨fun a => hirr a.1 a.2, fun a b hab => htour a.1 a.2 b.1 b.2 ?_⟩
    exact fun h => hab (Subtype.ext h)
  obtain ⟨ρ, hinj, _, hmed⟩ := exists_localMedian hH
  rw [Fintype.card_coe] at hinj hmed
  refine ⟨fun k => (ρ k).1, fun a ha b hb hab => hinj ha hb (Subtype.ext hab), fun k _ => (ρ k).2, ?_⟩
  intro i j hi hij hj
  convert hmed i j hi hij hj using 0

/-- **Corollary 1** (El Sahili) for in-branchings, in the form Theorem 1 uses: an in-branching (arcs `x → par x`)
on `n ≥ 2` nodes embeds into every set `S` of at least `2n − 2` vertices on which `G` is a tournament. -/
theorem OutTree.exists_inEmbedding_of_finset [DecidableEq V] {α : Type*} [DecidableEq α] (A : OutTree α)
    (hn : 2 ≤ #A.T) (S : Finset V) (hS : 2 * #A.T - 2 ≤ #S)
    (hirr : ∀ v ∈ S, ¬ G.Adj v v) (htour : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → (G.Adj u v ↔ ¬ G.Adj v u)) :
    ∃ g : α → V, Set.InjOn g A.T ∧ (∀ x ∈ A.T, g x ∈ S) ∧
      ∀ x ∈ A.T, x ≠ A.r → G.Adj (g x) (g (A.par x)) := by
  have hSne : S.Nonempty := by rw [← card_pos]; omega
  obtain ⟨τ, hτinj, hτS, hτ⟩ := exists_localMedian_finset S hSne hirr htour
  set m := #S
  have hrev := hτ.rev_out
  obtain ⟨f, hfinj, hfarc, hfM⟩ :=
    OutTree.exists_mEmbedding (G := rev G) (σ := fun k => τ (m - 1 - k)) #A.T A rfl hn (hrev.mono hS)
  have hfm : ∀ x ∈ A.T, f x < m := fun x hx => by
    have := hfM.1 (f x) (mem_image_of_mem f hx); omega
  refine ⟨fun x => τ (m - 1 - f x), ?_, fun x hx => hτS _ (by have := hfm x hx; omega), ?_⟩
  · intro a ha b hb hab
    have ha' := hfm a ha
    have hb' := hfm b hb
    have := hτinj (show m - 1 - f a ∈ Set.Iio m by simp; omega)
      (show m - 1 - f b ∈ Set.Iio m by simp; omega) hab
    exact hfinj ha hb (by omega)
  · intro x hx hxr
    exact hfarc x hx hxr

end SumnerFC

/- ===== SumnerFC/Oriented.lean ===== -/

/-!
# El Sahili's Theorem 1: well-rooted oriented trees in median orders

El Sahili, *Trees in tournaments*, JCTB 92 (2004) 183–187, Theorem 1.

An oriented tree is given as an `OutTree` (parent pointers, rank growing away from the root) together with an arc
direction `fwd : α → Bool` on the non-root nodes: `fwd x = true` is the arc `par x → x`, `fwd x = false` the arc
`x → par x`. It is *well-rooted* when every child of the root is forward (the root is a source).

* `bwd A fwd`: the backward non-root nodes (`b` = their number, the backward arcs).
* `tops A fwd`: the tops of the backward components, i.e. the forward non-root nodes with a backward child
  (`c` = their number). Each backward component has exactly one top, which is never the root (the root is a source).

`OutTree.exists_mEmbedding_oriented` is Theorem 1: a well-rooted oriented tree on `n` nodes has an M-embedding into
every window of length `w = 2n + 2(b − c)` (stated as `w + 2c = 2n + 2b`, so no subtraction is truncated) of an
injective position map satisfying the first half of (M2), in a tournament.

The proof follows the paper, with gap 1 of `PLAN.md` closed: when no forward leaf exists, the backward component
peeled off is the one whose top `y` has **maximal rank**; then everything below `y` is backward (`below_bwd`), so the
subtree at `y` is exactly that component, an in-branching, and removing it leaves a tree (`cut`).
-/

open Finset

namespace SumnerFC

namespace OutTree

variable {α : Type*}

/-! ### Iterated parents and subtrees -/

lemma iterate_par_mem (A : OutTree α) : ∀ (k : ℕ) {z : α}, z ∈ A.T → A.par^[k] z ∈ A.T := by
  intro k
  induction k with
  | zero => intro z hz; exact hz
  | succ k ih => intro z hz; rw [Function.iterate_succ_apply]; exact ih (A.par_mem z hz)

lemma iterate_par_root (A : OutTree α) : ∀ k : ℕ, A.par^[k] A.r = A.r := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, A.par_root, ih]

/-- Going up at least one step from `z` and landing on a non-root node `y` strictly lowers the rank. -/
lemma rk_iterate_lt (A : OutTree α) {y : α} (hy : y ≠ A.r) :
    ∀ (k : ℕ) (z : α), z ∈ A.T → A.par^[k + 1] z = y → A.rk y < A.rk z := by
  intro k
  induction k with
  | zero =>
    intro z hz h
    have hzr : z ≠ A.r := by
      rintro rfl; rw [iterate_par_root] at h; exact hy h.symm
    rw [zero_add, Function.iterate_one] at h
    rw [← h]; exact A.rk_lt z hz hzr
  | succ k ih =>
    intro z hz h
    have hzr : z ≠ A.r := by
      rintro rfl; rw [iterate_par_root] at h; exact hy h.symm
    rw [Function.iterate_succ_apply] at h
    have h1 := ih (A.par z) (A.par_mem z hz) h
    have h2 := A.rk_lt z hz hzr
    omega

/-- The nodes at or below `y`. -/
noncomputable def below (A : OutTree α) (y : α) : Finset α :=
  @Finset.filter α (fun z => ∃ k, A.par^[k] z = y) (Classical.decPred _) A.T

lemma mem_below {A : OutTree α} {y z : α} : z ∈ A.below y ↔ z ∈ A.T ∧ ∃ k, A.par^[k] z = y := by
  exact @mem_filter α (fun z => ∃ k, A.par^[k] z = y) (Classical.decPred _) A.T z

lemma below_subset (A : OutTree α) (y : α) : A.below y ⊆ A.T := fun _ hz => (mem_below.1 hz).1

lemma self_mem_below {A : OutTree α} {y : α} (hy : y ∈ A.T) : y ∈ A.below y := mem_below.2 ⟨hy, 0, rfl⟩

lemma root_notMem_below {A : OutTree α} {y : α} (hyr : y ≠ A.r) : A.r ∉ A.below y := by
  intro h
  obtain ⟨_, k, hk⟩ := mem_below.1 h
  rw [iterate_par_root] at hk
  exact hyr hk.symm

/-- A node whose parent is at or below `y` is itself below `y`. -/
lemma mem_below_of_par {A : OutTree α} {y x : α} (hx : x ∈ A.T) (h : A.par x ∈ A.below y) :
    x ∈ A.below y := by
  obtain ⟨_, k, hk⟩ := mem_below.1 h
  exact mem_below.2 ⟨hx, k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

lemma par_mem_below {A : OutTree α} {y z : α} (hz : z ∈ A.below y) (hzy : z ≠ y) :
    A.par z ∈ A.below y := by
  obtain ⟨hzT, k, hk⟩ := mem_below.1 hz
  cases k with
  | zero => exact absurd hk hzy
  | succ k =>
    exact mem_below.2 ⟨A.par_mem z hzT, k, by rwa [Function.iterate_succ_apply] at hk⟩

lemma rk_lt_of_mem_below {A : OutTree α} {y z : α} (hyr : y ≠ A.r) (hz : z ∈ A.below y) (hzy : z ≠ y) :
    A.rk y < A.rk z := by
  obtain ⟨hzT, k, hk⟩ := mem_below.1 hz
  cases k with
  | zero => exact absurd hk hzy
  | succ k => exact A.rk_iterate_lt hyr k z hzT hk

lemma par_notMem_below {A : OutTree α} {y : α} (hy : y ∈ A.T) (hyr : y ≠ A.r) : A.par y ∉ A.below y := by
  intro h
  obtain ⟨_, k, hk⟩ := mem_below.1 h
  have : A.par^[k + 1] y = y := by rw [Function.iterate_succ_apply]; exact hk
  have := A.rk_iterate_lt hyr k y hy this
  omega

variable [DecidableEq α]

/-- The subtree at a non-root node `y`, rooted at `y`. -/
noncomputable def subtree (A : OutTree α) (y : α) (hy : y ∈ A.T) (hyr : y ≠ A.r) : OutTree α where
  T := A.below y
  r := y
  par := fun z => if z = y then y else A.par z
  rk := A.rk
  root_mem := self_mem_below hy
  par_root := if_pos rfl
  par_mem := by
    intro z hz
    by_cases hzy : z = y
    · simp only [if_pos hzy]; exact self_mem_below hy
    · simp only [if_neg hzy]; exact par_mem_below hz hzy
  rk_lt := by
    intro z hz hzy
    obtain ⟨hzT, _, _⟩ := mem_below.1 hz
    have hzr : z ≠ A.r := fun h => root_notMem_below hyr (h ▸ hz)
    show A.rk (if z = y then y else A.par z) < A.rk z
    rw [if_neg hzy]
    exact A.rk_lt z hzT hzr

/-- The tree with the subtree at a non-root node `y` removed. -/
noncomputable def cut (A : OutTree α) (y : α) (hyr : y ≠ A.r) : OutTree α where
  T := A.T.filter (· ∉ A.below y)
  r := A.r
  par := A.par
  rk := A.rk
  root_mem := mem_filter.2 ⟨A.root_mem, root_notMem_below hyr⟩
  par_root := A.par_root
  par_mem := by
    intro x hx
    obtain ⟨hxT, hxB⟩ := mem_filter.1 hx
    exact mem_filter.2 ⟨A.par_mem x hxT, fun h => hxB (mem_below_of_par hxT h)⟩
  rk_lt := fun x hx hxr => A.rk_lt x (mem_filter.1 hx).1 hxr

/-! ### Backward arcs and backward components -/

/-- The backward non-root nodes (arc `x → par x`). -/
def bwd (A : OutTree α) (fwd : α → Bool) : Finset α :=
  A.T.filter (fun x => x ≠ A.r ∧ fwd x = false)

/-- The tops of the backward components: forward non-root nodes with a backward child. -/
def tops (A : OutTree α) (fwd : α → Bool) : Finset α :=
  A.T.filter (fun y => y ≠ A.r ∧ fwd y = true ∧ ∃ z ∈ A.T, z ≠ A.r ∧ A.par z = y ∧ fwd z = false)

/-- `c ≤ b`: every top is the parent of a backward node. -/
lemma card_tops_le (A : OutTree α) (fwd : α → Bool) : #(A.tops fwd) ≤ #(A.bwd fwd) := by
  have : A.tops fwd ⊆ (A.bwd fwd).image A.par := by
    intro y hy
    obtain ⟨_, _, _, z, hzT, hzr, hpz, hfz⟩ := mem_filter.1 hy
    exact mem_image.2 ⟨z, mem_filter.2 ⟨hzT, hzr, hfz⟩, hpz⟩
  exact (card_le_card this).trans card_image_le

/-- In a well-rooted tree, a backward node of least rank hangs from a top. -/
lemma tops_nonempty (A : OutTree α) (fwd : α → Bool)
    (hsrc : ∀ x ∈ A.T, x ≠ A.r → A.par x = A.r → fwd x = true) (hb : (A.bwd fwd).Nonempty) :
    (A.tops fwd).Nonempty := by
  obtain ⟨z, hz, hmin⟩ := exists_min_image (A.bwd fwd) A.rk hb
  obtain ⟨hzT, hzr, hfz⟩ := mem_filter.1 hz
  have hpr : A.par z ≠ A.r := fun h => by rw [hsrc z hzT hzr h] at hfz; exact Bool.noConfusion hfz
  have hpT := A.par_mem z hzT
  have hfp : fwd (A.par z) = true := by
    by_contra h
    have := hmin (A.par z) (mem_filter.2 ⟨hpT, hpr, by simpa using h⟩)
    have := A.rk_lt z hzT hzr
    omega
  exact ⟨A.par z, mem_filter.2 ⟨hpT, hpr, hfp, z, hzT, hzr, rfl, hfz⟩⟩

/-- **Gap 1.** If no forward node is a leaf and `y` is a top of maximal rank, every node strictly below `y` is
backward: the subtree at `y` is exactly the backward component of `y`. -/
lemma below_bwd (A : OutTree α) (fwd : α → Bool)
    (hnoleaf : ∀ u ∈ A.T, u ≠ A.r → fwd u = true → ∃ x ∈ A.T, x ≠ A.r ∧ A.par x = u)
    {y : α} (hy : y ∈ A.tops fwd) (hmax : ∀ t ∈ A.tops fwd, A.rk t ≤ A.rk y) :
    ∀ z ∈ A.below y, z ≠ y → fwd z = false := by
  have hyr : y ≠ A.r := (mem_filter.1 hy).2.1
  by_contra hcon
  push Not at hcon
  set F := (A.below y).filter (fun z => z ≠ y ∧ fwd z = true)
  have hF : F.Nonempty := by
    obtain ⟨z, hz, hzy, hfz⟩ := hcon
    exact ⟨z, mem_filter.2 ⟨hz, hzy, by simpa using hfz⟩⟩
  obtain ⟨u, hu, humax⟩ := exists_max_image F A.rk hF
  obtain ⟨huB, huy, hfu⟩ := mem_filter.1 hu
  have huT := A.below_subset y huB
  have hur : u ≠ A.r := fun h => root_notMem_below hyr (h ▸ huB)
  have hyu := rk_lt_of_mem_below hyr huB huy
  obtain ⟨x, hxT, hxr, hpx⟩ := hnoleaf u huT hur hfu
  have hxB : x ∈ A.below y := mem_below_of_par hxT (by rw [hpx]; exact huB)
  have hux : A.rk u < A.rk x := hpx ▸ A.rk_lt x hxT hxr
  have hxy : x ≠ y := by rintro rfl; omega
  cases hfx : fwd x with
  | true =>
    have := humax x (mem_filter.2 ⟨hxB, hxy, hfx⟩)
    omega
  | false =>
    have := hmax u (mem_filter.2 ⟨huT, hur, hfu, x, hxT, hxr, hpx, hfx⟩)
    omega

end OutTree

/-! ### Theorem 1 -/

variable {V : Type*} {G : Digraph V} [DecidableRel G.Adj] {σ : ℕ → V}

lemma isMSet_zero_two : IsMSet {0} 2 := by
  refine ⟨by simp, fun k hk => ?_⟩
  have h0 : ({0} : Finset ℕ).filter (fun q => k ≤ q) = ∅ := by
    rw [filter_eq_empty_iff]; intro q hq; rw [mem_singleton.1 hq]; omega
  rw [h0, card_empty]; omega

namespace OutTree

variable {α : Type*} [DecidableEq α]

/-- **Theorem 1** (El Sahili). A well-rooted oriented tree on `n` nodes, with `b` backward arcs and `c` backward
components, has an M-embedding into the window `[0, w)`, `w = 2n + 2(b − c)`, of any position map that is injective
on the window and satisfies the first half of (M2) there, in a tournament. Arcs are mapped onto arcs in their own
direction. -/
theorem exists_mEmbedding_oriented (hG : G.IsTournament) :
    ∀ (n : ℕ) (A : OutTree α) (fwd : α → Bool), #A.T = n →
      (∀ x ∈ A.T, x ≠ A.r → A.par x = A.r → fwd x = true) →
      ∀ w, w + 2 * #(A.tops fwd) = 2 * n + 2 * #(A.bwd fwd) →
        IsOutMedian G σ w → Set.InjOn σ (Set.Iio w) →
        ∃ f : α → ℕ, Set.InjOn f A.T ∧
          (∀ x ∈ A.T, x ≠ A.r →
            (fwd x = true → G.Adj (σ (f (A.par x))) (σ (f x))) ∧
            (fwd x = false → G.Adj (σ (f x)) (σ (f (A.par x))))) ∧
          IsMSet (A.T.image f) w := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A fwd hn hsrc w hw hσ hinj
  have hcb := A.card_tops_le fwd
  by_cases hleaf : ∃ y ∈ A.T, y ≠ A.r ∧ fwd y = true ∧ ∀ x ∈ A.T, x ≠ A.r → A.par x ≠ y
  · ------------------------------------------------------------------ a forward leaf: Proposition 1
    obtain ⟨y, hyT, hyr, hfy, hy⟩ := hleaf
    set A' := A.eraseLeaf y hyr hy with hA'
    have hT' : A'.T = A.T.erase y := rfl
    have hr' : A'.r = A.r := rfl
    have hp' : A'.par = A.par := rfl
    have hn2 : 2 ≤ n := by
      rw [← hn]
      have : ({A.r, y} : Finset α) ⊆ A.T := by
        intro z hz
        rcases mem_insert.1 hz with rfl | hz
        · exact A.root_mem
        · rw [mem_singleton.1 hz]; exact hyT
      have := card_le_card this
      rwa [card_pair (Ne.symm hyr)] at this
    have hcard' : #A'.T = n - 1 := by rw [hT', card_erase_of_mem hyT, hn]
    have hbwd : A'.bwd fwd = A.bwd fwd := by
      ext z
      simp only [bwd, hT', hr', mem_filter, mem_erase]
      constructor
      · rintro ⟨⟨_, hz⟩, h⟩; exact ⟨hz, h⟩
      · rintro ⟨hz, hzr, hfz⟩
        exact ⟨⟨fun h => by rw [h, hfy] at hfz; exact Bool.noConfusion hfz, hz⟩, hzr, hfz⟩
    have htops : A'.tops fwd = A.tops fwd := by
      ext z
      simp only [tops, hT', hr', hp', mem_filter, mem_erase]
      constructor
      · rintro ⟨⟨_, hz⟩, hzr, hfz, u, ⟨_, hu⟩, hur, hpu, hfu⟩
        exact ⟨hz, hzr, hfz, u, hu, hur, hpu, hfu⟩
      · rintro ⟨hz, hzr, hfz, u, hu, hur, hpu, hfu⟩
        refine ⟨⟨?_, hz⟩, hzr, hfz, u, ⟨?_, hu⟩, hur, hpu, hfu⟩
        · rintro rfl; exact hy u hu hur hpu
        · rintro rfl; rw [hfy] at hfu; exact Bool.noConfusion hfu
    have hw2 : 2 ≤ w := by omega
    obtain ⟨f, hfinj, hfarc, hM⟩ := ih (n - 1) (by omega) A' fwd hcard'
      (fun x hx hxr hpx => hsrc x (mem_of_mem_erase hx) hxr hpx) (w - 2)
      (by rw [hbwd, htops]; omega) (hσ.mono (by omega)) (hinj.mono (Set.Iio_subset_Iio (by omega)))
    set x := A.par y
    have hxy : x ≠ y := fun h => hy y hyT hyr h
    have hxT' : x ∈ A'.T := mem_erase.2 ⟨hxy, A.par_mem y hyT⟩
    have hσ' : IsOutMedian G σ (w - 2 + 2) := by rw [show w - 2 + 2 = w by omega]; exact hσ
    obtain ⟨p, _, _, hpP, hadj, hMp⟩ := hM.leaf_step hσ' (mem_image_of_mem f hxT')
    refine ⟨Function.update f y p, ?_, ?_, ?_⟩
    · intro a ha b hb hab
      simp only [mem_coe] at ha hb
      by_cases hay : a = y <;> by_cases hby : b = y
      · rw [hay, hby]
      · subst hay
        rw [Function.update_self, Function.update_of_ne hby] at hab
        exact absurd (hab ▸ mem_image_of_mem f (mem_erase.2 ⟨hby, hb⟩)) hpP
      · subst hby
        rw [Function.update_self, Function.update_of_ne hay] at hab
        exact absurd (hab.symm ▸ mem_image_of_mem f (mem_erase.2 ⟨hay, ha⟩)) hpP
      · rw [Function.update_of_ne hay, Function.update_of_ne hby] at hab
        exact hfinj (mem_erase.2 ⟨hay, ha⟩) (mem_erase.2 ⟨hby, hb⟩) hab
    · intro z hz hzr
      by_cases hzy : z = y
      · subst hzy
        rw [Function.update_self, Function.update_of_ne hxy]
        refine ⟨fun _ => hadj, fun h => ?_⟩
        rw [hfy] at h; exact Bool.noConfusion h
      · have hpz : A.par z ≠ y := hy z hz hzr
        rw [Function.update_of_ne hzy, Function.update_of_ne hpz]
        exact hfarc z (mem_erase.2 ⟨hzy, hz⟩) hzr
    · have himg : A.T.image (Function.update f y p) = insert p (A'.T.image f) := by
        ext q
        simp only [mem_image, mem_insert]
        constructor
        · rintro ⟨z, hz, rfl⟩
          by_cases hzy : z = y
          · left; rw [hzy, Function.update_self]
          · right; exact ⟨z, mem_erase.2 ⟨hzy, hz⟩, (Function.update_of_ne hzy _ _).symm⟩
        · rintro (rfl | ⟨z, hz, rfl⟩)
          · exact ⟨y, hyT, Function.update_self _ _ _⟩
          · obtain ⟨hzy, hzT⟩ := mem_erase.1 hz
            exact ⟨z, hzT, Function.update_of_ne hzy _ _⟩
      rw [himg, show w = w - 2 + 2 by omega]
      exact hMp
  · have hnoleaf : ∀ u ∈ A.T, u ≠ A.r → fwd u = true → ∃ x ∈ A.T, x ≠ A.r ∧ A.par x = u := by
      intro u hu hur hfu
      by_contra h
      push Not at h
      exact hleaf ⟨u, hu, hur, hfu, h⟩
    by_cases htop : (A.tops fwd).Nonempty
    · ---------------------------------------------- the backward component with the deepest top
      obtain ⟨y, hyt, hmax⟩ := exists_max_image (A.tops fwd) A.rk htop
      obtain ⟨hyT, hyr, hfy, z0, hz0T, hz0r, hpz0, hfz0⟩ := mem_filter.1 hyt
      have hB := A.below_bwd fwd hnoleaf hyt hmax
      set B := A.below y with hBdef
      set m := #B with hm
      have hz0B : z0 ∈ B := mem_below_of_par hz0T (by rw [hpz0]; exact self_mem_below hyT)
      have hz0y : z0 ≠ y := by rintro rfl; rw [hfy] at hfz0; exact Bool.noConfusion hfz0
      have hm2 : 2 ≤ m := by
        have : ({y, z0} : Finset α) ⊆ B := by
          intro z hz
          rcases mem_insert.1 hz with rfl | hz
          · exact self_mem_below hyT
          · rw [mem_singleton.1 hz]; exact hz0B
        have := card_le_card this
        rwa [card_pair (Ne.symm hz0y)] at this
      set A' := A.cut y hyr with hA'
      have hT' : A'.T = A.T.filter (· ∉ B) := rfl
      have hr' : A'.r = A.r := rfl
      have hp' : A'.par = A.par := rfl
      -- node count
      have hmB : m = #(A.below y) := rfl
      have hcardT : #A'.T + m = n := by
        have h1 : A.T.filter (· ∈ B) = B := by
          ext z; simp only [mem_filter]; exact ⟨fun h => h.2, fun h => ⟨A.below_subset y h, h⟩⟩
        have h3 := card_filter_add_card_filter_not (s := A.T) (· ∈ B)
        rw [h1] at h3
        rw [hT', ← hn]
        omega
      -- backward count: the component contributes `m − 1` backward arcs
      have hcardB : #(A'.bwd fwd) + (m - 1) = #(A.bwd fwd) := by
        have h1 : (A.bwd fwd).filter (· ∉ B) = A'.bwd fwd := by
          ext z
          simp only [bwd, hT', hr', mem_filter]
          tauto
        have h2 : (A.bwd fwd).filter (· ∈ B) = B.erase y := by
          ext z
          simp only [bwd, mem_filter, mem_erase]
          constructor
          · rintro ⟨⟨_, _, hfz⟩, hzB⟩
            exact ⟨fun h => by rw [h, hfy] at hfz; exact Bool.noConfusion hfz, hzB⟩
          · rintro ⟨hzy, hzB⟩
            exact ⟨⟨A.below_subset y hzB, fun h => root_notMem_below hyr (h ▸ hzB), hB z hzB hzy⟩, hzB⟩
        have h3 := card_filter_add_card_filter_not (s := A.bwd fwd) (· ∈ B)
        rw [h2, h1, card_erase_of_mem (self_mem_below hyT)] at h3
        omega
      -- component count: exactly one top, `y`, is inside the subtree
      have hcardC : #(A'.tops fwd) + 1 = #(A.tops fwd) := by
        have h1 : (A.tops fwd).filter (· ∉ B) = A'.tops fwd := by
          ext z
          simp only [tops, hT', hr', hp', mem_filter]
          constructor
          · rintro ⟨⟨hz, hzr, hfz, u, hu, hur, hpu, hfu⟩, hzB⟩
            refine ⟨⟨hz, hzB⟩, hzr, hfz, u, ⟨hu, fun huB => ?_⟩, hur, hpu, hfu⟩
            have huy : u ≠ y := by rintro rfl; rw [hfy] at hfu; exact Bool.noConfusion hfu
            exact hzB (hpu ▸ par_mem_below huB huy)
          · rintro ⟨⟨hz, hzB⟩, hzr, hfz, u, ⟨hu, _⟩, hur, hpu, hfu⟩
            exact ⟨⟨hz, hzr, hfz, u, hu, hur, hpu, hfu⟩, hzB⟩
        have h2 : (A.tops fwd).filter (· ∈ B) = {y} := by
          ext z
          simp only [mem_filter, mem_singleton]
          constructor
          · rintro ⟨hzt, hzB⟩
            by_contra hzy
            have := hB z hzB hzy
            rw [(mem_filter.1 hzt).2.2.1] at this
            exact Bool.noConfusion this
          · rintro rfl; exact ⟨hyt, self_mem_below hyT⟩
        have h3 := card_filter_add_card_filter_not (s := A.tops fwd) (· ∈ B)
        rw [h2, h1, card_singleton] at h3
        omega
      have hcb' := A'.card_tops_le fwd
      -- embed the rest in the first `w − (4m − 4)` positions
      set w' := w - (4 * m - 4) with hw'
      have hww : w' + 2 * (2 * m - 2) = w := by omega
      obtain ⟨f, hfinj, hfarc, hM⟩ := ih #A'.T (by omega) A' fwd rfl
        (fun x hx hxr hpx => hsrc x (mem_filter.1 hx).1 hxr hpx) w' (by omega)
        (hσ.mono (by omega)) (hinj.mono (Set.Iio_subset_Iio (by omega)))
      set x0 := A.par y
      have hx0T' : x0 ∈ A'.T := mem_filter.2 ⟨A.par_mem y hyT, par_notMem_below hyT hyr⟩
      -- add `2m − 2` out-neighbours of `x0`'s position: Proposition 1, `2m − 2` times
      obtain ⟨S, hS, hSP, hSx, hPS⟩ :=
        hM.leaves_step (mem_image_of_mem f hx0T') (2 * m - 2) (by rw [hww]; exact hσ)
      rw [hww] at hPS
      -- embed the component (an in-branching rooted at `y`) inside those positions: Corollary 1
      let G' : Digraph ℕ := ⟨fun p q => G.Adj (σ p) (σ q)⟩
      let _ : DecidableRel G'.Adj := fun p q => inferInstanceAs (Decidable (G.Adj (σ p) (σ q)))
      have hSw : ∀ p ∈ S, p < w := fun p hp => hPS.1 p (mem_union_right _ hp)
      obtain ⟨g, hginj, hgS, hgarc⟩ := OutTree.exists_inEmbedding_of_finset (G := G')
        (A.subtree y hyT hyr) (show 2 ≤ #B from hm2) S (show 2 * #B - 2 ≤ #S by rw [hS])
        (fun p _ => hG.1 (σ p))
        (fun p hp q hq hpq => hG.2 (σ p) (σ q) (fun h => hpq (hinj (show p ∈ Set.Iio w from hSw p hp)
          (show q ∈ Set.Iio w from hSw q hq) h)))
      have hgS' : ∀ z ∈ B, g z ∈ S := hgS
      have hgarc' : ∀ z ∈ B, z ≠ y → G.Adj (σ (g z)) (σ (g (A.par z))) := by
        intro z hz hzy
        have := hgarc z hz hzy
        simp only [subtree, if_neg hzy] at this
        exact this
      refine ⟨fun z => if z ∈ B then g z else f z, ?_, ?_, ?_⟩
      · intro a ha b hb hab
        simp only [mem_coe] at ha hb
        by_cases haB : a ∈ B <;> by_cases hbB : b ∈ B <;> simp only [haB, hbB, ite_true, ite_false] at hab
        · exact hginj haB hbB hab
        · exact absurd (mem_image_of_mem f (mem_filter.2 ⟨hb, hbB⟩))
            (disjoint_left.1 hSP (hab ▸ hgS' a haB))
        · exact absurd (mem_image_of_mem f (mem_filter.2 ⟨ha, haB⟩))
            (disjoint_left.1 hSP (hab.symm ▸ hgS' b hbB))
        · exact hfinj (mem_filter.2 ⟨ha, haB⟩) (mem_filter.2 ⟨hb, hbB⟩) hab
      · intro z hz hzr
        by_cases hzB : z ∈ B
        · by_cases hzy : z = y
          · have hx0B : A.par z ∉ B := hzy ▸ par_notMem_below hyT hyr
            simp only [hzB, hx0B, ite_true, ite_false]
            rw [hzy] at hzB ⊢
            refine ⟨fun _ => (hSx _ (hgS' _ hzB)).2, fun h => ?_⟩
            rw [hfy] at h; exact Bool.noConfusion h
          · have hfz := hB z hzB hzy
            have hpB : A.par z ∈ B := par_mem_below hzB hzy
            simp only [hzB, hpB, ite_true]
            refine ⟨fun h => ?_, fun _ => hgarc' z hzB hzy⟩
            rw [hfz] at h; exact Bool.noConfusion h
        · have hpB : A.par z ∉ B := fun h => hzB (mem_below_of_par hz h)
          simp only [hzB, hpB, ite_false]
          exact hfarc z (mem_filter.2 ⟨hz, hzB⟩) hzr
      · apply hPS.subset
        intro q hq
        obtain ⟨z, hz, rfl⟩ := mem_image.1 hq
        by_cases hzB : z ∈ B
        · simp only [hzB, ite_true]; exact mem_union_right _ (hgS' z hzB)
        · simp only [hzB, ite_false]
          exact mem_union_left _ (mem_image_of_mem f (mem_filter.2 ⟨hz, hzB⟩))
    · ------------------------------------------------------------------ a single node
      have hall : ∀ x ∈ A.T, x = A.r := by
        by_contra hx
        push Not at hx
        obtain ⟨x, hxT, hxr⟩ := hx
        have h2 : 2 ≤ #A.T := by
          have : ({A.r, x} : Finset α) ⊆ A.T := by
            intro z hz
            rcases mem_insert.1 hz with rfl | hz
            · exact A.root_mem
            · rw [mem_singleton.1 hz]; exact hxT
          have := card_le_card this
          rwa [card_pair (Ne.symm hxr)] at this
        obtain ⟨l, hlT, hlr, hl⟩ := A.exists_leaf h2
        have hfl : fwd l = false := by
          by_contra h
          exact hleaf ⟨l, hlT, hlr, by simpa using h, hl⟩
        exact htop (A.tops_nonempty fwd hsrc ⟨l, mem_filter.2 ⟨hlT, hlr, hfl⟩⟩)
      have hT : A.T = {A.r} := eq_singleton_iff_unique_mem.2 ⟨A.root_mem, hall⟩
      have hb0 : A.bwd fwd = ∅ := by
        rw [bwd, filter_eq_empty_iff]; intro x hx h; exact h.1 (hall x hx)
      have hc0 : A.tops fwd = ∅ := by
        rw [tops, filter_eq_empty_iff]; intro x hx h; exact h.1 (hall x hx)
      rw [hb0, hc0, card_empty] at hw
      rw [hT, card_singleton] at hn
      refine ⟨fun _ => 0, ?_, ?_, ?_⟩
      · intro a ha b hb _
        rw [hall a ha, hall b hb]
      · intro x hx hxr; exact absurd (hall x hx) hxr
      · rw [hT, image_singleton, show w = 2 by omega]
        exact isMSet_zero_two

/-- Theorem 1 in vertex terms: a finite tournament with at least `w = 2n + 2(b − c)` vertices contains every
well-rooted oriented tree on `n` nodes with `b` backward arcs and `c` backward components, arcs in their direction. -/
theorem exists_embedding_oriented [Fintype V] [DecidableEq V] (hG : G.IsTournament) (A : OutTree α)
    (fwd : α → Bool) (hsrc : ∀ x ∈ A.T, x ≠ A.r → A.par x = A.r → fwd x = true) (w : ℕ)
    (hw : w + 2 * #(A.tops fwd) = 2 * #A.T + 2 * #(A.bwd fwd)) (hV : w ≤ Fintype.card V) :
    ∃ g : α → V, Set.InjOn g A.T ∧
      ∀ x ∈ A.T, x ≠ A.r →
        (fwd x = true → G.Adj (g (A.par x)) (g x)) ∧ (fwd x = false → G.Adj (g x) (g (A.par x))) := by
  have hT1 : 1 ≤ #A.T := card_pos.2 ⟨A.r, A.root_mem⟩
  have hcb := A.card_tops_le fwd
  have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  let _ : Inhabited V := Classical.inhabited_of_nonempty this
  obtain ⟨σ, hinj, _, hmed⟩ := exists_localMedian hG
  obtain ⟨f, hfinj, hfarc, hM⟩ := exists_mEmbedding_oriented (σ := σ) hG #A.T A fwd rfl hsrc w hw
    ((hmed.mono le_rfl hV).toOut) (hinj.mono (Set.Iio_subset_Iio hV))
  have hfw : ∀ x ∈ A.T, f x < w := fun x hx => hM.1 _ (mem_image_of_mem f hx)
  refine ⟨fun x => σ (f x), fun a ha b hb hab => hfinj ha hb ?_, hfarc⟩
  exact hinj (show f a ∈ Set.Iio (Fintype.card V) from lt_of_lt_of_le (hfw a ha) hV)
    (show f b ∈ Set.Iio (Fintype.card V) from lt_of_lt_of_le (hfw b hb) hV) hab

end OutTree

end SumnerFC

/- ===== SumnerFC/Corollary2.lean ===== -/

/-!
# El Sahili's Corollary 2: the `3n − 3` bound, by choice of root and of converse

El Sahili, *Trees in tournaments*, JCTB 92 (2004) 183–187, Corollary 2.

The oriented tree is an `OutTree` (any root) together with an arc relation `adj` that orients each tree edge
`{x, par x}` in exactly one direction (`hor`). `Realizes A adj G g` says `g` is injective on the nodes and maps every
tree arc onto an arc of `G` in its own direction.

The paper chooses the root to minimise `d = b − c`, says the root is then a source, and then takes the converse
"if needed" to get `b ≤ (n − 1)/2`, without checking that the converse is still well-rooted at that root (gap 2 of
`PLAN.md`). This file minimises **`b`** instead, over roots and over `adj`/converse, which needs no bookkeeping of `c`:
re-rooting at a backward child `u` of the root lowers `b` by exactly one, so a root of least `b` is a source, and
`b + b′ = n − 1` gives `2b ≤ n − 1` at it.

* `reroot`: re-root an `OutTree` at a child `u` of its root. The node set and the set of tree edges are unchanged
  (`Realizes.of_reroot`), and the backward set loses exactly `u` (`bwd_reroot`).
* `card_bwd_add_card_bwd_flip`: at any root, `b(adj) + b(converse) = n − 1`, so one of the two has `2b ≤ n − 1`.
* `exists_realizes_of_le`: by induction on `b`, re-root at backward children (each step keeps `2b ≤ n − 1`) until
  the root is a source. Then `b = 0` is an out-branching (Corollary 1, window `2n − 2`, which is what `n = 2` needs);
  otherwise a backward component exists (`tops_nonempty`), so `c ≥ 1` and Theorem 1's window
  `2n + 2b − 2c ≤ 2n + (n − 1) − 2 = 3n − 3`.
* `exists_realizes`: Corollary 2. Every oriented tree on `n ≥ 2` nodes embeds, arcs in their direction, in every
  tournament with at least `3n − 3` vertices (the converse case runs in `rev G`).
-/

open Finset

namespace SumnerFC

namespace OutTree

variable {α : Type*} [DecidableEq α]

/-! ### Re-rooting at a child of the root -/

/-- Re-root `A` at a child `u` of its root: `par r = u`, `par u = u`, every other parent unchanged. The new rank is
`rk − rk u` below `u` and `rk + 1` elsewhere. -/
noncomputable def reroot (A : OutTree α) (u : α) (hu : u ∈ A.T) (hur : u ≠ A.r) : OutTree α where
  T := A.T
  r := u
  par := fun x => if x = A.r then u else if x = u then u else A.par x
  rk := fun x => if x ∈ A.below u then A.rk x - A.rk u else A.rk x + 1
  root_mem := hu
  par_root := by simp [hur]
  par_mem := by
    intro x hx
    by_cases hxr : x = A.r
    · simp [hxr, hu]
    by_cases hxu : x = u
    · simp [hxu, hu]
    · simp only [hxr, hxu, ite_false]; exact A.par_mem x hx
  rk_lt := by
    intro x hx hxu
    by_cases hxr : x = A.r
    · subst hxr
      simp only [ite_true, self_mem_below hu, root_notMem_below hur, ite_false, Nat.sub_self]
      omega
    simp only [hxr, hxu, ite_false]
    have hlt := A.rk_lt x hx hxr
    by_cases hxB : x ∈ A.below u
    · have hpB := par_mem_below hxB hxu
      have hle : A.rk u ≤ A.rk (A.par x) := by
        by_cases hpu : A.par x = u
        · rw [hpu]
        · exact (rk_lt_of_mem_below hur hpB hpu).le
      simp only [hpB, hxB, ite_true]
      omega
    · have hpB : A.par x ∉ A.below u := fun h => hxB (mem_below_of_par hx h)
      simp only [hpB, hxB, ite_false]
      omega

@[simp] lemma reroot_T (A : OutTree α) (u : α) (hu : u ∈ A.T) (hur : u ≠ A.r) : (A.reroot u hu hur).T = A.T := rfl
@[simp] lemma reroot_r (A : OutTree α) (u : α) (hu : u ∈ A.T) (hur : u ≠ A.r) : (A.reroot u hu hur).r = u := rfl

lemma reroot_par_root (A : OutTree α) (u : α) (hu : u ∈ A.T) (hur : u ≠ A.r) :
    (A.reroot u hu hur).par A.r = u := by
  show (if A.r = A.r then u else _) = u
  exact if_pos rfl

lemma reroot_par_of_ne (A : OutTree α) (u : α) (hu : u ∈ A.T) (hur : u ≠ A.r) {x : α} (hxr : x ≠ A.r)
    (hxu : x ≠ u) : (A.reroot u hu hur).par x = A.par x := by
  show (if x = A.r then u else if x = u then u else A.par x) = A.par x
  rw [if_neg hxr, if_neg hxu]

/-! ### Orientations and realisations -/

instance instDecidableRelFlip (adj : α → α → Prop) [DecidableRel adj] : DecidableRel (flip adj) :=
  fun a b => inferInstanceAs (Decidable (adj b a))

/-- `adj` orients every tree edge `{x, par x}` in exactly one direction. -/
def IsOrient (A : OutTree α) (adj : α → α → Prop) : Prop :=
  ∀ x ∈ A.T, x ≠ A.r → (adj (A.par x) x ↔ ¬ adj x (A.par x))

/-- The forward flag of `adj`: `true` on a node whose tree edge points away from the root. -/
def fwdOf (A : OutTree α) (adj : α → α → Prop) [DecidableRel adj] : α → Bool :=
  fun x => decide (adj (A.par x) x)

/-- `g` is injective on the nodes and maps every tree arc onto an arc of `G` in its own direction. -/
def Realizes {V : Type*} (A : OutTree α) (adj : α → α → Prop) (G : Digraph V) (g : α → V) : Prop :=
  Set.InjOn g A.T ∧ ∀ x ∈ A.T, x ≠ A.r →
    (adj (A.par x) x → G.Adj (g (A.par x)) (g x)) ∧ (adj x (A.par x) → G.Adj (g x) (g (A.par x)))

lemma IsOrient.reroot {A : OutTree α} {adj : α → α → Prop} (h : A.IsOrient adj) {u : α} (hu : u ∈ A.T)
    (hur : u ≠ A.r) (hpu : A.par u = A.r) : (A.reroot u hu hur).IsOrient adj := by
  intro x hx hxu
  simp only [reroot_r] at hxu
  by_cases hxr : x = A.r
  · subst hxr
    rw [reroot_par_root]
    have := h u hu hur
    rw [hpu] at this
    tauto
  · rw [reroot_par_of_ne A u hu hur hxr hxu]
    exact h x hx hxr

/-- The tree edges of `A` and of its re-rooting coincide, so a realisation of one is a realisation of the other. -/
lemma Realizes.of_reroot {V : Type*} {G : Digraph V} {A : OutTree α} {adj : α → α → Prop} {u : α} (hu : u ∈ A.T)
    (hur : u ≠ A.r) (hpu : A.par u = A.r) {g : α → V} (h : (A.reroot u hu hur).Realizes adj G g) :
    A.Realizes adj G g := by
  refine ⟨h.1, fun x hx hxr => ?_⟩
  by_cases hxu : x = u
  · subst hxu
    have := h.2 A.r A.root_mem (Ne.symm hur)
    rw [reroot_par_root] at this
    rw [hpu]
    exact ⟨this.2, this.1⟩
  · have := h.2 x hx hxu
    rwa [reroot_par_of_ne A u hu hur hxr hxu] at this

lemma mem_bwd_fwdOf {A : OutTree α} {adj : α → α → Prop} [DecidableRel adj] (h : A.IsOrient adj) {x : α} :
    x ∈ A.bwd (A.fwdOf adj) ↔ x ∈ A.T ∧ x ≠ A.r ∧ adj x (A.par x) := by
  unfold bwd fwdOf
  rw [mem_filter]
  constructor
  · rintro ⟨hx, hxr, hf⟩
    refine ⟨hx, hxr, ?_⟩
    have := h x hx hxr
    simp only [decide_eq_false_iff_not] at hf
    tauto
  · rintro ⟨hx, hxr, ha⟩
    refine ⟨hx, hxr, ?_⟩
    have := h x hx hxr
    simp only [decide_eq_false_iff_not]
    tauto

/-- Re-rooting at a backward child `u` of the root removes exactly `u` from the backward set. -/
lemma bwd_reroot {A : OutTree α} {adj : α → α → Prop} [DecidableRel adj] (h : A.IsOrient adj) {u : α}
    (hu : u ∈ A.T) (hur : u ≠ A.r) (hpu : A.par u = A.r) (hbu : adj u A.r) :
    (A.reroot u hu hur).bwd ((A.reroot u hu hur).fwdOf adj) = (A.bwd (A.fwdOf adj)).erase u := by
  ext x
  rw [mem_bwd_fwdOf (h.reroot hu hur hpu), mem_erase, mem_bwd_fwdOf h, reroot_T, reroot_r]
  constructor
  · rintro ⟨hx, hxu, ha⟩
    have hxr : x ≠ A.r := by
      rintro rfl
      rw [reroot_par_root] at ha
      have := h u hu hur
      rw [hpu] at this
      tauto
    rw [reroot_par_of_ne A u hu hur hxr hxu] at ha
    exact ⟨hxu, hx, hxr, ha⟩
  · rintro ⟨hxu, hx, hxr, ha⟩
    refine ⟨hx, hxu, ?_⟩
    rwa [reroot_par_of_ne A u hu hur hxr hxu]

/-- `b(adj) + b(converse) = n − 1` at any root. -/
lemma card_bwd_add_card_bwd_flip {A : OutTree α} {adj : α → α → Prop} [DecidableRel adj] (h : A.IsOrient adj) :
    #(A.bwd (A.fwdOf adj)) + #(A.bwd (A.fwdOf (flip adj))) + 1 = #A.T := by
  have hflip : A.IsOrient (flip adj) := fun x hx hxr => by
    have := h x hx hxr
    simp only [flip]
    tauto
  have h1 : A.bwd (A.fwdOf adj) = (A.T.erase A.r).filter (fun x => adj x (A.par x)) := by
    ext x; rw [mem_bwd_fwdOf h, mem_filter, mem_erase]; tauto
  have h2 : A.bwd (A.fwdOf (flip adj)) = (A.T.erase A.r).filter (fun x => ¬ adj x (A.par x)) := by
    ext x
    rw [mem_bwd_fwdOf hflip, mem_filter, mem_erase]
    simp only [flip]
    constructor
    · rintro ⟨hx, hxr, ha⟩; have := h x hx hxr; exact ⟨⟨hxr, hx⟩, by tauto⟩
    · rintro ⟨⟨hxr, hx⟩, ha⟩; have := h x hx hxr; exact ⟨hx, hxr, by tauto⟩
  rw [h1, h2, card_filter_add_card_filter_not, card_erase_of_mem A.root_mem]
  have : 1 ≤ #A.T := card_pos.2 ⟨A.r, A.root_mem⟩
  omega

/-! ### Corollary 2 -/

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]

/-- The well-rooted case: root a source and `2b ≤ n − 1`. -/
theorem exists_realizes_wellRooted (hG : G.IsTournament) (A : OutTree α) (adj : α → α → Prop) [DecidableRel adj]
    (h : A.IsOrient adj) (hn : 2 ≤ #A.T) (hb : 2 * #(A.bwd (A.fwdOf adj)) + 1 ≤ #A.T)
    (hsrc : ∀ x ∈ A.T, x ≠ A.r → A.par x = A.r → A.fwdOf adj x = true)
    (hV : 3 * #A.T - 3 ≤ Fintype.card V) : ∃ g : α → V, A.Realizes adj G g := by
  -- a node is backward iff its arc points to its parent
  have hback : ∀ x ∈ A.T, x ≠ A.r → (A.fwdOf adj x = false ↔ adj x (A.par x)) := by
    intro x hx hxr
    have := mem_bwd_fwdOf (A := A) h (x := x)
    unfold bwd at this
    rw [mem_filter] at this
    constructor
    · intro hf; exact (this.1 ⟨hx, hxr, hf⟩).2.2
    · intro ha; exact (this.2 ⟨hx, hxr, ha⟩).2.2
  rcases (A.bwd (A.fwdOf adj)).eq_empty_or_nonempty with hemp | hne
  · -- out-branching: Corollary 1 (window `2n − 2`), via in-branchings of `rev G`
    obtain ⟨g, hginj, -, hgarc⟩ := A.exists_inEmbedding_of_finset (G := rev G) hn univ
      (by rw [card_univ]; omega) (fun v _ => hG.1 v)
      (fun a _ b _ hab => by
        show G.Adj b a ↔ ¬ G.Adj a b
        exact hG.2 b a (Ne.symm hab))
    refine ⟨g, hginj, fun x hx hxr => ⟨fun _ => hgarc x hx hxr, fun ha => ?_⟩⟩
    have : x ∈ A.bwd (A.fwdOf adj) := (mem_bwd_fwdOf h).2 ⟨hx, hxr, ha⟩
    rw [hemp] at this
    exact absurd this (notMem_empty x)
  · -- Theorem 1 with `c ≥ 1`
    have hc := card_pos.2 (A.tops_nonempty (A.fwdOf adj) hsrc hne)
    have hcb := A.card_tops_le (A.fwdOf adj)
    obtain ⟨g, hginj, hgarc⟩ := A.exists_embedding_oriented hG (A.fwdOf adj) hsrc
      (2 * #A.T + 2 * #(A.bwd (A.fwdOf adj)) - 2 * #(A.tops (A.fwdOf adj))) (by omega) (by omega)
    refine ⟨g, hginj, fun x hx hxr => ⟨fun ha => (hgarc x hx hxr).1 ?_, fun ha => (hgarc x hx hxr).2 ?_⟩⟩
    · simp only [fwdOf, decide_eq_true_eq]; exact ha
    · exact (hback x hx hxr).2 ha

/-- Induction on `b`: re-root at backward children of the root until it is a source; `2b ≤ n − 1` is kept. -/
theorem exists_realizes_of_le (hG : G.IsTournament) (adj : α → α → Prop) [DecidableRel adj] :
    ∀ (k : ℕ) (A : OutTree α), #(A.bwd (A.fwdOf adj)) = k → A.IsOrient adj → 2 ≤ #A.T →
      2 * k + 1 ≤ #A.T → 3 * #A.T - 3 ≤ Fintype.card V → ∃ g : α → V, A.Realizes adj G g := by
  intro k
  induction k with
  | zero =>
    intro A hk h hn hb hV
    refine A.exists_realizes_wellRooted hG adj h hn (by omega) (fun x hx hxr _ => ?_) hV
    by_contra hf
    have : x ∈ A.bwd (A.fwdOf adj) := mem_filter.2 ⟨hx, hxr, by simpa using hf⟩
    rw [card_eq_zero.1 hk] at this
    exact notMem_empty x this
  | succ k ih =>
    intro A hk h hn hb hV
    by_cases hsrc : ∀ x ∈ A.T, x ≠ A.r → A.par x = A.r → A.fwdOf adj x = true
    · exact A.exists_realizes_wellRooted hG adj h hn (by omega) hsrc hV
    push Not at hsrc
    obtain ⟨u, hu, hur, hpu, hfu⟩ := hsrc
    have hbu : u ∈ A.bwd (A.fwdOf adj) := mem_filter.2 ⟨hu, hur, by simpa using hfu⟩
    have hadj : adj u A.r := by
      have := ((mem_bwd_fwdOf h).1 hbu).2.2
      rwa [hpu] at this
    have hk' : #((A.reroot u hu hur).bwd ((A.reroot u hu hur).fwdOf adj)) = k := by
      rw [bwd_reroot h hu hur hpu hadj, card_erase_of_mem hbu, hk, Nat.add_sub_cancel]
    obtain ⟨g, hg⟩ := ih (A.reroot u hu hur) hk' (h.reroot hu hur hpu) hn (by simp only [reroot_T]; omega) hV
    exact ⟨g, Realizes.of_reroot hu hur hpu hg⟩

/-- **Corollary 2** (El Sahili). Every oriented tree on `n ≥ 2` nodes, rooted anywhere, embeds with every arc in its
direction into every tournament with at least `3n − 3` vertices. -/
theorem exists_realizes (hG : G.IsTournament) (A : OutTree α) (adj : α → α → Prop) [DecidableRel adj]
    (h : A.IsOrient adj) (hn : 2 ≤ #A.T) (hV : 3 * #A.T - 3 ≤ Fintype.card V) :
    ∃ g : α → V, A.Realizes adj G g := by
  have hsum := card_bwd_add_card_bwd_flip h
  by_cases hb : 2 * #(A.bwd (A.fwdOf adj)) + 1 ≤ #A.T
  · exact exists_realizes_of_le hG adj _ A rfl h hn hb hV
  · -- the converse has `2b ≤ n − 1`: embed it in `rev G`
    have hflip : A.IsOrient (flip adj) := fun x hx hxr => by
      have := h x hx hxr
      simp only [flip]
      tauto
    have hGr : (rev G).IsTournament :=
      ⟨fun v => hG.1 v, fun a b hab => by
        show G.Adj b a ↔ ¬ G.Adj a b
        exact hG.2 b a (Ne.symm hab)⟩
    obtain ⟨g, hginj, hg⟩ :=
      exists_realizes_of_le (G := rev G) hGr (flip adj) _ A rfl hflip hn (by omega) hV
    exact ⟨g, hginj, fun x hx hxr => ⟨(hg x hx hxr).2, (hg x hx hxr).1⟩⟩

end OutTree

end SumnerFC

/- ===== SumnerFC/TreeGlue.lean ===== -/

/-!
# From formal-conjectures' oriented trees to `OutTree`: rung E5

formal-conjectures states an oriented tree as `∃ T : SimpleGraph W, T.IsTree ∧ D.IsOrientation T`. This file roots
the tree `T` at any vertex `r` and builds the `OutTree` of Corollary 2 on the whole vertex set:

* `pathTo x` is the unique path from `x` to `r` (trees have unique paths);
* `par x` is its second vertex (`r` for `x = r`), `rk x` is its length;
* `pathTo_eq_cons`: for `x ≠ r` the path is the edge `x — par x` followed by `pathTo (par x)`, so `rk` drops;
* `adj_eq_par`: every tree edge is a parent edge, `T.Adj u v → u = par v ∨ v = par u` (path uniqueness);
* `embeds_of_isTree`: Corollary 2 at this root, read back as an injective digraph homomorphism.

No distance function is used: the rank is the length of the unique path, and the only tree fact is path uniqueness.
-/

open Finset

namespace SumnerFC

namespace TreeRoot

variable {W : Type*} {T : SimpleGraph W} (hT : T.IsTree) (r : W)

/-- The unique path from `x` to the root `r`. -/
noncomputable def pathTo (x : W) : T.Walk x r := (hT.existsUnique_path x r).exists.choose

lemma pathTo_isPath (x : W) : (pathTo hT r x).IsPath := (hT.existsUnique_path x r).exists.choose_spec

lemma eq_pathTo {x : W} (p : T.Walk x r) (hp : p.IsPath) : p = pathTo hT r x :=
  (hT.existsUnique_path x r).unique hp (pathTo_isPath hT r x)

/-- The parent: the second vertex of the path to the root (`r` itself at the root). -/
noncomputable def par (x : W) : W := (pathTo hT r x).getVert 1

/-- The rank: the length of the path to the root. -/
noncomputable def rk (x : W) : ℕ := (pathTo hT r x).length

lemma pathTo_eq_cons {x : W} (hx : x ≠ r) :
    ∃ h : T.Adj x (par hT r x), pathTo hT r x = SimpleGraph.Walk.cons h (pathTo hT r (par hT r x)) := by
  unfold par
  have hp := pathTo_isPath hT r x
  have key : ∀ p : T.Walk x r, p.IsPath → p = pathTo hT r x →
      ∃ h : T.Adj x (p.getVert 1), p = SimpleGraph.Walk.cons h (pathTo hT r (p.getVert 1)) := by
    intro p hp _
    cases p with
    | nil => exact absurd rfl hx
    | @cons _ y _ h q =>
      have e1 : (SimpleGraph.Walk.cons h q).getVert 1 = y := by simp
      rw [e1]
      exact ⟨h, congrArg _ (eq_pathTo hT r q hp.of_cons)⟩
  obtain ⟨h, e⟩ := key _ hp rfl
  exact ⟨h, e⟩

lemma par_root : par hT r r = r := by
  unfold par
  have : pathTo hT r r = SimpleGraph.Walk.nil := (eq_pathTo hT r _ SimpleGraph.Walk.IsPath.nil).symm
  rw [this]
  simp

lemma rk_par_lt {x : W} (hx : x ≠ r) : rk hT r (par hT r x) < rk hT r x := by
  obtain ⟨h, e⟩ := pathTo_eq_cons hT r hx
  unfold rk
  conv_rhs => rw [e]
  simp

/-- Every edge of the tree is a parent edge. -/
lemma adj_eq_par {u v : W} (huv : T.Adj u v) : u = par hT r v ∨ v = par hT r u := by
  classical
  by_cases hu : u ∈ (pathTo hT r v).support
  · left
    have hp := pathTo_isPath hT r v
    have hq : ((pathTo hT r v).takeUntil u hu).IsPath := hp.takeUntil hu
    have hsingle : (SimpleGraph.Walk.cons huv.symm SimpleGraph.Walk.nil : T.Walk v u).IsPath :=
      SimpleGraph.Walk.IsPath.nil.cons (by simpa using huv.ne.symm)
    have hqe : (pathTo hT r v).takeUntil u hu = SimpleGraph.Walk.cons huv.symm SimpleGraph.Walk.nil :=
      (hT.existsUnique_path v u).unique hq hsingle
    have hspec := (pathTo hT r v).take_spec hu
    unfold par
    rw [← hspec]
    rw [hqe]
    simp
  · right
    have hp : (SimpleGraph.Walk.cons huv (pathTo hT r v)).IsPath :=
      (pathTo_isPath hT r v).cons hu
    have he := eq_pathTo hT r _ hp
    unfold par
    rw [← he]
    simp

variable [Fintype W] [DecidableEq W]

/-- The `OutTree` on all of `W`, rooted at `r`. -/
noncomputable def outTree : OutTree W where
  T := univ
  r := r
  par := par hT r
  rk := rk hT r
  root_mem := mem_univ r
  par_root := par_root hT r
  par_mem := fun _ _ => mem_univ _
  rk_lt := fun _ _ hx => rk_par_lt hT r hx

end TreeRoot

open TreeRoot in
/-- **E5.** An orientation `D` of a tree on `n ≥ 2` vertices embeds in every tournament on at least `3n − 3`
vertices: Corollary 2 at any root, read back as an injective digraph homomorphism. -/
theorem embeds_of_isTree {W : Type*} [Fintype W] [DecidableEq W] (D : Digraph W) [DecidableRel D.Adj]
    {T : SimpleGraph W} (hT : T.IsTree) (hor : D.IsOrientation T) (hn : 2 ≤ Fintype.card W)
    {V : Type*} [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (hV : 3 * Fintype.card W - 3 ≤ Fintype.card V) (hG : G.IsTournament) :
    ∃ f : D →g G, Function.Injective f := by
  have hne : Nonempty W := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨r⟩ := hne
  set A := outTree hT r with hA
  have hAT : A.T = univ := rfl
  have horient : A.IsOrient D.Adj := by
    intro x _ hx
    obtain ⟨h, _⟩ := pathTo_eq_cons hT r hx
    exact hor.2 _ _ h.symm
  have hcard : #A.T = Fintype.card W := by rw [hAT, card_univ]
  obtain ⟨g, hinj, hg⟩ :=
    A.exists_realizes hG D.Adj horient (by rw [hcard]; exact hn) (by rw [hcard]; exact hV)
  refine ⟨⟨g, fun {u v} huv => ?_⟩, ?_⟩
  · rcases adj_eq_par hT r (hor.1 u v huv) with e | e
    · have hv : v ≠ r := by
        rintro rfl
        rw [par_root] at e
        subst e
        exact (hor.1 _ _ huv).ne rfl
      have := (hg v (mem_univ v) hv).1
      change D.Adj (par hT r v) v → G.Adj (g (par hT r v)) (g v) at this
      rw [← e] at this
      exact this huv
    · have hu : u ≠ r := by
        rintro rfl
        rw [par_root] at e
        subst e
        exact (hor.1 _ _ huv).ne rfl
      have := (hg u (mem_univ u) hu).2
      change D.Adj u (par hT r u) → G.Adj (g u) (g (par hT r u)) at this
      rw [← e] at this
      exact this huv
  · intro x y hxy
    exact hinj (by simp [hAT]) (by simp [hAT]) hxy

end SumnerFC

end OMAPort_Sumner

open SimpleGraph Digraph SumnerUniversalTournamentConjecture in
theorem OMA.solution :
    type_of% @SumnerUniversalTournamentConjecture.sumner_conjecture.variants.el_sahili := by
  intro n hn W _ _ D _ hW hD V _ _ G _ hV hG
  obtain ⟨T, hT, hor⟩ := hD
  subst hW
  exact OMAPort_Sumner.SumnerFC.embeds_of_isTree D hT hor hn G hV.ge hG
