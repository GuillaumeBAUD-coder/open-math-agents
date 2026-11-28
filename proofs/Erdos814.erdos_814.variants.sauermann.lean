import FormalConjectures.ErdosProblems.«814»
import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

section
namespace P814

def edgeThreshold (k n : ℕ) : ℕ :=
  (k - 1) * (n + 2 - k) + (k - 2).choose 2 + 1

def Tmax (k : ℕ) : ℤ :=
  (((k - 1) * (k - 2) : ℕ) : ℤ) - ((k - 2).choose 2 : ℤ)

def problemT (k : ℕ) : ℤ :=
  Tmax k - 1

def uniformDen (k : ℕ) : ℕ :=
  10000 * k ^ 3

theorem edgeThreshold_cast_eq (k n : ℕ) (hk : 2 ≤ k) (hn : k - 1 ≤ n) :
    (edgeThreshold k n : ℤ) = (((k - 1) * n : ℕ) : ℤ) - problemT k := by
  have hkn : k ≤ n + 2 := by omega
  have hk1 : 1 ≤ k := by omega
  have hk2 : 2 ≤ k := hk
  simp only [edgeThreshold, problemT, Tmax]
  push_cast [Nat.cast_sub hkn, Nat.cast_sub hk1, Nat.cast_sub hk2]
  ring

@[simp] theorem problemT_two : problemT 2 = -1 := by
  norm_num [problemT, Tmax]

theorem problemT_add_one_le_Tmax (k : ℕ) : problemT k + 1 ≤ Tmax k := by
  simp [problemT]

theorem Tmax_le_sq (k : ℕ) : Tmax k ≤ (k ^ 2 : ℕ) := by
  have hmul : (k - 1) * (k - 2) ≤ k * k :=
    Nat.mul_le_mul (Nat.sub_le k 1) (Nat.sub_le k 2)
  calc
    Tmax k ≤ (((k - 1) * (k - 2) : ℕ) : ℤ) := by
      simp [Tmax]
    _ ≤ ((k * k : ℕ) : ℤ) := by exact_mod_cast hmul
    _ = (k ^ 2 : ℕ) := by simp [pow_two]

theorem uniformDen_pos (k : ℕ) (hk : 2 ≤ k) : 0 < uniformDen k := by
  simp only [uniformDen]
  positivity

theorem uniformDen_one_le (k : ℕ) (hk : 2 ≤ k) : 1 ≤ uniformDen k := by
  exact uniformDen_pos k hk

theorem uniformDen_cast (k : ℕ) :
    (uniformDen k : ℝ) = 10000 * (k : ℝ) ^ 3 := by
  norm_num [uniformDen]

theorem card_le_one_sub_inv_mul
    (k card n : ℕ) (hk : 2 ≤ k)
    (hsmall : uniformDen k * card ≤ (uniformDen k - 1) * n) :
    (card : ℝ) ≤ (1 - 1 / (10000 * (k : ℝ) ^ 3)) * (n : ℝ) := by
  have hDposNat : 0 < uniformDen k := uniformDen_pos k hk
  have hDpos : (0 : ℝ) < uniformDen k := by exact_mod_cast hDposNat
  have hsmall' :
      (uniformDen k : ℝ) * (card : ℝ) ≤
        ((uniformDen k - 1 : ℕ) : ℝ) * (n : ℝ) := by
    exact_mod_cast hsmall
  have hsubcast :
      ((uniformDen k - 1 : ℕ) : ℝ) = (uniformDen k : ℝ) - 1 := by
    rw [Nat.cast_sub (uniformDen_one_le k hk)]
    norm_num
  rw [hsubcast] at hsmall'
  have hcoef :
      1 - 1 / (10000 * (k : ℝ) ^ 3) =
        ((uniformDen k : ℝ) - 1) / (uniformDen k : ℝ) := by
    rw [← uniformDen_cast]
    field_simp
  rw [hcoef, div_mul_eq_mul_div]
  apply (le_div_iff₀ hDpos).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hsmall'

end P814

end

section
open scoped Sym2
open Finset SimpleGraph BigOperators

namespace P814

variable {V : Type*} [Fintype V] [DecidableEq V]

def edgeOn (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => e.toFinset ⊆ A

def edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : ℕ :=
  #(edgeOn G A)

def degreeOn (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (v : V) : ℕ :=
  #(G.neighborFinset v ∩ A)

def incidentEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V) : Finset (Sym2 V) :=
  edgeOn G A \ edgeOn G (A \ X)

def incidentCount (G : SimpleGraph V) [DecidableRel G.Adj] (A X : Finset V) : ℕ :=
  #(incidentEdges G A X)

def HasMinDegreeOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) : Prop :=
  A.Nonempty ∧ ∀ v ∈ A, k ≤ degreeOn G A v

def AdjacentSets (G : SimpleGraph V) (X Y : Finset V) : Prop :=
  ∃ x ∈ X, ∃ y ∈ Y, G.Adj x y

def shortage (k : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) : ℤ :=
  (((k - 1 : ℕ) : ℤ) * (A.card : ℤ)) - (edgeCount G A : ℤ)

def deletionPotential (k : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V) : ℤ :=
  (((k - 1 : ℕ) : ℤ) * (X.card : ℤ)) - (incidentCount G A X : ℤ)

@[simp] lemma mem_edgeOn {G : SimpleGraph V} [DecidableRel G.Adj]
    {A : Finset V} {e : Sym2 V} :
    e ∈ edgeOn G A ↔ e ∈ G.edgeFinset ∧ e.toFinset ⊆ A := by
  simp [edgeOn]

@[simp] lemma edgeOn_empty (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeOn G ∅ = ∅ := by
  ext e
  induction e using Sym2.inductionOn with
  | _ x y => simp [edgeOn]

@[simp] lemma edgeCount_empty (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeCount G ∅ = 0 := by
  simp [edgeCount]

@[simp] lemma edgeOn_univ (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeOn G univ = G.edgeFinset := by
  ext e
  simp [edgeOn]

@[simp] lemma edgeCount_univ (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeCount G univ = #G.edgeFinset := by
  simp [edgeCount]

lemma edgeOn_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (hAB : A ⊆ B) : edgeOn G A ⊆ edgeOn G B := by
  intro e he
  exact mem_edgeOn.mpr ⟨(mem_edgeOn.mp he).1, (mem_edgeOn.mp he).2.trans hAB⟩

lemma edgeCount_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (hAB : A ⊆ B) : edgeCount G A ≤ edgeCount G B := by
  exact card_le_card (edgeOn_mono G hAB)

lemma degreeOn_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (hAB : A ⊆ B) (v : V) : degreeOn G A v ≤ degreeOn G B v := by
  unfold degreeOn
  apply card_le_card
  intro x hx
  exact mem_inter.mpr ⟨(mem_inter.mp hx).1, hAB (mem_inter.mp hx).2⟩

lemma degreeOn_le_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (v : V) : degreeOn G A v ≤ A.card := by
  unfold degreeOn
  exact card_le_card inter_subset_right

lemma degreeOn_lt_card (G : SimpleGraph V) [DecidableRel G.Adj]
    {A : Finset V} {v : V} (hv : v ∈ A) : degreeOn G A v < A.card := by
  unfold degreeOn
  apply card_lt_card
  constructor
  · exact inter_subset_right
  · intro hreverse
    have hv' := hreverse hv
    exact G.notMem_neighborFinset_self v (mem_inter.mp hv').1

@[simp] lemma incidentEdges_empty (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) : incidentEdges G A ∅ = ∅ := by
  simp [incidentEdges]

@[simp] lemma incidentCount_empty (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) : incidentCount G A ∅ = 0 := by
  simp [incidentCount]

lemma incidentEdges_subset_edgeOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V) : incidentEdges G A X ⊆ edgeOn G A := by
  exact sdiff_subset

lemma edgeOn_sdiff_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V) : edgeOn G (A \ X) ⊆ edgeOn G A :=
  edgeOn_mono G sdiff_subset

lemma edgeOn_sdiff_union_incidentEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V) :
    edgeOn G (A \ X) ∪ incidentEdges G A X = edgeOn G A := by
  rw [incidentEdges, union_comm]
  simpa [union_comm] using union_sdiff_of_subset (edgeOn_sdiff_subset G A X)

lemma edgeCount_sdiff_add_incidentCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X : Finset V) :
    edgeCount G (A \ X) + incidentCount G A X = edgeCount G A := by
  rw [edgeCount, incidentCount, incidentEdges,
    card_sdiff_of_subset (edgeOn_sdiff_subset G A X)]
  exact Nat.add_sub_of_le (card_le_card (edgeOn_sdiff_subset G A X))

lemma incidentEdges_union (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X Y : Finset V) :
    incidentEdges G A (X ∪ Y) = incidentEdges G A X ∪ incidentEdges G A Y := by
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [incidentEdges, mem_sdiff, mem_edgeOn, Sym2.toFinset_mk_eq,
        insert_subset_iff, singleton_subset_iff, mem_union]
      tauto

lemma incidentEdges_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) {X Y : Finset V} (hXY : X ⊆ Y) :
    incidentEdges G A X ⊆ incidentEdges G A Y := by
  intro e he
  have he' : e ∈ incidentEdges G A (X ∪ Y) := by
    rw [incidentEdges_union]
    exact mem_union_left _ he
  simpa [union_eq_right.mpr hXY] using he'

lemma incidentCount_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) {X Y : Finset V} (hXY : X ⊆ Y) :
    incidentCount G A X ≤ incidentCount G A Y := by
  exact card_le_card (incidentEdges_mono G A hXY)

lemma incidentCount_union_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X Y : Finset V) :
    incidentCount G A (X ∪ Y) ≤ incidentCount G A X + incidentCount G A Y := by
  rw [incidentCount, incidentEdges_union]
  exact card_union_le _ _

lemma incidentCount_union_add_inter (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X Y : Finset V) :
    incidentCount G A (X ∪ Y) +
        #(incidentEdges G A X ∩ incidentEdges G A Y) =
      incidentCount G A X + incidentCount G A Y := by
  rw [incidentCount, incidentEdges_union]
  exact card_union_add_card_inter _ _

omit [Fintype V] [DecidableEq V] in
lemma AdjacentSets.symm {G : SimpleGraph V} {X Y : Finset V}
    (h : AdjacentSets G X Y) : AdjacentSets G Y X := by
  rcases h with ⟨x, hx, y, hy, hxy⟩
  exact ⟨y, hy, x, hx, hxy.symm⟩

lemma incidentCount_union_add_one_le_of_adjacent
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A X Y : Finset V} (hXA : X ⊆ A) (hYA : Y ⊆ A)
    (hXY : AdjacentSets G X Y) :
    incidentCount G A (X ∪ Y) + 1 ≤ incidentCount G A X + incidentCount G A Y := by
  rcases hXY with ⟨x, hx, y, hy, hxy⟩
  have heX : s(x, y) ∈ incidentEdges G A X := by
    simp only [incidentEdges, mem_sdiff, mem_edgeOn, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet, Sym2.toFinset_mk_eq, insert_subset_iff,
      singleton_subset_iff, mem_sdiff]
    refine ⟨⟨hxy, hXA hx, hYA hy⟩, ?_⟩
    tauto
  have heY : s(x, y) ∈ incidentEdges G A Y := by
    simp only [incidentEdges, mem_sdiff, mem_edgeOn, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet, Sym2.toFinset_mk_eq, insert_subset_iff,
      singleton_subset_iff, mem_sdiff]
    refine ⟨⟨hxy, hXA hx, hYA hy⟩, ?_⟩
    tauto
  have hone : 1 ≤ #(incidentEdges G A X ∩ incidentEdges G A Y) := by
    exact card_pos.mpr ⟨s(x, y), mem_inter.mpr ⟨heX, heY⟩⟩
  calc
    incidentCount G A (X ∪ Y) + 1 ≤
        incidentCount G A (X ∪ Y) +
          #(incidentEdges G A X ∩ incidentEdges G A Y) :=
      Nat.add_le_add_left hone _
    _ = incidentCount G A X + incidentCount G A Y :=
      incidentCount_union_add_inter G A X Y

lemma shortage_sdiff (k : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    {A X : Finset V} (hXA : X ⊆ A) :
    shortage k G (A \ X) = shortage k G A - deletionPotential k G A X := by
  have hcard : (A \ X).card + X.card = A.card := by
    rw [card_sdiff_of_subset hXA]
    exact Nat.sub_add_cancel (card_le_card hXA)
  have hedge := edgeCount_sdiff_add_incidentCount G A X
  have hcardZsum : ((A \ X).card : ℤ) + (X.card : ℤ) = (A.card : ℤ) := by
    exact_mod_cast hcard
  have hcardZ : ((A \ X).card : ℤ) = (A.card : ℤ) - (X.card : ℤ) := by
    omega
  have hedgeZsum : (edgeCount G (A \ X) : ℤ) + (incidentCount G A X : ℤ) =
      (edgeCount G A : ℤ) := by
    exact_mod_cast hedge
  have hedgeZ : (edgeCount G (A \ X) : ℤ) =
      (edgeCount G A : ℤ) - (incidentCount G A X : ℤ) := by
    omega
  unfold shortage deletionPotential
  rw [hcardZ, hedgeZ]
  ring

lemma edgeCount_eq_card_edgeFinset_induce
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    edgeCount G A = #((G.induce (↑A : Set V)).edgeFinset) := by
  unfold edgeCount edgeOn
  exact G.card_filter_edgeFinset_toFinset_subset A

lemma degreeOn_eq_degree_induce
    (G : SimpleGraph V) [DecidableRel G.Adj] {A : Finset V} {v : V} (hv : v ∈ A) :
    degreeOn G A v = (G.induce (↑A : Set V)).degree ⟨v, hv⟩ := by
  symm
  unfold SimpleGraph.degree degreeOn
  refine Finset.card_bij (fun x _ ↦ (x : V)) ?_ ?_ ?_
  · intro x hx
    simp only [mem_inter, mem_neighborFinset, SetLike.coe_mem, and_true] at hx ⊢
    exact hx
  · intro x _ y _ hxy
    exact Subtype.ext hxy
  · intro y hy
    refine ⟨⟨y, (mem_inter.mp hy).2⟩, ?_, rfl⟩
    simpa [SimpleGraph.mem_neighborFinset] using (mem_inter.mp hy).1

lemma hasMinDegreeOn_iff_induce_minDegree
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (k : ℕ) :
    HasMinDegreeOn G A k ↔
      A.Nonempty ∧ k ≤ (G.induce (↑A : Set V)).minDegree := by
  constructor
  · rintro ⟨hA, hdeg⟩
    refine ⟨hA, ?_⟩
    let : Nonempty (↑A : Set V) := hA.to_subtype
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro v
    rw [← degreeOn_eq_degree_induce G v.property]
    exact hdeg v v.property
  · rintro ⟨hA, hmin⟩
    refine ⟨hA, ?_⟩
    intro v hv
    rw [degreeOn_eq_degree_induce G hv]
    exact hmin.trans ((G.induce (↑A : Set V)).minDegree_le_degree ⟨v, hv⟩)

lemma sum_degreeOn_eq_twice_edgeCount
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    ∑ v ∈ A, degreeOn G A v = 2 * edgeCount G A := by
  calc
    ∑ v ∈ A, degreeOn G A v =
        ∑ v : (↑A : Set V), (G.induce (↑A : Set V)).degree v := by
      rw [Finset.sum_subtype A (fun _ ↦ Iff.rfl)]
      apply Finset.sum_congr rfl
      intro v _
      exact degreeOn_eq_degree_induce G v.property
    _ = 2 * #((G.induce (↑A : Set V)).edgeFinset) :=
      (G.induce (↑A : Set V)).sum_degrees_eq_twice_card_edges
    _ = 2 * edgeCount G A := by rw [edgeCount_eq_card_edgeFinset_induce]

end P814

end

section
open Finset SimpleGraph

namespace P814

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def coreFreeEdgeBound (k n : ℕ) : ℕ :=
  (k - 1).choose 2 + (k - 1) * (n - (k - 1))

private def induceEraseIso (A : Finset V) {v : V} (hv : v ∈ A) :
    G.induce (A.erase v : Set V) ≃g
      (G.induce (A : Set V)).induce ({(⟨v, hv⟩ : (A : Set V))}ᶜ) where
  toFun x := ⟨⟨x.1, Finset.mem_of_mem_erase x.2⟩, by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, Subtype.ext_iff,
      ne_eq] using (Finset.ne_of_mem_erase x.2)⟩
  invFun x := ⟨x.1.1, Finset.mem_erase.mpr ⟨by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, Subtype.ext_iff,
      ne_eq] using x.2, x.1.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by simp

lemma edgeCount_erase_add_degreeOn {A : Finset V} {v : V} (hv : v ∈ A) :
    edgeCount G (A.erase v) + degreeOn G A v = edgeCount G A := by
  have herase :
      #((G.induce (A.erase v : Set V)).edgeFinset) =
        #((G.induce (A : Set V)).edgeFinset) -
          (G.induce (A : Set V)).degree ⟨v, hv⟩ := by
    rw [(induceEraseIso G A hv).card_edgeFinset_eq]
    rw [(G.induce (A : Set V)).card_edgeFinset_induce_compl_singleton ⟨v, hv⟩]
    exact (G.induce (A : Set V)).card_edgeFinset_deleteIncidenceSet ⟨v, hv⟩
  have hdeg :
      (G.induce (A : Set V)).degree ⟨v, hv⟩ ≤
        #((G.induce (A : Set V)).edgeFinset) :=
    (G.induce (A : Set V)).degree_le_card_edgeFinset ⟨v, hv⟩
  simp only [edgeCount_eq_card_edgeFinset_induce,
    degreeOn_eq_degree_induce G hv]
  rw [herase, Nat.sub_add_cancel hdeg]

lemma exists_degreeOn_lt_of_no_core {A : Finset V} (hA : A.Nonempty)
    (hno : ∀ U ⊆ A, ¬ HasMinDegreeOn G U k) :
    ∃ v ∈ A, degreeOn G A v < k := by
  have hnot := hno A Subset.rfl
  rw [HasMinDegreeOn, not_and_or] at hnot
  rcases hnot with hfalse | hdeg
  · exact (hfalse hA).elim
  · push Not at hdeg
    exact hdeg

theorem edgeCount_le_coreFreeEdgeBound_of_no_core (k : ℕ) {A : Finset V}
    (hcard : k - 1 ≤ A.card)
    (hno : ∀ U ⊆ A, ¬ HasMinDegreeOn G U k) :
    edgeCount G A ≤ coreFreeEdgeBound k A.card := by
  revert hcard hno
  refine Finset.strongInductionOn A ?_
  intro A ih hcard hno
  by_cases hbase : A.card = k - 1
  · have hedge : edgeCount G A ≤ A.card.choose 2 := by
      rw [edgeCount_eq_card_edgeFinset_induce]
      simpa using (G.induce (A : Set V)).card_edgeFinset_le_card_choose_two
    simpa [coreFreeEdgeBound, hbase] using hedge
  · have hpos : 0 < A.card := by omega
    obtain ⟨v, hvA, hvdeg⟩ :=
      exists_degreeOn_lt_of_no_core (G := G) (k := k) (card_pos.mp hpos) hno
    have herasecard : (A.erase v).card = A.card - 1 := card_erase_of_mem hvA
    have heraselower : k - 1 ≤ (A.erase v).card := by omega
    have herasesub : A.erase v ⊂ A := erase_ssubset hvA
    have heraseno : ∀ U ⊆ A.erase v, ¬ HasMinDegreeOn G U k := by
      intro U hU
      exact hno U (hU.trans herasesub.subset)
    have hih := ih (A.erase v) herasesub heraselower heraseno
    have hvdeg' : degreeOn G A v ≤ k - 1 := by omega
    have hsubstep :
        (A.erase v).card - (k - 1) + 1 = A.card - (k - 1) := by
      omega
    rw [← edgeCount_erase_add_degreeOn G hvA]
    calc
      edgeCount G (A.erase v) + degreeOn G A v ≤
          coreFreeEdgeBound k (A.erase v).card + (k - 1) :=
        Nat.add_le_add hih hvdeg'
      _ = coreFreeEdgeBound k A.card := by
        simp only [coreFreeEdgeBound]
        rw [← hsubstep]
        simp only [Nat.mul_add, Nat.mul_one]
        omega

lemma coreFreeEdgeBound_cast_eq (k n : ℕ) (hk : 2 ≤ k) (hn : k - 1 ≤ n) :
    (coreFreeEdgeBound k n : ℤ) =
      (((k - 1) * n : ℕ) : ℤ) - (k.choose 2 : ℤ) := by
  have hkpred : k - 1 = (k - 2) + 1 := by omega
  have hksucc : k = (k - 1) + 1 := by omega
  have hnsub : n = (k - 1) + (n - (k - 1)) := by omega
  have hchoose : k.choose 2 = (k - 1) + (k - 1).choose 2 := by
    conv_lhs => rw [hksucc]
    rw [Nat.choose_succ_succ']
    simp
  simp only [coreFreeEdgeBound, Nat.cast_add, Nat.cast_mul]
  rw [Nat.cast_sub hn, hchoose]
  push_cast
  have hnsubZ : (n : ℤ) = (k - 1 : ℕ) + (n - (k - 1) : ℕ) := by
    exact_mod_cast hnsub
  rw [hnsubZ]
  have hchooseSquare : ∀ p : ℕ,
      (2 : ℤ) * (p.choose 2 : ℤ) + (p : ℤ) = (p : ℤ) ^ 2 := by
    intro p
    induction p with
    | zero => norm_num
    | succ p ih =>
        rw [show 2 = 1 + 1 by norm_num, Nat.choose_succ_succ']
        simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_succ]
        push_cast
        calc
          (2 : ℤ) * ((p : ℤ) + (p.choose 2 : ℤ)) + ((p : ℤ) + 1) =
              ((2 : ℤ) * (p.choose 2 : ℤ) + (p : ℤ)) + 2 * p + 1 := by ring
          _ = (p : ℤ) ^ 2 + 2 * p + 1 := by rw [ih]
          _ = ((p : ℤ) + 1) ^ 2 := by ring
  have hsq := hchooseSquare (k - 1)
  linear_combination hsq

theorem edgeCount_cast_le_of_no_core (k : ℕ) {A : Finset V}
    (hk : 2 ≤ k) (hcard : k - 1 ≤ A.card)
    (hno : ∀ U ⊆ A, ¬ HasMinDegreeOn G U k) :
    (edgeCount G A : ℤ) ≤
      (((k - 1) * A.card : ℕ) : ℤ) - (k.choose 2 : ℤ) := by
  rw [← coreFreeEdgeBound_cast_eq k A.card hk hcard]
  exact_mod_cast edgeCount_le_coreFreeEdgeBound_of_no_core G k hcard hno

theorem exists_core_of_efrsThreshold_le (k : ℕ) {A : Finset V}
    (hk : 2 ≤ k) (hcard : k - 1 ≤ A.card)
    (hedge :
      (k - 1) * (A.card + 2 - k) + (k - 2).choose 2 ≤ edgeCount G A) :
    ∃ U ⊆ A, HasMinDegreeOn G U k := by
  by_contra h
  push Not at h
  have hbound := edgeCount_le_coreFreeEdgeBound_of_no_core G k hcard h
  have hpred : k - 1 = (k - 2) + 1 := by omega
  have hcardstep : A.card + 2 - k = A.card - (k - 1) + 1 := by omega
  have hchoose : (k - 1).choose 2 = (k - 2) + (k - 2).choose 2 := by
    conv_lhs => rw [hpred]
    rw [Nat.choose_succ_succ']
    simp
  have hefrs :
      (k - 1) * (A.card + 2 - k) + (k - 2).choose 2 =
        coreFreeEdgeBound k A.card + 1 := by
    simp only [coreFreeEdgeBound]
    rw [hcardstep, hchoose]
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  rw [hefrs] at hedge
  omega

theorem exists_core_of_edgeThreshold_le (k : ℕ) {A : Finset V}
    (hk : 2 ≤ k) (hcard : k - 1 ≤ A.card)
    (hedge : edgeThreshold k A.card ≤ edgeCount G A) :
    ∃ U ⊆ A, HasMinDegreeOn G U k := by
  apply exists_core_of_efrsThreshold_le G k hk hcard
  have hbase :
      (k - 1) * (A.card + 2 - k) + (k - 2).choose 2 ≤
        edgeThreshold k A.card := by
    simp [edgeThreshold]
  exact hbase.trans hedge

lemma card_ge_succ_of_hasMinDegreeOn {A : Finset V}
    (hcore : HasMinDegreeOn G A k) : k + 1 ≤ A.card := by
  obtain ⟨v, hv⟩ := hcore.1
  have hdeg := hcore.2 v hv
  have hlt := degreeOn_lt_card G hv
  omega

theorem card_ge_succ_of_edgeThreshold_le (k : ℕ) {A : Finset V}
    (hk : 2 ≤ k) (hcard : k - 1 ≤ A.card)
    (hedge : edgeThreshold k A.card ≤ edgeCount G A) :
    k + 1 ≤ A.card := by
  obtain ⟨U, hUA, hcore⟩ := exists_core_of_edgeThreshold_le G k hk hcard hedge
  exact (card_ge_succ_of_hasMinDegreeOn (G := G) (A := U) (k := k) hcore).trans
    (card_le_card hUA)

end P814

end

section
open Finset SimpleGraph

namespace P814

variable {V : Type*} [Fintype V] [DecidableEq V]

def ConnectedOn (G : SimpleGraph V) (A : Finset V) : Prop :=
  (G.induce (↑A : Set V)).Connected

def IsSmallCoreOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k D : ℕ) (U : Finset V) : Prop :=
  U ⊆ A ∧ HasMinDegreeOn G U k ∧ D * U.card ≤ (D - 1) * A.card

def NoSmallCoreOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k D : ℕ) : Prop :=
  ¬ ∃ U, IsSmallCoreOn G A k D U

lemma IsSmallCoreOn.mono_den
    {G : SimpleGraph V} [DecidableRel G.Adj] {A U : Finset V} {k D E : ℕ}
    (hD : 1 ≤ D) (hDE : D ≤ E) (h : IsSmallCoreOn G A k D U) :
    IsSmallCoreOn G A k E U := by
  rcases h with ⟨hUA, hmin, hsmall⟩
  refine ⟨hUA, hmin, ?_⟩
  have hcard : U.card ≤ A.card := card_le_card hUA
  have hE : E = D + (E - D) := by omega
  have hsub : E - 1 = (D - 1) + (E - D) := by omega
  calc
    E * U.card = D * U.card + (E - D) * U.card := by
      conv_lhs => rw [hE, add_mul]
    _ ≤ (D - 1) * A.card + (E - D) * A.card :=
      Nat.add_le_add hsmall (Nat.mul_le_mul_left (E - D) hcard)
    _ = (E - 1) * A.card := by
      conv_rhs => rw [hsub, add_mul]

lemma NoSmallCoreOn.anti_den
    {G : SimpleGraph V} [DecidableRel G.Adj] {A : Finset V} {k D E : ℕ}
    (hD : 1 ≤ D) (hDE : D ≤ E) (hno : NoSmallCoreOn G A k E) :
    NoSmallCoreOn G A k D := by
  rintro ⟨U, hU⟩
  exact hno ⟨U, hU.mono_den hD hDE⟩

lemma degreeOn_eq_of_neighbor_closed
    (G : SimpleGraph V) [DecidableRel G.Adj] {U A : Finset V}
    (hUA : U ⊆ A)
    (hclosed : ∀ {x}, x ∈ U → ∀ {y}, y ∈ A → G.Adj x y → y ∈ U)
    {v : V} (hv : v ∈ U) :
    degreeOn G U v = degreeOn G A v := by
  unfold degreeOn
  congr 1
  ext w
  simp only [mem_inter]
  constructor
  · rintro ⟨hvw, hwU⟩
    exact ⟨hvw, hUA hwU⟩
  · rintro ⟨hvw, hwA⟩
    refine ⟨hvw, hclosed hv hwA ?_⟩
    simpa [SimpleGraph.mem_neighborFinset] using hvw

lemma exists_small_minDegree_side_of_not_connectedOn
    (G : SimpleGraph V) [DecidableRel G.Adj] {A : Finset V} {k : ℕ}
    (hmin : HasMinDegreeOn G A k) (hconn : ¬ ConnectedOn G A) :
    ∃ U : Finset V,
      U ⊆ A ∧ U ≠ A ∧ HasMinDegreeOn G U k ∧ 2 * U.card ≤ A.card := by
  classical
  let H : SimpleGraph (↑A : Set V) := G.induce (↑A : Set V)
  let : Nonempty (↑A : Set V) := hmin.1.to_subtype
  have hnconnected : ¬ H.Connected := by
    simpa [ConnectedOn, H] using hconn
  have hnpreconnected : ¬ H.Preconnected := by
    intro hpre
    exact hnconnected ⟨hpre⟩
  simp only [SimpleGraph.Preconnected, not_forall] at hnpreconnected
  obtain ⟨u, v, huv⟩ := hnpreconnected
  let InComponent : V → Prop := fun x ↦
    ∃ hx : x ∈ A, H.Reachable u ⟨x, hx⟩
  let C : Finset V := A.filter InComponent
  have hCA : C ⊆ A := filter_subset _ _
  have huC : (u : V) ∈ C := by
    rw [mem_filter]
    exact ⟨u.property, u.property, SimpleGraph.Reachable.rfl⟩
  have hvC : (v : V) ∉ C := by
    intro hv
    have hv' := (mem_filter.mp hv).2
    rcases hv' with ⟨hvA, huv'⟩
    apply huv
    simpa using huv'
  have hCne : C ≠ A := by
    intro hCAeq
    exact hvC (hCAeq.symm ▸ v.property)
  have hCclosed :
      ∀ {x}, x ∈ C → ∀ {y}, y ∈ A → G.Adj x y → y ∈ C := by
    intro x hx y hy hxy
    rw [mem_filter] at hx ⊢
    rcases hx with ⟨hxA, _hxA', hxreach⟩
    refine ⟨hy, hy, ?_⟩
    have hadj : H.Adj ⟨x, hxA⟩ ⟨y, hy⟩ := by simpa [H] using hxy
    exact hxreach.trans hadj.reachable
  have hCmin : HasMinDegreeOn G C k := by
    refine ⟨⟨u, huC⟩, ?_⟩
    intro x hx
    rw [degreeOn_eq_of_neighbor_closed G hCA hCclosed hx]
    exact hmin.2 x (hCA hx)
  by_cases hsmall : 2 * C.card ≤ A.card
  · exact ⟨C, hCA, hCne, hCmin, hsmall⟩
  · let U : Finset V := A \ C
    have hUA : U ⊆ A := sdiff_subset
    have hvU : (v : V) ∈ U := by
      exact mem_sdiff.mpr ⟨v.property, hvC⟩
    have huU : (u : V) ∉ U := by
      simp only [U, mem_sdiff]
      exact fun h ↦ h.2 huC
    have hUne : U ≠ A := by
      intro hUAeq
      exact huU (hUAeq.symm ▸ u.property)
    have hUclosed :
        ∀ {x}, x ∈ U → ∀ {y}, y ∈ A → G.Adj x y → y ∈ U := by
      intro x hx y hy hxy
      rw [mem_sdiff] at hx ⊢
      refine ⟨hy, ?_⟩
      intro hyC
      apply hx.2
      rw [mem_filter] at hyC ⊢
      rcases hyC with ⟨hyA, _hyA', hyreach⟩
      refine ⟨hx.1, hx.1, ?_⟩
      have hadj : H.Adj ⟨y, hyA⟩ ⟨x, hx.1⟩ := by simpa [H] using hxy.symm
      exact hyreach.trans hadj.reachable
    have hUmin : HasMinDegreeOn G U k := by
      refine ⟨⟨v, hvU⟩, ?_⟩
      intro x hx
      rw [degreeOn_eq_of_neighbor_closed G hUA hUclosed hx]
      exact hmin.2 x (hUA hx)
    have hcard : U.card = A.card - C.card := by
      simp [U, card_sdiff_of_subset hCA]
    have hCle : C.card ≤ A.card := card_le_card hCA
    have hUsmall : 2 * U.card ≤ A.card := by
      rw [hcard]
      omega
    exact ⟨U, hUA, hUne, hUmin, hUsmall⟩

lemma connectedOn_of_noSmallCoreOn
    (G : SimpleGraph V) [DecidableRel G.Adj] {A : Finset V} {k D : ℕ}
    (hD : 2 ≤ D) (hmin : HasMinDegreeOn G A k)
    (hnosmall : NoSmallCoreOn G A k D) :
    ConnectedOn G A := by
  by_contra hconn
  obtain ⟨U, hUA, -, hUmin, hhalf⟩ :=
    exists_small_minDegree_side_of_not_connectedOn G hmin hconn
  apply hnosmall
  refine ⟨U, hUA, hUmin, ?_⟩
  have hcoef : D ≤ 2 * (D - 1) := by omega
  calc
    D * U.card ≤ (2 * (D - 1)) * U.card := Nat.mul_le_mul_right U.card hcoef
    _ = (D - 1) * (2 * U.card) := by ring
    _ ≤ (D - 1) * A.card := Nat.mul_le_mul_left (D - 1) hhalf

end P814

end

section
open scoped Sym2
open Finset SimpleGraph BigOperators

namespace P814

variable {V : Type*} [Fintype V] [DecidableEq V]

def degreeEq (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) : Finset V :=
  A.filter fun v ↦ degreeOn G A v = k

@[simp] lemma mem_degreeEq {G : SimpleGraph V} [DecidableRel G.Adj]
    {A : Finset V} {k : ℕ} {v : V} :
    v ∈ degreeEq G A k ↔ v ∈ A ∧ degreeOn G A v = k := by
  simp [degreeEq]

private lemma degreeOn_deleteEdge_eq_of_ne
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    {x y v : V} (hvx : v ≠ x) (hvy : v ≠ y) :
    degreeOn (G.deleteEdges ({s(x, y)} : Set (Sym2 V))) A v = degreeOn G A v := by
  unfold degreeOn
  congr 1
  ext z
  simp only [mem_inter, SimpleGraph.mem_neighborFinset, deleteEdges_adj,
    Set.mem_singleton_iff, Sym2.eq_iff]
  constructor
  · rintro ⟨⟨hvz, _⟩, hzA⟩
    exact ⟨hvz, hzA⟩
  · rintro ⟨hvz, hzA⟩
    refine ⟨⟨hvz, ?_⟩, hzA⟩
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hvx h1
    · exact hvy h1

private lemma degreeOn_deleteEdge_add_one
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    {x y : V} (hxy : G.Adj x y) (hyA : y ∈ A) :
    degreeOn (G.deleteEdges ({s(x, y)} : Set (Sym2 V))) A x + 1 = degreeOn G A x := by
  unfold degreeOn
  let D := (G.deleteEdges ({s(x, y)} : Set (Sym2 V))).neighborFinset x ∩ A
  have hyold : y ∈ G.neighborFinset x ∩ A := by simp [hxy, hyA]
  have hyD : y ∉ D := by simp [D]
  have hdecomp : insert y D = G.neighborFinset x ∩ A := by
    ext z
    simp only [mem_insert, mem_inter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro (rfl | hz)
      · exact ⟨hxy, hyA⟩
      · have hle : G.deleteEdges ({s(x, y)} : Set (Sym2 V)) ≤ G :=
          SimpleGraph.deleteEdges_le _
        exact ⟨by
          apply hle
          simpa [SimpleGraph.mem_neighborFinset] using (mem_inter.mp hz).1,
          (mem_inter.mp hz).2⟩
    · rintro ⟨hxz, hzA⟩
      by_cases hzy : z = y
      · exact Or.inl hzy
      · exact Or.inr <| by
          refine mem_inter.mpr ⟨?_, hzA⟩
          simp only [SimpleGraph.mem_neighborFinset, deleteEdges_adj,
            Set.mem_singleton_iff, Sym2.eq_iff]
          refine ⟨hxz, ?_⟩
          rintro (⟨_, h⟩ | ⟨h, _⟩)
          · exact hzy h
          · subst y
            exact hxy.ne rfl
  rw [← hdecomp, card_insert_of_notMem hyD]

private lemma degreeOn_deleteEdge_add_one_right
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    {x y : V} (hxy : G.Adj x y) (hxA : x ∈ A) :
    degreeOn (G.deleteEdges ({s(x, y)} : Set (Sym2 V))) A y + 1 = degreeOn G A y := by
  simpa [Sym2.eq_swap] using
    (degreeOn_deleteEdge_add_one G A hxy.symm hxA)

lemma incidentCount_singleton (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) {v : V} (hv : v ∈ A) :
    incidentCount G A {v} = degreeOn G A v := by
  unfold incidentCount incidentEdges degreeOn
  let f : V → Sym2 V := fun w ↦ s(v, w)
  have hfmem (w : V) (hw : w ∈ G.neighborFinset v ∩ A) :
      f w ∈ edgeOn G A \ edgeOn G (A \ {v}) := by
    rcases mem_inter.mp hw with ⟨hvw, hwA⟩
    have hvw' : G.Adj v w := by simpa [SimpleGraph.mem_neighborFinset] using hvw
    refine mem_sdiff.mpr ⟨?_, ?_⟩
    · refine mem_edgeOn.mpr ⟨by simpa [f] using hvw', ?_⟩
      simpa only [f, Sym2.toFinset_mk_eq, insert_subset_iff,
        singleton_subset_iff] using And.intro hv hwA
    · intro hret
      have hvret : v ∈ A \ {v} := (mem_edgeOn.mp hret).2 (by simp [f])
      simp at hvret
  symm
  refine Finset.card_bij (fun w hw ↦ f w) ?_ ?_ ?_
  · intro w hw
    exact hfmem w hw
  · intro w₁ hw₁ w₂ _ heq
    rcases (Sym2.eq_iff.mp heq) with h | h
    · exact h.2
    · have hvw₁ : v ≠ w₁ := by
        have hadj : G.Adj v w₁ := by
          simpa [SimpleGraph.mem_neighborFinset] using (mem_inter.mp hw₁).1
        exact hadj.ne
      exact (hvw₁ h.2.symm).elim
  · intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
      simp only [mem_sdiff, mem_edgeOn, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, Sym2.toFinset_mk_eq, insert_subset_iff,
        singleton_subset_iff, mem_sdiff, mem_singleton] at he
      rcases he with ⟨⟨hxy, hxA, hyA⟩, hnot⟩
      have hvxy : x = v ∨ y = v := by
        by_contra h
        push Not at h
        exact hnot ⟨hxy, ⟨hxA, h.1⟩, hyA, h.2⟩
      rcases hvxy with rfl | rfl
      · refine ⟨y, mem_inter.mpr ⟨?_, hyA⟩, ?_⟩
        · simpa [SimpleGraph.mem_neighborFinset] using hxy
        · rfl
      · refine ⟨x, mem_inter.mpr ⟨?_, hxA⟩, ?_⟩
        · simpa [SimpleGraph.mem_neighborFinset] using hxy.symm
        · simp [f, Sym2.eq_swap]

lemma incidentCount_le_sum_degreeOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) {X : Finset V} (hXA : X ⊆ A) :
    incidentCount G A X ≤ ∑ v ∈ X, degreeOn G A v := by
  induction X using Finset.induction_on with
  | empty => simp
  | @insert v X hvX ih =>
      have hvA : v ∈ A := hXA (mem_insert_self v X)
      have hsub : X ⊆ A := fun x hx ↦ hXA (mem_insert_of_mem hx)
      calc
        incidentCount G A (insert v X) = incidentCount G A ({v} ∪ X) := by
          rw [singleton_union]
        _ ≤ incidentCount G A {v} + incidentCount G A X :=
          incidentCount_union_le G A {v} X
        _ ≤ degreeOn G A v + ∑ x ∈ X, degreeOn G A x := by
          rw [incidentCount_singleton G A hvA]
          exact Nat.add_le_add_left (ih hsub) _
        _ = ∑ x ∈ insert v X, degreeOn G A x := by simp [hvX]

private def SparseCandidate (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (H : SimpleGraph V) : Prop := by
  exact H ≤ G ∧ ∃ _hdec : DecidableRel H.Adj,
    HasMinDegreeOn H A k ∧
      ∀ v ∈ A, degreeOn H A v = k → degreeOn G A v = k

private lemma exists_sparse_candidate
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (k : ℕ)
    (hmin : HasMinDegreeOn G A k) :
    ∃ H : SimpleGraph V, SparseCandidate G A k H ∧
      ∀ H', SparseCandidate G A k H' → H' ≤ H → H ≤ H' := by
  classical
  let candidates := (Finset.univ : Finset (SimpleGraph V)).filter (SparseCandidate G A k)
  have hG : G ∈ candidates := by
    simp only [candidates, mem_filter, mem_univ, true_and]
    exact ⟨le_rfl, inferInstance, hmin, fun _ _ h ↦ h⟩
  obtain ⟨H, hHmin⟩ := candidates.exists_minimal ⟨G, hG⟩
  refine ⟨H, ?_, ?_⟩
  · exact (mem_filter.mp hHmin.1).2
  · intro H' hH' hle
    exact hHmin.2 (mem_filter.mpr ⟨mem_univ _, hH'⟩) hle

private lemma sparse_edge_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (k : ℕ)
    (hmin : HasMinDegreeOn G A k) :
    ∃ H : SimpleGraph V, ∃ _hdec : DecidableRel H.Adj,
      H ≤ G ∧ HasMinDegreeOn H A k ∧
      (∀ v ∈ A, degreeOn H A v = k → degreeOn G A v = k) ∧
      edgeCount H A ≤ (k + 1) * A.card := by
  classical
  obtain ⟨H, hcandidate, hminimal⟩ := exists_sparse_candidate G A k hmin
  have hcandidate' : H ≤ G ∧ ∃ _hdec : DecidableRel H.Adj,
      HasMinDegreeOn H A k ∧
        ∀ v ∈ A, degreeOn H A v = k → degreeOn G A v = k := by
    simpa [SparseCandidate] using hcandidate
  rcases hcandidate' with ⟨hHG, hdecH, hHmin, hlow⟩
  let : DecidableRel H.Adj := hdecH
  have hnoHigh : ∀ {x y}, x ∈ A → y ∈ A → H.Adj x y →
      k + 2 ≤ degreeOn H A x → k + 2 ≤ degreeOn H A y → False := by
    intro x y hxA hyA hxy hdx hdy
    let H' := H.deleteEdges ({s(x, y)} : Set (Sym2 V))
    have hH'leH : H' ≤ H := SimpleGraph.deleteEdges_le _
    have hH'min : HasMinDegreeOn H' A k := by
      refine ⟨hHmin.1, ?_⟩
      intro v hvA
      by_cases hvx : v = x
      · subst v
        have heq : degreeOn H' A x + 1 = degreeOn H A x := by
          simpa [H'] using degreeOn_deleteEdge_add_one H A hxy hyA
        change k ≤ degreeOn H' A x
        omega
      · by_cases hvy : v = y
        · subst v
          have heq : degreeOn H' A y + 1 = degreeOn H A y := by
            simpa [H'] using degreeOn_deleteEdge_add_one_right H A hxy hxA
          change k ≤ degreeOn H' A y
          omega
        · rw [degreeOn_deleteEdge_eq_of_ne H A hvx hvy]
          exact hHmin.2 v hvA
    have hH'low : ∀ v ∈ A, degreeOn H' A v = k → degreeOn G A v = k := by
      intro v hvA hvdeg
      apply hlow v hvA
      by_cases hvx : v = x
      · subst v
        have heq : degreeOn H' A x + 1 = degreeOn H A x := by
          simpa [H'] using degreeOn_deleteEdge_add_one H A hxy hyA
        change degreeOn H' A x = k at hvdeg
        omega
      · by_cases hvy : v = y
        · subst v
          have heq : degreeOn H' A y + 1 = degreeOn H A y := by
            simpa [H'] using degreeOn_deleteEdge_add_one_right H A hxy hxA
          change degreeOn H' A y = k at hvdeg
          omega
        · change degreeOn H A v = k
          rw [← degreeOn_deleteEdge_eq_of_ne H A hvx hvy]
          exact hvdeg
    have hH'candidate : SparseCandidate G A k H' := by
      change H' ≤ G ∧ ∃ _hdec : DecidableRel H'.Adj,
        HasMinDegreeOn H' A k ∧ _
      exact ⟨hH'leH.trans hHG, inferInstance, hH'min, hH'low⟩
    have hback : H ≤ H' := hminimal H' hH'candidate hH'leH
    have : H'.Adj x y := hback hxy
    simp [H'] at this
  let L := A.filter fun v ↦ degreeOn H A v ≤ k + 1
  have hLA : L ⊆ A := filter_subset _ _
  have hremain : edgeCount H (A \ L) = 0 := by
    rw [edgeCount, card_eq_zero]
    ext e
    constructor
    · intro he
      induction e using Sym2.inductionOn with
      | _ x y =>
        have hem := mem_edgeOn.mp he
        simp only [Sym2.toFinset_mk_eq, insert_subset_iff, singleton_subset_iff,
          mem_sdiff] at hem
        rcases hem with ⟨hxy, ⟨hxA, hxL⟩, hyA, hyL⟩
        have hxyAdj : H.Adj x y := by
          simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hxy
        have hxhigh : k + 2 ≤ degreeOn H A x := by
          have hkx := hHmin.2 x hxA
          have : ¬ degreeOn H A x ≤ k + 1 := by simpa [L, hxA] using hxL
          omega
        have hyhigh : k + 2 ≤ degreeOn H A y := by
          have hky := hHmin.2 y hyA
          have : ¬ degreeOn H A y ≤ k + 1 := by simpa [L, hyA] using hyL
          omega
        exact (hnoHigh hxA hyA hxyAdj hxhigh hyhigh).elim
    · simp
  have hincident : incidentCount H A L = edgeCount H A := by
    have hsplit := edgeCount_sdiff_add_incidentCount H A L
    rw [hremain, zero_add] at hsplit
    exact hsplit
  have hedge : edgeCount H A ≤ (k + 1) * A.card := by
    calc
      edgeCount H A = incidentCount H A L := hincident.symm
      _ ≤ ∑ v ∈ L, degreeOn H A v := incidentCount_le_sum_degreeOn H A hLA
      _ ≤ ∑ _v ∈ L, (k + 1) := by
        apply sum_le_sum
        intro v hv
        exact (mem_filter.mp hv).2
      _ = (k + 1) * L.card := by simp [Nat.mul_comm]
      _ ≤ (k + 1) * A.card := Nat.mul_le_mul_left _ (card_le_card hLA)
  exact ⟨H, inferInstance, hHG, hHmin, hlow, hedge⟩

private lemma degreeOn_mono_graph
    {H G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (hHG : H ≤ G) (A : Finset V) (v : V) :
    degreeOn H A v ≤ degreeOn G A v := by
  unfold degreeOn
  apply card_le_card
  intro x hx
  refine mem_inter.mpr ⟨?_, (mem_inter.mp hx).2⟩
  have hxAdj : H.Adj v x := by
    simpa [SimpleGraph.mem_neighborFinset] using (mem_inter.mp hx).1
  simpa [SimpleGraph.mem_neighborFinset] using hHG hxAdj

private def ProtectedPair (H : SimpleGraph V) [DecidableRel H.Adj]
    (A T : Finset V) (k : ℕ) (R B : Finset V) : Prop :=
  R ⊆ T ∧ B ⊆ A ∧ Disjoint R B ∧
    (∀ v ∈ A, (∃ r ∈ R, H.Adj r v) → k ≤ degreeOn H B v) ∧
    B.card ≤ (9 * k ^ 2 - 1) * R.card

private lemma protectedPair_empty
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (A T : Finset V) (k : ℕ) : ProtectedPair H A T k ∅ ∅ := by
  simp [ProtectedPair, degreeOn]

private lemma ProtectedPair.extend
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (A T : Finset V) (k : ℕ) (hk : 2 ≤ k)
    (hmin : HasMinDegreeOn H A k)
    {R B : Finset V} (hpair : ProtectedPair H A T k R B)
    {w : V} (hwT : w ∈ T) (hwRB : w ∉ R ∪ B)
    (hwA : w ∈ A)
    (hwlow : degreeOn H A w < 9 * k)
    (hwaway : ∀ v ∈ A, H.Adj w v → degreeOn H A v ≠ k) :
    ∃ B', ProtectedPair H A T k (insert w R) B' := by
  classical
  rcases hpair with ⟨hRT, hBA, hdisj, hprotect, hbudget⟩
  have hwR : w ∉ R := fun hw ↦ hwRB (mem_union_left B hw)
  have hwB : w ∉ B := fun hw ↦ hwRB (mem_union_right R hw)
  let Nw : Finset V := H.neighborFinset w ∩ A
  have havail (v : ↑Nw) (hred : ¬ ∃ r ∈ R, H.Adj r (v : V)) :
      k ≤ ((H.neighborFinset (v : V) ∩ A).erase w).card := by
    have hwv : H.Adj w (v : V) := by
      simpa [Nw, SimpleGraph.mem_neighborFinset] using (mem_inter.mp v.property).1
    have hvA : (v : V) ∈ A := (mem_inter.mp v.property).2
    have hdeg : k ≤ degreeOn H A (v : V) := hmin.2 v hvA
    have hne : degreeOn H A (v : V) ≠ k := hwaway v hvA hwv
    have hsucc : k + 1 ≤ degreeOn H A (v : V) := by omega
    have hwmem : w ∈ H.neighborFinset (v : V) ∩ A := by
      refine mem_inter.mpr ⟨?_, hwA⟩
      simpa [SimpleGraph.mem_neighborFinset] using hwv.symm
    rw [card_erase_of_mem hwmem]
    change k ≤ degreeOn H A (v : V) - 1
    omega
  let C : ↑Nw → Finset V := fun v ↦
    if hred : ∃ r ∈ R, H.Adj r (v : V) then ∅
    else Classical.choose (Finset.exists_subset_card_eq (havail v hred))
  have hC_empty (v : ↑Nw) (hred : ∃ r ∈ R, H.Adj r (v : V)) : C v = ∅ := by
    simp [C, hred]
  have hC_subset (v : ↑Nw) (hred : ¬ ∃ r ∈ R, H.Adj r (v : V)) :
      C v ⊆ (H.neighborFinset (v : V) ∩ A).erase w := by
    simpa [C, hred] using
      (Classical.choose_spec (Finset.exists_subset_card_eq (havail v hred))).1
  have hC_card (v : ↑Nw) (hred : ¬ ∃ r ∈ R, H.Adj r (v : V)) :
      (C v).card = k := by
    simpa [C, hred] using
      (Classical.choose_spec (Finset.exists_subset_card_eq (havail v hred))).2
  have hC_card_le (v : ↑Nw) : (C v).card ≤ k := by
    by_cases hred : ∃ r ∈ R, H.Adj r (v : V)
    · simp [hC_empty v hred]
    · exact (hC_card v hred).le
  have hC_away (v : ↑Nw) {x : V} (hxC : x ∈ C v) : x ∉ insert w R := by
    by_cases hred : ∃ r ∈ R, H.Adj r (v : V)
    · rw [hC_empty v hred] at hxC
      simp at hxC
    · have hxAvail := hC_subset v hred hxC
      have hxw : x ≠ w := (mem_erase.mp hxAvail).1
      have hxNbr : x ∈ H.neighborFinset (v : V) :=
        (mem_inter.mp (mem_erase.mp hxAvail).2).1
      intro hxIns
      rcases mem_insert.mp hxIns with rfl | hxR
      · exact hxw rfl
      · apply hred
        refine ⟨x, hxR, ?_⟩
        have hvx : H.Adj (v : V) x := by
          simpa [SimpleGraph.mem_neighborFinset] using hxNbr
        exact hvx.symm
  let New : Finset V := Nw.attach.biUnion C
  let B' : Finset V := B ∪ New
  refine ⟨B', ?_⟩
  unfold ProtectedPair
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases mem_insert.mp hx with rfl | hxR
    · exact hwT
    · exact hRT hxR
  · intro x hx
    rcases mem_union.mp hx with hxB | hxNew
    · exact hBA hxB
    · obtain ⟨v, hvAttach, hxC⟩ := mem_biUnion.mp hxNew
      by_cases hred : ∃ r ∈ R, H.Adj r (v : V)
      · rw [hC_empty v hred] at hxC
        simp at hxC
      · exact (mem_inter.mp (mem_erase.mp (hC_subset v hred hxC)).2).2
  · rw [Finset.disjoint_left]
    intro x hxIns hxB'
    rcases mem_union.mp hxB' with hxB | hxNew
    · rcases mem_insert.mp hxIns with rfl | hxR
      · exact hwB hxB
      · exact (Finset.disjoint_left.mp hdisj hxR hxB)
    · obtain ⟨v, hvAttach, hxC⟩ := mem_biUnion.mp hxNew
      exact hC_away v hxC hxIns
  · intro v hvA hredNew
    by_cases hredOld : ∃ r ∈ R, H.Adj r v
    · exact (hprotect v hvA hredOld).trans
        (degreeOn_mono H (show B ⊆ B' by intro x hx; exact mem_union_left _ hx) v)
    · obtain ⟨r, hrIns, hrv⟩ := hredNew
      have hrw : r = w := (mem_insert.mp hrIns).resolve_right
        (fun hrR ↦ hredOld ⟨r, hrR, hrv⟩)
      subst r
      have hvNw : v ∈ Nw := by
        exact mem_inter.mpr ⟨by simpa [SimpleGraph.mem_neighborFinset] using hrv, hvA⟩
      let vv : ↑Nw := ⟨v, hvNw⟩
      have hCsub := hC_subset vv hredOld
      have hCdeg : (C vv).card = k := hC_card vv hredOld
      rw [← hCdeg]
      apply card_le_card
      intro x hxC
      refine mem_inter.mpr ⟨?_, ?_⟩
      · exact (mem_inter.mp (mem_erase.mp (hCsub hxC)).2).1
      · exact mem_union_right B (mem_biUnion.mpr ⟨vv, mem_attach _ _, hxC⟩)
  · have hNewCard : New.card ≤ Nw.card * k := by
      calc
        New.card ≤ ∑ v ∈ Nw.attach, (C v).card := Finset.card_biUnion_le
        _ ≤ ∑ _v ∈ Nw.attach, k := by
          apply sum_le_sum
          intro v hv
          exact hC_card_le v
        _ = Nw.card * k := by simp
    have hstep : Nw.card * k ≤ 9 * k ^ 2 - 1 := by
      have hn : Nw.card = degreeOn H A w := by rfl
      rw [hn]
      have hdeg : degreeOn H A w ≤ 9 * k - 1 := by omega
      have hmul := Nat.mul_le_mul_right k hdeg
      have hnum : (9 * k - 1) * k ≤ 9 * k ^ 2 - 1 := by
        rw [Nat.sub_mul]
        simp only [one_mul]
        have heq : 9 * k * k = 9 * k ^ 2 := by ring
        rw [heq]
        exact Nat.sub_le_sub_left (by omega) _
      exact hmul.trans hnum
    calc
      B'.card ≤ B.card + New.card := card_union_le _ _
      _ ≤ (9 * k ^ 2 - 1) * R.card + (9 * k ^ 2 - 1) :=
        Nat.add_le_add hbudget (hNewCard.trans hstep)
      _ = (9 * k ^ 2 - 1) * (insert w R).card := by simp [hwR, Nat.mul_add]

private lemma exists_covering_protectedPair
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (A T : Finset V) (k : ℕ) (hk : 2 ≤ k)
    (hmin : HasMinDegreeOn H A k)
    (hTA : T ⊆ A)
    (hgood : ∀ w ∈ T,
      degreeOn H A w < 9 * k ∧
      ∀ v ∈ A, H.Adj w v → degreeOn H A v ≠ k) :
    ∃ R B, ProtectedPair H A T k R B ∧ T ⊆ R ∪ B := by
  classical
  let candidates := T.powerset.filter fun R ↦ ∃ B, ProtectedPair H A T k R B
  have hempty : ∅ ∈ candidates := by
    simp only [candidates, mem_filter, mem_powerset, empty_subset, true_and]
    exact ⟨∅, protectedPair_empty H A T k⟩
  obtain ⟨R, hRmax⟩ := candidates.exists_maximal ⟨∅, hempty⟩
  rcases mem_filter.mp hRmax.1 with ⟨hRpow, B, hpair⟩
  refine ⟨R, B, hpair, ?_⟩
  intro w hwT
  by_contra hwRB
  have hwNot : w ∉ R ∪ B := hwRB
  obtain ⟨B', hpair'⟩ := ProtectedPair.extend H A T k hk hmin hpair hwT hwNot
    (hTA hwT) (hgood w hwT).1 (hgood w hwT).2
  have hInsCand : insert w R ∈ candidates := by
    refine mem_filter.mpr ⟨?_, B', hpair'⟩
    exact mem_powerset.mpr (insert_subset hwT (mem_powerset.mp hRpow))
  have hback : insert w R ⊆ R := hRmax.2 hInsCand (subset_insert w R)
  have hwR : w ∉ R := fun hw ↦ hwNot (mem_union_left B hw)
  exact hwR (hback (mem_insert_self w R))

private lemma sparse_degreeKSupply
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (A : Finset V) (k : ℕ) (hk : 2 ≤ k)
    (hmin : HasMinDegreeOn H A k)
    (hedge : edgeCount H A ≤ (k + 1) * A.card)
    (hFew : 3 * k * (degreeEq H A k).card ≤ A.card) :
    ∃ W : Finset V, W ⊆ A ∧ HasMinDegreeOn H W k ∧
      27 * k ^ 2 * W.card ≤ (27 * k ^ 2 - 1) * A.card := by
  classical
  let D := degreeEq H A k
  let T₁ := D.biUnion fun v ↦ H.neighborFinset v ∩ A
  let T₂ := A.filter fun v ↦ 9 * k ≤ degreeOn H A v
  let U := T₁ ∪ T₂
  let T := A \ U
  have hDdeg : ∀ v ∈ D, degreeOn H A v = k := by
    intro v hv
    exact (mem_degreeEq.mp (show v ∈ degreeEq H A k by simpa [D] using hv)).2
  have hT₁A : T₁ ⊆ A := by
    intro x hx
    obtain ⟨v, hvD, hxN⟩ := mem_biUnion.mp hx
    exact (mem_inter.mp hxN).2
  have hT₁card : T₁.card ≤ k * D.card := by
    calc
      T₁.card ≤ ∑ v ∈ D, (H.neighborFinset v ∩ A).card :=
        Finset.card_biUnion_le
      _ = ∑ _v ∈ D, k := by
        apply sum_congr rfl
        intro v hv
        exact hDdeg v hv
      _ = k * D.card := by simp [Nat.mul_comm]
  have hT₁third : 3 * T₁.card ≤ A.card := by
    calc
      3 * T₁.card ≤ 3 * (k * D.card) := Nat.mul_le_mul_left 3 hT₁card
      _ = 3 * k * (degreeEq H A k).card := by simp [D, Nat.mul_assoc]
      _ ≤ A.card := hFew
  have hT₂A : T₂ ⊆ A := filter_subset _ _
  have hHighSum : 9 * k * T₂.card ≤ ∑ v ∈ T₂, degreeOn H A v := by
    calc
      9 * k * T₂.card = ∑ _v ∈ T₂, 9 * k := by
        simp
        ring
      _ ≤ ∑ v ∈ T₂, degreeOn H A v := by
        apply sum_le_sum
        intro v hv
        exact (mem_filter.mp hv).2
  have hHighTotal : 9 * k * T₂.card ≤ ∑ v ∈ A, degreeOn H A v := by
    exact hHighSum.trans (sum_le_sum_of_subset_of_nonneg hT₂A (by simp))
  have hTotal : (∑ v ∈ A, degreeOn H A v) ≤ 3 * k * A.card := by
    calc
      (∑ v ∈ A, degreeOn H A v) = 2 * edgeCount H A :=
        sum_degreeOn_eq_twice_edgeCount H A
      _ ≤ 2 * ((k + 1) * A.card) := Nat.mul_le_mul_left 2 hedge
      _ ≤ (3 * k) * A.card := by
        have hcoef : 2 * (k + 1) ≤ 3 * k := by omega
        simpa [Nat.mul_assoc] using Nat.mul_le_mul_right A.card hcoef
      _ = 3 * k * A.card := by simp [Nat.mul_assoc]
  have hT₂third : 3 * T₂.card ≤ A.card := by
    apply Nat.le_of_mul_le_mul_left (c := 3 * k) ?_ (by omega)
    calc
      (3 * k) * (3 * T₂.card) = 9 * k * T₂.card := by ring
      _ ≤ 3 * k * A.card := hHighTotal.trans hTotal
      _ = (3 * k) * A.card := by ring
  have hUA : U ⊆ A := union_subset hT₁A hT₂A
  have hUbound : 3 * U.card ≤ 2 * A.card := by
    calc
      3 * U.card ≤ 3 * (T₁.card + T₂.card) :=
        Nat.mul_le_mul_left 3 (card_union_le T₁ T₂)
      _ = 3 * T₁.card + 3 * T₂.card := by ring
      _ ≤ A.card + A.card := Nat.add_le_add hT₁third hT₂third
      _ = 2 * A.card := by omega
  have hTA : T ⊆ A := sdiff_subset
  have hsplitT : T.card + U.card = A.card := by
    have := Nat.sub_add_cancel (card_le_card hUA)
    simpa [T, card_sdiff_of_subset hUA] using this
  have hTthird : A.card ≤ 3 * T.card := by omega
  have hgood : ∀ w ∈ T,
      degreeOn H A w < 9 * k ∧
      ∀ v ∈ A, H.Adj w v → degreeOn H A v ≠ k := by
    intro w hwT
    have hwA : w ∈ A := hTA hwT
    have hwU : w ∉ U := (mem_sdiff.mp hwT).2
    have hwT₂ : w ∉ T₂ := fun hw ↦ hwU (mem_union_right T₁ hw)
    constructor
    · have hnot : ¬ 9 * k ≤ degreeOn H A w := by
        simpa [T₂, hwA] using hwT₂
      omega
    · intro v hvA hwv heq
      have hvD : v ∈ D := by
        simp [D, mem_degreeEq, hvA, heq]
      have hwT₁ : w ∈ T₁ := by
        apply mem_biUnion.mpr
        refine ⟨v, hvD, mem_inter.mpr ⟨?_, hwA⟩⟩
        simpa [SimpleGraph.mem_neighborFinset] using hwv.symm
      exact hwU (mem_union_left T₂ hwT₁)
  obtain ⟨R, B, hpair, hcover⟩ :=
    exists_covering_protectedPair H A T k hk hmin hTA hgood
  rcases hpair with ⟨hRT, hBA, hdisj, hprotect, hbudget⟩
  have hTRB : T.card ≤ R.card + B.card := by
    calc
      T.card ≤ (R ∪ B).card := card_le_card hcover
      _ ≤ R.card + B.card := card_union_le R B
  have hqpos : 0 < 9 * k ^ 2 := by positivity
  have hTred : T.card ≤ 9 * k ^ 2 * R.card := by
    calc
      T.card ≤ R.card + B.card := hTRB
      _ ≤ R.card + (9 * k ^ 2 - 1) * R.card := Nat.add_le_add_left hbudget _
      _ = 9 * k ^ 2 * R.card := by
        have : 9 * k ^ 2 - 1 + 1 = 9 * k ^ 2 := by omega
        calc
          R.card + (9 * k ^ 2 - 1) * R.card =
              (1 + (9 * k ^ 2 - 1)) * R.card := by ring
          _ = 9 * k ^ 2 * R.card := by rw [Nat.add_comm 1, this]
  have hAR : A.card ≤ 27 * k ^ 2 * R.card := by
    calc
      A.card ≤ 3 * T.card := hTthird
      _ ≤ 3 * (9 * k ^ 2 * R.card) := Nat.mul_le_mul_left 3 hTred
      _ = 27 * k ^ 2 * R.card := by ring
  have hRA : R ⊆ A := hRT.trans hTA
  let W := A \ R
  have hBW : B ⊆ W := by
    intro b hb
    refine mem_sdiff.mpr ⟨hBA hb, ?_⟩
    intro hbR
    exact Finset.disjoint_left.mp hdisj hbR hb
  have hWnonempty : W.Nonempty := by
    by_cases hRne : R.Nonempty
    · obtain ⟨r, hrR⟩ := hRne
      have hrA : r ∈ A := hRA hrR
      have hrpos : 0 < degreeOn H A r := lt_of_lt_of_le (by omega) (hmin.2 r hrA)
      obtain ⟨v, hvNbr⟩ := card_pos.mp hrpos
      have hrv : H.Adj r v := by
        simpa [degreeOn, SimpleGraph.mem_neighborFinset] using (mem_inter.mp hvNbr).1
      have hvA : v ∈ A := (mem_inter.mp hvNbr).2
      have hBpos : 0 < degreeOn H B v :=
        lt_of_lt_of_le (by omega) (hprotect v hvA ⟨r, hrR, hrv⟩)
      obtain ⟨b, hbNbr⟩ := card_pos.mp hBpos
      exact ⟨b, hBW (mem_inter.mp hbNbr).2⟩
    · have hRempty : R = ∅ := not_nonempty_iff_eq_empty.mp hRne
      simpa [W, hRempty] using hmin.1
  have hWmin : HasMinDegreeOn H W k := by
    refine ⟨hWnonempty, ?_⟩
    intro v hvW
    have hvA : v ∈ A := (mem_sdiff.mp hvW).1
    by_cases hred : ∃ r ∈ R, H.Adj r v
    · exact (hprotect v hvA hred).trans (degreeOn_mono H hBW v)
    · exact (hmin.2 v hvA).trans <| by
        unfold degreeOn
        apply card_le_card
        intro x hx
        refine mem_inter.mpr ⟨(mem_inter.mp hx).1, mem_sdiff.mpr ⟨(mem_inter.mp hx).2, ?_⟩⟩
        intro hxR
        apply hred
        refine ⟨x, hxR, ?_⟩
        have hvx : H.Adj v x := by
          simpa [SimpleGraph.mem_neighborFinset] using (mem_inter.mp hx).1
        exact hvx.symm
  have hsplitR : W.card + R.card = A.card := by
    have := Nat.sub_add_cancel (card_le_card hRA)
    simpa [W, card_sdiff_of_subset hRA] using this
  have hshrink : 27 * k ^ 2 * W.card ≤ (27 * k ^ 2 - 1) * A.card := by
    have hadd : 27 * k ^ 2 * W.card + A.card ≤ 27 * k ^ 2 * A.card := by
      calc
        27 * k ^ 2 * W.card + A.card ≤
            27 * k ^ 2 * W.card + 27 * k ^ 2 * R.card :=
          Nat.add_le_add_left hAR _
        _ = 27 * k ^ 2 * A.card := by rw [← hsplitR]; ring
    have hsub : 27 * k ^ 2 * W.card ≤ 27 * k ^ 2 * A.card - A.card :=
      Nat.le_sub_of_add_le hadd
    simpa [Nat.sub_mul] using hsub
  exact ⟨W, sdiff_subset, hWmin, hshrink⟩

theorem degreeKSupply
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (hk : 2 ≤ k)
    (hmin : HasMinDegreeOn G A k)
    (hFew : 3 * k * (degreeEq G A k).card ≤ A.card) :
    ∃ W : Finset V, W ⊆ A ∧ HasMinDegreeOn G W k ∧
      27 * k ^ 2 * W.card ≤ (27 * k ^ 2 - 1) * A.card := by
  classical
  obtain ⟨H, hdecH, hHG, hHmin, hlow, hedge⟩ := sparse_edge_bound G A k hmin
  let : DecidableRel H.Adj := hdecH
  have hdegSub : degreeEq H A k ⊆ degreeEq G A k := by
    intro v hv
    rcases mem_degreeEq.mp hv with ⟨hvA, hvdeg⟩
    exact mem_degreeEq.mpr ⟨hvA, hlow v hvA hvdeg⟩
  have hFewH : 3 * k * (degreeEq H A k).card ≤ A.card := by
    exact (Nat.mul_le_mul_left (3 * k) (card_le_card hdegSub)).trans hFew
  obtain ⟨W, hWA, hWmin, hshrink⟩ :=
    sparse_degreeKSupply H A k hk hHmin hedge hFewH
  refine ⟨W, hWA, ⟨hWmin.1, ?_⟩, hshrink⟩
  intro v hvW
  exact (hWmin.2 v hvW).trans (degreeOn_mono_graph hHG W v)

theorem many_degree_eq_k_of_counterexample
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (hk : 2 ≤ k)
    (hmin : HasMinDegreeOn G A k)
    (hno : ¬ ∃ W : Finset V, W ⊆ A ∧ HasMinDegreeOn G W k ∧
      27 * k ^ 2 * W.card ≤ (27 * k ^ 2 - 1) * A.card) :
    A.card ≤ 3 * k * (degreeEq G A k).card := by
  by_contra hmany
  have hFew : 3 * k * (degreeEq G A k).card ≤ A.card := by omega
  exact hno (degreeKSupply G A k hk hmin hFew)

end P814

end

section
open Finset SimpleGraph BigOperators

namespace P814

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def LocalExpansion (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) : Prop :=
  ∀ X, X.Nonempty → X ⊆ A → X.card ≤ A.card - k + 1 →
    (k - 1) * X.card + 1 ≤ incidentCount G A X

inductive Good (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) : Finset V → Prop
  | singleton {v : V} (hv : v ∈ A) (hdeg : degreeOn G A v = k) :
      Good G A k {v}
  | insert {D : Finset V} {v : V} (hD : Good G A k D)
      (hv : v ∈ A \ D) (hdeg : degreeOn G (A \ D) v ≤ k - 1) :
      Good G A k (insert v D)
  | union_inter {D E : Finset V} (hD : Good G A k D)
      (hE : Good G A k E) (hne : (D ∩ E).Nonempty) :
      Good G A k (D ∪ E)
  | union_adj {D E : Finset V} (hD : Good G A k D)
      (hE : Good G A k E) (hadj : AdjacentSets G D E) :
      Good G A k (D ∪ E)

namespace Good

lemma subset {A D : Finset V} {k : ℕ} (hD : Good G A k D) : D ⊆ A := by
  induction hD with
  | singleton hv _ => simpa using hv
  | insert hD hv _ ih =>
      exact insert_subset (mem_sdiff.mp hv).1 ih
  | union_inter _ _ _ ihD ihE => exact union_subset ihD ihE
  | union_adj _ _ _ ihD ihE => exact union_subset ihD ihE

lemma nonempty {A D : Finset V} {k : ℕ} (hD : Good G A k D) : D.Nonempty := by
  induction hD with
  | singleton => simp
  | insert => simp
  | union_inter _ _ _ ihD _ => exact ihD.mono subset_union_left
  | union_adj _ _ _ ihD _ => exact ihD.mono subset_union_left

end Good

lemma incidentCount_insert {A D : Finset V} {v : V}
    (hv : v ∈ A \ D) :
    incidentCount G A (insert v D) =
      incidentCount G A D + degreeOn G (A \ D) v := by
  have h₁ := edgeCount_sdiff_add_incidentCount G A D
  have h₂ := edgeCount_sdiff_add_incidentCount G (A \ D) {v}
  have h₃ := edgeCount_sdiff_add_incidentCount G A (insert v D)
  have hsingle := incidentCount_singleton G (A \ D) hv
  have hs : (A \ D) \ {v} = A \ insert v D := by
    ext x
    simp only [mem_sdiff, mem_singleton, mem_insert]
    tauto
  rw [hs, hsingle] at h₂
  omega

lemma incidentCount_union_add_inter_le (A D E : Finset V) :
    incidentCount G A (D ∪ E) + incidentCount G A (D ∩ E) ≤
      incidentCount G A D + incidentCount G A E := by
  have hsub : incidentEdges G A (D ∩ E) ⊆
      incidentEdges G A D ∩ incidentEdges G A E := by
    intro e he
    exact mem_inter.mpr
      ⟨incidentEdges_mono G A inter_subset_left he,
       incidentEdges_mono G A inter_subset_right he⟩
  have hcard : incidentCount G A (D ∩ E) ≤
      #(incidentEdges G A D ∩ incidentEdges G A E) := by
    exact card_le_card hsub
  calc
    incidentCount G A (D ∪ E) + incidentCount G A (D ∩ E) ≤
        incidentCount G A (D ∪ E) +
          #(incidentEdges G A D ∩ incidentEdges G A E) :=
      Nat.add_le_add_left hcard _
    _ = incidentCount G A D + incidentCount G A E :=
      incidentCount_union_add_inter G A D E

omit [Fintype V] in
private lemma card_inter_le_card_union {D E : Finset V} :
    (D ∩ E).card ≤ (D ∪ E).card :=
  card_le_card (inter_subset_left.trans subset_union_left)

lemma Good.incidentCount_le_of_card_le
    {A D : Finset V} {k : ℕ} (hlocal : LocalExpansion G A k)
    (hD : Good G A k D) (hcard : D.card ≤ A.card - k + 1) :
    incidentCount G A D ≤ (k - 1) * D.card + 1 := by
  induction hD with
  | singleton hv hdeg =>
      rw [incidentCount_singleton G A hv, hdeg]
      simp only [card_singleton, mul_one]
      omega
  | @insert D v hD hv hdeg ih =>
      have hDcard : D.card ≤ A.card - k + 1 :=
        (card_le_card (subset_insert v D)).trans hcard
      have hi := ih hDcard
      rw [incidentCount_insert G hv]
      have hvD : v ∉ D := (mem_sdiff.mp hv).2
      rw [card_insert_of_notMem hvD]
      simp only [Nat.mul_add, Nat.mul_one]
      omega
  | @union_inter D E hD hE hne ihD ihE =>
      have hDcard : D.card ≤ A.card - k + 1 :=
        (card_le_card subset_union_left).trans hcard
      have hEcard : E.card ≤ A.card - k + 1 :=
        (card_le_card subset_union_right).trans hcard
      have hIcard : (D ∩ E).card ≤ A.card - k + 1 :=
        card_inter_le_card_union.trans hcard
      have hIlower := hlocal (D ∩ E) hne
        ((inter_subset_left.trans hD.subset)) hIcard
      have hsub := incidentCount_union_add_inter_le G A D E
      have hc := card_union_add_card_inter D E
      nlinarith [ihD hDcard, ihE hEcard]
  | @union_adj D E hD hE hadj ihD ihE =>
      by_cases hne : (D ∩ E).Nonempty
      · have hDcard : D.card ≤ A.card - k + 1 :=
          (card_le_card subset_union_left).trans hcard
        have hEcard : E.card ≤ A.card - k + 1 :=
          (card_le_card subset_union_right).trans hcard
        have hIcard : (D ∩ E).card ≤ A.card - k + 1 :=
          card_inter_le_card_union.trans hcard
        have hIlower := hlocal (D ∩ E) hne
          ((inter_subset_left.trans hD.subset)) hIcard
        have hsub := incidentCount_union_add_inter_le G A D E
        have hc := card_union_add_card_inter D E
        nlinarith [ihD hDcard, ihE hEcard]
      · have hdisj : Disjoint D E := Finset.disjoint_left.mpr (by
          intro x hxD hxE
          exact hne ⟨x, mem_inter.mpr ⟨hxD, hxE⟩⟩)
        have hDcard : D.card ≤ A.card - k + 1 := by
          exact (card_le_card subset_union_left).trans hcard
        have hEcard : E.card ≤ A.card - k + 1 := by
          exact (card_le_card subset_union_right).trans hcard
        have hadjCount := incidentCount_union_add_one_le_of_adjacent G
          hD.subset hE.subset hadj
        rw [card_union_of_disjoint hdisj]
        nlinarith [ihD hDcard, ihE hEcard]

lemma Good.exists_proper_subgood_of_one_lt
    {A D : Finset V} {k : ℕ} (hD : Good G A k D) (hone : 1 < D.card) :
    ∃ E, Good G A k E ∧ E ⊂ D ∧ D.card ≤ 2 * E.card := by
  induction hD with
  | singleton hv hdeg => simp at hone
  | @insert D v hD hv hdeg ih =>
      have hvD : v ∉ D := (mem_sdiff.mp hv).2
      refine ⟨D, hD, ?_, ?_⟩
      · exact ssubset_insert hvD
      · rw [card_insert_of_notMem hvD]
        have hne := (Good.nonempty G hD).card_pos
        omega
  | @union_inter D E hD hE hne ihD ihE =>
      by_cases hDall : D = D ∪ E
      · rw [← hDall] at hone ⊢
        exact ihD hone
      · by_cases hEall : E = D ∪ E
        · rw [← hEall] at hone ⊢
          exact ihE hone
        · have hDss : D ⊂ D ∪ E :=
            Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_left, hDall⟩
          have hEss : E ⊂ D ∪ E :=
            Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_right, hEall⟩
          have hcard := card_union_le D E
          by_cases hle : E.card ≤ D.card
          · exact ⟨D, hD, hDss, by omega⟩
          · exact ⟨E, hE, hEss, by omega⟩
  | @union_adj D E hD hE hadj ihD ihE =>
      by_cases hDall : D = D ∪ E
      · rw [← hDall] at hone ⊢
        exact ihD hone
      · by_cases hEall : E = D ∪ E
        · rw [← hEall] at hone ⊢
          exact ihE hone
        · have hDss : D ⊂ D ∪ E :=
            Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_left, hDall⟩
          have hEss : E ⊂ D ∪ E :=
            Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_right, hEall⟩
          have hcard := card_union_le D E
          by_cases hle : E.card ≤ D.card
          · exact ⟨D, hD, hDss, by omega⟩
          · exact ⟨E, hE, hEss, by omega⟩

theorem Good.exists_core_in_complement
    {A D : Finset V} {k : ℕ} (hk : 2 ≤ k)
    (hcardA : k - 1 ≤ A.card)
    (hlocal : LocalExpansion G A k)
    (hedge : edgeThreshold k A.card ≤ edgeCount G A)
    (hD : Good G A k D) (hcard : D.card ≤ A.card - k + 1) :
    ∃ U ⊆ A \ D, HasMinDegreeOn G U k := by
  have hDA := Good.subset G hD
  have hinc := Good.incidentCount_le_of_card_le G hlocal hD hcard
  have hsplit := edgeCount_sdiff_add_incidentCount G A D
  have hremcard : (A \ D).card = A.card - D.card :=
    card_sdiff_of_subset hDA
  have hAfeasible :=
    card_ge_succ_of_edgeThreshold_le G k hk hcardA hedge
  have hremLower : k - 1 ≤ (A \ D).card := by
    rw [hremcard]
    have hDpos := (Good.nonempty G hD).card_pos
    omega
  apply exists_core_of_efrsThreshold_le G k hk hremLower
  rw [hremcard]
  simp only [edgeThreshold] at hedge
  have harg :
      A.card + 2 - k = (A.card - D.card + 2 - k) + D.card := by
    have hDpos := (Good.nonempty G hD).card_pos
    omega
  have hdecomp :
      (k - 1) * (A.card + 2 - k) + (k - 2).choose 2 + 1 =
        ((k - 1) * (A.card - D.card + 2 - k) + (k - 2).choose 2) +
          ((k - 1) * D.card + 1) := by
    rw [harg, Nat.mul_add]
    omega
  rw [hdecomp] at hedge
  have hinc' :
      ((k - 1) * (A.card - D.card + 2 - k) + (k - 2).choose 2) +
          incidentCount G A D ≤ edgeCount G A :=
    (Nat.add_le_add_left hinc _).trans hedge
  rw [← hsplit] at hinc'
  omega

theorem Good.card_mul_le_of_noSmallCoreOn
    {A D : Finset V} {k q : ℕ} (hk : 2 ≤ k) (hq : 2 * k ≤ q)
    (hcardA : k - 1 ≤ A.card)
    (hlocal : LocalExpansion G A k)
    (hedge : edgeThreshold k A.card ≤ edgeCount G A)
    (hnosmall : NoSmallCoreOn G A k q)
    (hD : Good G A k D) :
    k * D.card ≤ A.card := by
  classical
  by_contra hbad
  have hbad' : A.card < k * D.card := by omega
  let candidates : Finset (Finset V) :=
    A.powerset.filter fun E ↦ Good G A k E ∧ A.card < k * E.card
  have hDmem : D ∈ candidates := by
    simp only [candidates, mem_filter, mem_powerset]
    exact ⟨Good.subset G hD, hD, hbad'⟩
  obtain ⟨M, hMmax⟩ := candidates.exists_minimal ⟨D, hDmem⟩
  have hMmem := hMmax.1
  have hMdata : Good G A k M ∧ A.card < k * M.card := by
    exact (mem_filter.mp hMmem).2
  have hMone : 1 < M.card := by
    have hAfeasible := card_ge_succ_of_edgeThreshold_le G k hk hcardA hedge
    have hMne := Good.nonempty G hMdata.1
    by_contra h
    have : M.card = 1 := by
      have := hMne.card_pos
      omega
    rw [this] at hMdata
    omega
  obtain ⟨E, hEgood, hEss, hhalf⟩ :=
    Good.exists_proper_subgood_of_one_lt G hMdata.1 hMone
  have hEnotmem : E ∉ candidates := by
    intro hEmem
    exact hEss.ne (Subset.antisymm hEss.subset (hMmax.2 hEmem hEss.subset))
  have hEnotbad : ¬ A.card < k * E.card := by
    intro hEbad
    apply hEnotmem
    simp only [candidates, mem_filter, mem_powerset]
    exact ⟨Good.subset G hEgood, hEgood, hEbad⟩
  have hEsmall : k * E.card ≤ A.card := by omega
  have hEcard : E.card ≤ A.card - k + 1 := by
    have hEpos := (Good.nonempty G hEgood).card_pos
    have hEk : E.card + k ≤ A.card + 1 := by
      nlinarith
    omega
  obtain ⟨U, hUcomp, hUcore⟩ :=
    Good.exists_core_in_complement G hk hcardA hlocal hedge hEgood hEcard
  have hUA : U ⊆ A := hUcomp.trans sdiff_subset
  have hsum : U.card + E.card ≤ A.card := by
    have hUcard := card_le_card hUcomp
    rw [card_sdiff_of_subset (Good.subset G hEgood)] at hUcard
    omega
  have hAM : A.card < 2 * k * E.card := by nlinarith
  have hAEq : A.card ≤ q * E.card := by nlinarith
  have hmul := Nat.mul_le_mul_left q hsum
  have hkey : q * U.card + A.card ≤ q * A.card := by nlinarith
  have hqpos : 1 ≤ q := by omega
  have hqsplit : q = (q - 1) + 1 := by omega
  have hsmall : q * U.card ≤ (q - 1) * A.card := by
    exact (Nat.add_le_add_iff_right).mp <| by
      calc
        q * U.card + A.card ≤ q * A.card := hkey
        _ = (q - 1) * A.card + A.card := by
          calc
            q * A.card = ((q - 1) + 1) * A.card :=
              congrArg (fun r : ℕ ↦ r * A.card) hqsplit
            _ = (q - 1) * A.card + A.card := by
              rw [add_mul, one_mul]
  exact hnosmall ⟨U, hUA, hUcore, hsmall⟩

def MaximalGood (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (D : Finset V) : Prop :=
  Good G A k D ∧ ∀ E, Good G A k E → D ⊆ E → E ⊆ D

noncomputable def maxGood (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) : Finset (Finset V) := by
  classical
  exact A.powerset.filter (MaximalGood G A k)

@[simp] lemma mem_maxGood {A D : Finset V} {k : ℕ} :
    D ∈ maxGood G A k ↔ MaximalGood G A k D := by
  classical
  rw [maxGood]
  constructor
  · intro h
    exact (mem_filter.mp h).2
  · intro h
    exact mem_filter.mpr ⟨mem_powerset.mpr (Good.subset G h.1), h⟩

lemma Good.exists_maximalGood_superset
    {A D : Finset V} {k : ℕ} (hD : Good G A k D) :
    ∃ M ∈ maxGood G A k, D ⊆ M := by
  classical
  let goods : Finset (Finset V) := A.powerset.filter (Good G A k)
  have hDmem : D ∈ goods := by
    exact mem_filter.mpr ⟨mem_powerset.mpr (Good.subset G hD), hD⟩
  obtain ⟨M, hDM, hMmax⟩ := goods.exists_le_maximal hDmem
  refine ⟨M, (mem_maxGood (G := G)).mpr ⟨?_, ?_⟩, hDM⟩
  · exact (mem_filter.mp hMmax.1).2
  · intro E hE hME
    apply hMmax.2
    · exact mem_filter.mpr ⟨mem_powerset.mpr (Good.subset G hE), hE⟩
    · exact hME

theorem maxGood_pairwiseDisjoint {A : Finset V} {k : ℕ} :
    ((maxGood G A k : Finset (Finset V)) : Set (Finset V)).PairwiseDisjoint id := by
  intro D hD E hE hDE
  have hD' : MaximalGood G A k D := (mem_maxGood (G := G)).mp (by simpa using hD)
  have hE' : MaximalGood G A k E := (mem_maxGood (G := G)).mp (by simpa using hE)
  apply Finset.disjoint_left.mpr
  intro v hvD hvE
  have hne : (D ∩ E).Nonempty := ⟨v, mem_inter.mpr ⟨hvD, hvE⟩⟩
  have hU : Good G A k (D ∪ E) := Good.union_inter hD'.1 hE'.1 hne
  have hUD := hD'.2 (D ∪ E) hU subset_union_left
  have hEU : E ⊆ D := subset_union_right.trans hUD
  have hDU := hE'.2 (D ∪ E) hU subset_union_right
  have hDE' : D ⊆ E := subset_union_left.trans hDU
  exact hDE (Subset.antisymm hDE' hEU)

theorem maxGood_pairwise_not_adjacent {A : Finset V} {k : ℕ}
    {D E : Finset V} (hD : D ∈ maxGood G A k)
    (hE : E ∈ maxGood G A k) (hDE : D ≠ E) :
    ¬ AdjacentSets G D E := by
  have hD' := (mem_maxGood (G := G)).mp hD
  have hE' := (mem_maxGood (G := G)).mp hE
  intro hadj
  have hU : Good G A k (D ∪ E) := Good.union_adj hD'.1 hE'.1 hadj
  have hUD := hD'.2 (D ∪ E) hU subset_union_left
  have hEU : E ⊆ D := subset_union_right.trans hUD
  have hDU := hE'.2 (D ∪ E) hU subset_union_right
  have hDE' : D ⊆ E := subset_union_left.trans hDU
  exact hDE (Subset.antisymm hDE' hEU)

theorem degreeEq_subset_biUnion_maxGood {A : Finset V} {k : ℕ} :
    degreeEq G A k ⊆ (maxGood G A k).biUnion id := by
  intro v hv
  have hvdata := mem_degreeEq.mp hv
  have hsingle : Good G A k {v} := Good.singleton hvdata.1 hvdata.2
  obtain ⟨M, hM, hvM⟩ := hsingle.exists_maximalGood_superset
  exact mem_biUnion.mpr ⟨M, hM, hvM (mem_singleton_self v)⟩

theorem maximalGood_complement_hasMinDegreeOn
    {A D : Finset V} {k : ℕ} (hD : MaximalGood G A k D)
    (hne : (A \ D).Nonempty) : HasMinDegreeOn G (A \ D) k := by
  refine ⟨hne, ?_⟩
  intro v hv
  by_contra hdeg
  have hle : degreeOn G (A \ D) v ≤ k - 1 := by omega
  have hins : Good G A k (insert v D) := Good.insert hD.1 hv hle
  have hback := hD.2 (insert v D) hins (subset_insert v D)
  exact (mem_sdiff.mp hv).2 (hback (mem_insert_self v D))

theorem card_degreeEq_le_maxGood_mass {A : Finset V} {k : ℕ} :
    (degreeEq G A k).card ≤ ∑ D ∈ maxGood G A k, D.card := by
  calc
    (degreeEq G A k).card ≤ #((maxGood G A k).biUnion id) :=
      card_le_card (degreeEq_subset_biUnion_maxGood (G := G))
    _ = ∑ D ∈ maxGood G A k, D.card :=
      card_biUnion (maxGood_pairwiseDisjoint (G := G))

end P814

end

section
namespace P814
namespace Dyadic

open scoped BigOperators

variable {V : Type*}

def levelStart (j : ℕ) : ℕ := 2 ^ j - 1

def levelIndices (j : ℕ) : Finset ℕ :=
  Finset.Ico (levelStart j) (levelStart (j + 1))

def levelMembers (C : List (Finset V)) (j : ℕ) : List (Finset V) :=
  (C.drop (levelStart j)).take (2 ^ j)

def retainedMembers (C : List (Finset V)) (J : ℕ) : List (Finset V) :=
  C.take (levelStart J)

def cardAt (C : List (Finset V)) (i : ℕ) : ℕ :=
  (C.getD i ∅).card

def Nonincreasing (C : List (Finset V)) : Prop :=
  ∀ {i j : ℕ}, i ≤ j → j < C.length → cardAt C j ≤ cardAt C i

def levelMass (C : List (Finset V)) (j : ℕ) : ℕ :=
  ∑ i ∈ levelIndices j, cardAt C i

def retainedMass (C : List (Finset V)) (J : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (levelStart J), cardAt C i

def totalMass (C : List (Finset V)) : ℕ :=
  ∑ i ∈ Finset.range C.length, cardAt C i

def tailMass (C : List (Finset V)) (J : ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico (levelStart J) C.length, cardAt C i

def betweenMass (C : List (Finset V)) (J₀ J₁ : ℕ) : ℕ :=
  ∑ i ∈ Finset.Ico (levelStart J₀) (levelStart J₁), cardAt C i

def CompleteThrough (C : List (Finset V)) (J : ℕ) : Prop :=
  levelStart J ≤ C.length

def MaximalComplete (C : List (Finset V)) (J : ℕ) : Prop :=
  CompleteThrough C J ∧ C.length < levelStart (J + 1)

lemma levelStart_zero : levelStart 0 = 0 := by
  simp [levelStart]

lemma levelStart_succ (j : ℕ) : levelStart (j + 1) = levelStart j + 2 ^ j := by
  simp only [levelStart, pow_succ]
  omega

lemma levelStart_mono : Monotone levelStart := by
  intro i j hij
  exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by omega) hij) 1

lemma levelStart_le_succ (j : ℕ) : levelStart j ≤ levelStart (j + 1) :=
  levelStart_mono (Nat.le_succ j)

@[simp] lemma card_levelIndices (j : ℕ) : (levelIndices j).card = 2 ^ j := by
  simp [levelIndices, Nat.card_Ico, levelStart_succ]

lemma mem_levelIndices {i j : ℕ} :
    i ∈ levelIndices j ↔ levelStart j ≤ i ∧ i < levelStart (j + 1) := by
  simp [levelIndices]

lemma levelIndices_subset_range {C : List (Finset V)} {j : ℕ}
    (hC : CompleteThrough C (j + 1)) :
    levelIndices j ⊆ Finset.range C.length := by
  intro i hi
  rw [mem_levelIndices] at hi
  exact Finset.mem_range.2 (hi.2.trans_le hC)

@[simp] lemma length_retainedMembers {C : List (Finset V)} {J : ℕ}
    (hC : CompleteThrough C J) :
    (retainedMembers C J).length = levelStart J := by
  rw [retainedMembers, List.length_take, min_eq_left]
  exact hC

@[simp] lemma length_levelMembers {C : List (Finset V)} {j : ℕ}
    (hC : CompleteThrough C (j + 1)) :
    (levelMembers C j).length = 2 ^ j := by
  rw [levelMembers, List.length_take, List.length_drop]
  have : 2 ^ j ≤ C.length - levelStart j := by
    unfold CompleteThrough at hC
    rw [levelStart_succ] at hC
    omega
  simp [this]

lemma levelMembers_nonempty {C : List (Finset V)} {j : ℕ}
    (hC : CompleteThrough C (j + 1)) :
    levelMembers C j ≠ [] := by
  intro hnil
  have hlen := length_levelMembers hC
  rw [hnil] at hlen
  have hpow : 0 < 2 ^ j := pow_pos (by omega) _
  simp only [List.length_nil] at hlen
  omega

lemma cardAt_eq_card_getElem (C : List (Finset V)) (i : ℕ) (hi : i < C.length) :
    cardAt C i = C[i].card := by
  simp [cardAt, List.getD, hi]

lemma totalMass_eq_sum_card (C : List (Finset V)) :
    totalMass C = (C.map Finset.card).sum := by
  rw [totalMass, Finset.sum_range, ← Fin.sum_univ_fun_getElem]
  apply Finset.sum_congr rfl
  intro i _
  simp [cardAt]

lemma retainedMass_succ (C : List (Finset V)) (j : ℕ) :
    retainedMass C (j + 1) = retainedMass C j + levelMass C j := by
  rw [retainedMass, retainedMass, levelMass, levelIndices]
  exact (Finset.sum_range_add_sum_Ico (cardAt C) (levelStart_le_succ j)).symm

lemma totalMass_eq_retained_add_tail {C : List (Finset V)} {J : ℕ}
    (hJ : CompleteThrough C J) :
    totalMass C = retainedMass C J + tailMass C J := by
  rw [totalMass, retainedMass, tailMass]
  exact (Finset.sum_range_add_sum_Ico (cardAt C) hJ).symm

lemma betweenMass_eq_retained_sub {C : List (Finset V)} {J₀ J₁ : ℕ}
    (hJJ : J₀ ≤ J₁) :
    betweenMass C J₀ J₁ = retainedMass C J₁ - retainedMass C J₀ := by
  have hadd := Finset.sum_range_add_sum_Ico (cardAt C) (levelStart_mono hJJ)
  unfold betweenMass retainedMass
  omega

lemma retained_add_between {C : List (Finset V)} {J₀ J₁ : ℕ}
    (hJJ : J₀ ≤ J₁) :
    retainedMass C J₀ + betweenMass C J₀ J₁ = retainedMass C J₁ := by
  rw [betweenMass_eq_retained_sub hJJ, Nat.add_sub_of_le]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (levelStart_mono hJJ))

private lemma sum_le_card_mul {s : Finset ℕ} {f : ℕ → ℕ} {b : ℕ}
    (h : ∀ i ∈ s, f i ≤ b) :
    s.sum f ≤ s.card * b := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      have ha_le : f a ≤ b := h a (Finset.mem_insert_self a s)
      have hs : ∀ i ∈ s, f i ≤ b := by
        intro i hi
        exact h i (Finset.mem_insert_of_mem hi)
      have hsum := ih hs
      calc
        f a + s.sum f ≤ b + s.card * b := Nat.add_le_add ha_le hsum
        _ = (s.card + 1) * b := by ring

private lemma card_mul_le_sum {s : Finset ℕ} {f : ℕ → ℕ} {b : ℕ}
    (h : ∀ i ∈ s, b ≤ f i) :
    s.card * b ≤ s.sum f := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      have ha_ge : b ≤ f a := h a (Finset.mem_insert_self a s)
      have hs : ∀ i ∈ s, b ≤ f i := by
        intro i hi
        exact h i (Finset.mem_insert_of_mem hi)
      have hsum := ih hs
      calc
        (s.card + 1) * b = b + s.card * b := by ring
        _ ≤ f a + s.sum f := Nat.add_le_add ha_ge hsum

lemma levelMass_succ_le_two_mul (C : List (Finset V)) (j : ℕ)
    (hord : Nonincreasing C) (hcomplete : CompleteThrough C (j + 2)) :
    levelMass C (j + 1) ≤ 2 * levelMass C j := by
  let b := levelStart (j + 1)
  let x := cardAt C b
  have hb_lt : b < C.length := by
    have hb_step : b < levelStart (j + 2) := by
      rw [show j + 2 = (j + 1) + 1 by omega, levelStart_succ]
      exact Nat.lt_add_of_pos_right (pow_pos (by omega) _)
    exact hb_step.trans_le hcomplete
  have hnext : levelMass C (j + 1) ≤ (levelIndices (j + 1)).card * x := by
    apply sum_le_card_mul
    intro i hi
    rw [mem_levelIndices] at hi
    exact hord hi.1 (hi.2.trans_le hcomplete)
  have hcurrent : (levelIndices j).card * x ≤ levelMass C j := by
    apply card_mul_le_sum
    intro i hi
    rw [mem_levelIndices] at hi
    exact hord (Nat.le_of_lt hi.2) hb_lt
  simp only [card_levelIndices] at hnext hcurrent
  calc
    levelMass C (j + 1) ≤ 2 ^ (j + 1) * x := hnext
    _ = 2 * (2 ^ j * x) := by rw [pow_succ]; ring
    _ ≤ 2 * levelMass C j := Nat.mul_le_mul_left 2 hcurrent

lemma tailMass_le_retainedMass (C : List (Finset V)) (J : ℕ)
    (hord : Nonincreasing C) (hmax : MaximalComplete C J) :
    tailMass C J ≤ retainedMass C J := by
  by_cases hempty : C.length = levelStart J
  · simp [tailMass, hempty]
  · have hb_lt : levelStart J < C.length := lt_of_le_of_ne hmax.1 (Ne.symm hempty)
    let x := cardAt C (levelStart J)
    have htail : tailMass C J ≤ (Finset.Ico (levelStart J) C.length).card * x := by
      apply sum_le_card_mul
      intro i hi
      rw [Finset.mem_Ico] at hi
      exact hord hi.1 hi.2
    have hretained : (Finset.range (levelStart J)).card * x ≤ retainedMass C J := by
      apply card_mul_le_sum
      intro i hi
      rw [Finset.mem_range] at hi
      exact hord (Nat.le_of_lt hi) hb_lt
    have hcards : (Finset.Ico (levelStart J) C.length).card ≤
        (Finset.range (levelStart J)).card := by
      simp only [Nat.card_Ico, Finset.card_range]
      have hmaxUpper := hmax.2
      rw [show levelStart (J + 1) = 2 * levelStart J + 1 by
        have hp : 0 < 2 ^ J := pow_pos (by omega) _
        simp only [levelStart, pow_succ]
        omega] at hmaxUpper
      omega
    exact htail.trans <| (Nat.mul_le_mul_right x hcards).trans hretained

lemma two_mul_retainedMass_ge_totalMass (C : List (Finset V)) (J : ℕ)
    (hord : Nonincreasing C) (hmax : MaximalComplete C J) :
    totalMass C ≤ 2 * retainedMass C J := by
  rw [totalMass_eq_retained_add_tail hmax.1, two_mul]
  exact Nat.add_le_add_left (tailMass_le_retainedMass C J hord hmax) _

lemma retainedMass_ge_half_total (C : List (Finset V)) (J : ℕ)
    (hord : Nonincreasing C) (hmax : MaximalComplete C J) :
    totalMass C / 2 ≤ retainedMass C J := by
  exact Nat.div_le_of_le_mul (two_mul_retainedMass_ge_totalMass C J hord hmax)

structure IsMinimalCutoff (C : List (Finset V)) (q J : ℕ) : Prop where
  pos : 0 < J
  reaches : q ≤ retainedMass C J
  previous_lt : retainedMass C (J - 1) < q

lemma exists_minimalCutoff (C : List (Finset V)) {q Jmax : ℕ}
    (hq : 0 < q) (hr : q ≤ retainedMass C Jmax) :
    ∃ J ≤ Jmax, IsMinimalCutoff C q J := by
  let P : ℕ → Prop := fun J ↦ q ≤ retainedMass C J
  have hex : ∃ J, P J := ⟨Jmax, hr⟩
  let J := Nat.find hex
  have hJP : P J := Nat.find_spec hex
  change q ≤ retainedMass C J at hJP
  have hJpos : 0 < J := by
    by_contra h
    have hJ0 : J = 0 := Nat.eq_zero_of_not_pos h
    have hzero : retainedMass C J = 0 := by
      simp [retainedMass, hJ0, levelStart]
    have hqzero : q ≤ 0 := hJP.trans_eq hzero
    omega
  have hJle : J ≤ Jmax := Nat.find_min' hex hr
  refine ⟨J, hJle, hJpos, hJP, ?_⟩
  by_contra hnot
  have hpred : P (J - 1) := Nat.le_of_not_gt hnot
  have := Nat.find_min' hex hpred
  omega

lemma cutoff_level_lt_two_mul (C : List (Finset V)) {q J : ℕ}
    (hord : Nonincreasing C) (hcomplete : CompleteThrough C J)
    (hcut : IsMinimalCutoff C q J) (hJ : 1 < J) :
    levelMass C (J - 1) < 2 * q := by
  have hidx : J - 2 + 1 = J - 1 := by omega
  have hcompleteIdx : J - 2 + 2 = J := by omega
  have hsucc : levelMass C (J - 1) ≤ 2 * levelMass C (J - 2) := by
    have hc : CompleteThrough C (J - 2 + 2) := by
      simpa [hcompleteIdx] using hcomplete
    have hs := levelMass_succ_le_two_mul C (J - 2) hord hc
    simpa [hidx] using hs
  have hlevel_prev : levelMass C (J - 2) ≤ retainedMass C (J - 1) := by
    have hs := retainedMass_succ C (J - 2)
    rw [hidx] at hs
    omega
  have hprev := hcut.previous_lt
  omega

lemma cutoff_retained_lt_three_mul (C : List (Finset V)) {q J : ℕ}
    (hord : Nonincreasing C) (hcomplete : CompleteThrough C J)
    (hcut : IsMinimalCutoff C q J) (hJ : 1 < J) :
    retainedMass C J < 3 * q := by
  rw [show J = (J - 1) + 1 by omega, retainedMass_succ]
  have hlevel := cutoff_level_lt_two_mul C hord hcomplete hcut hJ
  have hprev := hcut.previous_lt
  omega

lemma cutoff_tail_gt (C : List (Finset V)) {q J Jmax lower : ℕ}
    (hJJ : J ≤ Jmax)
    (hlower : lower + 3 * q ≤ retainedMass C Jmax)
    (hprefix : retainedMass C J < 3 * q) :
    lower < betweenMass C J Jmax := by
  have hadd := retained_add_between (C := C) hJJ
  omega

private lemma levelIndices_disjoint_of_lt {j l : ℕ} (hjl : j < l) :
    Disjoint (levelIndices j) (levelIndices l) := by
  rw [Finset.disjoint_left]
  intro i hij hil
  rw [mem_levelIndices] at hij hil
  have hboundary : levelStart (j + 1) ≤ levelStart l :=
    levelStart_mono (Nat.succ_le_of_lt hjl)
  omega

lemma levelIndices_disjoint {j l : ℕ} (hjl : j ≠ l) :
    Disjoint (levelIndices j) (levelIndices l) := by
  rcases lt_or_gt_of_ne hjl with hlt | hgt
  · exact levelIndices_disjoint_of_lt hlt
  · exact (levelIndices_disjoint_of_lt hgt).symm

lemma biUnion_levelIndices_Ico {J₀ J : ℕ} (hJJ : J₀ ≤ J) :
    (Finset.Ico J₀ J).biUnion levelIndices =
      Finset.Ico (levelStart J₀) (levelStart J) := by
  induction J, hJJ using Nat.le_induction with
  | base => simp
  | @succ J hJJ ih =>
      rw [Nat.Ico_succ_right_eq_insert_Ico hJJ, Finset.biUnion_insert, ih,
        levelIndices, Finset.union_comm]
      exact Finset.Ico_union_Ico_eq_Ico (levelStart_mono hJJ) (levelStart_le_succ J)

lemma betweenMass_succ (C : List (Finset V)) {J₀ J : ℕ} (hJJ : J₀ ≤ J) :
    betweenMass C J₀ (J + 1) = betweenMass C J₀ J + levelMass C J := by
  unfold betweenMass levelMass levelIndices
  exact (Finset.sum_Ico_consecutive (cardAt C) (levelStart_mono hJJ)
    (levelStart_le_succ J)).symm

lemma twice_selected_level_le_previous
    (C : List (Finset V)) (S : Finset ℕ) {j : ℕ}
    (hord : Nonincreasing C) (hcomplete : CompleteThrough C (j + 1))
    (hj : 0 < j) (hS : S ⊆ levelIndices j)
    (hquarter : 4 * S.card ≤ 2 ^ j) :
    2 * S.sum (cardAt C) ≤ levelMass C (j - 1) := by
  let b := levelStart j
  let x := cardAt C b
  have hb_lt : b < C.length := by
    have hb_step : b < levelStart (j + 1) := by
      rw [levelStart_succ]
      exact Nat.lt_add_of_pos_right (pow_pos (by omega) _)
    exact hb_step.trans_le hcomplete
  have hselected : S.sum (cardAt C) ≤ S.card * x := by
    apply sum_le_card_mul
    intro i hi
    have hiLevel := hS hi
    rw [mem_levelIndices] at hiLevel
    exact hord hiLevel.1 (hiLevel.2.trans_le hcomplete)
  have hprev : (levelIndices (j - 1)).card * x ≤ levelMass C (j - 1) := by
    apply card_mul_le_sum
    intro i hi
    rw [mem_levelIndices] at hi
    have hidx : j - 1 + 1 = j := by omega
    have hib : i < b := by simpa [b, hidx] using hi.2
    exact hord hib.le hb_lt
  have hpow : 2 ^ j = 2 * 2 ^ (j - 1) := by
    calc
      2 ^ j = 2 ^ ((j - 1) + 1) := by congr 1; omega
      _ = 2 ^ (j - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (j - 1) := by ring
  have hcard : 2 * S.card ≤ 2 ^ (j - 1) := by
    rw [hpow] at hquarter
    omega
  calc
    2 * S.sum (cardAt C) ≤ 2 * (S.card * x) := Nat.mul_le_mul_left 2 hselected
    _ = (2 * S.card) * x := by ring
    _ ≤ 2 ^ (j - 1) * x := Nat.mul_le_mul_right x hcard
    _ = (levelIndices (j - 1)).card * x := by simp
    _ ≤ levelMass C (j - 1) := hprev

private lemma sum_previous_levels_add_last
    (C : List (Finset V)) {J₀ J : ℕ} (_hJ₀ : 0 < J₀) (hJJ : J₀ ≤ J) :
    (Finset.Ico J₀ J).sum (fun j ↦ levelMass C (j - 1)) + levelMass C (J - 1) =
      levelMass C (J₀ - 1) + betweenMass C J₀ J := by
  induction J, hJJ using Nat.le_induction with
  | base => simp [betweenMass]
  | @succ J hJJ ih =>
      rw [Finset.sum_Ico_succ_top hJJ, betweenMass_succ C hJJ]
      have hsub : J + 1 - 1 = J := by omega
      rw [hsub]
      omega

lemma twice_selected_mass_le
    (C : List (Finset V)) (S : Finset ℕ) {J₀ J : ℕ}
    (hord : Nonincreasing C) (hcomplete : CompleteThrough C J)
    (hJ₀ : 0 < J₀) (hJJ : J₀ ≤ J)
    (hsel : S ⊆ Finset.Ico (levelStart J₀) (levelStart J))
    (hquarter : ∀ j, J₀ ≤ j → j < J →
      4 * (S ∩ levelIndices j).card ≤ 2 ^ j) :
    2 * S.sum (cardAt C) ≤ levelMass C (J₀ - 1) + betweenMass C J₀ J := by
  let levels := Finset.Ico J₀ J
  let selectedAt : ℕ → Finset ℕ := fun j ↦ S ∩ levelIndices j
  have hpair : (↑levels : Set ℕ).PairwiseDisjoint selectedAt := by
    intro j hj l hl hjl
    exact (levelIndices_disjoint hjl).mono Finset.inter_subset_right Finset.inter_subset_right
  have hunion : levels.biUnion selectedAt = S := by
    apply Finset.ext
    intro i
    constructor
    · intro hi
      rcases Finset.mem_biUnion.mp hi with ⟨j, hj, hij⟩
      exact (Finset.mem_inter.mp hij).1
    · intro hi
      have hiRange := hsel hi
      rw [← biUnion_levelIndices_Ico hJJ] at hiRange
      rcases Finset.mem_biUnion.mp hiRange with ⟨j, hj, hij⟩
      exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_inter.mpr ⟨hi, hij⟩⟩
  have hmassDecompose :
      S.sum (cardAt C) = levels.sum (fun j ↦ (selectedAt j).sum (cardAt C)) := by
    have hsum := Finset.sum_biUnion (f := cardAt C) hpair
    simpa [hunion] using hsum
  have hperLevel : ∀ j ∈ levels,
      2 * (selectedAt j).sum (cardAt C) ≤ levelMass C (j - 1) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hc : CompleteThrough C (j + 1) :=
      hcomplete.trans' (levelStart_mono (by omega))
    exact twice_selected_level_le_previous C (selectedAt j) hord hc (by omega)
      Finset.inter_subset_right (hquarter j hj.1 hj.2)
  have hsumLevels :
      levels.sum (fun j ↦ 2 * (selectedAt j).sum (cardAt C)) ≤
        levels.sum (fun j ↦ levelMass C (j - 1)) := by
    exact Finset.sum_le_sum hperLevel
  have hprevious := sum_previous_levels_add_last C hJ₀ hJJ
  have hpreviousLe :
      levels.sum (fun j ↦ levelMass C (j - 1)) ≤
        levelMass C (J₀ - 1) + betweenMass C J₀ J := by
    calc
      levels.sum (fun j ↦ levelMass C (j - 1)) ≤
          levels.sum (fun j ↦ levelMass C (j - 1)) + levelMass C (J - 1) := by
            omega
      _ = levelMass C (J₀ - 1) + betweenMass C J₀ J := by
        simpa [levels] using hprevious
  rw [hmassDecompose, Finset.mul_sum]
  exact hsumLevels.trans hpreviousLe

lemma retainedMass_le_first (C : List (Finset V)) (J : ℕ)
    (hord : Nonincreasing C) (hcomplete : CompleteThrough C J) :
    retainedMass C J ≤ levelStart J * cardAt C 0 := by
  by_cases hJ : levelStart J = 0
  · simp [retainedMass, hJ]
  · have hs : (Finset.range (levelStart J)).sum (cardAt C) ≤
        (Finset.range (levelStart J)).card * cardAt C 0 := by
      apply sum_le_card_mul
      intro i hi
      rw [Finset.mem_range] at hi
      have hi_len : i < C.length := hi.trans_le hcomplete
      exact hord (Nat.zero_le i) hi_len
    simpa [retainedMass] using hs

lemma exists_large_member_of_retained_mass (C : List (Finset V)) {q J : ℕ}
    (hq : 0 < q) (hord : Nonincreasing C) (hcomplete : CompleteThrough C J)
    (hmass : q ≤ retainedMass C J) :
    ∃ i < levelStart J, q ≤ levelStart J * cardAt C i := by
  have hstart : 0 < levelStart J := by
    by_contra h
    have : levelStart J = 0 := Nat.eq_zero_of_not_pos h
    have hzero : retainedMass C J = 0 := by simp [retainedMass, this]
    have hqzero : q ≤ 0 := by simpa [hzero] using hmass
    omega
  refine ⟨0, hstart, ?_⟩
  exact hmass.trans (retainedMass_le_first C J hord hcomplete)

lemma signed_shortage_lt_two_pow (C : List (Finset V)) {q J : ℕ} {t : ℤ}
    (_hJ : 0 < J) (hord : Nonincreasing C) (hcomplete : CompleteThrough C J)
    (hmass : q ≤ retainedMass C J)
    (hforbidden : t * (cardAt C 0 : ℤ) < q) :
    t < (2 ^ J : ℕ) := by
  by_contra hnot
  have hpow : ((2 ^ J : ℕ) : ℤ) ≤ t := by omega
  have hret := retainedMass_le_first C J hord hcomplete
  have hstart : levelStart J < 2 ^ J := by
    simp [levelStart, pow_pos (by omega : 0 < (2 : ℕ))]
  have hq : (q : ℤ) ≤ (levelStart J : ℤ) * (cardAt C 0 : ℤ) := by
    exact_mod_cast hmass.trans hret
  have hnonneg : (0 : ℤ) ≤ cardAt C 0 := by positivity
  have hmul : (levelStart J : ℤ) * (cardAt C 0 : ℤ) ≤
      t * (cardAt C 0 : ℤ) := by
    apply mul_le_mul_of_nonneg_right _ hnonneg
    exact (Int.ofNat_lt.2 hstart).le.trans hpow
  omega

end Dyadic
end P814

end

section
open Finset SimpleGraph
open scoped Sym2

namespace P814

variable {V : Type*} [Fintype V] [DecidableEq V]

structure ProtectedFamily (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (k : ℕ) where
  blocks : Finset (Finset V)
  nonempty : ∀ D ∈ blocks, D.Nonempty
  subset_ambient : ∀ D ∈ blocks, D ⊆ U
  pairwise_disjoint : ∀ D ∈ blocks, ∀ E ∈ blocks, D ≠ E → Disjoint D E
  high_degree : ∀ D ∈ blocks, ∀ x ∈ D, k ≤ degreeOn G U x
  incident_le : ∀ D ∈ blocks,
    incidentCount G U D ≤ (k - 1) * D.card + 1

namespace ProtectedFamily

variable {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V} {k : ℕ}

def Free (C : ProtectedFamily G U k) (x : V) : Prop :=
  ∀ D ∈ C.blocks, x ∉ D

def WholeBlocks (C : ProtectedFamily G U k) (Y : Finset V) : Prop :=
  ∀ D ∈ C.blocks, D ⊆ Y ∨ Disjoint D Y

lemma free_of_degree_lt (C : ProtectedFamily G U k) {x : V}
    (hx : degreeOn G U x < k) : C.Free x := by
  intro D hD hxD
  exact (not_le_of_gt hx) (C.high_degree D hD x hxD)

lemma wholeBlocks_singleton (C : ProtectedFamily G U k) {w : V}
    (hw : degreeOn G U w < k) : C.WholeBlocks {w} := by
  intro D hD
  right
  rw [Finset.disjoint_singleton_right]
  exact C.free_of_degree_lt hw D hD

end ProtectedFamily

variable {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V} {k : ℕ}

structure ShadowClosed (C : ProtectedFamily G U k) (w : V) (Y : Finset V) : Prop where
  subset_ambient : Y ⊆ U
  root_mem : w ∈ Y
  whole_blocks : C.WholeBlocks Y
  residual_degree : ∀ x ∈ U \ Y, AdjacentSets G {x} Y → k ≤ degreeOn G (U \ Y) x
  adjacent_blocks : ∀ D ∈ C.blocks, AdjacentSets G D Y → D ⊆ Y

inductive ShadowStep (C : ProtectedFamily G U k) : Finset V → Finset V → Prop
  | vertex (Y : Finset V) (x : V)
      (hxU : x ∈ U) (hxY : x ∉ Y) (hfree : C.Free x)
      (hadj : AdjacentSets G {x} Y) (hdeg : degreeOn G (U \ Y) x ≤ k - 1) :
      ShadowStep C Y (Y ∪ {x})
  | block (Y D : Finset V) (hD : D ∈ C.blocks) (hdisj : Disjoint D Y)
      (hadj : AdjacentSets G D Y) :
      ShadowStep C Y (Y ∪ D)

abbrev ShadowReachable (C : ProtectedFamily G U k) (Y Z : Finset V) : Prop :=
  Relation.ReflTransGen (ShadowStep C) Y Z

def ShadowTerminal (C : ProtectedFamily G U k) (Y : Finset V) : Prop :=
  ¬ ∃ Z, ShadowStep C Y Z

lemma ShadowStep.subset {C : ProtectedFamily G U k} {Y Z : Finset V}
    (h : ShadowStep C Y Z) : Y ⊆ Z := by
  cases h <;> simp

lemma ShadowStep.subset_ambient {C : ProtectedFamily G U k} {Y Z : Finset V}
    (hYU : Y ⊆ U) (h : ShadowStep C Y Z) : Z ⊆ U := by
  cases h with
  | vertex x hxU => simpa using union_subset hYU (singleton_subset_iff.mpr hxU)
  | block D hD => exact union_subset hYU (C.subset_ambient D hD)

lemma ShadowStep.card_lt {C : ProtectedFamily G U k} {Y Z : Finset V}
    (h : ShadowStep C Y Z) : Y.card < Z.card := by
  cases h with
  | vertex x hxU hxY hfree hadj hdeg =>
      have hdisj : Disjoint Y {x} := Finset.disjoint_singleton_right.mpr hxY
      rw [card_union_of_disjoint hdisj, card_singleton]
      omega
  | block D hD hdisj hadj =>
      rw [card_union_of_disjoint hdisj.symm]
      have hpos : 0 < D.card := card_pos.mpr (C.nonempty D hD)
      omega

lemma ShadowStep.wholeBlocks {C : ProtectedFamily G U k} {Y Z : Finset V}
    (hY : C.WholeBlocks Y) (h : ShadowStep C Y Z) : C.WholeBlocks Z := by
  intro D hD
  cases h with
  | vertex x hxU hxY hfree hadj hdeg =>
      rcases hY D hD with hDY | hDY
      · exact Or.inl (hDY.trans subset_union_left)
      · right
        rw [Finset.disjoint_union_right]
        exact ⟨hDY, by simpa [Finset.disjoint_singleton_right] using hfree D hD⟩
  | block E hE hEY hadj =>
      by_cases hDE : D = E
      · subst E
        exact Or.inl subset_union_right
      · rcases hY D hD with hDY | hDY
        · exact Or.inl (hDY.trans subset_union_left)
        · right
          rw [Finset.disjoint_union_right]
          exact ⟨hDY, C.pairwise_disjoint D hD E hE hDE⟩

lemma shadowReachable_subset_ambient {C : ProtectedFamily G U k} {Y Z : Finset V}
    (hYU : Y ⊆ U) (h : ShadowReachable C Y Z) : Z ⊆ U := by
  induction h with
  | refl => exact hYU
  | tail hreach hstep ih => exact hstep.subset_ambient ih

lemma shadowReachable_wholeBlocks {C : ProtectedFamily G U k} {Y Z : Finset V}
    (hY : C.WholeBlocks Y) (h : ShadowReachable C Y Z) : C.WholeBlocks Z := by
  induction h with
  | refl => exact hY
  | tail hreach hstep ih => exact hstep.wholeBlocks ih

lemma shadowReachable_mono {C : ProtectedFamily G U k} {Y Z : Finset V}
    (h : ShadowReachable C Y Z) : Y ⊆ Z := by
  induction h with
  | refl => exact Subset.rfl
  | tail hreach hstep ih => exact ih.trans hstep.subset

noncomputable def shadowSaturate (C : ProtectedFamily G U k) (Y : Finset V) : Finset V := by
  classical
  by_cases h : ∃ Z, ShadowStep C Y Z
  · exact shadowSaturate C (Classical.choose h)
  · exact Y
termination_by Fintype.card V - Y.card
decreasing_by
  have hlt := (Classical.choose_spec h).card_lt
  have hle : (Classical.choose h).card ≤ Fintype.card V := by
    simpa using card_le_card (show Classical.choose h ⊆ (univ : Finset V) by simp)
  omega

lemma shadowSaturate_terminal (C : ProtectedFamily G U k) (Y : Finset V) :
    ShadowTerminal C (shadowSaturate C Y) := by
  rw [shadowSaturate]
  split
  · rename_i h
    exact shadowSaturate_terminal C (Classical.choose h)
  · rename_i h
    exact h
termination_by Fintype.card V - Y.card
decreasing_by
  have hex : ∃ Z, ShadowStep C Y Z := by assumption
  have hlt := (Classical.choose_spec hex).card_lt
  have hle : (Classical.choose hex).card ≤ Fintype.card V := by
    simpa using card_le_card
      (show Classical.choose hex ⊆ (univ : Finset V) by simp)
  omega

lemma shadowSaturate_reachable (C : ProtectedFamily G U k) (Y : Finset V) :
    ShadowReachable C Y (shadowSaturate C Y) := by
  rw [shadowSaturate]
  split
  · rename_i h
    exact (Relation.ReflTransGen.single (Classical.choose_spec h)).trans
      (shadowSaturate_reachable C (Classical.choose h))
  · exact Relation.ReflTransGen.refl
termination_by Fintype.card V - Y.card
decreasing_by
  have hex : ∃ Z, ShadowStep C Y Z := by assumption
  have hlt := (Classical.choose_spec hex).card_lt
  have hle : (Classical.choose hex).card ≤ Fintype.card V := by
    simpa using card_le_card
      (show Classical.choose hex ⊆ (univ : Finset V) by simp)
  omega

noncomputable def shadow (C : ProtectedFamily G U k) (w : V) : Finset V :=
  shadowSaturate C {w}

lemma shadow_reachable (C : ProtectedFamily G U k) (w : V) :
    ShadowReachable C {w} (shadow C w) :=
  shadowSaturate_reachable C {w}

lemma shadow_terminal (C : ProtectedFamily G U k) (w : V) :
    ShadowTerminal C (shadow C w) :=
  shadowSaturate_terminal C {w}

lemma ShadowStep.subset_of_closed {C : ProtectedFamily G U k} {w : V}
    {Y Z W : Finset V} (hk : 1 ≤ k) (hYW : Y ⊆ W) (hW : ShadowClosed C w W)
    (hstep : ShadowStep C Y Z) : Z ⊆ W := by
  cases hstep with
  | vertex x hxU hxY hfree hadj hdeg =>
      apply union_subset hYW
      rw [singleton_subset_iff]
      by_contra hxW
      have hxUW : x ∈ U \ W := mem_sdiff.mpr ⟨hxU, hxW⟩
      have hadjW : AdjacentSets G {x} W := by
        rcases hadj with ⟨a, ha, y, hy, hay⟩
        exact ⟨a, ha, y, hYW hy, hay⟩
      have hres := hW.residual_degree x hxUW hadjW
      have hsub : U \ W ⊆ U \ Y := by
        intro z hz
        exact mem_sdiff.mpr ⟨(mem_sdiff.mp hz).1,
          fun hzY ↦ (mem_sdiff.mp hz).2 (hYW hzY)⟩
      have hmono := degreeOn_mono G hsub x
      omega
  | block D hD hdisj hadj =>
      apply union_subset hYW
      apply hW.adjacent_blocks D hD
      rcases hadj with ⟨x, hx, y, hy, hxy⟩
      exact ⟨x, hx, y, hYW hy, hxy⟩

lemma shadowReachable_subset_of_closed {C : ProtectedFamily G U k} {w : V}
    {Y Z W : Finset V} (hk : 1 ≤ k) (hYW : Y ⊆ W) (hW : ShadowClosed C w W)
    (hreach : ShadowReachable C Y Z) : Z ⊆ W := by
  induction hreach with
  | refl => exact hYW
  | tail hreach hstep ih => exact hstep.subset_of_closed hk ih hW

lemma terminal_shadowClosed (C : ProtectedFamily G U k) {w : V} {Y : Finset V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1)
    (hreach : ShadowReachable C {w} Y) (hterm : ShadowTerminal C Y) :
    ShadowClosed C w Y := by
  have hYsub : Y ⊆ U := shadowReachable_subset_ambient (by simpa) hreach
  have hwhole : C.WholeBlocks Y :=
    shadowReachable_wholeBlocks (C.wholeBlocks_singleton (by omega)) hreach
  refine ⟨hYsub, ?_, hwhole, ?_, ?_⟩
  · exact shadowReachable_mono hreach (by simp)
  · intro x hxUY hadj
    by_contra hnot
    have hdegcontra : degreeOn G (U \ Y) x ≤ k - 1 := by omega
    have hfree : C.Free x := by
      intro D hD hxD
      rcases hwhole D hD with hDY | hDY
      · exact (mem_sdiff.mp hxUY).2 (hDY hxD)
      · have hadjDY : AdjacentSets G D Y := by
          rcases hadj with ⟨a, ha, y, hy, hay⟩
          have hax : a = x := by simpa using ha
          subst a
          exact ⟨x, hxD, y, hy, hay⟩
        exact hterm ⟨Y ∪ D, ShadowStep.block Y D hD hDY hadjDY⟩
    exact hterm ⟨Y ∪ {x}, ShadowStep.vertex Y x (mem_sdiff.mp hxUY).1
      (mem_sdiff.mp hxUY).2 hfree hadj hdegcontra⟩
  · intro D hD hadj
    rcases hwhole D hD with hDY | hDY
    · exact hDY
    · exact False.elim (hterm ⟨Y ∪ D, ShadowStep.block Y D hD hDY hadj⟩)

lemma shadow_closed (C : ProtectedFamily G U k) {w : V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1) :
    ShadowClosed C w (shadow C w) :=
  terminal_shadowClosed C hk hwU hwdeg (shadow_reachable C w) (shadow_terminal C w)

lemma shadow_minimal (C : ProtectedFamily G U k) {w : V}
    (hk : 1 ≤ k) (_hwU : w ∈ U) (_hwdeg : degreeOn G U w ≤ k - 1)
    {Y : Finset V} (hY : ShadowClosed C w Y) : shadow C w ⊆ Y := by
  exact shadowReachable_subset_of_closed hk (by simpa using hY.root_mem) hY
    (shadow_reachable C w)

lemma shadow_choice_independent (C : ProtectedFamily G U k) {w : V} {Y : Finset V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1)
    (hreach : ShadowReachable C {w} Y) (hterm : ShadowTerminal C Y) :
    Y = shadow C w := by
  apply Subset.antisymm
  · have hwsh : w ∈ shadow C w :=
      shadowReachable_mono (shadow_reachable C w) (by simp)
    have hroot : {w} ⊆ shadow C w := singleton_subset_iff.mpr hwsh
    exact shadowReachable_subset_of_closed hk hroot
      (shadow_closed C hk hwU hwdeg) hreach
  · exact shadow_minimal C hk hwU hwdeg
      (terminal_shadowClosed C hk hwU hwdeg hreach hterm)

lemma shadow_subset_ambient (C : ProtectedFamily G U k) {w : V}
    (hwU : w ∈ U) : shadow C w ⊆ U :=
  shadowReachable_subset_ambient (by simpa) (shadow_reachable C w)

lemma root_mem_shadow (C : ProtectedFamily G U k) (w : V) : w ∈ shadow C w :=
  shadowReachable_mono (shadow_reachable C w) (by simp)

def lowDefect (k : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (U X : Finset V) : ℕ :=
  ∑ x ∈ X, if degreeOn G U x ≤ k - 1 then k - degreeOn G U x else 0

private lemma shadow_incidentCount_singleton {A : Finset V} {v : V} (hv : v ∈ A) :
    incidentCount G A {v} = degreeOn G A v := by
  unfold incidentCount incidentEdges degreeOn
  symm
  refine Finset.card_bij (fun w _ ↦ s(v, w)) ?_ ?_ ?_
  · intro w hw
    rcases mem_inter.mp hw with ⟨hvw, hwA⟩
    refine mem_sdiff.mpr ⟨mem_edgeOn.mpr ⟨?_, ?_⟩, ?_⟩
    · simpa [SimpleGraph.mem_neighborFinset] using hvw
    · intro z hz
      have hz' : z = v ∨ z = w := by
        simpa [Sym2.toFinset_mk_eq] using hz
      rcases hz' with rfl | rfl
      · exact hv
      · exact hwA
    · intro hres
      have hvend : v ∈ s(v, w).toFinset := by simp [Sym2.toFinset_mk_eq]
      have hvres := (mem_edgeOn.mp hres).2 hvend
      exact (mem_sdiff.mp hvres).2 (by simp)
  · intro w₁ hw₁ w₂ hw₂ heq
    rcases Sym2.eq_iff.mp heq with h | h
    · exact h.2
    · have hadj : G.Adj v w₁ := by
        simpa [SimpleGraph.mem_neighborFinset] using (mem_inter.mp hw₁).1
      have hvw₁ : v ≠ w₁ := by
        intro hvw
        subst w₁
        exact G.loopless.irrefl v hadj
      exact (hvw₁ h.2.symm).elim
  · intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
        rcases mem_sdiff.mp he with ⟨heA, hnot⟩
        have hxy : G.Adj x y := by
          simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using
            (mem_edgeOn.mp heA).1
        have hsub := (mem_edgeOn.mp heA).2
        have hxA : x ∈ A := hsub (by simp)
        have hyA : y ∈ A := hsub (by simp)
        have hvxy : x = v ∨ y = v := by
          by_contra h
          have hxv : x ≠ v := fun hxv ↦ h (Or.inl hxv)
          have hyv : y ≠ v := fun hyv ↦ h (Or.inr hyv)
          apply hnot
          apply mem_edgeOn.mpr
          refine ⟨(mem_edgeOn.mp heA).1, ?_⟩
          intro z hz
          have hz' : z = x ∨ z = y := by
            simpa [Sym2.toFinset_mk_eq] using hz
          rcases hz' with rfl | rfl
          · exact mem_sdiff.mpr ⟨hxA, by simpa using hxv⟩
          · exact mem_sdiff.mpr ⟨hyA, by simpa using hyv⟩
        rcases hvxy with rfl | rfl
        · refine ⟨y, ?_, rfl⟩
          exact mem_inter.mpr
            ⟨by simpa [SimpleGraph.mem_neighborFinset] using hxy, hyA⟩
        · refine ⟨x, ?_, Sym2.eq_swap⟩
          exact mem_inter.mpr
            ⟨by simpa [SimpleGraph.mem_neighborFinset] using hxy.symm, hxA⟩

private lemma shadow_incidentCount_insert {A Y : Finset V} {x : V}
    (hx : x ∈ A \ Y) :
    incidentCount G A (insert x Y) =
      incidentCount G A Y + degreeOn G (A \ Y) x := by
  have h₁ := edgeCount_sdiff_add_incidentCount G A Y
  have h₂ := edgeCount_sdiff_add_incidentCount G (A \ Y) {x}
  have h₃ := edgeCount_sdiff_add_incidentCount G A (insert x Y)
  have hsingle := shadow_incidentCount_singleton (G := G) hx
  have hs : (A \ Y) \ {x} = A \ insert x Y := by
    ext z
    simp only [mem_sdiff, mem_singleton, mem_insert]
    tauto
  rw [hs, hsingle] at h₂
  omega

private lemma degreeOn_sdiff_add_one_le_of_adjacent
    {A Y : Finset V} {x : V} (hYA : Y ⊆ A)
    (hadj : AdjacentSets G {x} Y) :
    degreeOn G (A \ Y) x + 1 ≤ degreeOn G A x := by
  unfold degreeOn
  apply Nat.succ_le_iff.mpr
  apply card_lt_card
  constructor
  · intro z hz
    exact mem_inter.mpr ⟨(mem_inter.mp hz).1, (mem_sdiff.mp (mem_inter.mp hz).2).1⟩
  · intro hreverse
    rcases hadj with ⟨a, ha, y, hy, hay⟩
    have hax : a = x := by simpa using ha
    subst a
    have hybig : y ∈ G.neighborFinset x ∩ A := by
      exact mem_inter.mpr ⟨by simpa [SimpleGraph.mem_neighborFinset], hYA hy⟩
    have hysmall := hreverse hybig
    exact (mem_sdiff.mp (mem_inter.mp hysmall).2).2 hy

lemma degreeOn_sdiff_eq_of_not_adjacent {A Y : Finset V} {x : V}
    (_hYA : Y ⊆ A) (hnot : ¬ AdjacentSets G {x} Y) :
    degreeOn G (A \ Y) x = degreeOn G A x := by
  apply Nat.le_antisymm
  · exact degreeOn_mono G sdiff_subset x
  · unfold degreeOn
    apply card_le_card
    intro y hy
    rcases mem_inter.mp hy with ⟨hxy, hyA⟩
    refine mem_inter.mpr ⟨hxy, mem_sdiff.mpr ⟨hyA, ?_⟩⟩
    intro hyY
    apply hnot
    exact ⟨x, by simp, y, hyY, by simpa [SimpleGraph.mem_neighborFinset] using hxy⟩

lemma ShadowStep.potential_mono {C : ProtectedFamily G U k} {Y Z : Finset V}
    (hYU : Y ⊆ U) (h : ShadowStep C Y Z) :
    deletionPotential k G U Y ≤ deletionPotential k G U Z := by
  cases h with
  | vertex x hxU hxY hfree hadj hdeg =>
      have hx : x ∈ U \ Y := mem_sdiff.mpr ⟨hxU, hxY⟩
      have hcard : (insert x Y).card = Y.card + 1 := by simp [hxY]
      have hinc := shadow_incidentCount_insert (G := G) hx
      simp only [union_singleton] at hinc ⊢
      unfold deletionPotential
      rw [hcard, hinc]
      push_cast
      have hdegZ : (degreeOn G (U \ Y) x : ℤ) ≤ (k - 1 : ℕ) := by
        exact_mod_cast hdeg
      ring_nf
      omega
  | block D hD hdisj hadj =>
      have hDU := C.subset_ambient D hD
      have hcard : (Y ∪ D).card = Y.card + D.card := by
        rw [card_union_of_disjoint hdisj.symm]
      have hadjCount := incidentCount_union_add_one_le_of_adjacent G hYU hDU hadj.symm
      have hincD := C.incident_le D hD
      have hinc : incidentCount G U (Y ∪ D) ≤
          incidentCount G U Y + (k - 1) * D.card := by
        omega
      unfold deletionPotential
      rw [hcard]
      push_cast
      have hincZ : (incidentCount G U (Y ∪ D) : ℤ) ≤
          (incidentCount G U Y : ℤ) + ((k - 1) * D.card : ℕ) := by
        exact_mod_cast hinc
      push_cast at hincZ
      ring_nf at hincZ ⊢
      omega

lemma ShadowStep.lowDefect_growth_le {C : ProtectedFamily G U k} {Y Z : Finset V}
    (hYU : Y ⊆ U) (h : ShadowStep C Y Z) :
    (lowDefect k G U Z : ℤ) - (lowDefect k G U Y : ℤ) ≤
      deletionPotential k G U Z - deletionPotential k G U Y := by
  have hpot := h.potential_mono hYU
  cases h with
  | vertex x hxU hxY hfree hadj hdeg =>
      have hx : x ∈ U \ Y := mem_sdiff.mpr ⟨hxU, hxY⟩
      have hcard : (insert x Y).card = Y.card + 1 := by simp [hxY]
      have hinc := shadow_incidentCount_insert (G := G) hx
      have hdegree := degreeOn_sdiff_add_one_le_of_adjacent (G := G) hYU hadj
      simp only [union_singleton] at hinc ⊢
      unfold lowDefect deletionPotential
      rw [sum_insert hxY, hcard, hinc]
      by_cases hlow : degreeOn G U x ≤ k - 1
      · simp only [hlow, if_true]
        push_cast
        have hlt : degreeOn G U x < k := by omega
        rw [Nat.cast_sub hlt.le]
        ring_nf
        omega
      · simp only [hlow, if_false]
        push_cast
        ring_nf
        have hd : (degreeOn G (U \ Y) x : ℤ) ≤ ((k - 1 : ℕ) : ℤ) := by
          exact_mod_cast hdeg
        omega
  | block D hD hdisj hadj =>
      have hDU := C.subset_ambient D hD
      have hzero : ∀ x ∈ D,
          (if degreeOn G U x ≤ k - 1 then k - degreeOn G U x else 0) = 0 := by
        intro x hxD
        have hxhigh := C.high_degree D hD x hxD
        by_cases hlow : degreeOn G U x ≤ k - 1
        · simp [hlow, Nat.sub_eq_zero_of_le hxhigh]
        · simp [hlow]
      have hdef : lowDefect k G U (Y ∪ D) = lowDefect k G U Y := by
        unfold lowDefect
        rw [sum_union hdisj.symm]
        have hsum : ∑ x ∈ D,
            (if degreeOn G U x ≤ k - 1 then k - degreeOn G U x else 0) = 0 := by
          apply sum_eq_zero
          intro x hxD
          exact hzero x hxD
        rw [hsum, add_zero]
      rw [hdef]
      simp only [sub_self]
      exact sub_nonneg.mpr hpot

lemma shadowReachable_potential_mono {C : ProtectedFamily G U k} {Y Z : Finset V}
    (hYU : Y ⊆ U) (hreach : ShadowReachable C Y Z) :
    deletionPotential k G U Y ≤ deletionPotential k G U Z := by
  induction hreach with
  | refl => exact le_rfl
  | tail hreach hstep ih =>
      exact ih.trans (hstep.potential_mono (shadowReachable_subset_ambient hYU hreach))

lemma shadowReachable_accounting (C : ProtectedFamily G U k) {w : V} {Y : Finset V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1)
    (hreach : ShadowReachable C {w} Y) :
    0 ≤ deletionPotential k G U Y ∧
      (lowDefect k G U Y : ℤ) ≤ deletionPotential k G U Y + 1 := by
  have hstartDef : lowDefect k G U {w} = k - degreeOn G U w := by
    simp [lowDefect, hwdeg]
  have hstartInc : incidentCount G U {w} = degreeOn G U w :=
    shadow_incidentCount_singleton (G := G) hwU
  have hstartEq : (lowDefect k G U {w} : ℤ) =
      deletionPotential k G U {w} + 1 := by
    rw [hstartDef]
    unfold deletionPotential
    rw [hstartInc]
    simp only [card_singleton]
    have hdeglt : degreeOn G U w < k := by omega
    rw [Nat.cast_sub hdeglt.le]
    push_cast
    omega
  have hstartNonneg : 0 ≤ deletionPotential k G U {w} := by
    unfold deletionPotential
    rw [hstartInc]
    simp only [card_singleton]
    push_cast
    have hd : (degreeOn G U w : ℤ) ≤ ((k - 1 : ℕ) : ℤ) := by
      exact_mod_cast hwdeg
    simpa using hd
  induction hreach with
  | refl => exact ⟨hstartNonneg, hstartEq.le⟩
  | tail hreach hstep ih =>
      have hYU : _ ⊆ U := shadowReachable_subset_ambient (by simpa) hreach
      have hpot := hstep.potential_mono hYU
      have hgrowth := hstep.lowDefect_growth_le hYU
      constructor
      · exact ih.1.trans hpot
      · omega

theorem shadow_potential_nonneg (C : ProtectedFamily G U k) {w : V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1) :
    0 ≤ deletionPotential k G U (shadow C w) :=
  (shadowReachable_accounting C hk hwU hwdeg (shadow_reachable C w)).1

theorem lowDefect_shadow_le (C : ProtectedFamily G U k) {w : V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1) :
    (lowDefect k G U (shadow C w) : ℤ) ≤
      deletionPotential k G U (shadow C w) + 1 :=
  (shadowReachable_accounting C hk hwU hwdeg (shadow_reachable C w)).2

theorem lowDefect_shadow_le_two_mul (C : ProtectedFamily G U k) {w : V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1)
    (hpos : 0 < deletionPotential k G U (shadow C w)) :
    (lowDefect k G U (shadow C w) : ℤ) ≤
      2 * deletionPotential k G U (shadow C w) := by
  have hle := lowDefect_shadow_le C hk hwU hwdeg
  omega

theorem shadow_zero_unique_low (C : ProtectedFamily G U k) {w : V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1)
    (hzero : deletionPotential k G U (shadow C w) = 0) :
    (∀ s ∈ shadow C w, degreeOn G U s ≤ k - 1 → s = w) ∧
      degreeOn G U w = k - 1 := by
  have hle := lowDefect_shadow_le C hk hwU hwdeg
  rw [hzero] at hle
  have hdef : lowDefect k G U (shadow C w) ≤ 1 := by
    exact_mod_cast hle
  have hwsh : w ∈ shadow C w := root_mem_shadow C w
  constructor
  · intro s hs hslow
    by_contra hsw
    have hpair : {w, s} ⊆ shadow C w := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hwsh
      · exact hs
    have hpairsum :
        (∑ x ∈ {w, s},
          if degreeOn G U x ≤ k - 1 then k - degreeOn G U x else 0) ≤
          lowDefect k G U (shadow C w) := by
      unfold lowDefect
      exact sum_le_sum_of_subset hpair
    have hwpos : 1 ≤ k - degreeOn G U w := by omega
    have hspos : 1 ≤ k - degreeOn G U s := by omega
    have hwn : w ∉ ({s} : Finset V) := by
      simp only [mem_singleton]
      intro hws
      exact hsw hws.symm
    have htwo : 2 ≤
        ∑ x ∈ {w, s},
          if degreeOn G U x ≤ k - 1 then k - degreeOn G U x else 0 := by
      rw [sum_insert hwn, sum_singleton]
      simp only [hwdeg, hslow, if_true]
      omega
    omega
  · have hwle :
        (if degreeOn G U w ≤ k - 1 then k - degreeOn G U w else 0) ≤
          lowDefect k G U (shadow C w) := by
      unfold lowDefect
      exact single_le_sum
        (f := fun x ↦ if degreeOn G U x ≤ k - 1 then k - degreeOn G U x else 0)
        (fun _ _ ↦ Nat.zero_le _) hwsh
    have hwterm :
        (if degreeOn G U w ≤ k - 1 then k - degreeOn G U w else 0) =
          k - degreeOn G U w := by simp [hwdeg]
    rw [hwterm] at hwle
    omega

theorem shortage_delete_shadow_le (C : ProtectedFamily G U k) {w : V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1) :
    shortage k G (U \ shadow C w) ≤ shortage k G U := by
  rw [shortage_sdiff k G (shadow_subset_ambient C hwU)]
  have hpot := shadow_potential_nonneg C hk hwU hwdeg
  omega

theorem shortage_delete_shadow_eq (C : ProtectedFamily G U k) {w : V}
    (hwU : w ∈ U)
    (hzero : deletionPotential k G U (shadow C w) = 0) :
    shortage k G (U \ shadow C w) = shortage k G U := by
  rw [shortage_sdiff k G (shadow_subset_ambient C hwU), hzero, sub_zero]

theorem low_degree_after_delete_shadow (C : ProtectedFamily G U k) {w x : V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1)
    (hx : x ∈ U \ shadow C w)
    (hxlow : degreeOn G (U \ shadow C w) x ≤ k - 1) :
    degreeOn G U x ≤ k - 1 ∧ x ≠ w := by
  have hclosed := shadow_closed C hk hwU hwdeg
  have hnot : ¬ AdjacentSets G {x} (shadow C w) := by
    intro hadj
    have hhigh := hclosed.residual_degree x hx hadj
    omega
  have heq := degreeOn_sdiff_eq_of_not_adjacent (G := G)
    (shadow_subset_ambient C hwU) hnot
  constructor
  · rwa [heq] at hxlow
  · intro hxw
    subst x
    exact (mem_sdiff.mp hx).2 (root_mem_shadow C w)

theorem shadow_complement_minDegree_of_unique_low
    (C : ProtectedFamily G U k) {w : V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1)
    (hproper : shadow C w ≠ U)
    (hunique : ∀ x ∈ U, degreeOn G U x ≤ k - 1 → x = w) :
    HasMinDegreeOn G (U \ shadow C w) k := by
  have hsub := shadow_subset_ambient C hwU
  have hnonempty : (U \ shadow C w).Nonempty := by
    by_contra hempty
    have hUsub : U ⊆ shadow C w := by
      intro x hxU
      by_contra hxsh
      exact hempty ⟨x, mem_sdiff.mpr ⟨hxU, hxsh⟩⟩
    exact hproper (Subset.antisymm hsub hUsub)
  refine ⟨hnonempty, ?_⟩
  intro x hx
  by_contra hnot
  have hxlow : degreeOn G (U \ shadow C w) x ≤ k - 1 := by omega
  have hold := low_degree_after_delete_shadow C hk hwU hwdeg hx hxlow
  exact hold.2 (hunique x (mem_sdiff.mp hx).1 hold.1)

lemma incidentCount_ambient_mono {A B X : Finset V} (hAB : A ⊆ B) :
    incidentCount G A X ≤ incidentCount G B X := by
  unfold incidentCount
  apply card_le_card
  intro e he
  rcases mem_sdiff.mp he with ⟨heA, hnotA⟩
  refine mem_sdiff.mpr ⟨edgeOn_mono G hAB heA, ?_⟩
  intro heBX
  apply hnotA
  apply mem_edgeOn.mpr
  refine ⟨(mem_edgeOn.mp heA).1, ?_⟩
  intro x hx
  exact mem_sdiff.mpr
    ⟨(mem_edgeOn.mp heA).2 hx, (mem_sdiff.mp ((mem_edgeOn.mp heBX).2 hx)).2⟩

lemma incidentCount_extension_eq {A D : Finset V} (hUA : U ⊆ A) (hDU : D ⊆ U)
    (hanti : ¬ AdjacentSets G (A \ U) D) :
    incidentCount G A D = incidentCount G U D := by
  apply Nat.le_antisymm
  · unfold incidentCount
    apply card_le_card
    intro e he
    rcases mem_sdiff.mp he with ⟨heA, hnotAD⟩
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hxy : G.Adj x y := by
          simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using
            (mem_edgeOn.mp heA).1
        have hsubA := (mem_edgeOn.mp heA).2
        have hxA : x ∈ A := hsubA (by simp [Sym2.toFinset_mk_eq])
        have hyA : y ∈ A := hsubA (by simp [Sym2.toFinset_mk_eq])
        have hxyD : x ∈ D ∨ y ∈ D := by
          by_contra hnone
          have hxD : x ∉ D := fun hx ↦ hnone (Or.inl hx)
          have hyD : y ∉ D := fun hy ↦ hnone (Or.inr hy)
          apply hnotAD
          apply mem_edgeOn.mpr
          refine ⟨(mem_edgeOn.mp heA).1, ?_⟩
          intro z hz
          have hz' : z = x ∨ z = y := by
            simpa [Sym2.toFinset_mk_eq] using hz
          rcases hz' with rfl | rfl
          · exact mem_sdiff.mpr ⟨hxA, hxD⟩
          · exact mem_sdiff.mpr ⟨hyA, hyD⟩
        have hxU : x ∈ U := by
          rcases hxyD with hxD | hyD
          · exact hDU hxD
          · by_contra hxU
            apply hanti
            exact ⟨x, mem_sdiff.mpr ⟨hxA, hxU⟩, y, hyD, hxy⟩
        have hyU : y ∈ U := by
          rcases hxyD with hxD | hyD
          · by_contra hyU
            apply hanti
            exact ⟨y, mem_sdiff.mpr ⟨hyA, hyU⟩, x, hxD, hxy.symm⟩
          · exact hDU hyD
        refine mem_sdiff.mpr ⟨mem_edgeOn.mpr ⟨(mem_edgeOn.mp heA).1, ?_⟩, ?_⟩
        · intro z hz
          have hz' : z = x ∨ z = y := by
            simpa [Sym2.toFinset_mk_eq] using hz
          rcases hz' with rfl | rfl
          · exact hxU
          · exact hyU
        · intro heUD
          apply hnotAD
          have hsub : U \ D ⊆ A \ D := by
            intro z hz
            exact mem_sdiff.mpr ⟨hUA (mem_sdiff.mp hz).1, (mem_sdiff.mp hz).2⟩
          exact edgeOn_mono G hsub heUD
  · exact incidentCount_ambient_mono (G := G) hUA

noncomputable def ProtectedFamily.extendAmbient (C : ProtectedFamily G U k)
    {A : Finset V} (hUA : U ⊆ A)
    (hnew : ∀ D ∈ C.blocks, ¬ AdjacentSets G (A \ U) D) :
    ProtectedFamily G A k where
  blocks := C.blocks
  nonempty := C.nonempty
  subset_ambient := by
    intro D hD
    exact (C.subset_ambient D hD).trans hUA
  pairwise_disjoint := C.pairwise_disjoint
  high_degree := by
    intro D hD x hxD
    exact (C.high_degree D hD x hxD).trans
      (degreeOn_mono G hUA x)
  incident_le := by
    intro D hD
    rw [incidentCount_extension_eq (G := G) hUA (C.subset_ambient D hD) (hnew D hD)]
    exact C.incident_le D hD

@[simp] lemma ProtectedFamily.extendAmbient_blocks
    (C : ProtectedFamily G U k) {A : Finset V} (hUA : U ⊆ A)
    (hnew : ∀ D ∈ C.blocks, ¬ AdjacentSets G (A \ U) D) :
    (C.extendAmbient hUA hnew).blocks = C.blocks := by
  rfl

private lemma degreeOn_extension_sdiff_add_one_le
    {A Y : Finset V} {x : V} (hUA : U ⊆ A) (hYU : Y ⊆ U)
    (hadj : AdjacentSets G {x} (A \ U)) :
    degreeOn G (U \ Y) x + 1 ≤ degreeOn G (A \ Y) x := by
  unfold degreeOn
  apply Nat.succ_le_iff.mpr
  apply card_lt_card
  constructor
  · intro z hz
    rcases mem_inter.mp hz with ⟨hxz, hz⟩
    exact mem_inter.mpr ⟨hxz, mem_sdiff.mpr
      ⟨hUA (mem_sdiff.mp hz).1, (mem_sdiff.mp hz).2⟩⟩
  · intro hreverse
    rcases hadj with ⟨a, ha, y, hy, hay⟩
    have hax : a = x := by simpa using ha
    subst a
    have hyA := (mem_sdiff.mp hy).1
    have hyU := (mem_sdiff.mp hy).2
    have hyY : y ∉ Y := fun hyin ↦ hyU (hYU hyin)
    have hybig : y ∈ G.neighborFinset x ∩ (A \ Y) := by
      exact mem_inter.mpr
        ⟨by simpa [SimpleGraph.mem_neighborFinset] using hay,
          mem_sdiff.mpr ⟨hyA, hyY⟩⟩
    have hysmall := hreverse hybig
    exact hyU (mem_sdiff.mp (mem_inter.mp hysmall).2).1

private lemma vertex_step_potential_add_one_le
    {Y : Finset V} {x : V} (hxU : x ∈ U) (hxY : x ∉ Y)
    (hdeg : degreeOn G (U \ Y) x + 1 ≤ k - 1) :
    deletionPotential k G U Y + 1 ≤ deletionPotential k G U (Y ∪ {x}) := by
  have hx : x ∈ U \ Y := mem_sdiff.mpr ⟨hxU, hxY⟩
  have hcard : (insert x Y).card = Y.card + 1 := by simp [hxY]
  have hinc := shadow_incidentCount_insert (G := G) hx
  simp only [union_singleton] at hinc ⊢
  unfold deletionPotential
  rw [hcard, hinc]
  push_cast
  have hdegZ : (degreeOn G (U \ Y) x : ℤ) + 1 ≤ ((k - 1 : ℕ) : ℤ) := by
    exact_mod_cast hdeg
  ring_nf
  omega

lemma potential_eq_zero_of_shadowReachable
    (C : ProtectedFamily G U k) {w : V} {Y : Finset V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1)
    (hzero : deletionPotential k G U (shadow C w) = 0)
    (hreach : ShadowReachable C {w} Y) :
    deletionPotential k G U Y = 0 := by
  have hnonneg := (shadowReachable_accounting C hk hwU hwdeg hreach).1
  have hsat := shadowSaturate_reachable C Y
  have hrootSat : ShadowReachable C {w} (shadowSaturate C Y) := hreach.trans hsat
  have heq : shadowSaturate C Y = shadow C w :=
    shadow_choice_independent C hk hwU hwdeg hrootSat (shadowSaturate_terminal C Y)
  have hYU : Y ⊆ U := shadowReachable_subset_ambient (by simpa) hreach
  have hmono := shadowReachable_potential_mono hYU hsat
  rw [heq, hzero] at hmono
  omega

lemma shadowReachable_extension_simulation
    (C : ProtectedFamily G U k) {A : Finset V} {w : V}
    (hk : 1 ≤ k) (hUA : U ⊆ A) (hwU : w ∈ U)
    (hwlowA : degreeOn G A w ≤ k - 1)
    (hnew : ∀ D ∈ C.blocks, ¬ AdjacentSets G (A \ U) D)
    (hzero : deletionPotential k G U (shadow C w) = 0)
    {Y : Finset V}
    (hreachA : ShadowReachable (C.extendAmbient hUA hnew) {w} Y) :
    ShadowReachable C {w} Y ∧ ¬ AdjacentSets G Y (A \ U) := by
  have hwdeg : degreeOn G U w ≤ k - 1 :=
    (degreeOn_mono G hUA w).trans hwlowA
  have hwexact := (shadow_zero_unique_low C hk hwU hwdeg hzero).2
  induction hreachA with
  | refl =>
      refine ⟨Relation.ReflTransGen.refl, ?_⟩
      intro hadj
      have hstrict := degreeOn_extension_sdiff_add_one_le
        (G := G) hUA (empty_subset U) hadj
      simp only [sdiff_empty] at hstrict
      omega
  | @tail Ycur Zcur hreachA hstep ih =>
      rcases ih with ⟨hreachOld, hantiY⟩
      cases hstep with
      | vertex x hxA hxY hfreeA hadj hdegA =>
          have hxU : x ∈ U := by
            by_contra hxU
            apply hantiY
            rcases hadj with ⟨a, ha, y, hy, hay⟩
            have hax : a = x := by simpa using ha
            subst a
            exact ⟨y, hy, x, mem_sdiff.mpr ⟨hxA, hxU⟩, hay.symm⟩
          have hfree : C.Free x := by
            intro D hD hxD
            exact hfreeA D (by simpa using hD) hxD
          have hsub : U \ Ycur ⊆ A \ Ycur := by
            intro z hz
            exact mem_sdiff.mpr ⟨hUA (mem_sdiff.mp hz).1, (mem_sdiff.mp hz).2⟩
          have hdegOld : degreeOn G (U \ Ycur) x ≤ k - 1 :=
            (degreeOn_mono G hsub x).trans hdegA
          have hstepOld : ShadowStep C Ycur (Ycur ∪ {x}) :=
            ShadowStep.vertex Ycur x hxU hxY hfree hadj hdegOld
          have hreachOld' := Relation.ReflTransGen.tail hreachOld hstepOld
          refine ⟨hreachOld', ?_⟩
          intro hadjNew
          rcases hadjNew with ⟨z, hz, a, ha, hza⟩
          rcases mem_union.mp hz with hzY | hzx
          · exact hantiY ⟨z, hzY, a, ha, hza⟩
          · have hzx' : z = x := by simpa using hzx
            subst z
            have hcross : AdjacentSets G {x} (A \ U) :=
              ⟨x, by simp, a, ha, hza⟩
            have hstrictDeg := degreeOn_extension_sdiff_add_one_le
              (G := G) hUA (shadowReachable_subset_ambient (by simpa) hreachOld) hcross
            have hslack : degreeOn G (U \ Ycur) x + 1 ≤ k - 1 :=
              hstrictDeg.trans hdegA
            have hstrictPot := vertex_step_potential_add_one_le
              (G := G) hxU hxY hslack
            have hpotY := potential_eq_zero_of_shadowReachable C hk hwU hwdeg hzero hreachOld
            have hpotZ := potential_eq_zero_of_shadowReachable C hk hwU hwdeg hzero hreachOld'
            rw [hpotY, hpotZ] at hstrictPot
            omega
      | block D hD hdisj hadj =>
          have hDold : D ∈ C.blocks := by simpa using hD
          have hstepOld : ShadowStep C Ycur (Ycur ∪ D) :=
            ShadowStep.block Ycur D hDold hdisj hadj
          refine ⟨Relation.ReflTransGen.tail hreachOld hstepOld, ?_⟩
          intro hadjNew
          rcases hadjNew with ⟨z, hz, a, ha, hza⟩
          rcases mem_union.mp hz with hzY | hzD
          · exact hantiY ⟨z, hzY, a, ha, hza⟩
          · exact hnew D hDold ⟨a, ha, z, hzD, hza.symm⟩

theorem shadow_stable_in_extension
    (C : ProtectedFamily G U k) {A : Finset V} {w : V}
    (hk : 1 ≤ k) (hUA : U ⊆ A) (hwU : w ∈ U)
    (hwlowA : degreeOn G A w ≤ k - 1)
    (hnew : ∀ D ∈ C.blocks, ¬ AdjacentSets G (A \ U) D)
    (hzero : deletionPotential k G U (shadow C w) = 0) :
    shadow (C.extendAmbient hUA hnew) w ⊆ shadow C w ∧
      ¬ AdjacentSets G (shadow (C.extendAmbient hUA hnew) w) (A \ U) := by
  have hwdeg : degreeOn G U w ≤ k - 1 :=
    (degreeOn_mono G hUA w).trans hwlowA
  have hsim := shadowReachable_extension_simulation C hk hUA hwU hwlowA hnew hzero
    (shadow_reachable (C.extendAmbient hUA hnew) w)
  refine ⟨?_, hsim.2⟩
  exact shadowReachable_subset_of_closed hk
    (singleton_subset_iff.mpr (root_mem_shadow C w))
    (shadow_closed C hk hwU hwdeg) hsim.1

theorem extension_shadow_potential_eq_zero
    (C : ProtectedFamily G U k) {A : Finset V} {w : V}
    (hk : 1 ≤ k) (hUA : U ⊆ A) (hwU : w ∈ U)
    (hwlowA : degreeOn G A w ≤ k - 1)
    (hnew : ∀ D ∈ C.blocks, ¬ AdjacentSets G (A \ U) D)
    (hzero : deletionPotential k G U (shadow C w) = 0) :
    deletionPotential k G A (shadow (C.extendAmbient hUA hnew) w) = 0 := by
  let W := shadow (C.extendAmbient hUA hnew) w
  have hwdeg : degreeOn G U w ≤ k - 1 :=
    (degreeOn_mono G hUA w).trans hwlowA
  have hsim := shadowReachable_extension_simulation C hk hUA hwU hwlowA hnew hzero
    (shadow_reachable (C.extendAmbient hUA hnew) w)
  have hWU : W ⊆ U := shadowReachable_subset_ambient (by simpa) hsim.1
  have hanti : ¬ AdjacentSets G (A \ U) W := by
    intro hadj
    exact hsim.2 hadj.symm
  have hinc : incidentCount G A W = incidentCount G U W :=
    incidentCount_extension_eq (G := G) hUA hWU hanti
  have hpotOld : deletionPotential k G U W = 0 :=
    potential_eq_zero_of_shadowReachable C hk hwU hwdeg hzero hsim.1
  unfold deletionPotential at hpotOld ⊢
  rw [hinc]
  exact hpotOld

theorem shortage_delete_extension_shadow_eq
    (C : ProtectedFamily G U k) {A : Finset V} {w : V}
    (hk : 1 ≤ k) (hUA : U ⊆ A) (hwU : w ∈ U)
    (hwlowA : degreeOn G A w ≤ k - 1)
    (hnew : ∀ D ∈ C.blocks, ¬ AdjacentSets G (A \ U) D)
    (hzero : deletionPotential k G U (shadow C w) = 0) :
    shortage k G (A \ shadow (C.extendAmbient hUA hnew) w) = shortage k G A := by
  have hWA : shadow (C.extendAmbient hUA hnew) w ⊆ A :=
    shadow_subset_ambient (C.extendAmbient hUA hnew) (hUA hwU)
  rw [shortage_sdiff k G hWA,
    extension_shadow_potential_eq_zero C hk hUA hwU hwlowA hnew hzero, sub_zero]

lemma shadow_anticomplete_block_of_disjoint (C : ProtectedFamily G U k) {w : V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1)
    {D : Finset V} (hD : D ∈ C.blocks) (hdisj : Disjoint D (shadow C w)) :
    ¬ AdjacentSets G D (shadow C w) := by
  intro hadj
  have hinside := (shadow_closed C hk hwU hwdeg).adjacent_blocks D hD hadj
  obtain ⟨x, hxD⟩ := C.nonempty D hD
  exact (Finset.disjoint_left.mp hdisj) hxD (hinside hxD)

noncomputable def ProtectedFamily.restrictShadowComplement (C : ProtectedFamily G U k) {w : V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1) :
    ProtectedFamily G (U \ shadow C w) k where
  blocks := C.blocks.filter fun D ↦ D ⊆ U \ shadow C w
  nonempty := by
    intro D hD
    exact C.nonempty D (mem_filter.mp hD).1
  subset_ambient := by
    intro D hD
    exact (mem_filter.mp hD).2
  pairwise_disjoint := by
    intro D hD E hE hne
    exact C.pairwise_disjoint D (mem_filter.mp hD).1 E (mem_filter.mp hE).1 hne
  high_degree := by
    intro D hD x hxD
    have hDold := (mem_filter.mp hD).1
    have hDsub := (mem_filter.mp hD).2
    have hdisj : Disjoint D (shadow C w) := by
      rw [Finset.disjoint_left]
      intro y hyD hysh
      exact (mem_sdiff.mp (hDsub hyD)).2 hysh
    have hanti := shadow_anticomplete_block_of_disjoint C hk hwU hwdeg hDold hdisj
    have hnotx : ¬ AdjacentSets G {x} (shadow C w) := by
      intro hadj
      apply hanti
      rcases hadj with ⟨a, ha, y, hy, hay⟩
      have hax : a = x := by simpa using ha
      subst a
      exact ⟨x, hxD, y, hy, hay⟩
    rw [degreeOn_sdiff_eq_of_not_adjacent (G := G)
      (shadow_subset_ambient C hwU) hnotx]
    exact C.high_degree D hDold x hxD
  incident_le := by
    intro D hD
    exact (incidentCount_ambient_mono (G := G) sdiff_subset).trans
      (C.incident_le D (mem_filter.mp hD).1)

@[simp] lemma ProtectedFamily.mem_restrictShadowComplement_blocks
    (C : ProtectedFamily G U k) {w : V}
    (hk : 1 ≤ k) (hwU : w ∈ U) (hwdeg : degreeOn G U w ≤ k - 1)
    {D : Finset V} :
    D ∈ (C.restrictShadowComplement hk hwU hwdeg).blocks ↔
      D ∈ C.blocks ∧ D ⊆ U \ shadow C w := by
  simp [ProtectedFamily.restrictShadowComplement]

end P814

end

section
open Finset SimpleGraph BigOperators

namespace P814

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

def lowVertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) : Finset V :=
  A.filter fun v ↦ degreeOn G A v ≤ k - 1

def veryLowVertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) : Finset V :=
  A.filter fun v ↦ degreeOn G A v ≤ k - 2

@[simp] lemma mem_lowVertices {A : Finset V} {k : ℕ} {v : V} :
    v ∈ lowVertices G A k ↔ v ∈ A ∧ degreeOn G A v ≤ k - 1 := by
  simp [lowVertices]

@[simp] lemma mem_veryLowVertices {A : Finset V} {k : ℕ} {v : V} :
    v ∈ veryLowVertices G A k ↔ v ∈ A ∧ degreeOn G A v ≤ k - 2 := by
  simp [veryLowVertices]

lemma veryLowVertices_subset_lowVertices {A : Finset V} {k : ℕ} (hk : 2 ≤ k) :
    veryLowVertices G A k ⊆ lowVertices G A k := by
  intro v hv
  rw [mem_veryLowVertices] at hv
  rw [mem_lowVertices]
  exact ⟨hv.1, by omega⟩

def Anticomplete (G : SimpleGraph V) (X Y : Finset V) : Prop :=
  ¬ AdjacentSets G X Y

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma Anticomplete.symm {X Y : Finset V} (h : Anticomplete G X Y) :
    Anticomplete G Y X := by
  intro hadj
  exact h hadj.symm

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma Anticomplete.mono {X Y X' Y' : Finset V} (h : Anticomplete G X Y)
    (hX : X' ⊆ X) (hY : Y' ⊆ Y) : Anticomplete G X' Y' := by
  intro hadj
  rcases hadj with ⟨x, hx, y, hy, hxy⟩
  exact h ⟨x, hX hx, y, hY hy, hxy⟩

omit [Fintype V] [DecidableRel G.Adj] in
lemma Anticomplete.union_left {X Y Z : Finset V}
    (hX : Anticomplete G X Z) (hY : Anticomplete G Y Z) :
    Anticomplete G (X ∪ Y) Z := by
  intro hadj
  rcases hadj with ⟨x, hx, z, hz, hxz⟩
  rcases mem_union.mp hx with hx | hx
  · exact hX ⟨x, hx, z, hz, hxz⟩
  · exact hY ⟨x, hx, z, hz, hxz⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma anticomplete_empty_left (X : Finset V) : Anticomplete G ∅ X := by
  simp [Anticomplete, AdjacentSets]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma anticomplete_empty_right (X : Finset V) : Anticomplete G X ∅ := by
  simp [Anticomplete, AdjacentSets]

def reserveUnion (B : V → Finset V) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) : Finset V :=
  (lowVertices G A k).biUnion B

structure ExtensionConclusion
    (C : ProtectedFamily G U k) (B : V → Finset V) (A U' : Finset V) : Prop where

  minDegree : HasMinDegreeOn G U' k

  subset_extension : U' ⊆ A

  shortage_le : shortage k G U' ≤ shortage k G A

  deleted_subset_reserves : A \ U' ⊆ reserveUnion B G A k

  deleted_subset_old : A \ U' ⊆ U

  deleted_anticomplete_new : Anticomplete G (A \ U') (A \ U)

  blocks_whole : C.WholeBlocks U'

  retained_blocks_anticomplete :
    ∀ D ∈ C.blocks, D ⊆ U' → Anticomplete G D (A \ U')

def HasExtensionProperty
    (C : ProtectedFamily G U k) (S : Finset V) (B : V → Finset V) : Prop :=
  ∀ A : Finset V,
    U ⊂ A →
    lowVertices G A k ⊆ lowVertices G U k \ S →
    (∀ D ∈ C.blocks, Anticomplete G (A \ U) D) →
    ∃ U' : Finset V, ExtensionConclusion C B A U'

structure ExtensionCertificate
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (k : ℕ) (C : ProtectedFamily G U k) where

  S : Finset V
  S_subset_low : S ⊆ lowVertices G U k
  veryLow_subset_S : veryLowVertices G U k ⊆ S

  reserve : V → Finset V
  reserve_subset : ∀ v ∈ lowVertices G U k \ S, reserve v ⊆ U
  reserve_pairwise :
    ∀ v ∈ lowVertices G U k \ S,
      ∀ w ∈ lowVertices G U k \ S, v ≠ w → Disjoint (reserve v) (reserve w)

  deficit_le :
    ((S.sum fun s ↦ k - degreeOn G U s : ℕ) : ℤ) ≤ 2 * shortage k G U
  extension : HasExtensionProperty C S reserve

namespace ExtensionCertificate

variable {U : Finset V} {k : ℕ} {C : ProtectedFamily G U k}

lemma reserve_subset_old (E : ExtensionCertificate G U k C)
    {v : V} (hv : v ∈ lowVertices G U k \ E.S) : E.reserve v ⊆ U :=
  E.reserve_subset v hv

lemma reserve_disjoint (E : ExtensionCertificate G U k C)
    {v w : V} (hv : v ∈ lowVertices G U k \ E.S)
    (hw : w ∈ lowVertices G U k \ E.S) (hvw : v ≠ w) :
    Disjoint (E.reserve v) (E.reserve w) :=
  E.reserve_pairwise v hv w hw hvw

end ExtensionCertificate

lemma hasMinDegreeOn_of_lowVertices_eq_empty {A : Finset V} {k : ℕ}
    (hA : A.Nonempty) (hlow : lowVertices G A k = ∅) :
    HasMinDegreeOn G A k := by
  refine ⟨hA, ?_⟩
  intro v hv
  by_contra hnot
  have hvlow : v ∈ lowVertices G A k := by
    rw [mem_lowVertices]
    exact ⟨hv, by omega⟩
  simp [hlow] at hvlow

omit [Fintype V] [DecidableEq V] in
lemma nonempty_of_ssubset {A B : Finset V} (h : A ⊂ B) : B.Nonempty := by
  rcases Finset.ssubset_iff_subset_ne.mp h with ⟨hAB, hne⟩
  by_contra hB
  rw [Finset.not_nonempty_iff_eq_empty] at hB
  subst B
  have hA : A = ∅ := Finset.subset_empty.mp hAB
  exact hne hA

lemma extensionConclusion_self {U A : Finset V} {k : ℕ}
    (C : ProtectedFamily G U k) (B : V → Finset V)
    (hUA : U ⊆ A) (hmin : HasMinDegreeOn G A k) :
    ExtensionConclusion C B A A := by
  refine
    { minDegree := hmin
      subset_extension := Subset.rfl
      shortage_le := le_rfl
      deleted_subset_reserves := ?_
      deleted_subset_old := ?_
      deleted_anticomplete_new := ?_
      blocks_whole := ?_
      retained_blocks_anticomplete := ?_ }
  · simp
  · simp
  · simpa using anticomplete_empty_left (G := G) (A \ U)
  · intro D hD
    exact Or.inl ((C.subset_ambient D hD).trans hUA)
  · intro D hD hDA
    simpa using anticomplete_empty_right (G := G) D

lemma lowVertices_eq_empty_of_subset_empty {A : Finset V} {k : ℕ}
    (h : lowVertices G A k ⊆ ∅) : lowVertices G A k = ∅ :=
  Finset.subset_empty.mp h

lemma extensionConclusion_self_of_low_empty {U A : Finset V} {k : ℕ}
    (C : ProtectedFamily G U k) (B : V → Finset V)
    (hUA : U ⊆ A) (hproper : U ⊂ A)
    (hlow : lowVertices G A k ⊆ ∅) :
    ExtensionConclusion C B A A := by
  apply extensionConclusion_self C B hUA
  exact hasMinDegreeOn_of_lowVertices_eq_empty (nonempty_of_ssubset hproper)
    (lowVertices_eq_empty_of_subset_empty hlow)

lemma ExtensionConclusion.lift_shadow_complement
    {U W F A U' : Finset V} {k : ℕ}
    (C : ProtectedFamily G U k) (CF : ProtectedFamily G F k)
    (B : V → Finset V)
    (_hWU : W ⊆ U) (hF : F = U \ W) (hUA : U ⊆ A)
    (hCF : ∀ D, D ∈ CF.blocks ↔ D ∈ C.blocks ∧ D ⊆ F)
    (hwhole : C.WholeBlocks W)
    (R : ExtensionConclusion CF B A U') :
    ExtensionConclusion C B A U' := by
  have hFU : F ⊆ U := by
    rw [hF]
    exact sdiff_subset
  have hnew : A \ U ⊆ A \ F := by
    intro x hx
    rw [mem_sdiff] at hx ⊢
    exact ⟨hx.1, fun hxF ↦ hx.2 (hFU hxF)⟩
  refine
    { minDegree := R.minDegree
      subset_extension := R.subset_extension
      shortage_le := R.shortage_le
      deleted_subset_reserves := R.deleted_subset_reserves
      deleted_subset_old := fun x hx ↦ hFU (R.deleted_subset_old hx)
      deleted_anticomplete_new :=
        R.deleted_anticomplete_new.mono Subset.rfl hnew
      blocks_whole := ?_
      retained_blocks_anticomplete := ?_ }
  · intro D hDC
    by_cases hDCF : D ∈ CF.blocks
    · exact R.blocks_whole D hDCF
    · have hDW : D ⊆ W := by
        rcases hwhole D hDC with hDW | hdisj
        · exact hDW
        · exfalso
          apply hDCF
          rw [hCF]
          refine ⟨hDC, ?_⟩
          intro x hxD
          rw [hF, mem_sdiff]
          exact ⟨C.subset_ambient D hDC hxD,
            fun hxW ↦ Finset.disjoint_left.mp hdisj hxD hxW⟩
      left
      intro x hxD
      have hxA : x ∈ A := hUA (C.subset_ambient D hDC hxD)
      by_contra hxU'
      have hxdel : x ∈ A \ U' := mem_sdiff.mpr ⟨hxA, hxU'⟩
      have hxF := R.deleted_subset_old hxdel
      rw [hF, mem_sdiff] at hxF
      exact hxF.2 (hDW hxD)
  · intro D hDC hDU'
    by_cases hDCF : D ∈ CF.blocks
    · exact R.retained_blocks_anticomplete D hDCF hDU'
    · have hDW : D ⊆ W := by
        rcases hwhole D hDC with hDW | hdisj
        · exact hDW
        · exfalso
          apply hDCF
          rw [hCF]
          refine ⟨hDC, ?_⟩
          intro x hxD
          rw [hF, mem_sdiff]
          exact ⟨C.subset_ambient D hDC hxD,
            fun hxW ↦ Finset.disjoint_left.mp hdisj hxD hxW⟩
      have hDAF : D ⊆ A \ F := by
        intro x hxD
        rw [mem_sdiff]
        refine ⟨hUA (C.subset_ambient D hDC hxD), ?_⟩
        intro hxF
        rw [hF, mem_sdiff] at hxF
        exact hxF.2 (hDW hxD)
      exact R.deleted_anticomplete_new.symm.mono hDAF Subset.rfl

lemma deficitSum_mono_of_subset {F U S : Finset V} {k : ℕ}
    (hFU : F ⊆ U) (_hS : S ⊆ lowVertices G F k) :
    (S.sum fun s ↦ k - degreeOn G U s) ≤
      S.sum fun s ↦ k - degreeOn G F s := by
  exact Finset.sum_le_sum (s := S) fun s hs ↦
    Nat.sub_le_sub_left (degreeOn_mono G hFU s) k

lemma lowVertices_mono_degree {F U : Finset V} {k : ℕ}
    (hFU : F ⊆ U) {x : V} (hxF : x ∈ F)
    (hxlow : x ∈ lowVertices G U k) : x ∈ lowVertices G F k := by
  rw [mem_lowVertices] at hxlow ⊢
  exact ⟨hxF, (degreeOn_mono G hFU x).trans hxlow.2⟩

lemma veryLowVertices_mono_degree {F U : Finset V} {k : ℕ}
    (hFU : F ⊆ U) {x : V} (hxF : x ∈ F)
    (hxlow : x ∈ veryLowVertices G U k) : x ∈ veryLowVertices G F k := by
  rw [mem_veryLowVertices] at hxlow ⊢
  exact ⟨hxF, (degreeOn_mono G hFU x).trans hxlow.2⟩

private lemma extensionCertificate_empty (k : ℕ)
    (C : ProtectedFamily G (∅ : Finset V) k) :
    Nonempty (ExtensionCertificate G ∅ k C) := by
  let B : V → Finset V := fun _ ↦ ∅
  refine ⟨{
    S := ∅
    S_subset_low := by simp
    veryLow_subset_S := by simp [veryLowVertices]
    reserve := B
    reserve_subset := ?_
    reserve_pairwise := ?_
    deficit_le := ?_
    extension := ?_ }⟩
  · intro v hv
    simp [lowVertices] at hv
  · intro v hv
    simp [lowVertices] at hv
  · simp [shortage]
  · intro A hproper hlow hblocks
    refine ⟨A, extensionConclusion_self_of_low_empty C B ?_ hproper ?_⟩
    · simp
    · simpa [lowVertices] using hlow

lemma lowDefect_eq_sum_lowVertices_inter {U X : Finset V} {k : ℕ}
    (hXU : X ⊆ U) :
    lowDefect k G U X =
      (lowVertices G U k ∩ X).sum (fun x ↦ k - degreeOn G U x) := by
  classical
  have heq : X.filter (fun x ↦ degreeOn G U x ≤ k - 1) =
      lowVertices G U k ∩ X := by
    ext x
    simp only [mem_filter, mem_inter, mem_lowVertices]
    constructor
    · rintro ⟨hxX, hxlow⟩
      exact ⟨⟨hXU hxX, hxlow⟩, hxX⟩
    · rintro ⟨⟨hxU, hxlow⟩, hxX⟩
      exact ⟨hxX, hxlow⟩
  unfold lowDefect
  calc
    X.sum (fun x ↦ if degreeOn G U x ≤ k - 1 then
        k - degreeOn G U x else 0) =
        (X.filter (fun x ↦ degreeOn G U x ≤ k - 1)).sum
          (fun x ↦ k - degreeOn G U x) :=
      (Finset.sum_filter (s := X) (fun x ↦ degreeOn G U x ≤ k - 1)
        (fun x ↦ k - degreeOn G U x)).symm
    _ = (lowVertices G U k ∩ X).sum (fun x ↦ k - degreeOn G U x) := by rw [heq]

private lemma extensionCertificate_allLow {U : Finset V} {k : ℕ}
    (C : ProtectedFamily G U k) (hk : 2 ≤ k)
    (hdef : (lowDefect k G U U : ℤ) ≤ 2 * shortage k G U) :
    Nonempty (ExtensionCertificate G U k C) := by
  let B : V → Finset V := fun _ ↦ ∅
  refine ⟨{
    S := lowVertices G U k
    S_subset_low := Subset.rfl
    veryLow_subset_S := veryLowVertices_subset_lowVertices (G := G) hk
    reserve := B
    reserve_subset := ?_
    reserve_pairwise := ?_
    deficit_le := ?_
    extension := ?_ }⟩
  · intro v hv
    simp at hv
  · intro v hv
    simp at hv
  · have hsum : lowDefect k G U U =
        (lowVertices G U k ∩ U).sum (fun x ↦ k - degreeOn G U x) :=
      lowDefect_eq_sum_lowVertices_inter (G := G) (k := k)
        (U := U) (X := U) Subset.rfl
    have hinter : lowVertices G U k ∩ U = lowVertices G U k := by
      apply inter_eq_left.mpr
      intro x hx
      exact (mem_lowVertices.mp hx).1
    rw [hinter] at hsum
    exact hsum ▸ hdef
  · intro A hproper hlow hblocks
    refine ⟨A, extensionConclusion_self_of_low_empty C B
      (Finset.ssubset_iff_subset_ne.mp hproper).1 hproper ?_⟩
    simpa using hlow

private lemma delete_zero_shadow_conclusion
    {U A : Finset V} {k : ℕ} {w : V}
    (C : ProtectedFamily G U k) (B : V → Finset V)
    (hk : 2 ≤ k) (hUA : U ⊆ A) (hproper : U ⊂ A)
    (hwU : w ∈ U) (_hwlowU : degreeOn G U w ≤ k - 1)
    (hwlowA : degreeOn G A w ≤ k - 1)
    (huniqueA : ∀ x ∈ A, degreeOn G A x ≤ k - 1 → x = w)
    (hnew : ∀ D ∈ C.blocks, Anticomplete G (A \ U) D)
    (hzero : deletionPotential k G U (shadow C w) = 0)
    (hreserve : shadow C w ⊆ B w) :
    ∃ U' : Finset V, ExtensionConclusion C B A U' := by
  let CA : ProtectedFamily G A k := C.extendAmbient hUA hnew
  let WA : Finset V := shadow CA w
  have hwA : w ∈ A := hUA hwU
  have hstable := shadow_stable_in_extension C (by omega) hUA hwU hwlowA hnew hzero
  have hWAold : WA ⊆ shadow C w := by simpa [CA, WA] using hstable.1
  have hWAanti : Anticomplete G WA (A \ U) := by
    change ¬ AdjacentSets G WA (A \ U)
    simpa [CA, WA] using hstable.2
  have hWAA : WA ⊆ A := by
    simpa [CA, WA] using shadow_subset_ambient CA hwA
  have hWAproper : WA ≠ A := by
    intro heq
    have hAU : A ⊆ U := by
      intro x hxA
      have hxWA : x ∈ WA := by simpa [heq] using hxA
      exact (shadow_subset_ambient C hwU) (hWAold hxWA)
    exact (Finset.ssubset_iff_subset_ne.mp hproper).2 (Subset.antisymm hUA hAU)
  have hmin : HasMinDegreeOn G (A \ WA) k := by
    apply shadow_complement_minDegree_of_unique_low CA (by omega) hwA hwlowA
      (by simpa [WA])
    intro x hxA hxlow
    exact huniqueA x hxA hxlow
  have hshort : shortage k G (A \ WA) ≤ shortage k G A := by
    simpa [WA] using shortage_delete_shadow_le CA (by omega) hwA hwlowA
  have hdel : A \ (A \ WA) = WA := by
    ext x
    simp only [mem_sdiff]
    constructor
    · rintro ⟨hxA, hxnot⟩
      by_contra hxWA
      exact hxnot ⟨hxA, hxWA⟩
    · intro hxWA
      exact ⟨hWAA hxWA, fun hx ↦ hx.2 hxWA⟩
  refine ⟨A \ WA, ?_⟩
  refine
    { minDegree := hmin
      subset_extension := sdiff_subset
      shortage_le := hshort
      deleted_subset_reserves := ?_
      deleted_subset_old := ?_
      deleted_anticomplete_new := ?_
      blocks_whole := ?_
      retained_blocks_anticomplete := ?_ }
  · rw [hdel]
    intro x hxWA
    rw [reserveUnion, mem_biUnion]
    refine ⟨w, ?_, hreserve (hWAold hxWA)⟩
    rw [mem_lowVertices]
    exact ⟨hwA, hwlowA⟩
  · rw [hdel]
    exact hWAold.trans (shadow_subset_ambient C hwU)
  · simpa [hdel] using hWAanti
  · intro D hDC
    have hDCA : D ∈ CA.blocks := by
      change D ∈ C.blocks
      exact hDC
    have hclosed := shadow_closed CA (by omega) hwA hwlowA
    rcases hclosed.whole_blocks D hDCA with hDWA | hdisj
    · right
      rw [Finset.disjoint_left]
      intro x hxD hxcomp
      exact (mem_sdiff.mp hxcomp).2 (hDWA hxD)
    · left
      intro x hxD
      rw [mem_sdiff]
      exact ⟨hUA (C.subset_ambient D hDC hxD),
        fun hxWA ↦ Finset.disjoint_left.mp hdisj hxD hxWA⟩
  · intro D hDC hDret
    rw [hdel]
    intro hadj
    have hDCA : D ∈ CA.blocks := by
      change D ∈ C.blocks
      exact hDC
    have hclosed := shadow_closed CA (by omega) hwA hwlowA
    have hDWA : D ⊆ WA := hclosed.adjacent_blocks D hDCA hadj
    obtain ⟨x, hxD⟩ := C.nonempty D hDC
    have hxret := hDret hxD
    exact (mem_sdiff.mp hxret).2 (hDWA hxD)

private lemma extensionCertificate_zero_full_shadow
    {U : Finset V} {k : ℕ} {w : V}
    (C : ProtectedFamily G U k) (hk : 2 ≤ k)
    (hwU : w ∈ U) (hwlow : degreeOn G U w ≤ k - 1)
    (hfull : shadow C w = U)
    (hzero : deletionPotential k G U (shadow C w) = 0) :
    Nonempty (ExtensionCertificate G U k C) := by
  let B : V → Finset V := fun v ↦ if v = w then shadow C w else ∅
  have huniq := shadow_zero_unique_low C (by omega) hwU hwlow hzero
  refine ⟨{
    S := ∅
    S_subset_low := by simp
    veryLow_subset_S := ?_
    reserve := B
    reserve_subset := ?_
    reserve_pairwise := ?_
    deficit_le := ?_
    extension := ?_ }⟩
  · intro x hx
    rw [mem_veryLowVertices] at hx
    have hxw := huniq.1 x (by simpa [hfull] using hx.1) (by omega)
    subst x
    rw [huniq.2] at hx
    omega
  · intro v hv
    rw [mem_sdiff, mem_lowVertices] at hv
    have hvw := huniq.1 v (by simpa [hfull] using hv.1.1) hv.1.2
    subst v
    simp [B, hfull]
  · intro v hv z hz hvz
    rw [mem_sdiff, mem_lowVertices] at hv hz
    have hvw := huniq.1 v (by simpa [hfull] using hv.1.1) hv.1.2
    have hzw := huniq.1 z (by simpa [hfull] using hz.1.1) hz.1.2
    exact (hvz (hvw.trans hzw.symm)).elim
  · have hshort := shortage_delete_shadow_eq C hwU hzero
    rw [hfull] at hshort
    simp [shortage] at hshort ⊢
    omega
  · intro A hproper hlow hnew
    have hUA := (Finset.ssubset_iff_subset_ne.mp hproper).1
    by_cases hempty : lowVertices G A k = ∅
    · exact ⟨A, extensionConclusion_self C B hUA
        (hasMinDegreeOn_of_lowVertices_eq_empty (nonempty_of_ssubset hproper) hempty)⟩
    · obtain ⟨x, hxlow⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hxold := hlow hxlow
      rw [mem_sdiff, mem_lowVertices] at hxold
      have hxw := huniq.1 x (by simpa [hfull] using hxold.1.1) hxold.1.2
      have hwlowA : degreeOn G A w ≤ k - 1 := by
        subst x
        exact (mem_lowVertices.mp hxlow).2
      have huniqueA : ∀ y ∈ A, degreeOn G A y ≤ k - 1 → y = w := by
        intro y hyA hylow
        have hyold := hlow (mem_lowVertices.mpr ⟨hyA, hylow⟩)
        rw [mem_sdiff, mem_lowVertices] at hyold
        exact huniq.1 y (by simpa [hfull] using hyold.1.1) hyold.1.2
      apply delete_zero_shadow_conclusion C B hk hUA hproper hwU hwlow hwlowA
        huniqueA hnew hzero
      intro y hy
      change y ∈ (if w = w then shadow C w else ∅)
      simp only [ite_true]
      exact hy

lemma shadow_anticomplete_restricted_block
    {U : Finset V} {k : ℕ} {w : V}
    (C : ProtectedFamily G U k) (hk : 1 ≤ k)
    (hwU : w ∈ U) (hwlow : degreeOn G U w ≤ k - 1)
    {D : Finset V}
    (hD : D ∈ (C.restrictShadowComplement hk hwU hwlow).blocks) :
    Anticomplete G (shadow C w) D := by
  intro hadj
  have hmem := (ProtectedFamily.mem_restrictShadowComplement_blocks
    C hk hwU hwlow).mp hD
  have hDW : D ⊆ shadow C w :=
    (shadow_closed C hk hwU hwlow).adjacent_blocks D hmem.1 hadj.symm
  obtain ⟨x, hxD⟩ := C.nonempty D hmem.1
  exact (mem_sdiff.mp (hmem.2 hxD)).2 (hDW hxD)

lemma extension_anticomplete_restricted_block
    {U A : Finset V} {k : ℕ} {w : V}
    (C : ProtectedFamily G U k) (hk : 1 ≤ k)
    (hwU : w ∈ U) (hwlow : degreeOn G U w ≤ k - 1)
    (_hUA : U ⊆ A)
    (hnew : ∀ D ∈ C.blocks, Anticomplete G (A \ U) D)
    {D : Finset V}
    (hD : D ∈ (C.restrictShadowComplement hk hwU hwlow).blocks) :
    Anticomplete G (A \ (U \ shadow C w)) D := by
  have hmem := (ProtectedFamily.mem_restrictShadowComplement_blocks
    C hk hwU hwlow).mp hD
  have hcontain : A \ (U \ shadow C w) ⊆ (A \ U) ∪ shadow C w := by
    intro x hx
    rw [mem_sdiff] at hx
    by_cases hxU : x ∈ U
    · exact mem_union_right _ (by
        by_contra hxW
        exact hx.2 (mem_sdiff.mpr ⟨hxU, hxW⟩))
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hx.1, hxU⟩)
  exact (Anticomplete.union_left (hnew D hmem.1)
    (shadow_anticomplete_restricted_block C hk hwU hwlow hD)).mono
      hcontain Subset.rfl

private lemma extensionCertificate_positive_proper_shadow
    {U : Finset V} {k : ℕ} {w : V}
    (C : ProtectedFamily G U k) (hk : 2 ≤ k)
    (hwU : w ∈ U) (hwlow : degreeOn G U w ≤ k - 1)
    (_hproperW : shadow C w ≠ U)
    (hpos : 0 < deletionPotential k G U (shadow C w))
    (EF : ExtensionCertificate G (U \ shadow C w) k
      (C.restrictShadowComplement (by omega) hwU hwlow)) :
    Nonempty (ExtensionCertificate G U k C) := by
  let W := shadow C w
  let F := U \ W
  let CF := C.restrictShadowComplement (by omega) hwU hwlow
  let T := lowVertices G U k ∩ W
  let S := EF.S ∪ T
  have hWU : W ⊆ U := by simpa [W] using shadow_subset_ambient C hwU
  have hFU : F ⊆ U := by simp [F]
  have hlowFU : lowVertices G F k ⊆ lowVertices G U k := by
    intro x hx
    rw [mem_lowVertices] at hx ⊢
    have hold := low_degree_after_delete_shadow C (by omega) hwU hwlow
      (by simpa [F, W] using hx.1) (by simpa [F, W] using hx.2)
    exact ⟨hFU hx.1, hold.1⟩
  refine ⟨{
    S := S
    S_subset_low := ?_
    veryLow_subset_S := ?_
    reserve := EF.reserve
    reserve_subset := ?_
    reserve_pairwise := ?_
    deficit_le := ?_
    extension := ?_ }⟩
  · intro x hx
    rcases mem_union.mp hx with hx | hx
    · exact hlowFU (EF.S_subset_low hx)
    · exact (mem_inter.mp hx).1
  · intro x hx
    rw [mem_veryLowVertices] at hx
    by_cases hxW : x ∈ W
    · exact mem_union_right _ (mem_inter.mpr
        ⟨mem_lowVertices.mpr ⟨hx.1, by omega⟩, hxW⟩)
    · apply mem_union_left
      apply EF.veryLow_subset_S
      exact veryLowVertices_mono_degree hFU (mem_sdiff.mpr ⟨hx.1, hxW⟩)
        (mem_veryLowVertices.mpr hx)
  · intro v hv
    rw [mem_sdiff] at hv
    have hvlow := mem_lowVertices.mp hv.1
    have hvW : v ∉ W := by
      intro hvW
      exact hv.2 (mem_union_right _ (mem_inter.mpr ⟨hv.1, hvW⟩))
    have hvS : v ∉ EF.S := fun hvS ↦ hv.2 (mem_union_left _ hvS)
    exact (EF.reserve_subset v (mem_sdiff.mpr
      ⟨lowVertices_mono_degree hFU (mem_sdiff.mpr ⟨hvlow.1, hvW⟩) hv.1, hvS⟩)).trans hFU
  · intro v hv z hz hvz
    rw [mem_sdiff] at hv hz
    have index : ∀ x, x ∈ lowVertices G U k → x ∉ S →
        x ∈ lowVertices G F k \ EF.S := by
      intro x hxlow hxS
      have hxW : x ∉ W := by
        intro hxW
        exact hxS (mem_union_right _ (mem_inter.mpr ⟨hxlow, hxW⟩))
      exact mem_sdiff.mpr
        ⟨lowVertices_mono_degree hFU
          (mem_sdiff.mpr ⟨(mem_lowVertices.mp hxlow).1, hxW⟩) hxlow,
          fun hxEF ↦ hxS (mem_union_left _ hxEF)⟩
    exact EF.reserve_pairwise v (index v hv.1 hv.2) z (index z hz.1 hz.2) hvz
  · have hdisj : Disjoint EF.S T := by
      rw [Finset.disjoint_left]
      intro x hxS hxT
      have hxF := (mem_lowVertices.mp (EF.S_subset_low hxS)).1
      exact (mem_sdiff.mp (by simpa [F, W] using hxF)).2 (mem_inter.mp hxT).2
    have hunion : S.sum (fun x ↦ k - degreeOn G U x) =
        EF.S.sum (fun x ↦ k - degreeOn G U x) +
          T.sum (fun x ↦ k - degreeOn G U x) := by
      simpa [S] using Finset.sum_union hdisj
    have hmono := deficitSum_mono_of_subset (G := G) hFU EF.S_subset_low
    have hmonoZ : ((EF.S.sum (fun x ↦ k - degreeOn G U x) : ℕ) : ℤ) ≤
        ((EF.S.sum (fun x ↦ k - degreeOn G F x) : ℕ) : ℤ) := by
      exact_mod_cast hmono
    have hshadow := lowDefect_shadow_le_two_mul C (by omega) hwU hwlow hpos
    have hdefeq := lowDefect_eq_sum_lowVertices_inter (G := G) (k := k)
      (U := U) (X := W) hWU
    have hshort : shortage k G F = shortage k G U -
        deletionPotential k G U W := by
      simpa [F, W] using shortage_sdiff k G (shadow_subset_ambient C hwU)
    rw [hunion]
    rw [Nat.cast_add]
    have hshadowT : ((T.sum (fun x ↦ k - degreeOn G U x) : ℕ) : ℤ) ≤
        2 * deletionPotential k G U W := by
      simpa [T, W, hdefeq] using hshadow
    have hEF := EF.deficit_le
    change ((EF.S.sum (fun x ↦ k - degreeOn G F x) : ℕ) : ℤ) ≤
      2 * shortage k G F at hEF
    omega
  · intro A hproper hlow hnew
    have hUA := (Finset.ssubset_iff_subset_ne.mp hproper).1
    have hFA : F ⊂ A := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hFU.trans hUA, ?_⟩
      intro hFAeq
      have hAU : A ⊆ U := fun x hx ↦ hFU (by simpa [hFAeq] using hx)
      exact (Finset.ssubset_iff_subset_ne.mp hproper).2 (Subset.antisymm hUA hAU)
    have hlowF : lowVertices G A k ⊆ lowVertices G F k \ EF.S := by
      intro x hxA
      have hx := hlow hxA
      rw [mem_sdiff] at hx
      have hxW : x ∉ W := by
        intro hxW
        exact hx.2 (mem_union_right _ (mem_inter.mpr ⟨hx.1, hxW⟩))
      exact mem_sdiff.mpr
        ⟨lowVertices_mono_degree hFU
          (mem_sdiff.mpr ⟨(mem_lowVertices.mp hx.1).1, hxW⟩) hx.1,
          fun hxEF ↦ hx.2 (mem_union_left _ hxEF)⟩
    have hnewF : ∀ D ∈ CF.blocks, Anticomplete G (A \ F) D := by
      intro D hD
      simpa [CF, F, W] using extension_anticomplete_restricted_block
        C (by omega) hwU hwlow hUA hnew hD
    obtain ⟨U', R⟩ := EF.extension A hFA hlowF hnewF
    refine ⟨U', ?_⟩
    apply R.lift_shadow_complement C CF EF.reserve hWU rfl hUA
    · intro D
      simp [CF]
    · simpa [W] using (shadow_closed C (by omega) hwU hwlow).whole_blocks

lemma ExtensionConclusion.lift_shadow_then_complement
    {U W F A WA U' : Finset V} {k : ℕ} {w : V}
    (C : ProtectedFamily G U k) (CF : ProtectedFamily G F k)
    (B BF : V → Finset V)
    (_hWU : W ⊆ U) (hF : F = U \ W) (hUA : U ⊆ A)
    (hWAU : WA ⊆ U) (hwlowA : w ∈ lowVertices G A k)
    (hWAres : WA ⊆ B w)
    (hBFres : ∀ v ∈ lowVertices G (A \ WA) k, BF v ⊆ B v)
    (hshort : shortage k G (A \ WA) ≤ shortage k G A)
    (hWAanti : Anticomplete G WA (A \ U))
    (hlow : lowVertices G (A \ WA) k ⊆ lowVertices G A k)
    (hwholeW : C.WholeBlocks W) (hwholeWA : C.WholeBlocks WA)
    (hCF : ∀ D, D ∈ CF.blocks ↔ D ∈ C.blocks ∧ D ⊆ F)
    (hblockAntiWA : ∀ D ∈ C.blocks, Disjoint D WA → Anticomplete G D WA)
    (R : ExtensionConclusion CF BF (A \ WA) U') :
    ExtensionConclusion C B A U' := by
  have hFU : F ⊆ U := by rw [hF]; exact sdiff_subset
  have hnewSub : A \ U ⊆ (A \ WA) \ F := by
    intro x hx
    exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨(mem_sdiff.mp hx).1,
      fun hxWA ↦ (mem_sdiff.mp hx).2 (hWAU hxWA)⟩,
      fun hxF ↦ (mem_sdiff.mp hx).2 (hFU hxF)⟩
  have hdelSub : A \ U' ⊆ WA ∪ ((A \ WA) \ U') := by
    intro x hx
    by_cases hxWA : x ∈ WA
    · exact mem_union_left _ hxWA
    · exact mem_union_right _ (mem_sdiff.mpr
        ⟨mem_sdiff.mpr ⟨(mem_sdiff.mp hx).1, hxWA⟩, (mem_sdiff.mp hx).2⟩)
  have hblockW : ∀ {D}, D ∈ C.blocks → D ∉ CF.blocks → D ⊆ W := by
    intro D hDC hnot
    rcases hwholeW D hDC with hDW | hdisj
    · exact hDW
    · exfalso
      apply hnot
      apply (hCF D).2
      refine ⟨hDC, ?_⟩
      intro x hxD
      have hxUW : x ∈ U \ W := mem_sdiff.mpr
        ⟨C.subset_ambient D hDC hxD,
         fun hxW ↦ Finset.disjoint_left.mp hdisj hxD hxW⟩
      simpa [hF] using hxUW
  refine
    { minDegree := R.minDegree
      subset_extension := R.subset_extension.trans sdiff_subset
      shortage_le := R.shortage_le.trans hshort
      deleted_subset_reserves := ?_
      deleted_subset_old := ?_
      deleted_anticomplete_new := ?_
      blocks_whole := ?_
      retained_blocks_anticomplete := ?_ }
  · intro x hx
    rcases mem_union.mp (hdelSub hx) with hxWA | hxR
    · rw [reserveUnion, mem_biUnion]
      exact ⟨w, hwlowA, hWAres hxWA⟩
    · have hr := R.deleted_subset_reserves hxR
      rw [reserveUnion, mem_biUnion] at hr ⊢
      rcases hr with ⟨v, hv, hxBF⟩
      exact ⟨v, hlow hv, hBFres v hv hxBF⟩
  · intro x hx
    rcases mem_union.mp (hdelSub hx) with hxWA | hxR
    · exact hWAU hxWA
    · exact hFU (R.deleted_subset_old hxR)
  · intro hadj
    rcases hadj with ⟨x, hx, y, hy, hxy⟩
    rcases mem_union.mp (hdelSub hx) with hxWA | hxR
    · exact hWAanti ⟨x, hxWA, y, hy, hxy⟩
    · exact R.deleted_anticomplete_new ⟨x, hxR, y, hnewSub hy, hxy⟩
  · intro D hDC
    rcases hwholeWA D hDC with hDWA | hdisjWA
    · right
      rw [Finset.disjoint_left]
      intro x hxD hxU'
      exact (mem_sdiff.mp (R.subset_extension (hxU'))).2 (hDWA hxD)
    · by_cases hDCF : D ∈ CF.blocks
      · exact R.blocks_whole D hDCF
      · left
        have hDW := hblockW hDC hDCF
        intro x hxD
        have hxAF : x ∈ A \ WA := mem_sdiff.mpr
          ⟨hUA (C.subset_ambient D hDC hxD),
           fun hxWA ↦ Finset.disjoint_left.mp hdisjWA hxD hxWA⟩
        by_contra hxU'
        have hxF := R.deleted_subset_old (mem_sdiff.mpr ⟨hxAF, hxU'⟩)
        have hxUW : x ∈ U \ W := by simpa [hF] using hxF
        exact (mem_sdiff.mp hxUW).2 (hDW hxD)
  · intro D hDC hDU'
    have hdisjWA : Disjoint D WA := by
      rw [Finset.disjoint_left]
      intro x hxD hxWA
      exact (mem_sdiff.mp (R.subset_extension (hDU' hxD))).2 hxWA
    have hantiWA := hblockAntiWA D hDC hdisjWA
    have hantiR : Anticomplete G D ((A \ WA) \ U') := by
      by_cases hDCF : D ∈ CF.blocks
      · exact R.retained_blocks_anticomplete D hDCF hDU'
      · have hDW := hblockW hDC hDCF
        have hDnew : D ⊆ (A \ WA) \ F := by
          intro x hxD
          refine mem_sdiff.mpr ⟨R.subset_extension (hDU' hxD), ?_⟩
          intro hxF
          have hxUW : x ∈ U \ W := by simpa [hF] using hxF
          exact (mem_sdiff.mp hxUW).2 (hDW hxD)
        exact R.deleted_anticomplete_new.symm.mono hDnew Subset.rfl
    intro hadj
    rcases hadj with ⟨x, hxD, y, hy, hxy⟩
    rcases mem_union.mp (hdelSub hy) with hyWA | hyR
    · exact hantiWA ⟨x, hxD, y, hyWA, hxy⟩
    · exact hantiR ⟨x, hxD, y, hyR, hxy⟩

lemma ExtensionConclusion.map_reserve
    {U A U' : Finset V} {k : ℕ}
    {C : ProtectedFamily G U k} {B B' : V → Finset V}
    (R : ExtensionConclusion C B A U')
    (hBB : ∀ v ∈ lowVertices G A k, B v ⊆ B' v) :
    ExtensionConclusion C B' A U' := by
  refine
    { minDegree := R.minDegree
      subset_extension := R.subset_extension
      shortage_le := R.shortage_le
      deleted_subset_reserves := ?_
      deleted_subset_old := R.deleted_subset_old
      deleted_anticomplete_new := R.deleted_anticomplete_new
      blocks_whole := R.blocks_whole
      retained_blocks_anticomplete := R.retained_blocks_anticomplete }
  intro x hx
  have hr := R.deleted_subset_reserves hx
  rw [reserveUnion, mem_biUnion] at hr ⊢
  rcases hr with ⟨v, hv, hxB⟩
  exact ⟨v, hv, hBB v hv hxB⟩

private lemma extensionCertificate_zero_proper_shadow
    {U : Finset V} {k : ℕ} {w : V}
    (C : ProtectedFamily G U k) (hk : 2 ≤ k)
    (hwU : w ∈ U) (hwlow : degreeOn G U w ≤ k - 1)
    (_hproperW : shadow C w ≠ U)
    (hzero : deletionPotential k G U (shadow C w) = 0)
    (EF : ExtensionCertificate G (U \ shadow C w) k
      (C.restrictShadowComplement (by omega) hwU hwlow)) :
    Nonempty (ExtensionCertificate G U k C) := by
  let W := shadow C w
  let F := U \ W
  let CF := C.restrictShadowComplement (by omega) hwU hwlow
  let B : V → Finset V := fun v ↦ if v = w then W else EF.reserve v
  have hWU : W ⊆ U := by simpa [W] using shadow_subset_ambient C hwU
  have hFU : F ⊆ U := by simp [F]
  have huniq := shadow_zero_unique_low C (by omega) hwU hwlow hzero
  have hlowFU : lowVertices G F k ⊆ lowVertices G U k := by
    intro x hx
    rw [mem_lowVertices] at hx ⊢
    have hold := low_degree_after_delete_shadow C (by omega) hwU hwlow
      (by simpa [F, W] using hx.1) (by simpa [F, W] using hx.2)
    exact ⟨hFU hx.1, hold.1⟩
  have index_of_ne : ∀ x, x ∈ lowVertices G U k → x ∉ EF.S → x ≠ w →
      x ∈ lowVertices G F k \ EF.S := by
    intro x hxlow hxS hxw
    have hxW : x ∉ W := by
      intro hxW
      exact hxw (huniq.1 x (by simpa [W] using hxW) (mem_lowVertices.mp hxlow).2)
    exact mem_sdiff.mpr
      ⟨lowVertices_mono_degree hFU
        (mem_sdiff.mpr ⟨(mem_lowVertices.mp hxlow).1, hxW⟩) hxlow, hxS⟩
  refine ⟨{
    S := EF.S
    S_subset_low := fun x hx ↦ hlowFU (EF.S_subset_low hx)
    veryLow_subset_S := ?_
    reserve := B
    reserve_subset := ?_
    reserve_pairwise := ?_
    deficit_le := ?_
    extension := ?_ }⟩
  · intro x hx
    rw [mem_veryLowVertices] at hx
    have hxne : x ≠ w := by
      intro hxw
      subst x
      rw [huniq.2] at hx
      omega
    apply EF.veryLow_subset_S
    have hxW : x ∉ W := by
      intro hxW
      exact hxne (huniq.1 x (by simpa [W] using hxW) (by omega))
    exact veryLowVertices_mono_degree hFU (mem_sdiff.mpr ⟨hx.1, hxW⟩)
      (mem_veryLowVertices.mpr hx)
  · intro v hv
    rw [mem_sdiff] at hv
    by_cases hvw : v = w
    · subst v
      simp [B, hWU]
    · have hidx := index_of_ne v hv.1 hv.2 hvw
      have hsub := (EF.reserve_subset v hidx).trans hFU
      simpa [B, hvw] using hsub
  · intro v hv z hz hvz
    rw [mem_sdiff] at hv hz
    by_cases hvw : v = w
    · by_cases hzw : z = w
      · exact (hvz (hvw.trans hzw.symm)).elim
      · have hzidx := index_of_ne z hz.1 hz.2 hzw
        simp only [B, hvw, hzw, if_pos]
        rw [Finset.disjoint_left]
        intro x hxW hxB
        have hxF := EF.reserve_subset z hzidx hxB
        exact (mem_sdiff.mp (by simpa [F, W] using hxF)).2 hxW
    · by_cases hzw : z = w
      · have hvidx := index_of_ne v hv.1 hv.2 hvw
        simp only [B, hvw, hzw, if_pos]
        rw [Finset.disjoint_left]
        intro x hxB hxW
        have hxF := EF.reserve_subset v hvidx hxB
        exact (mem_sdiff.mp (by simpa [F, W] using hxF)).2 hxW
      · simpa [B, hvw, hzw] using
          EF.reserve_pairwise v (index_of_ne v hv.1 hv.2 hvw)
            z (index_of_ne z hz.1 hz.2 hzw) hvz
  · have hmono := deficitSum_mono_of_subset (G := G) hFU EF.S_subset_low
    have hmonoZ : ((EF.S.sum (fun x ↦ k - degreeOn G U x) : ℕ) : ℤ) ≤
        ((EF.S.sum (fun x ↦ k - degreeOn G F x) : ℕ) : ℤ) := by
      exact_mod_cast hmono
    have hshort : shortage k G F = shortage k G U := by
      simpa [F, W] using shortage_delete_shadow_eq C hwU hzero
    have hEF := EF.deficit_le
    change ((EF.S.sum (fun x ↦ k - degreeOn G F x) : ℕ) : ℤ) ≤
      2 * shortage k G F at hEF
    omega
  · intro A hproper hlow hnew
    have hUA := (Finset.ssubset_iff_subset_ne.mp hproper).1
    by_cases hwA : w ∈ lowVertices G A k
    · let CA : ProtectedFamily G A k := C.extendAmbient hUA hnew
      let WA : Finset V := shadow CA w
      let AF : Finset V := A \ WA
      have hwlowA := (mem_lowVertices.mp hwA).2
      have hstable := shadow_stable_in_extension C (by omega) hUA hwU hwlowA hnew hzero
      have hWA_W : WA ⊆ W := by simpa [CA, WA, W] using hstable.1
      have hWAU : WA ⊆ U := hWA_W.trans hWU
      have hWAanti : Anticomplete G WA (A \ U) := by
        change ¬ AdjacentSets G WA (A \ U)
        simpa [CA, WA] using hstable.2
      have hFAF : F ⊂ AF := by
        apply Finset.ssubset_iff_subset_ne.mpr
        constructor
        · intro x hxF
          rw [mem_sdiff] at hxF
          exact mem_sdiff.mpr ⟨hUA hxF.1, fun hxWA ↦ hxF.2 (hWA_W hxWA)⟩
        · intro hEq
          have hAU : A ⊆ U := by
            intro x hxA
            by_cases hxWA : x ∈ WA
            · exact hWAU hxWA
            · have hxAF : x ∈ AF := mem_sdiff.mpr ⟨hxA, hxWA⟩
              exact hFU (by simpa [hEq] using hxAF)
          exact (Finset.ssubset_iff_subset_ne.mp hproper).2 (Subset.antisymm hUA hAU)
      have hlowAF : lowVertices G AF k ⊆ lowVertices G F k \ EF.S := by
        intro x hxAF
        have hr := low_degree_after_delete_shadow CA (by omega) (hUA hwU) hwlowA
          (by simpa [AF, WA] using (mem_lowVertices.mp hxAF).1)
          (by simpa [AF, WA] using (mem_lowVertices.mp hxAF).2)
        have hxlowA : x ∈ lowVertices G A k := mem_lowVertices.mpr
          ⟨(mem_sdiff.mp (mem_lowVertices.mp hxAF).1).1, hr.1⟩
        have hxUS := hlow hxlowA
        rw [mem_sdiff] at hxUS
        have hxnotW : x ∉ W := by
          intro hxW
          exact hr.2 (huniq.1 x (by simpa [W] using hxW)
            (mem_lowVertices.mp hxUS.1).2)
        exact mem_sdiff.mpr
          ⟨lowVertices_mono_degree hFU
            (mem_sdiff.mpr ⟨(mem_lowVertices.mp hxUS.1).1, hxnotW⟩) hxUS.1,
            hxUS.2⟩
      have hnewAF : ∀ D ∈ CF.blocks, Anticomplete G (AF \ F) D := by
        intro D hD
        have hantiA : Anticomplete G (A \ F) D := by
          simpa [CF, F, W] using extension_anticomplete_restricted_block
            C (by omega) hwU hwlow hUA hnew hD
        apply hantiA.mono ?_ Subset.rfl
        intro x hx
        exact mem_sdiff.mpr
          ⟨(mem_sdiff.mp ((mem_sdiff.mp hx).1)).1, (mem_sdiff.mp hx).2⟩
      obtain ⟨U', R⟩ := EF.extension AF hFAF hlowAF hnewAF
      refine ⟨U', ?_⟩
      have hshort : shortage k G AF ≤ shortage k G A := by
        have heq := shortage_delete_extension_shadow_eq C (by omega) hUA hwU
          hwlowA hnew hzero
        simpa [CA, WA, AF] using heq.le
      have hlowAFA : lowVertices G AF k ⊆ lowVertices G A k := by
        intro x hxAF
        have hr := low_degree_after_delete_shadow CA (by omega) (hUA hwU) hwlowA
          (by simpa [AF, WA] using (mem_lowVertices.mp hxAF).1)
          (by simpa [AF, WA] using (mem_lowVertices.mp hxAF).2)
        exact mem_lowVertices.mpr
          ⟨(mem_sdiff.mp (mem_lowVertices.mp hxAF).1).1, hr.1⟩
      have hwholeWA : C.WholeBlocks WA := by
        intro D hDC
        have hDCA : D ∈ CA.blocks := by change D ∈ C.blocks; exact hDC
        simpa [WA] using (shadow_closed CA (by omega) (hUA hwU) hwlowA).whole_blocks D hDCA
      apply R.lift_shadow_then_complement C CF B EF.reserve hWU rfl hUA hWAU hwA
      · intro x hxWA
        change x ∈ (if w = w then W else EF.reserve w)
        simp only [ite_true]
        exact hWA_W hxWA
      · intro v hvlow x hxB
        have hr := low_degree_after_delete_shadow CA (by omega) (hUA hwU) hwlowA
          (by simpa [AF, WA] using (mem_lowVertices.mp hvlow).1)
          (by simpa [AF, WA] using (mem_lowVertices.mp hvlow).2)
        simpa [B, hr.2] using hxB
      · exact hshort
      · exact hWAanti
      · exact hlowAFA
      · simpa [W] using (shadow_closed C (by omega) hwU hwlow).whole_blocks
      · exact hwholeWA
      · intro D
        simp [CF]
      · intro D hDC hdisj
        have hDCA : D ∈ CA.blocks := by change D ∈ C.blocks; exact hDC
        have hanti := shadow_anticomplete_block_of_disjoint CA (by omega)
          (hUA hwU) hwlowA hDCA (by simpa [WA] using hdisj)
        change ¬ AdjacentSets G D WA
        simpa [WA] using hanti
    · have hFA : F ⊂ A := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨hFU.trans hUA, ?_⟩
        intro hEq
        have hAU : A ⊆ U := fun x hx ↦ hFU (by simpa [hEq] using hx)
        exact (Finset.ssubset_iff_subset_ne.mp hproper).2 (Subset.antisymm hUA hAU)
      have hlowF : lowVertices G A k ⊆ lowVertices G F k \ EF.S := by
        intro x hxA
        have hxUS := hlow hxA
        rw [mem_sdiff] at hxUS
        have hxne : x ≠ w := fun hxw ↦ hwA (hxw ▸ hxA)
        exact index_of_ne x hxUS.1 hxUS.2 hxne
      have hnewF : ∀ D ∈ CF.blocks, Anticomplete G (A \ F) D := by
        intro D hD
        simpa [CF, F, W] using extension_anticomplete_restricted_block
          C (by omega) hwU hwlow hUA hnew hD
      obtain ⟨U', R⟩ := EF.extension A hFA hlowF hnewF
      have RB : ExtensionConclusion CF B A U' := R.map_reserve fun v hv ↦ by
        have hvne : v ≠ w := fun hvw ↦ hwA (hvw ▸ hv)
        simp [B, hvne]
      refine ⟨U', ?_⟩
      apply RB.lift_shadow_complement C CF B hWU rfl hUA
      · intro D
        simp [CF]
      · simpa [W] using (shadow_closed C (by omega) hwU hwlow).whole_blocks

theorem exists_extensionCertificate {U : Finset V} {k : ℕ}
    (C : ProtectedFamily G U k) (hk : 2 ≤ k)
    (hno : ∀ X : Finset V, X ⊆ U → ¬ HasMinDegreeOn G X k) :
    Nonempty (ExtensionCertificate G U k C) := by
  classical
  refine Finset.strongInduction (p := fun U : Finset V ↦
    ∀ C : ProtectedFamily G U k,
      (∀ X : Finset V, X ⊆ U → ¬ HasMinDegreeOn G X k) →
      Nonempty (ExtensionCertificate G U k C)) ?_ U C hno
  intro U ih C hno
  by_cases hU : U = ∅
  · subst U
    exact extensionCertificate_empty k C
  have hUne : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hU
  have hex : ∃ w ∈ U, degreeOn G U w < k := by
    by_contra hnot
    push Not at hnot
    exact hno U Subset.rfl ⟨hUne, hnot⟩
  obtain ⟨w, hwU, hwlt⟩ := hex
  have hwlow : degreeOn G U w ≤ k - 1 := by omega
  let W := shadow C w
  have hWU : W ⊆ U := by simpa [W] using shadow_subset_ambient C hwU
  have hqnonneg : 0 ≤ deletionPotential k G U W := by
    simpa [W] using shadow_potential_nonneg C (by omega) hwU hwlow
  by_cases hfull : W = U
  · by_cases hzero : deletionPotential k G U W = 0
    · apply extensionCertificate_zero_full_shadow C hk hwU hwlow
      · simpa [W] using hfull
      · simpa [W] using hzero
    · have hpos : 0 < deletionPotential k G U W := by omega
      apply extensionCertificate_allLow C hk
      have hdef := lowDefect_shadow_le_two_mul C (by omega) hwU hwlow
        (by simpa [W] using hpos)
      have hpot : deletionPotential k G U U = shortage k G U := by
        have hi := edgeCount_sdiff_add_incidentCount G U U
        simp only [Finset.sdiff_self, edgeCount_empty, zero_add] at hi
        unfold deletionPotential shortage
        rw [hi]
      simpa [W, hfull, hpot] using hdef
  · let F := U \ W
    have hFsub : F ⊂ U := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨by simp [F], ?_⟩
      intro hEq
      have hwF : w ∈ F := by simpa [hEq] using hwU
      exact (mem_sdiff.mp (by simpa [F] using hwF)).2
        (by simpa [W] using root_mem_shadow C w)
    let CF := C.restrictShadowComplement (by omega) hwU hwlow
    have hnoF : ∀ X : Finset V, X ⊆ F → ¬ HasMinDegreeOn G X k := by
      intro X hXF
      exact hno X (hXF.trans (by simp [F]))
    have hIH := ih F hFsub CF hnoF
    obtain ⟨EF⟩ := hIH
    by_cases hzero : deletionPotential k G U W = 0
    · apply extensionCertificate_zero_proper_shadow C hk hwU hwlow
        (by simpa [W] using hfull) (by simpa [W] using hzero)
      simpa [F, W, CF] using EF
    · have hpos : 0 < deletionPotential k G U W := by omega
      apply extensionCertificate_positive_proper_shadow C hk hwU hwlow
        (by simpa [W] using hfull) (by simpa [W] using hpos)
      simpa [F, W, CF] using EF

end P814

end

section
namespace P814

section GreedyColoring

variable {Item Scope : Type*} [Finite Item] [Fintype Scope]
  [DecidableEq Item]

theorem exists_scope_coloring
    {r a b q : ℕ}
    (scope : Scope → Finset Item)
    (avoid : Scope → Finset (Fin q))
    (hfrequency : ∀ x : Item,
      (Finset.univ.filter fun s : Scope ↦ x ∈ scope s).card ≤ r)
    (hscope : ∀ s : Scope, (scope s).card ≤ a + 1)
    (havoid : ∀ s : Scope, (avoid s).card ≤ b)
    (hpalette : r * (a + b) < q) :
    ∃ color : Item → Fin q,
      (∀ s : Scope, Set.InjOn color (scope s : Set Item)) ∧
      (∀ s : Scope, ∀ x ∈ scope s, color x ∉ avoid s) := by
  let := Fintype.ofFinite Item
  have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le _) hpalette
  let ValidOn := fun (U : Finset Item) (color : Item → Fin q) ↦
    (∀ s : Scope, ∀ x ∈ scope s, x ∈ U → color x ∉ avoid s) ∧
    (∀ s : Scope, ∀ x ∈ scope s, x ∈ U →
      ∀ y ∈ scope s, y ∈ U → color x = color y → x = y)
  have hpartl : ∀ U : Finset Item, ∃ color : Item → Fin q, ValidOn U color := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
        refine ⟨fun _ ↦ ⟨0, hq⟩, ?_⟩
        constructor
        · intro s x hx
          simp
        · intro s x hx
          simp
    | @insert v U hv ih =>
        obtain ⟨color, hvalid⟩ := ih
        let containing : Finset Scope :=
          Finset.univ.filter fun s : Scope ↦ v ∈ scope s
        let forbidden : Finset (Fin q) :=
          containing.biUnion fun s ↦ avoid s ∪ (scope s ∩ U).image color
        have hcontaining : containing.card ≤ r := by
          simpa [containing] using hfrequency v
        have hlocal : ∀ s ∈ containing,
            (avoid s ∪ (scope s ∩ U).image color).card ≤ a + b := by
          intro s hs
          have hvs : v ∈ scope s := (Finset.mem_filter.mp hs).2
          have hinter_subset : scope s ∩ U ⊆ (scope s).erase v := by
            intro x hx
            have hxs : x ∈ scope s := (Finset.mem_inter.mp hx).1
            have hxU : x ∈ U := (Finset.mem_inter.mp hx).2
            exact Finset.mem_erase.mpr ⟨fun h ↦ hv (h ▸ hxU), hxs⟩
          have hinter_card : (scope s ∩ U).card ≤ a := by
            have hcard := Finset.card_le_card hinter_subset
            rw [Nat.le_iff_lt_add_one]
            exact (hcard.trans_lt (Finset.card_erase_lt_of_mem hvs)).trans_le (hscope s)
          have himage : ((scope s ∩ U).image color).card ≤ a :=
            (Finset.card_image_le).trans hinter_card
          calc
            (avoid s ∪ (scope s ∩ U).image color).card
                ≤ (avoid s).card + ((scope s ∩ U).image color).card :=
              Finset.card_union_le _ _
            _ ≤ b + a := Nat.add_le_add (havoid s) himage
            _ = a + b := Nat.add_comm b a
        have hforbidden_card : forbidden.card ≤ r * (a + b) := by
          calc
            forbidden.card ≤ containing.card * (a + b) := by
              exact Finset.card_biUnion_le_card_mul containing
                (fun s ↦ avoid s ∪ (scope s ∩ U).image color) (a + b) hlocal
            _ ≤ r * (a + b) := Nat.mul_le_mul_right (a + b) hcontaining
        have hforbidden_lt : forbidden.card < Fintype.card (Fin q) := by
          simpa using hforbidden_card.trans_lt hpalette
        have hforbidden_ne : forbidden ≠ Finset.univ :=
          (Finset.card_lt_iff_ne_univ forbidden).mp hforbidden_lt
        obtain ⟨fresh, hfresh⟩ : ∃ fresh : Fin q, fresh ∉ forbidden := by
          by_contra h
          apply hforbidden_ne
          apply Finset.ext
          intro z
          constructor
          · intro
            exact Finset.mem_univ z
          · intro
            by_contra hz
            exact h ⟨z, hz⟩
        let newColor : Item → Fin q := fun x ↦ if x = v then fresh else color x
        refine ⟨newColor, ?_⟩
        constructor
        · intro s x hxs hxU
          by_cases hxv : x = v
          · subst x
            have hscontaining : s ∈ containing := by
              simp [containing, hxs]
            have havSubset : avoid s ⊆ forbidden := by
              intro z hz
              exact Finset.mem_biUnion.mpr ⟨s, hscontaining,
                Finset.mem_union_left _ hz⟩
            simpa [newColor] using fun hmem ↦ hfresh (havSubset hmem)
          · have hxOld : x ∈ U := (Finset.mem_insert.mp hxU).resolve_left hxv
            simpa [newColor, hxv] using hvalid.1 s x hxs hxOld
        · intro s x hxs hxU y hys hyU hxy
          by_cases hxv : x = v
          · subst x
            by_cases hyv : y = v
            · exact hyv.symm
            · have hyOld : y ∈ U := (Finset.mem_insert.mp hyU).resolve_left hyv
              have hscontaining : s ∈ containing := by
                simp [containing, hxs]
              have hyImage : color y ∈ (scope s ∩ U).image color := by
                exact Finset.mem_image.mpr ⟨y, Finset.mem_inter.mpr ⟨hys, hyOld⟩, rfl⟩
              have hyForbidden : color y ∈ forbidden := by
                exact Finset.mem_biUnion.mpr ⟨s, hscontaining,
                  Finset.mem_union_right _ hyImage⟩
              have heq : fresh = color y := by
                simpa [newColor, hyv] using hxy
              exact (hfresh (heq ▸ hyForbidden)).elim
          · have hxOld : x ∈ U := (Finset.mem_insert.mp hxU).resolve_left hxv
            by_cases hyv : y = v
            · subst y
              have hscontaining : s ∈ containing := by
                simp [containing, hys]
              have hxImage : color x ∈ (scope s ∩ U).image color := by
                exact Finset.mem_image.mpr ⟨x, Finset.mem_inter.mpr ⟨hxs, hxOld⟩, rfl⟩
              have hxForbidden : color x ∈ forbidden := by
                exact Finset.mem_biUnion.mpr ⟨s, hscontaining,
                  Finset.mem_union_right _ hxImage⟩
              have heq : color x = fresh := by
                simpa [newColor, hxv] using hxy
              exact (hfresh (heq ▸ hxForbidden)).elim
            · have hyOld : y ∈ U := (Finset.mem_insert.mp hyU).resolve_left hyv
              apply hvalid.2 s x hxs hxOld y hys hyOld
              simpa [newColor, hxv, hyv] using hxy
  obtain ⟨color, hcolor⟩ := hpartl Finset.univ
  refine ⟨color, ?_, ?_⟩
  · intro s x hxs y hys hxy
    exact hcolor.2 s x hxs (Finset.mem_univ x) y hys (Finset.mem_univ y) hxy
  · intro s x hxs
    exact hcolor.1 s x hxs (Finset.mem_univ x)

theorem exists_erdos814_scope_coloring
    {k : ℕ} (hk : 0 < k)
    (scope : Scope → Finset Item)
    (avoid : Scope → Finset (Fin (401 * k)))
    (hfrequency : ∀ x : Item,
      (Finset.univ.filter fun s : Scope ↦ x ∈ scope s).card ≤ 200)
    (hscope : ∀ s : Scope, (scope s).card ≤ k + 1)
    (havoid : ∀ s : Scope, (avoid s).card ≤ k) :
    ∃ color : Item → Fin (401 * k),
      (∀ s : Scope, Set.InjOn color (scope s : Set Item)) ∧
      (∀ s : Scope, ∀ x ∈ scope s, color x ∉ avoid s) := by
  apply exists_scope_coloring (r := 200) (a := k) (b := k)
    scope avoid hfrequency hscope havoid
  calc
    200 * (k + k) = 200 * k + 200 * k := Nat.mul_add 200 k k
    _ = (200 + 200) * k := (Nat.add_mul 200 200 k).symm
    _ = 400 * k := rfl
    _ < 401 * k := Nat.mul_lt_mul_of_pos_right (by decide) hk

end GreedyColoring

end P814

end

section
open Finset SimpleGraph BigOperators

namespace P814

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def orderedMaxGood
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) : List (Finset V) :=
  (maxGood G A k).toList.mergeSort fun D E ↦ decide (E.card ≤ D.card)

@[simp] lemma length_orderedMaxGood (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) :
    (orderedMaxGood G A k).length = (maxGood G A k).card := by
  simp [orderedMaxGood, List.length_mergeSort]

lemma mem_orderedMaxGood_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (D : Finset V) :
    D ∈ orderedMaxGood G A k ↔ D ∈ maxGood G A k := by
  simp [orderedMaxGood]

lemma orderedMaxGood_nodup (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) : (orderedMaxGood G A k).Nodup := by
  unfold orderedMaxGood
  exact (List.Perm.nodup_iff (List.mergeSort_perm (maxGood G A k).toList
    (fun D E ↦ decide (E.card ≤ D.card)))).2 (Finset.nodup_toList _)

lemma orderedMaxGood_nonincreasing (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) :
    Dyadic.Nonincreasing (orderedMaxGood G A k) := by
  intro i j hij hj
  by_cases hEq : i = j
  · subst j
    exact le_rfl
  have hlt : i < j := lt_of_le_of_ne hij hEq
  have hp : List.Pairwise (fun D E : Finset V ↦ E.card ≤ D.card)
      (orderedMaxGood G A k) := by
    exact List.pairwise_mergeSort' _ _
  have hi : i < (orderedMaxGood G A k).length := hlt.trans hj
  have hrel := hp.rel_get_of_lt
    (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) (by simpa using hlt)
  rw [Dyadic.cardAt, Dyadic.cardAt,
    List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
  exact hrel

structure ColoringSystem
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (t : ℤ)
    (C : List (Finset V)) (J0 J : ℕ) : Prop where
  hk : 2 ≤ k
  hJ0 : 0 < J0
  hJ : J0 ≤ J
  complete : Dyadic.CompleteThrough C J
  nonincreasing : Dyadic.Nonincreasing C
  nodup : C.Nodup
  block_nonempty : ∀ r < Dyadic.levelStart J, (C.getD r ∅).Nonempty
  block_subset : ∀ r < Dyadic.levelStart J, C.getD r ∅ ⊆ A
  block_incident : ∀ r < Dyadic.levelStart J,
    incidentCount G A (C.getD r ∅) ≤ (k - 1) * (C.getD r ∅).card + 1
  block_complement_minDegree : ∀ r < Dyadic.levelStart J,
    HasMinDegreeOn G (A \ C.getD r ∅) k
  blocks_disjoint : ∀ r < Dyadic.levelStart J, ∀ s < Dyadic.levelStart J,
    r ≠ s → Disjoint (C.getD r ∅) (C.getD s ∅)
  blocks_anticomplete : ∀ r < Dyadic.levelStart J, ∀ s < Dyadic.levelStart J,
    r ≠ s → Anticomplete G (C.getD r ∅) (C.getD s ∅)
  minDegree : HasMinDegreeOn G A k
  connected : ConnectedOn G A
  noSmallCore : NoSmallCoreOn G A k (uniformDen k)
  shortage_le : shortage k G A ≤ t
  power : t < (2 ^ J0 : ℕ)
  early_mass : A.card ≤ 100 * k * Dyadic.retainedMass C J0
  cutoff_level : 50 * k * Dyadic.levelMass C (J0 - 1) < A.card
  late_mass : A.card < 8 * k * Dyadic.betweenMass C J0 J

namespace ColoringSystem

variable {A : Finset V} {k : ℕ} {t : ℤ}
variable {C : List (Finset V)} {J0 J : ℕ}

lemma block_index_lt_length (S : ColoringSystem G A k t C J0 J)
    {r : ℕ} (hr : r < Dyadic.levelStart J) : r < C.length :=
  hr.trans_le S.complete

lemma block_eq_getElem (S : ColoringSystem G A k t C J0 J)
    {r : ℕ} (hr : r < Dyadic.levelStart J) :
    C.getD r ∅ = C[r]'(S.block_index_lt_length hr) := by
  exact List.getD_eq_getElem _ _ (S.block_index_lt_length hr)

lemma blocks_disjoint_set (S : ColoringSystem G A k t C J0 J) :
    (↑(Finset.range (Dyadic.levelStart J)) : Set ℕ).PairwiseDisjoint
      (fun r ↦ C.getD r ∅) := by
  intro r hr s hs hrs
  exact S.blocks_disjoint r (mem_range.mp hr) s (mem_range.mp hs) hrs

end ColoringSystem

abbrev Color (k : ℕ) := Fin (401 * k)

abbrev PartialColoring (V : Type*) (k : ℕ) := V → Option (Color k)

def colorClass (A : Finset V) (phi : PartialColoring V k) (i : Color k) : Finset V :=
  A.filter fun v ↦ phi v = some i

def BlockUncolored (phi : PartialColoring V k) (D : Finset V) : Prop :=
  ∀ v ∈ D, phi v = none

def Monochromatic (phi : PartialColoring V k) (D : Finset V) (i : Color k) : Prop :=
  ∀ v ∈ D, phi v = some i

def IsMonochromatic (phi : PartialColoring V k) (D : Finset V) : Prop :=
  ∃ i, Monochromatic phi D i

noncomputable def uncoloredBlockCount (C : List (Finset V))
    (phi : PartialColoring V k) (j : ℕ) : ℕ := by
  classical
  exact ((Dyadic.levelIndices j).filter fun r ↦
    BlockUncolored phi (C.getD r ∅)).card

noncomputable def monochromaticBlockCount (C : List (Finset V))
    (phi : PartialColoring V k) (ell : ℕ) (i : Color k) : ℕ := by
  classical
  exact ((Finset.range (Dyadic.levelStart ell)).filter fun r ↦
    Monochromatic phi (C.getD r ∅) i).card

def UncoloredNeighborhood (G : SimpleGraph V) (A : Finset V)
    (phi : PartialColoring V k) (D : Finset V) : Prop :=
  ∀ v ∈ D, ∀ w ∈ A, G.Adj v w → phi w = none

structure Appropriate
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (C : List (Finset V))
    (J0 ell J : ℕ) (phi : PartialColoring V k) : Prop where

  support : ∀ v, v ∉ A → phi v = none

  blocks : ∀ r < Dyadic.levelStart J,
    IsMonochromatic phi (C.getD r ∅) ∨ BlockUncolored phi (C.getD r ∅)

  incidence : ∀ i,
    incidentCount G A (colorClass A phi i) ≤
      (k - 1) * (colorClass A phi i).card + monochromaticBlockCount C phi ell i

  minDegree : ∀ i, HasMinDegreeOn G (A \ colorClass A phi i) k

  early : ∀ r < Dyadic.levelStart J0, BlockUncolored phi (C.getD r ∅)

  processed : ∀ j, J0 ≤ j → j < ell → 4 * uncoloredBlockCount C phi j ≤ 2 ^ j

  future : ∀ r, Dyadic.levelStart ell ≤ r → r < Dyadic.levelStart J →
    BlockUncolored phi (C.getD r ∅) →
      UncoloredNeighborhood G A phi (C.getD r ∅)

omit [DecidableEq V] [Fintype V] in
@[simp] lemma colorClass_uncolored (A : Finset V) (i : Color k) :
    colorClass A (fun _ ↦ none) i = ∅ := by
  ext v
  simp [colorClass]

omit [DecidableEq V] [Fintype V] in
@[simp] lemma blockUncolored_uncolored (D : Finset V) :
    BlockUncolored (k := k) (fun _ ↦ none) D := by
  simp [BlockUncolored]

lemma appropriate_uncolored
    {A : Finset V} {k J0 J : ℕ} {C : List (Finset V)}
    (hmin : HasMinDegreeOn G A k) :
    Appropriate G A k C J0 J0 J (fun _ ↦ none) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · intro r hr
    exact Or.inr (blockUncolored_uncolored _)
  · intro i
    rw [colorClass_uncolored]
    simp [incidentCount, incidentEdges, edgeOn]
  · intro i
    simpa using hmin
  · intro r hr
    exact blockUncolored_uncolored _
  · intro j hj hlt
    omega
  · intro r hr hR hu
    simp [UncoloredNeighborhood]

omit [DecidableEq V] [Fintype V] in
lemma monochromaticBlockCount_mono_ell
    (C : List (Finset V)) (phi : PartialColoring V k) (ell : ℕ) (i : Color k) :
    monochromaticBlockCount C phi ell i ≤
      monochromaticBlockCount C phi (ell + 1) i := by
  classical
  unfold monochromaticBlockCount
  apply card_le_card
  intro r hr
  rw [mem_filter] at hr ⊢
  exact ⟨mem_range.mpr ((mem_range.mp hr.1).trans_le (Dyadic.levelStart_le_succ ell)), hr.2⟩

lemma Appropriate.advance_without_change
    {A : Finset V} {k J0 ell J : ℕ} {C : List (Finset V)}
    {phi : PartialColoring V k}
    (hphi : Appropriate G A k C J0 ell J phi)
    (hquarter : 4 * uncoloredBlockCount C phi ell ≤ 2 ^ ell) :
    Appropriate G A k C J0 (ell + 1) J phi := by
  refine ⟨hphi.support, hphi.blocks, ?_, hphi.minDegree, hphi.early, ?_, ?_⟩
  · intro i
    exact hphi.incidence i |>.trans <|
      Nat.add_le_add_left (monochromaticBlockCount_mono_ell C phi ell i) _
  · intro j hj hje
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hje) with hjell | rfl
    · exact hphi.processed j hj hjell
    · exact hquarter
  · intro r hr hJ hu
    exact hphi.future r (Dyadic.levelStart_le_succ ell |>.trans hr) hJ hu

lemma incidentCount_union_eq_add_restricted
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A X Y : Finset V) :
    incidentCount G A (X ∪ Y) =
      incidentCount G A X + incidentCount G (A \ X) Y := by
  have hAll := edgeCount_sdiff_add_incidentCount G A (X ∪ Y)
  have hX := edgeCount_sdiff_add_incidentCount G A X
  have hY := edgeCount_sdiff_add_incidentCount G (A \ X) Y
  have hs : A \ (X ∪ Y) = (A \ X) \ Y := by
    ext v
    simp only [mem_sdiff, mem_union]
    tauto
  rw [hs] at hAll
  omega

def Extends (phi rho : PartialColoring V k) : Prop :=
  ∀ v i, phi v = some i → rho v = some i

omit [DecidableEq V] [Fintype V] in
lemma Extends.blockUncolored {phi rho : PartialColoring V k}
    (h : Extends phi rho) {D : Finset V}
    (hD : BlockUncolored rho D) : BlockUncolored phi D := by
  intro v hv
  cases hphi : phi v with
  | none => rfl
  | some i =>
      have hrho := h v i hphi
      rw [hD v hv] at hrho
      contradiction

omit [DecidableEq V] [Fintype V] in
lemma Extends.uncoloredBlockCount_le {phi rho : PartialColoring V k}
    (h : Extends phi rho) (C : List (Finset V)) (j : ℕ) :
    uncoloredBlockCount C rho j ≤ uncoloredBlockCount C phi j := by
  classical
  unfold uncoloredBlockCount
  apply card_le_card
  intro r hr
  simp only [mem_filter] at hr ⊢
  exact ⟨hr.1, h.blockUncolored hr.2⟩

def coloredVertices (A : Finset V) (phi : PartialColoring V k) : Finset V :=
  A.filter fun v ↦ (phi v).isSome

omit [DecidableEq V] [Fintype V] in
lemma mem_coloredVertices_iff {A : Finset V} {phi : PartialColoring V k} {v : V} :
    v ∈ coloredVertices A phi ↔ v ∈ A ∧ ∃ i, phi v = some i := by
  simp [coloredVertices, Option.isSome_iff_exists]

omit [DecidableEq V] [Fintype V] in
lemma colorClass_subset_coloredVertices
    (A : Finset V) (phi : PartialColoring V k) (i : Color k) :
    colorClass A phi i ⊆ coloredVertices A phi := by
  intro v hv
  have hv' : v ∈ A ∧ phi v = some i := by simpa [colorClass] using hv
  exact mem_coloredVertices_iff.mpr ⟨hv'.1, i, hv'.2⟩

omit [Fintype V] in
lemma coloredVertices_eq_biUnion_colorClass
    (A : Finset V) (phi : PartialColoring V k) :
    coloredVertices A phi = Finset.univ.biUnion (colorClass A phi) := by
  ext v
  rw [mem_coloredVertices_iff]
  simp [colorClass]

omit [DecidableEq V] [Fintype V] in
lemma pairwise_disjoint_colorClass
    (A : Finset V) (phi : PartialColoring V k) :
    (↑(Finset.univ : Finset (Color k)) : Set (Color k)).PairwiseDisjoint
      (colorClass A phi) := by
  intro i hi j hj hij
  change Disjoint (colorClass A phi i) (colorClass A phi j)
  rw [Finset.disjoint_left]
  intro v hvi hvj
  simp only [colorClass, mem_filter] at hvi hvj
  exact hij (Option.some.inj (hvi.2.symm.trans hvj.2))

noncomputable def uncoloredPrefixIndices (C : List (Finset V))
    (phi : PartialColoring V k) (ell : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (Dyadic.levelStart ell)).filter fun r ↦
    BlockUncolored phi (C.getD r ∅)

noncomputable def uncoloredPrefixUnion (C : List (Finset V))
    (phi : PartialColoring V k) (ell : ℕ) : Finset V := by
  classical
  exact (uncoloredPrefixIndices C phi ell).biUnion fun r ↦ C.getD r ∅

noncomputable def deficitResidual (A : Finset V) (C : List (Finset V))
    (phi : PartialColoring V k) (ell : ℕ) : Finset V :=
  A \ (coloredVertices A phi ∪ uncoloredPrefixUnion C phi ell)

noncomputable def uncoloredCurrentIndices (C : List (Finset V))
    (phi : PartialColoring V k) (ell : ℕ) : Finset ℕ := by
  classical
  exact (Dyadic.levelIndices ell).filter fun r ↦
    BlockUncolored phi (C.getD r ∅)

lemma incidentCount_biUnion_le_sum
    {ι : Type*}
    (A : Finset V) (s : Finset ι) (D : ι → Finset V) :
    incidentCount G A (s.biUnion D) ≤
      ∑ i ∈ s, incidentCount G A (D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [biUnion_insert]
      calc
        incidentCount G A (D a ∪ s.biUnion D) ≤
            incidentCount G A (D a) + incidentCount G A (s.biUnion D) :=
          incidentCount_union_le G A (D a) (s.biUnion D)
        _ ≤ incidentCount G A (D a) + ∑ i ∈ s, incidentCount G A (D i) :=
          Nat.add_le_add_left ih _
        _ = ∑ i ∈ insert a s, incidentCount G A (D i) := by simp [ha]

lemma shortage_sdiff_biUnion_le_add_sum
    {ι : Type*}
    {A : Finset V} {k : ℕ}
    (s : Finset ι) (D : ι → Finset V) (b : ι → ℕ)
    (hsubset : ∀ i ∈ s, D i ⊆ A)
    (hdisj : (s : Set ι).PairwiseDisjoint D)
    (hincident : ∀ i ∈ s,
      incidentCount G A (D i) ≤ (k - 1) * (D i).card + b i) :
    shortage k G (A \ s.biUnion D) ≤
      shortage k G A + ((∑ i ∈ s, b i : ℕ) : ℤ) := by
  let X : Finset V := s.biUnion D
  have hXA : X ⊆ A := by
    intro x hx
    rw [mem_biUnion] at hx
    obtain ⟨i, his, hxi⟩ := hx
    exact hsubset i his hxi
  have hincNat :
      incidentCount G A X ≤
        (k - 1) * X.card + ∑ i ∈ s, b i := by
    calc
      incidentCount G A X ≤ ∑ i ∈ s, incidentCount G A (D i) := by
        simpa [X] using incidentCount_biUnion_le_sum (G := G) A s D
      _ ≤ ∑ i ∈ s, ((k - 1) * (D i).card + b i) :=
        sum_le_sum fun i hi ↦ hincident i hi
      _ = (k - 1) * (∑ i ∈ s, (D i).card) + ∑ i ∈ s, b i := by
        rw [sum_add_distrib, mul_sum]
      _ = (k - 1) * X.card + ∑ i ∈ s, b i := by
        rw [card_biUnion hdisj]
  have hincZ :
      (incidentCount G A X : ℤ) ≤
        ((k - 1 : ℕ) : ℤ) * (X.card : ℤ) +
          ((∑ i ∈ s, b i : ℕ) : ℤ) := by
    exact_mod_cast hincNat
  rw [shortage_sdiff k G hXA]
  unfold deletionPotential
  omega

lemma monochromaticBlockCount_add_uncoloredPrefix
    {A : Finset V} {k J0 ell J : ℕ} {C : List (Finset V)}
    {phi : PartialColoring V k}
    (hphi : Appropriate G A k C J0 ell J phi)
    (hellJ : ell ≤ J)
    (hnonempty : ∀ r < Dyadic.levelStart ell, (C.getD r ∅).Nonempty) :
    (∑ i : Color k, monochromaticBlockCount C phi ell i) +
        (uncoloredPrefixIndices C phi ell).card =
      Dyadic.levelStart ell := by
  classical
  have hblocks : ∀ r < Dyadic.levelStart ell,
      IsMonochromatic phi (C.getD r ∅) ∨
        BlockUncolored phi (C.getD r ∅) := by
    intro r hr
    exact hphi.blocks r (hr.trans_le (Dyadic.levelStart_mono hellJ))
  have hone : ∀ r < Dyadic.levelStart ell,
      (∑ i : Color k, if Monochromatic phi (C.getD r ∅) i then 1 else 0) +
          (if BlockUncolored phi (C.getD r ∅) then 1 else 0) = 1 := by
    intro r hr
    rcases hblocks r hr with hm | hu
    · obtain ⟨i, hi⟩ := hm
      have hnotu : ¬ BlockUncolored phi (C.getD r ∅) := by
        intro hU
        obtain ⟨v, hv⟩ := hnonempty r hr
        have := (hi v hv).symm.trans (hU v hv)
        simp at this
      have hiff : ∀ j : Color k,
          Monochromatic phi (C.getD r ∅) j ↔ j = i := by
        intro j
        constructor
        · intro hj
          obtain ⟨v, hv⟩ := hnonempty r hr
          exact Option.some.inj ((hj v hv).symm.trans (hi v hv))
        · intro hji
          subst j
          exact hi
      have hsum :
          (∑ j : Color k,
            if Monochromatic phi (C.getD r ∅) j then 1 else 0) = 1 := by
        simp_rw [hiff]
        simp
      rw [hsum, if_neg hnotu]
    · have hnotm : ∀ i : Color k,
          ¬ Monochromatic phi (C.getD r ∅) i := by
        intro i hi
        obtain ⟨v, hv⟩ := hnonempty r hr
        have := (hi v hv).symm.trans (hu v hv)
        simp at this
      have hsum :
          (∑ i : Color k,
            if Monochromatic phi (C.getD r ∅) i then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [if_neg (hnotm i)]
      rw [hsum, if_pos hu]
  calc
    (∑ i : Color k, monochromaticBlockCount C phi ell i) +
        (uncoloredPrefixIndices C phi ell).card =
      (∑ i : Color k, ∑ r ∈ Finset.range (Dyadic.levelStart ell),
          if Monochromatic phi (C.getD r ∅) i then 1 else 0) +
        ∑ r ∈ Finset.range (Dyadic.levelStart ell),
          if BlockUncolored phi (C.getD r ∅) then 1 else 0 := by
            congr 1
            · apply Finset.sum_congr rfl
              intro i hi
              simp [monochromaticBlockCount]
            · simp [uncoloredPrefixIndices]
    _ = ∑ r ∈ Finset.range (Dyadic.levelStart ell),
        ((∑ x : Color k, if Monochromatic phi (C.getD r ∅) x then 1 else 0) +
          if BlockUncolored phi (C.getD r ∅) then 1 else 0) := by
            rw [Finset.sum_comm]
            rw [← Finset.sum_add_distrib]
    _ = ∑ _r ∈ Finset.range (Dyadic.levelStart ell), 1 := by
          apply Finset.sum_congr rfl
          intro r hr
          exact hone r (Finset.mem_range.mp hr)
    _ = Dyadic.levelStart ell := by simp

omit [DecidableEq V] [Fintype V] in
lemma uncoloredPrefixIndices_card_succ
    (C : List (Finset V)) (phi : PartialColoring V k) (ell : ℕ) :
    (uncoloredPrefixIndices C phi (ell + 1)).card =
      (uncoloredPrefixIndices C phi ell).card +
        uncoloredBlockCount C phi ell := by
  classical
  let f : ℕ → ℕ := fun r ↦
    if BlockUncolored phi (C.getD r ∅) then 1 else 0
  have hsplit := Finset.sum_range_add_sum_Ico f
    (Dyadic.levelStart_le_succ ell)
  change
    ((Finset.range (Dyadic.levelStart (ell + 1))).filter fun r ↦
      BlockUncolored phi (C.getD r ∅)).card =
      ((Finset.range (Dyadic.levelStart ell)).filter fun r ↦
        BlockUncolored phi (C.getD r ∅)).card +
        ((Finset.Ico (Dyadic.levelStart ell)
          (Dyadic.levelStart (ell + 1))).filter fun r ↦
            BlockUncolored phi (C.getD r ∅)).card
  simpa [f] using hsplit.symm

lemma shortage_deficitResidual_le
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (_hJ0ell : J0 ≤ ell) (hellJ : ell < J) :
    shortage k G (deficitResidual A C phi (ell + 1)) ≤
      t + (Dyadic.levelStart ell : ℕ) + uncoloredBlockCount C phi ell := by
  classical
  let U : Finset V := coloredVertices A phi
  let R : Finset ℕ := uncoloredPrefixIndices C phi (ell + 1)
  let B : Finset V := A \ U
  let blocks : ℕ → Finset V := fun r ↦ C.getD r ∅
  have hellSuccJ : ell + 1 ≤ J := Nat.succ_le_iff.mpr hellJ
  have hcolorRaw := shortage_sdiff_biUnion_le_add_sum (G := G)
    (A := A) (k := k) (s := (Finset.univ : Finset (Color k)))
    (D := colorClass A phi) (b := monochromaticBlockCount C phi ell)
    (fun _ _ ↦ filter_subset _ _)
    (pairwise_disjoint_colorClass A phi)
    (fun i _ ↦ hphi.incidence i)
  have hcolor :
      shortage k G B ≤ shortage k G A +
        ((∑ i : Color k, monochromaticBlockCount C phi ell i : ℕ) : ℤ) := by
    simpa [B, U, coloredVertices_eq_biUnion_colorClass] using hcolorRaw
  have hRsubset : ∀ r ∈ R, blocks r ⊆ B := by
    intro r hr v hv
    have hr' : r ∈ uncoloredPrefixIndices C phi (ell + 1) := by
      simpa [R] using hr
    have hrData : r ∈ Finset.range (Dyadic.levelStart (ell + 1)) ∧
        BlockUncolored phi (C.getD r ∅) := by
      simpa [uncoloredPrefixIndices] using hr'
    have hrlt : r < Dyadic.levelStart J :=
      (Finset.mem_range.mp hrData.1).trans_le
        (Dyadic.levelStart_mono hellSuccJ)
    refine mem_sdiff.mpr ⟨S.block_subset r hrlt hv, ?_⟩
    intro hvU
    rw [mem_coloredVertices_iff] at hvU
    obtain ⟨hvA, i, hi⟩ := hvU
    have hnone := hrData.2 v hv
    rw [hnone] at hi
    contradiction
  have hRdisj : (R : Set ℕ).PairwiseDisjoint blocks := by
    intro r hr s hs hrs
    have hr' : r ∈ uncoloredPrefixIndices C phi (ell + 1) := by simpa [R] using hr
    have hs' : s ∈ uncoloredPrefixIndices C phi (ell + 1) := by simpa [R] using hs
    have hrAll : r ∈ Finset.range (Dyadic.levelStart (ell + 1)) ∧
        BlockUncolored phi (C.getD r ∅) := by
      simpa [uncoloredPrefixIndices] using hr'
    have hsAll : s ∈ Finset.range (Dyadic.levelStart (ell + 1)) ∧
        BlockUncolored phi (C.getD s ∅) := by
      simpa [uncoloredPrefixIndices] using hs'
    have hrData := hrAll.1
    have hsData := hsAll.1
    exact S.blocks_disjoint r ((mem_range.mp hrData).trans_le
      (Dyadic.levelStart_mono hellSuccJ)) s ((mem_range.mp hsData).trans_le
      (Dyadic.levelStart_mono hellSuccJ)) hrs
  have hRincident : ∀ r ∈ R,
      incidentCount G B (blocks r) ≤ (k - 1) * (blocks r).card + 1 := by
    intro r hr
    have hr' : r ∈ uncoloredPrefixIndices C phi (ell + 1) := by simpa [R] using hr
    have hrAll : r ∈ Finset.range (Dyadic.levelStart (ell + 1)) ∧
        BlockUncolored phi (C.getD r ∅) := by
      simpa [uncoloredPrefixIndices] using hr'
    have hrData := hrAll.1
    have hrlt : r < Dyadic.levelStart J := (mem_range.mp hrData).trans_le
      (Dyadic.levelStart_mono hellSuccJ)
    exact (incidentCount_ambient_mono (G := G) (A := B) (B := A)
      sdiff_subset).trans (S.block_incident r hrlt)
  have hblockRaw := shortage_sdiff_biUnion_le_add_sum (G := G)
    (A := B) (k := k) R blocks (fun _ ↦ 1)
    hRsubset hRdisj hRincident
  have hblock :
      shortage k G (B \ R.biUnion blocks) ≤
        shortage k G B + (R.card : ℤ) := by simpa using hblockRaw
  have hshape :
      B \ R.biUnion blocks = deficitResidual A C phi (ell + 1) := by
    ext v
    simp [B, U, R, blocks, deficitResidual, uncoloredPrefixUnion]
    tauto
  rw [hshape] at hblock
  have hRcard : R.card = (uncoloredPrefixIndices C phi (ell + 1)).card := rfl
  rw [hRcard] at hblock
  have hellLeJ : ell ≤ J := hellJ.le
  have hbook := monochromaticBlockCount_add_uncoloredPrefix
    (G := G) hphi hellLeJ fun r hr ↦
      S.block_nonempty r (hr.trans_le (Dyadic.levelStart_mono hellLeJ))
  have hsplit := uncoloredPrefixIndices_card_succ C phi ell
  have hshort := S.shortage_le
  omega

lemma shortage_deficitResidual_le_twelve
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hJ0ell : J0 ≤ ell) (hellJ : ell < J)
    (hquarter : 2 ^ ell < 4 * uncoloredBlockCount C phi ell) :
    shortage k G (deficitResidual A C phi (ell + 1)) ≤
      12 * uncoloredBlockCount C phi ell := by
  have hdt := shortage_deficitResidual_le S hphi hJ0ell hellJ
  have hmono : 2 ^ J0 ≤ 2 ^ ell := Nat.pow_le_pow_right (by omega) hJ0ell
  have htell : t < (2 ^ ell : ℕ) :=
    lt_of_lt_of_le S.power (by exact_mod_cast hmono)
  have hstart : Dyadic.levelStart ell <
      4 * uncoloredBlockCount C phi ell := by
    exact lt_of_le_of_lt (Nat.sub_le _ _) hquarter
  have ht4 : t < (4 * uncoloredBlockCount C phi ell : ℕ) :=
    lt_of_lt_of_le htell (by exact_mod_cast hquarter.le)
  omega

structure SuccessorData
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (C : List (Finset V))
    (J0 ell J : ℕ) (phi rho : PartialColoring V k) where
  Z : Color k → Finset V
  X : Color k → Finset V
  newBlockCount : Color k → ℕ
  refines : Extends phi rho
  support : ∀ v, v ∉ A → rho v = none
  block_status : ∀ r < Dyadic.levelStart J,
    IsMonochromatic rho (C.getD r ∅) ∨ BlockUncolored rho (C.getD r ∅)
  class_eq : ∀ i,
    colorClass A rho i = colorClass A phi i ∪ (Z i ∪ X i)
  class_card : ∀ i,
    (colorClass A rho i).card =
      (colorClass A phi i).card + (Z i).card + (X i).card
  block_incidence : ∀ i,
    incidentCount G (A \ colorClass A phi i) (Z i) ≤
      (k - 1) * (Z i).card + newBlockCount i
  removed_incidence : ∀ i,
    incidentCount G ((A \ colorClass A phi i) \ Z i) (X i) ≤
      (k - 1) * (X i).card
  block_count_gain : ∀ i,
    monochromaticBlockCount C phi ell i + newBlockCount i ≤
      monochromaticBlockCount C rho (ell + 1) i
  retained_core : ∀ i, HasMinDegreeOn G (A \ colorClass A rho i) k
  early : ∀ r < Dyadic.levelStart J0, BlockUncolored rho (C.getD r ∅)
  quarter : 4 * uncoloredBlockCount C rho ell ≤ 2 ^ ell
  future_anticomplete : ∀ r,
    Dyadic.levelStart (ell + 1) ≤ r → r < Dyadic.levelStart J →
    BlockUncolored rho (C.getD r ∅) → ∀ i,
      ¬ AdjacentSets G (C.getD r ∅) (Z i ∪ X i)

theorem Appropriate.succ_of_data
    {A : Finset V} {k J0 ell J : ℕ} {C : List (Finset V)}
    {phi rho : PartialColoring V k}
    (hphi : Appropriate G A k C J0 ell J phi)
    (d : SuccessorData G A k C J0 ell J phi rho) :
    Appropriate G A k C J0 (ell + 1) J rho := by
  refine ⟨d.support, d.block_status, ?_, d.retained_core, d.early, ?_, ?_⟩
  · intro i
    let O := colorClass A phi i
    have hsplit1 := incidentCount_union_eq_add_restricted G A O (d.Z i ∪ d.X i)
    have hsplit2 := incidentCount_union_eq_add_restricted G (A \ O) (d.Z i) (d.X i)
    calc
      incidentCount G A (colorClass A rho i) =
          incidentCount G A (O ∪ (d.Z i ∪ d.X i)) := by rw [d.class_eq i]
      _ = incidentCount G A O + incidentCount G (A \ O) (d.Z i ∪ d.X i) :=
        hsplit1
      _ = incidentCount G A O +
          (incidentCount G (A \ O) (d.Z i) +
            incidentCount G ((A \ O) \ d.Z i) (d.X i)) := by rw [hsplit2]
      _ ≤ ((k - 1) * O.card + monochromaticBlockCount C phi ell i) +
          (((k - 1) * (d.Z i).card + d.newBlockCount i) +
            ((k - 1) * (d.X i).card)) := by
        exact Nat.add_le_add (hphi.incidence i)
          (Nat.add_le_add (d.block_incidence i) (d.removed_incidence i))
      _ = (k - 1) * (colorClass A rho i).card +
          (monochromaticBlockCount C phi ell i + d.newBlockCount i) := by
        rw [d.class_card i]
        ring
      _ ≤ (k - 1) * (colorClass A rho i).card +
          monochromaticBlockCount C rho (ell + 1) i :=
        Nat.add_le_add_left (d.block_count_gain i) _
  · intro j hj0 hj
    have hjle : j ≤ ell := Nat.lt_succ_iff.mp hj
    rcases Nat.lt_or_eq_of_le hjle with hjell | rfl
    · exact (Nat.mul_le_mul_left 4 (d.refines.uncoloredBlockCount_le C j)).trans
        (hphi.processed j hj0 hjell)
    · exact d.quarter
  · intro r hr hJ hrun
    have hrunOld : BlockUncolored phi (C.getD r ∅) :=
      d.refines.blockUncolored hrun
    have hrOld : Dyadic.levelStart ell ≤ r :=
      (Dyadic.levelStart_le_succ ell).trans hr
    have hOldNeighborhood := hphi.future r hrOld hJ hrunOld
    intro v hv w hwA hvw
    cases hrho : rho w with
    | none => rfl
    | some i =>
        have hwClass : w ∈ colorClass A rho i := by
          simp [colorClass, hwA, hrho]
        rw [d.class_eq i] at hwClass
        rcases mem_union.mp hwClass with hwOld | hwNew
        · have hphiwi : phi w = some i := (mem_filter.mp hwOld).2
          have hphinone := hOldNeighborhood v hv w hwA hvw
          rw [hphinone] at hphiwi
          contradiction
        · exact False.elim <| d.future_anticomplete r hr hJ hrun i
            ⟨v, hv, w, hwNew, hvw⟩

theorem appropriateColoring_succ
    {A : Finset V} {k J0 ell J : ℕ} {C : List (Finset V)}
    {phi : PartialColoring V k}
    (hphi : Appropriate G A k C J0 ell J phi)
    (hrepair : ∃ rho, Nonempty (SuccessorData G A k C J0 ell J phi rho)) :
    ∃ rho, Appropriate G A k C J0 (ell + 1) J rho := by
  obtain ⟨rho, ⟨d⟩⟩ := hrepair
  exact ⟨rho, hphi.succ_of_data d⟩

lemma incidentCount_deleted_le_of_shortage_le
    {A U' : Finset V} {k : ℕ}
    (hsub : U' ⊆ A) (hshort : shortage k G U' ≤ shortage k G A) :
    incidentCount G A (A \ U') ≤ (k - 1) * (A \ U').card := by
  have hcomp : A \ (A \ U') = U' := by
    ext x
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨hxA, hx⟩
      by_contra hxU'
      exact hx ⟨hxA, hxU'⟩
    · intro hxU'
      exact ⟨hsub hxU', fun hx ↦ hx.2 hxU'⟩
  have hs := shortage_sdiff k G (show A \ U' ⊆ A from sdiff_subset)
  rw [hcomp] at hs
  have hpot : 0 ≤ deletionPotential k G A (A \ U') := by omega
  unfold deletionPotential at hpot
  exact_mod_cast (sub_nonneg.mp hpot)

omit [DecidableEq V] [Fintype V] in
lemma card_coloredVertices
    (A : Finset V) (phi : PartialColoring V k) :
    (coloredVertices A phi).card =
      ∑ i : Color k, (colorClass A phi i).card := by
  classical
  rw [coloredVertices_eq_biUnion_colorClass]
  exact Finset.card_biUnion (pairwise_disjoint_colorClass A phi)

noncomputable def uncoloredLevelMass (C : List (Finset V))
    (phi : PartialColoring V k) (j : ℕ) : ℕ := by
  classical
  exact ∑ r ∈ Dyadic.levelIndices j,
    if BlockUncolored phi (C.getD r ∅) then Dyadic.cardAt C r else 0

noncomputable def uncoloredBetweenMass (C : List (Finset V))
    (phi : PartialColoring V k) (J0 J : ℕ) : ℕ := by
  classical
  exact ∑ r ∈ Finset.Ico (Dyadic.levelStart J0) (Dyadic.levelStart J),
    if BlockUncolored phi (C.getD r ∅) then Dyadic.cardAt C r else 0

noncomputable def coloredBlockMass (C : List (Finset V))
    (phi : PartialColoring V k) (J0 J : ℕ) : ℕ := by
  classical
  exact ∑ r ∈ Finset.Ico (Dyadic.levelStart J0) (Dyadic.levelStart J),
    if BlockUncolored phi (C.getD r ∅) then 0 else Dyadic.cardAt C r

private lemma sum_le_card_mul' {s : Finset ℕ} {f : ℕ → ℕ} {b : ℕ}
    (h : ∀ i ∈ s, f i ≤ b) : s.sum f ≤ s.card * b := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      have ha_le : f a ≤ b := h a (Finset.mem_insert_self a s)
      have hs : ∀ i ∈ s, f i ≤ b := by
        intro i hi
        exact h i (Finset.mem_insert_of_mem hi)
      have hsum := ih hs
      nlinarith

private lemma card_mul_le_sum' {s : Finset ℕ} {f : ℕ → ℕ} {b : ℕ}
    (h : ∀ i ∈ s, b ≤ f i) : s.card * b ≤ s.sum f := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      have ha_ge : b ≤ f a := h a (Finset.mem_insert_self a s)
      have hs : ∀ i ∈ s, b ≤ f i := by
        intro i hi
        exact h i (Finset.mem_insert_of_mem hi)
      have hsum := ih hs
      nlinarith

omit [DecidableEq V] [Fintype V] in
lemma uncoloredLevelMass_le_count_mul
    (C : List (Finset V)) (phi : PartialColoring V k) {j J : ℕ}
    (hord : Dyadic.Nonincreasing C) (hcomplete : Dyadic.CompleteThrough C J)
    (hjJ : j < J) :
    uncoloredLevelMass C phi j ≤
      uncoloredBlockCount C phi j * Dyadic.cardAt C (Dyadic.levelStart j) := by
  classical
  rw [uncoloredLevelMass, ← Finset.sum_filter]
  apply sum_le_card_mul'
  intro r hr
  rw [Finset.mem_filter] at hr
  rw [Dyadic.mem_levelIndices] at hr
  apply hord hr.1.1
  exact hr.1.2.trans_le
    ((Dyadic.levelStart_mono (Nat.succ_le_of_lt hjJ)).trans hcomplete)

omit [DecidableEq V] [Fintype V] in
lemma prevLevel_card_mul_le_mass
    (C : List (Finset V)) {j J : ℕ}
    (hj : 0 < j) (hjJ : j < J)
    (hord : Dyadic.Nonincreasing C) (hcomplete : Dyadic.CompleteThrough C J) :
    2 ^ (j - 1) * Dyadic.cardAt C (Dyadic.levelStart j) ≤
      Dyadic.levelMass C (j - 1) := by
  have hstart_lt : Dyadic.levelStart j < C.length := by
    have hlt : Dyadic.levelStart j < Dyadic.levelStart (j + 1) := by
      rw [Dyadic.levelStart_succ]
      exact Nat.lt_add_of_pos_right (pow_pos (by omega) _)
    exact hlt.trans_le
      ((Dyadic.levelStart_mono (Nat.succ_le_of_lt hjJ)).trans hcomplete)
  have hsum : (Dyadic.levelIndices (j - 1)).card *
      Dyadic.cardAt C (Dyadic.levelStart j) ≤ Dyadic.levelMass C (j - 1) := by
    apply card_mul_le_sum'
    intro r hr
    rw [Dyadic.mem_levelIndices] at hr
    apply hord (Nat.le_of_lt ?_) hstart_lt
    simpa [show j - 1 + 1 = j by omega] using hr.2
  simpa using hsum

omit [DecidableEq V] [Fintype V] in
lemma two_mul_uncoloredLevelMass_le_prev
    (C : List (Finset V)) (phi : PartialColoring V k) {j J : ℕ}
    (hj : 0 < j) (hjJ : j < J)
    (hord : Dyadic.Nonincreasing C) (hcomplete : Dyadic.CompleteThrough C J)
    (hprocessed : 4 * uncoloredBlockCount C phi j ≤ 2 ^ j) :
    2 * uncoloredLevelMass C phi j ≤ Dyadic.levelMass C (j - 1) := by
  have hu := uncoloredLevelMass_le_count_mul C phi hord hcomplete hjJ
  have hp := prevLevel_card_mul_le_mass C hj hjJ hord hcomplete
  have hpow : 2 ^ j = 2 * 2 ^ (j - 1) := by
    calc
      2 ^ j = 2 ^ ((j - 1) + 1) := by congr 1; omega
      _ = 2 ^ (j - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (j - 1) := Nat.mul_comm _ _
  rw [hpow] at hprocessed
  have hcount : 2 * uncoloredBlockCount C phi j ≤ 2 ^ (j - 1) := by omega
  calc
    2 * uncoloredLevelMass C phi j ≤
        2 * (uncoloredBlockCount C phi j * Dyadic.cardAt C (Dyadic.levelStart j)) :=
      Nat.mul_le_mul_left 2 hu
    _ = (2 * uncoloredBlockCount C phi j) * Dyadic.cardAt C (Dyadic.levelStart j) := by
      ring
    _ ≤ 2 ^ (j - 1) * Dyadic.cardAt C (Dyadic.levelStart j) :=
      Nat.mul_le_mul_right _ hcount
    _ ≤ Dyadic.levelMass C (j - 1) := hp

omit [DecidableEq V] [Fintype V] in
lemma uncoloredBetweenMass_succ
    (C : List (Finset V)) (phi : PartialColoring V k) {J0 j : ℕ}
    (hJ0j : J0 ≤ j) :
    uncoloredBetweenMass C phi J0 (j + 1) =
      uncoloredBetweenMass C phi J0 j + uncoloredLevelMass C phi j := by
  classical
  unfold uncoloredBetweenMass uncoloredLevelMass Dyadic.levelIndices
  exact (Finset.sum_Ico_consecutive _ (Dyadic.levelStart_mono hJ0j)
    (Dyadic.levelStart_le_succ j)).symm

omit [DecidableEq V] [Fintype V] in
lemma betweenMass_succ
    (C : List (Finset V)) {J0 j : ℕ} (hJ0j : J0 ≤ j) :
    Dyadic.betweenMass C J0 (j + 1) =
      Dyadic.betweenMass C J0 j + Dyadic.levelMass C j := by
  unfold Dyadic.betweenMass Dyadic.levelMass Dyadic.levelIndices
  exact (Finset.sum_Ico_consecutive _ (Dyadic.levelStart_mono hJ0j)
    (Dyadic.levelStart_le_succ j)).symm

omit [DecidableEq V] [Fintype V] in
lemma two_mul_uncoloredBetweenMass_add_last_le
    (C : List (Finset V)) (phi : PartialColoring V k) {J0 J : ℕ}
    (hJ0 : 0 < J0) (hJ0J : J0 ≤ J)
    (hord : Dyadic.Nonincreasing C) (hcomplete : Dyadic.CompleteThrough C J)
    (hprocessed : ∀ j, J0 ≤ j → j < J →
      4 * uncoloredBlockCount C phi j ≤ 2 ^ j) :
    2 * uncoloredBetweenMass C phi J0 J + Dyadic.levelMass C (J - 1) ≤
      Dyadic.levelMass C (J0 - 1) + Dyadic.betweenMass C J0 J := by
  induction J, hJ0J using Nat.le_induction with
  | base => simp [uncoloredBetweenMass, Dyadic.betweenMass]
  | @succ j hj ih =>
      rw [uncoloredBetweenMass_succ C phi hj, betweenMass_succ C hj]
      have hjpos : 0 < j := hJ0.trans_le hj
      have hcompj : Dyadic.CompleteThrough C (j + 1) := hcomplete
      have hcompPrev : Dyadic.CompleteThrough C j :=
        (Dyadic.levelStart_mono (Nat.le_succ j)).trans hcomplete
      have ih' := ih hcompPrev
        (fun j' hj' hj'lt ↦ hprocessed j' hj'
          (hj'lt.trans (Nat.lt_succ_self j)))
      have hlev := two_mul_uncoloredLevelMass_le_prev C phi hjpos
        (Nat.lt_succ_self j) hord hcompj
        (hprocessed j hj (Nat.lt_succ_self j))
      have hjm : j + 1 - 1 = j := by omega
      rw [hjm]
      omega

omit [DecidableEq V] [Fintype V] in
lemma two_mul_uncoloredBetweenMass_le
    (C : List (Finset V)) (phi : PartialColoring V k) {J0 J : ℕ}
    (hJ0 : 0 < J0) (hJ0J : J0 ≤ J)
    (hord : Dyadic.Nonincreasing C) (hcomplete : Dyadic.CompleteThrough C J)
    (hprocessed : ∀ j, J0 ≤ j → j < J →
      4 * uncoloredBlockCount C phi j ≤ 2 ^ j) :
    2 * uncoloredBetweenMass C phi J0 J ≤
      Dyadic.levelMass C (J0 - 1) + Dyadic.betweenMass C J0 J := by
  exact (Nat.le_add_right _ _).trans
    (two_mul_uncoloredBetweenMass_add_last_le C phi hJ0 hJ0J hord hcomplete hprocessed)

omit [DecidableEq V] [Fintype V] in
lemma betweenMass_eq_uncolored_add_colored
    (C : List (Finset V)) (phi : PartialColoring V k) (J0 J : ℕ) :
    Dyadic.betweenMass C J0 J =
      uncoloredBetweenMass C phi J0 J + coloredBlockMass C phi J0 J := by
  classical
  unfold Dyadic.betweenMass uncoloredBetweenMass coloredBlockMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases h : BlockUncolored phi (C[r]?.getD ∅) <;> simp [h]

lemma coloredBlockMass_le_coloredVertices
    {A : Finset V} {k : ℕ} {t : ℤ} {C : List (Finset V)}
    {J0 J : ℕ} {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 J J phi) :
    coloredBlockMass C phi J0 J ≤ (coloredVertices A phi).card := by
  classical
  let s := (Finset.Ico (Dyadic.levelStart J0) (Dyadic.levelStart J)).filter fun r ↦
    ¬ BlockUncolored phi (C.getD r ∅)
  have hsrange : ∀ r ∈ s, r < Dyadic.levelStart J := by
    intro r hr
    simp only [s, Finset.mem_filter] at hr
    exact (Finset.mem_Ico.mp hr.1).2
  have hdisj : (s : Set ℕ).PairwiseDisjoint fun r ↦ C.getD r ∅ := by
    intro r hr s' hs' hrs
    exact S.blocks_disjoint r (hsrange r hr) s' (hsrange s' hs') hrs
  have hunion : s.biUnion (fun r ↦ C.getD r ∅) ⊆ coloredVertices A phi := by
    intro v hv
    rw [Finset.mem_biUnion] at hv
    rcases hv with ⟨r, hrs, hvr⟩
    have hrs' : r ∈ Finset.Ico (Dyadic.levelStart J0) (Dyadic.levelStart J) ∧
        ¬ BlockUncolored phi (C.getD r ∅) := by
      simpa only [s, Finset.mem_filter] using hrs
    have hrIco := Finset.mem_Ico.mp hrs'.1
    have hvA := S.block_subset r hrIco.2 hvr
    have hmono : IsMonochromatic phi (C.getD r ∅) :=
      (hphi.blocks r hrIco.2).resolve_right hrs'.2
    rcases hmono with ⟨i, hi⟩
    exact mem_coloredVertices_iff.mpr ⟨hvA, i, hi v hvr⟩
  have hcard := Finset.card_le_card hunion
  rw [Finset.card_biUnion hdisj] at hcard
  have heq : coloredBlockMass C phi J0 J =
      ∑ r ∈ s, Dyadic.cardAt C r := by
    unfold coloredBlockMass
    simp only [s, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r hr
    simp
  rw [heq]
  exact hcard

lemma final_colored_mass
    {A : Finset V} {k : ℕ} {t : ℤ} {C : List (Finset V)}
    {J0 J : ℕ} {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 J J phi) :
    A.card < 20 * k * (coloredVertices A phi).card := by
  have hu := two_mul_uncoloredBetweenMass_le C phi S.hJ0 S.hJ
    S.nonincreasing S.complete hphi.processed
  have hsplit := betweenMass_eq_uncolored_add_colored C phi J0 J
  have hcm := coloredBlockMass_le_coloredVertices S hphi
  nlinarith [S.late_mass, S.cutoff_level]

omit [DecidableEq V] [Fintype V] in

lemma exists_large_colorClass
    {A : Finset V} {k : ℕ} {phi : PartialColoring V k}
    (hk : 0 < k)
    (hcolored : A.card < 20 * k * (coloredVertices A phi).card) :
    ∃ i : Color k, A.card < 10000 * k ^ 2 * (colorClass A phi i).card := by
  by_contra h
  push Not at h
  have hsum :
      10000 * k ^ 2 * (∑ i : Color k, (colorClass A phi i).card) ≤
        (401 * k) * A.card := by
    calc
      10000 * k ^ 2 * (∑ i : Color k, (colorClass A phi i).card) =
          ∑ i : Color k, 10000 * k ^ 2 * (colorClass A phi i).card := by
            rw [Finset.mul_sum]
      _ ≤ ∑ _i : Color k, A.card := Finset.sum_le_sum fun i _ ↦ h i
      _ = (401 * k) * A.card := by simp
  rw [← card_coloredVertices] at hsum
  have hposA : 0 < A.card := by
    by_contra hA
    have hAz : A.card = 0 := Nat.eq_zero_of_not_pos hA
    have hsub : (coloredVertices A phi).card ≤ A.card :=
      card_le_card (filter_subset _ _)
    have hcz : (coloredVertices A phi).card = 0 := by omega
    rw [hAz, hcz] at hcolored
    simp at hcolored
  have hchain : 500 * k * A.card < 401 * k * A.card := by
    calc
      500 * k * A.card = (500 * k) * A.card := rfl
      _ < (500 * k) * (20 * k * (coloredVertices A phi).card) :=
        Nat.mul_lt_mul_of_pos_left hcolored (by positivity)
      _ = 10000 * k ^ 2 * (coloredVertices A phi).card := by ring
      _ ≤ 401 * k * A.card := hsum
  have hback : 401 * k * A.card < 500 * k * A.card := by
    exact Nat.mul_lt_mul_of_pos_right
      (Nat.mul_lt_mul_of_pos_right (by decide : 401 < 500) hk) hposA
  exact (Nat.lt_asymm hchain hback).elim

lemma smallCore_of_appropriate_and_colored
    {A : Finset V} {k J0 J : ℕ} {C : List (Finset V)}
    {phi : PartialColoring V k}
    (hk : 2 ≤ k) (hphi : Appropriate G A k C J0 J J phi)
    (hcolored : A.card < 20 * k * (coloredVertices A phi).card) :
    ∃ W, IsSmallCoreOn G A k (uniformDen k) W := by
  obtain ⟨i, hi⟩ := exists_large_colorClass (A := A) (phi := phi)
    (by omega : 0 < k) hcolored
  refine ⟨A \ colorClass A phi i, sdiff_subset, hphi.minDegree i, ?_⟩
  have hclass : (colorClass A phi i).card ≤ A.card :=
    card_le_card (filter_subset _ _)
  have hcard : (A \ colorClass A phi i).card =
      A.card - (colorClass A phi i).card := by
    exact card_sdiff_of_subset (filter_subset _ _)
  have hden : A.card ≤ uniformDen k * (colorClass A phi i).card := by
    have hkle : 10000 * k ^ 2 ≤ uniformDen k := by
      simp only [uniformDen]
      nlinarith
    exact hi.le.trans (Nat.mul_le_mul_right _ hkle)
  have hdenpos := uniformDen_pos k hk
  rw [hcard]
  rw [Nat.mul_sub_left_distrib]
  calc
    uniformDen k * A.card - uniformDen k * (colorClass A phi i).card ≤
        uniformDen k * A.card - A.card := Nat.sub_le_sub_left hden _
    _ = (uniformDen k - 1) * A.card := by
      rw [Nat.sub_mul]
      simp

omit [DecidableEq V] [Fintype V] in
lemma exists_maximalComplete (C : List (Finset V)) :
    ∃ J, Dyadic.MaximalComplete C J := by
  let J := Nat.findGreatest (fun j => Dyadic.levelStart j ≤ C.length) C.length
  have hcomp : Dyadic.levelStart J ≤ C.length := by
    simpa [J] using
      (Nat.findGreatest_spec (P := fun j => Dyadic.levelStart j ≤ C.length)
        (m := 0) (Nat.zero_le C.length) (by simp [Dyadic.levelStart]))
  refine ⟨J, hcomp, ?_⟩
  by_contra hn
  have hp : Dyadic.levelStart (J + 1) ≤ C.length := Nat.le_of_not_gt hn
  have hb : J + 1 ≤ C.length := by
    have hpow := (J + 1).lt_two_pow_self
    simp only [Dyadic.levelStart] at hp
    omega
  exact (Nat.findGreatest_is_greatest
    (P := fun j => Dyadic.levelStart j ≤ C.length)
    (n := C.length) (by omega) hb) hp

theorem exists_coloringSystem
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (t : ℤ) (hk : 2 ≤ k) (ht : t + 1 ≤ Tmax k)
    (A : Finset V) (hcard : k - 1 ≤ A.card)
    (hshort : shortage k G A ≤ t)
    (hlocal : LocalExpansion G A k)
    (hmin : HasMinDegreeOn G A k)
    (hconn : ConnectedOn G A)
    (hno : NoSmallCoreOn G A k (uniformDen k)) :
    ∃ C J0 J, ColoringSystem G A k t C J0 J := by
  classical
  let C := orderedMaxGood G A k
  obtain ⟨J, hJmax⟩ := exists_maximalComplete C
  have hCnoninc : Dyadic.Nonincreasing C := by
    dsimp only [C]
    exact orderedMaxGood_nonincreasing G A k
  have hCnodup : C.Nodup := by
    simpa [C] using orderedMaxGood_nodup G A k
  have htprob : t ≤ problemT k := by
    simp only [problemT, Tmax] at ht ⊢
    omega
  have hshortprob : shortage k G A ≤ problemT k := hshort.trans htprob
  have hedge : edgeThreshold k A.card ≤ edgeCount G A := by
    have hcast := edgeThreshold_cast_eq k A.card hk hcard
    have hcastle : (edgeThreshold k A.card : ℤ) ≤ (edgeCount G A : ℤ) := by
      rw [hcast]
      simpa [shortage, add_comm] using hshortprob
    exact_mod_cast hcastle
  have hden2k : 2 * k ≤ uniformDen k := by
    have hk2pos : 1 ≤ k ^ 2 := by nlinarith
    have hcoef : 2 ≤ 10000 * k ^ 2 := by nlinarith
    calc
      2 * k ≤ (10000 * k ^ 2) * k := Nat.mul_le_mul_right k hcoef
      _ = uniformDen k := by simp only [uniformDen]; ring
  have hden27 : 27 * k ^ 2 ≤ uniformDen k := by
    have hcoef : 27 ≤ 10000 * k := by nlinarith
    calc
      27 * k ^ 2 ≤ (10000 * k) * k ^ 2 := Nat.mul_le_mul_right (k ^ 2) hcoef
      _ = uniformDen k := by simp only [uniformDen]; ring
  have hden27pos : 1 ≤ 27 * k ^ 2 := by
    have : 0 < 27 * k ^ 2 := by positivity
    omega
  have hno27 : NoSmallCoreOn G A k (27 * k ^ 2) :=
    hno.anti_den hden27pos hden27
  have hnoSupply : ¬ ∃ W : Finset V, W ⊆ A ∧ HasMinDegreeOn G W k ∧
      27 * k ^ 2 * W.card ≤ (27 * k ^ 2 - 1) * A.card := by
    simpa only [NoSmallCoreOn, IsSmallCoreOn] using hno27
  have hsupply : A.card ≤ 3 * k * (degreeEq G A k).card :=
    many_degree_eq_k_of_counterexample G A k hk hmin hnoSupply
  have hdegmass : (degreeEq G A k).card ≤
      ∑ D ∈ maxGood G A k, D.card :=
    card_degreeEq_le_maxGood_mass (G := G)
  have htotal : Dyadic.totalMass C = ∑ D ∈ maxGood G A k, D.card := by
    rw [Dyadic.totalMass_eq_sum_card]
    have hp := (List.mergeSort_perm (maxGood G A k).toList
      (fun D E : Finset V ↦ decide (E.card ≤ D.card))).map Finset.card
    have hs := hp.sum_eq
    simpa only [C, orderedMaxGood] using hs.trans (by simp)
  have hmassTotal : A.card ≤ 3 * k * Dyadic.totalMass C := by
    rw [htotal]
    exact hsupply.trans (Nat.mul_le_mul_left (3 * k) hdegmass)
  have hmassRet : A.card ≤ 6 * k * Dyadic.retainedMass C J := by
    have htail := Dyadic.two_mul_retainedMass_ge_totalMass C J hCnoninc hJmax
    calc
      A.card ≤ 3 * k * Dyadic.totalMass C := hmassTotal
      _ ≤ 3 * k * (2 * Dyadic.retainedMass C J) :=
        Nat.mul_le_mul_left (3 * k) htail
      _ = 6 * k * Dyadic.retainedMass C J := by ring
  have hreachJ : A.card ≤ 100 * k * Dyadic.retainedMass C J := by
    calc
      A.card ≤ 6 * k * Dyadic.retainedMass C J := hmassRet
      _ ≤ 100 * k * Dyadic.retainedMass C J := by nlinarith
  let P : ℕ → Prop := fun j ↦ A.card ≤ 100 * k * Dyadic.retainedMass C j
  have hPex : ∃ j, P j := ⟨J, hreachJ⟩
  let J0 := Nat.find hPex
  have hreach0 : A.card ≤ 100 * k * Dyadic.retainedMass C J0 := by
    exact Nat.find_spec hPex
  have hApos : 0 < A.card := hmin.1.card_pos
  have hJ0pos : 0 < J0 := by
    by_contra hn
    have hzero : J0 = 0 := Nat.eq_zero_of_not_pos hn
    have hretzero : Dyadic.retainedMass C J0 = 0 := by
      rw [hzero]
      simp [Dyadic.retainedMass, Dyadic.levelStart]
    rw [hretzero] at hreach0
    omega
  have hJ0J : J0 ≤ J := Nat.find_min' hPex hreachJ
  have hprev : 100 * k * Dyadic.retainedMass C (J0 - 1) < A.card := by
    by_contra hn
    have hp : P (J0 - 1) := Nat.le_of_not_gt hn
    have := Nat.find_min' hPex hp
    omega
  have hgetMax : ∀ r, r < Dyadic.levelStart J →
      MaximalGood G A k (C.getD r ∅) := by
    intro r hr
    have hrlen : r < C.length := hr.trans_le hJmax.1
    have hmemC : C.getD r ∅ ∈ C := by
      rw [List.getD_eq_getElem _ _ hrlen]
      exact List.get_mem C ⟨r, hrlen⟩
    have hmemOrd : C.getD r ∅ ∈ orderedMaxGood G A k := by
      simpa only [C] using hmemC
    exact (mem_maxGood (G := G)).mp
      ((mem_orderedMaxGood_iff G A k _).mp hmemOrd)
  have hgetGood : ∀ r, r < Dyadic.levelStart J → Good G A k (C.getD r ∅) :=
    fun r hr ↦ (hgetMax r hr).1
  have hgetNonempty : ∀ r, r < Dyadic.levelStart J → (C.getD r ∅).Nonempty :=
    fun r hr ↦ Good.nonempty G (hgetGood r hr)
  have hgetSubset : ∀ r, r < Dyadic.levelStart J → C.getD r ∅ ⊆ A :=
    fun r hr ↦ Good.subset G (hgetGood r hr)
  have hgetMul : ∀ r, r < Dyadic.levelStart J →
      k * (C.getD r ∅).card ≤ A.card := by
    intro r hr
    exact Good.card_mul_le_of_noSmallCoreOn G hk hden2k hcard hlocal hedge hno
      (hgetGood r hr)
  have hgetCardRange : ∀ r, r < Dyadic.levelStart J →
      (C.getD r ∅).card ≤ A.card - k + 1 := by
    intro r hr
    have hpos := (hgetNonempty r hr).card_pos
    have hmul := hgetMul r hr
    have hprod : 0 ≤ (k - 1) * ((C.getD r ∅).card - 1) := Nat.zero_le _
    have hsum : (C.getD r ∅).card + k ≤ A.card + 1 := by
      nlinarith
    omega
  have hgetIncident : ∀ r, r < Dyadic.levelStart J →
      incidentCount G A (C.getD r ∅) ≤
        (k - 1) * (C.getD r ∅).card + 1 := by
    intro r hr
    exact Good.incidentCount_le_of_card_le G hlocal (hgetGood r hr)
      (hgetCardRange r hr)
  have hgetComplement : ∀ r, r < Dyadic.levelStart J →
      HasMinDegreeOn G (A \ C.getD r ∅) k := by
    intro r hr
    apply maximalGood_complement_hasMinDegreeOn G (hgetMax r hr)
    have hpos := (hgetNonempty r hr).card_pos
    have hmul := hgetMul r hr
    have hlt : (C.getD r ∅).card < A.card := by nlinarith
    rw [Finset.nonempty_iff_ne_empty, ne_eq, Finset.sdiff_eq_empty_iff_subset]
    exact fun hsub ↦ (not_le_of_gt hlt) (card_le_card hsub)
  have hgetLarge : ∀ r, r < Dyadic.levelStart J →
      uniformDen k * (C.getD r ∅).card < A.card := by
    intro r hr
    by_contra hn
    have hAle : A.card ≤ uniformDen k * (C.getD r ∅).card :=
      Nat.le_of_not_gt hn
    apply hno
    refine ⟨A \ C.getD r ∅, sdiff_subset, hgetComplement r hr, ?_⟩
    rw [card_sdiff_of_subset (hgetSubset r hr), Nat.mul_sub_left_distrib,
      Nat.sub_mul]
    simpa only [one_mul] using Nat.sub_le_sub_left hAle (uniformDen k * A.card)
  have hdisjoint : ∀ r, r < Dyadic.levelStart J →
      ∀ s, s < Dyadic.levelStart J → r ≠ s →
        Disjoint (C.getD r ∅) (C.getD s ∅) := by
    intro r hr s hs hrs
    have hrlen : r < C.length := hr.trans_le hJmax.1
    have hslen : s < C.length := hs.trans_le hJmax.1
    have hne : C.getD r ∅ ≠ C.getD s ∅ := by
      intro heq
      rw [List.getD_eq_getElem _ _ hrlen, List.getD_eq_getElem _ _ hslen] at heq
      have hi := (hCnodup.get_inj_iff (i := ⟨r, hrlen⟩) (j := ⟨s, hslen⟩)).mp heq
      exact hrs (Fin.ext_iff.mp hi)
    have hrmem : C.getD r ∅ ∈ maxGood G A k :=
      (mem_maxGood (G := G)).mpr (hgetMax r hr)
    have hsmem : C.getD s ∅ ∈ maxGood G A k :=
      (mem_maxGood (G := G)).mpr (hgetMax s hs)
    exact maxGood_pairwiseDisjoint (G := G) hrmem hsmem hne
  have hanti : ∀ r, r < Dyadic.levelStart J →
      ∀ s, s < Dyadic.levelStart J → r ≠ s →
        Anticomplete G (C.getD r ∅) (C.getD s ∅) := by
    intro r hr s hs hrs
    have hrlen : r < C.length := hr.trans_le hJmax.1
    have hslen : s < C.length := hs.trans_le hJmax.1
    have hne : C.getD r ∅ ≠ C.getD s ∅ := by
      intro heq
      rw [List.getD_eq_getElem _ _ hrlen, List.getD_eq_getElem _ _ hslen] at heq
      have hi := (hCnodup.get_inj_iff (i := ⟨r, hrlen⟩) (j := ⟨s, hslen⟩)).mp heq
      exact hrs (Fin.ext_iff.mp hi)
    exact maxGood_pairwise_not_adjacent (G := G)
      ((mem_maxGood (G := G)).mpr (hgetMax r hr))
      ((mem_maxGood (G := G)).mpr (hgetMax s hs)) hne
  have hJ0one : 1 < J0 := by
    by_contra hn
    have heq : J0 = 1 := by omega
    have hzeroJ : 0 < Dyadic.levelStart J := by
      have hJpos : 0 < J := hJ0pos.trans_le hJ0J
      simp only [Dyadic.levelStart]
      have := Nat.one_lt_pow hJpos.ne' (by omega : 1 < (2 : ℕ))
      omega
    have hlarge0 := hgetLarge 0 hzeroJ
    have hmass0 : Dyadic.retainedMass C J0 = (C.getD 0 ∅).card := by
      simp [heq, Dyadic.retainedMass, Dyadic.levelStart, Dyadic.cardAt]
    rw [hmass0] at hreach0
    have hcoef : 100 * k ≤ uniformDen k := by
      simp only [uniformDen]
      nlinarith
    have : A.card ≤ uniformDen k * (C.getD 0 ∅).card :=
      hreach0.trans (Nat.mul_le_mul_right _ hcoef)
    omega
  have hcutLevel : 50 * k * Dyadic.levelMass C (J0 - 1) < A.card := by
    have hcomplete0 : Dyadic.CompleteThrough C J0 :=
      hJmax.1.trans' (Dyadic.levelStart_mono hJ0J)
    have hidx : J0 - 2 + 1 = J0 - 1 := by omega
    have hc : Dyadic.CompleteThrough C (J0 - 2 + 2) := by
      convert hcomplete0 using 1
      omega
    have hlevel2 := Dyadic.levelMass_succ_le_two_mul C (J0 - 2) hCnoninc hc
    rw [hidx] at hlevel2
    have hprevMass : Dyadic.levelMass C (J0 - 2) ≤
        Dyadic.retainedMass C (J0 - 1) := by
      have hadd := Dyadic.retainedMass_succ C (J0 - 2)
      rw [hidx] at hadd
      omega
    calc
      50 * k * Dyadic.levelMass C (J0 - 1) ≤
          50 * k * (2 * Dyadic.levelMass C (J0 - 2)) :=
        Nat.mul_le_mul_left (50 * k) hlevel2
      _ = 100 * k * Dyadic.levelMass C (J0 - 2) := by ring
      _ ≤ 100 * k * Dyadic.retainedMass C (J0 - 1) :=
        Nat.mul_le_mul_left (100 * k) hprevMass
      _ < A.card := hprev
  have hprefix : 100 * k * Dyadic.retainedMass C J0 < 3 * A.card := by
    rw [show J0 = (J0 - 1) + 1 by omega, Dyadic.retainedMass_succ]
    have hlevscaled : 100 * k * Dyadic.levelMass C (J0 - 1) < 2 * A.card := by
      have hh := (Nat.mul_lt_mul_left (by omega : 0 < 2)).mpr hcutLevel
      convert hh using 1
      ring
    calc
      100 * k * (Dyadic.retainedMass C (J0 - 1) +
          Dyadic.levelMass C (J0 - 1)) =
          100 * k * Dyadic.retainedMass C (J0 - 1) +
            100 * k * Dyadic.levelMass C (J0 - 1) := by ring
      _ < A.card + 2 * A.card := Nat.add_lt_add hprev hlevscaled
      _ = 3 * A.card := by ring
  have hlate : A.card < 8 * k * Dyadic.betweenMass C J0 J := by
    have hadd := Dyadic.retained_add_between (C := C) hJ0J
    by_contra hn
    have hB : 8 * k * Dyadic.betweenMass C J0 J ≤ A.card :=
      Nat.le_of_not_gt hn
    have hBscaled : 100 * k * Dyadic.betweenMass C J0 J ≤ 13 * A.card := by
      calc
        100 * k * Dyadic.betweenMass C J0 J ≤
            13 * (8 * k * Dyadic.betweenMass C J0 J) := by
              calc
                100 * k * Dyadic.betweenMass C J0 J =
                    100 * (k * Dyadic.betweenMass C J0 J) := by ring
                _ ≤ 104 * (k * Dyadic.betweenMass C J0 J) :=
                  Nat.mul_le_mul_right _ (by omega)
                _ = 13 * (8 * k * Dyadic.betweenMass C J0 J) := by ring
        _ ≤ 13 * A.card := Nat.mul_le_mul_left 13 hB
    have hRupper : 100 * k * Dyadic.retainedMass C J < 16 * A.card := by
      calc
        100 * k * Dyadic.retainedMass C J =
            100 * k * Dyadic.retainedMass C J0 +
              100 * k * Dyadic.betweenMass C J0 J := by rw [← hadd]; ring
        _ < 3 * A.card + 13 * A.card :=
          Nat.add_lt_add_of_lt_of_le hprefix hBscaled
        _ = 16 * A.card := by ring
    have hRlower : 50 * A.card ≤ 300 * k * Dyadic.retainedMass C J := by
      have := Nat.mul_le_mul_left 50 hmassRet
      convert this using 1
      ring
    have hRupper' : 300 * k * Dyadic.retainedMass C J < 48 * A.card := by
      have := (Nat.mul_lt_mul_left (by omega : 0 < 3)).mpr hRupper
      convert this using 1 <;> ring
    omega
  have hpower : t < (2 ^ J0 : ℕ) := by
    have hJpos : 0 < J := hJ0pos.trans_le hJ0J
    have hzeroJ : 0 < Dyadic.levelStart J := by
      simp only [Dyadic.levelStart]
      have := Nat.one_lt_pow hJpos.ne' (by omega : 1 < (2 : ℕ))
      omega
    have hlarge0 := hgetLarge 0 hzeroJ
    have htT : t ≤ Tmax k := by omega
    have htK : t ≤ (k ^ 2 : ℕ) := htT.trans (Tmax_le_sq k)
    have hkmass : k ^ 2 * (Dyadic.cardAt C 0) < Dyadic.retainedMass C J0 := by
      have hchain : 100 * k * (100 * k ^ 2 * Dyadic.cardAt C 0) <
          100 * k * Dyadic.retainedMass C J0 := by
        calc
          100 * k * (100 * k ^ 2 * Dyadic.cardAt C 0) =
              uniformDen k * (C.getD 0 ∅).card := by
                simp only [uniformDen, Dyadic.cardAt]; ring
          _ < A.card := hlarge0
          _ ≤ 100 * k * Dyadic.retainedMass C J0 := hreach0
      have hcanceled : 100 * k ^ 2 * Dyadic.cardAt C 0 <
          Dyadic.retainedMass C J0 := Nat.lt_of_mul_lt_mul_left hchain
      have hcard0pos : 0 < Dyadic.cardAt C 0 := by
        simpa only [Dyadic.cardAt] using (hgetNonempty 0 hzeroJ).card_pos
      have hk2pos : 0 < k ^ 2 := by positivity
      have hcoefmul : k ^ 2 < 100 * k ^ 2 := by
        calc
          k ^ 2 = 1 * k ^ 2 := by simp
          _ < 100 * k ^ 2 := Nat.mul_lt_mul_of_pos_right (by omega) hk2pos
      exact (Nat.mul_lt_mul_of_pos_right hcoefmul hcard0pos).trans hcanceled
    have hforbid : t * (Dyadic.cardAt C 0 : ℤ) <
        (Dyadic.retainedMass C J0 : ℕ) := by
      have hnonneg : (0 : ℤ) ≤ Dyadic.cardAt C 0 := by positivity
      have htKz : t ≤ (k ^ 2 : ℕ) := htK
      have hmulz : t * (Dyadic.cardAt C 0 : ℤ) ≤
          ((k ^ 2 : ℕ) : ℤ) * (Dyadic.cardAt C 0 : ℤ) :=
        mul_le_mul_of_nonneg_right htKz hnonneg
      have hkmassz : ((k ^ 2 : ℕ) : ℤ) * (Dyadic.cardAt C 0 : ℤ) <
          (Dyadic.retainedMass C J0 : ℤ) := by exact_mod_cast hkmass
      exact hmulz.trans_lt hkmassz
    exact Dyadic.signed_shortage_lt_two_pow
      (C := C) (q := Dyadic.retainedMass C J0) (J := J0) (t := t)
      hJ0pos hCnoninc
      (hJmax.1.trans' (Dyadic.levelStart_mono hJ0J)) le_rfl hforbid
  refine ⟨C, J0, J, ?_⟩
  exact
    { hk := hk
      hJ0 := hJ0pos
      hJ := hJ0J
      complete := hJmax.1
      nonincreasing := hCnoninc
      nodup := hCnodup
      block_nonempty := hgetNonempty
      block_subset := hgetSubset
      block_incident := hgetIncident
      block_complement_minDegree := hgetComplement
      blocks_disjoint := hdisjoint
      blocks_anticomplete := hanti
      minDegree := hmin
      connected := hconn
      noSmallCore := hno
      shortage_le := hshort
      power := hpower
      early_mass := hreach0
      cutoff_level := hcutLevel
      late_mass := hlate }

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

def redBlockIndices (U : Finset ℕ) (blockColor : ℕ → Option I)
    (i : I) : Finset ℕ :=
  U.filter fun r ↦ blockColor r = some i

def redBlockUnion (C : List (Finset V)) (U : Finset ℕ)
    (blockColor : ℕ → Option I) (i : I) : Finset V :=
  (redBlockIndices U blockColor i).biUnion fun r ↦ C.getD r ∅

omit [DecidableRel G.Adj] [Fintype I] [Fintype V] in

lemma adjacent_block_of_adjacent_redBlockUnion
    (C : List (Finset V)) (U : Finset ℕ)
    (blockColor : ℕ → Option I) (i : I) {v : V}
    (h : AdjacentSets G {v} (redBlockUnion C U blockColor i)) :
    ∃ r ∈ U, blockColor r = some i ∧
      AdjacentSets G {v} (C.getD r ∅) := by
  rcases h with ⟨x, hx, y, hy, hxy⟩
  have hxv : x = v := by simpa using hx
  subst x
  rw [redBlockUnion, mem_biUnion] at hy
  obtain ⟨r, hr, hyr⟩ := hy
  rw [redBlockIndices, mem_filter] at hr
  exact ⟨r, hr.1, hr.2, v, by simp, y, hyr, hxy⟩

lemma adjacent_of_low_after_delete
    {B Z : Finset V} {k : ℕ} {v : V}
    (hk : 2 ≤ k) (hZB : Z ⊆ B) (_hv : v ∈ B \ Z)
    (hhigh : k ≤ degreeOn G B v)
    (hlow : degreeOn G (B \ Z) v ≤ k - 1) :
    AdjacentSets G {v} Z := by
  by_contra hnot
  have heq := degreeOn_sdiff_eq_of_not_adjacent (G := G) hZB hnot
  rw [heq] at hlow
  omega

lemma lowVertices_after_red_delete_subset_residual
    {A O Z P : Finset V} {k : ℕ}
    (phi : PartialColoring V k)
    (hk : 2 ≤ k)
    (hZ : Z ⊆ A \ O)
    (hmin : HasMinDegreeOn G (A \ O) k)
    (hneigh_uncolored : ∀ v ∈ A,
      AdjacentSets G {v} Z → phi v = none)
    (hprefix_anti : ∀ v ∈ P, ¬ AdjacentSets G {v} Z) :
    lowVertices G ((A \ O) \ Z) k ⊆
      A \ (coloredVertices A phi ∪ P) := by
  intro v hv
  have hvdata := mem_lowVertices.mp hv
  have hvB : v ∈ A \ O := (mem_sdiff.mp hvdata.1).1
  have hadj : AdjacentSets G {v} Z :=
    adjacent_of_low_after_delete (G := G) hk hZ hvdata.1
      (hmin.2 v hvB) hvdata.2
  have hvnone : phi v = none := hneigh_uncolored v (mem_sdiff.mp hvB).1 hadj
  refine mem_sdiff.mpr ⟨(mem_sdiff.mp hvB).1, ?_⟩
  intro hvbad
  rcases mem_union.mp hvbad with hvcolored | hvP
  · rw [mem_coloredVertices_iff] at hvcolored
    obtain ⟨_, i, hi⟩ := hvcolored
    rw [hvnone] at hi
    contradiction
  · exact hprefix_anti v hvP hadj

structure PerColorExtensionConclusion
    (C : ProtectedFamily G H k) (E : ExtensionCertificate G H k C)
    (Atilde : I → Finset V) where
  retained : I → Finset V
  X : I → Finset V
  deleted_eq : ∀ i, X i = Atilde i \ retained i
  retained_eq : ∀ i, retained i = Atilde i \ X i
  X_subset_H : ∀ i, X i ⊆ H
  X_subset_reserves : ∀ i, X i ⊆ reserveUnion E.reserve G (Atilde i) k
  incidence : ∀ i,
    incidentCount G (Atilde i) (X i) ≤ (k - 1) * (X i).card
  minDegree : ∀ i, HasMinDegreeOn G (retained i) k
  whole_blocks_deleted : ∀ i D, D ∈ C.blocks →
    D ⊆ X i ∨ Disjoint D (X i)
  retained_blocks_anticomplete : ∀ i D, D ∈ C.blocks →
    Disjoint D (X i) → Anticomplete G D (X i)
  disjoint_from_old : ∀ D, Disjoint D H → ∀ i, Disjoint D (X i)
  low_index_description : ∀ i x, x ∈ X i →
    ∃ v ∈ lowVertices G (Atilde i) k,
      x ∈ E.reserve v
  pairwise_X : ∀ i j, i ≠ j → Disjoint (X i) (X j)

omit [DecidableEq I] [Fintype I] in

theorem apply_extension_per_color
    {H : Finset V} {k : ℕ}
    (C : ProtectedFamily G H k) (E : ExtensionCertificate G H k C)
    (hk : 2 ≤ k)
    (Atilde : I → Finset V)
    (hH : ∀ i, H ⊆ Atilde i)
    (hproper : ∀ i, H ⊂ Atilde i)
    (hinside : ∀ i, lowVertices G (Atilde i) k ⊆ H)
    (hprotect : ∀ i s, s ∈ E.S → s ∈ Atilde i →
      k ≤ degreeOn G (Atilde i) s)
    (hnew : ∀ i D, D ∈ C.blocks →
      Anticomplete G (Atilde i \ H) D)
    (selectedBlocks : Finset (Finset V))
    (blockColor : Finset V → Option I)
    (hred : ∀ i v, v ∈ lowVertices G (Atilde i) k →
      (∃ D ∈ selectedBlocks, AdjacentSets G {v} D) ∧
      (∀ D ∈ selectedBlocks, AdjacentSets G {v} D →
        blockColor D = some i)) :
    Nonempty (PerColorExtensionConclusion C E Atilde) := by
  classical
  have hlow : ∀ i,
      lowVertices G (Atilde i) k ⊆ lowVertices G H k \ E.S := by
    intro i v hv
    have hvdata := mem_lowVertices.mp hv
    have hvH : v ∈ H := hinside i hv
    have hvlowH : degreeOn G H v ≤ k - 1 :=
      (degreeOn_mono G (hH i) v).trans hvdata.2
    refine mem_sdiff.mpr ⟨mem_lowVertices.mpr ⟨hvH, hvlowH⟩, ?_⟩
    intro hvS
    have hhigh := hprotect i v hvS hvdata.1
    omega
  have hext : ∀ i, ∃ U' : Finset V, ExtensionConclusion C E.reserve (Atilde i) U' := by
    intro i
    exact E.extension (Atilde i) (hproper i) (hlow i) (hnew i)
  let U' : I → Finset V := fun i ↦ Classical.choose (hext i)
  have hR : ∀ i, ExtensionConclusion C E.reserve (Atilde i) (U' i) :=
    fun i ↦ Classical.choose_spec (hext i)
  let X : I → Finset V := fun i ↦ Atilde i \ U' i
  have hret : ∀ i, U' i = Atilde i \ X i := by
    intro i
    ext x
    constructor
    · intro hx
      exact mem_sdiff.mpr ⟨(hR i).subset_extension hx, by
        intro hxX
        exact (mem_sdiff.mp hxX).2 hx⟩
    · intro hx
      rw [mem_sdiff] at hx
      by_contra hxU
      exact hx.2 (mem_sdiff.mpr ⟨hx.1, hxU⟩)
  have hXH : ∀ i, X i ⊆ H := fun i ↦ (hR i).deleted_subset_old
  have hXres : ∀ i, X i ⊆ reserveUnion E.reserve G (Atilde i) k :=
    fun i ↦ (hR i).deleted_subset_reserves
  have hindex_unique : ∀ i j v,
      v ∈ lowVertices G (Atilde i) k →
      v ∈ lowVertices G (Atilde j) k → i = j := by
    intro i j v hvi hvj
    obtain ⟨D, hDB, hvD⟩ := (hred i v hvi).1
    have hi := (hred i v hvi).2 D hDB hvD
    have hj := (hred j v hvj).2 D hDB hvD
    exact Option.some.inj (hi.symm.trans hj)
  have hpair : ∀ i j, i ≠ j → Disjoint (X i) (X j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    have hri := hXres i hxi
    have hrj := hXres j hxj
    rw [reserveUnion, mem_biUnion] at hri hrj
    obtain ⟨v, hvi, hxv⟩ := hri
    obtain ⟨w, hwj, hxw⟩ := hrj
    have hviOld := hlow i hvi
    have hwjOld := hlow j hwj
    have hvw : v = w := by
      by_contra hvw
      have hd := E.reserve_pairwise v hviOld w hwjOld hvw
      exact (Finset.disjoint_left.mp hd) hxv hxw
    subst w
    exact hij (hindex_unique i j v hvi hwj)
  refine ⟨{
    retained := U'
    X := X
    deleted_eq := fun _ ↦ rfl
    retained_eq := hret
    X_subset_H := hXH
    X_subset_reserves := hXres
    incidence := ?_
    minDegree := fun i ↦ (hR i).minDegree
    whole_blocks_deleted := ?_
    retained_blocks_anticomplete := ?_
    disjoint_from_old := ?_
    low_index_description := ?_
    pairwise_X := hpair }⟩
  · intro i
    exact incidentCount_deleted_le_of_shortage_le
      (hR i).subset_extension (hR i).shortage_le
  · intro i D hDC
    rcases (hR i).blocks_whole D hDC with hDU | hdisj
    · right
      rw [Finset.disjoint_left]
      intro x hxD hxX
      exact (mem_sdiff.mp hxX).2 (hDU hxD)
    · left
      intro x hxD
      refine mem_sdiff.mpr ⟨hH i (C.subset_ambient D hDC hxD), ?_⟩
      exact fun hxU ↦ Finset.disjoint_left.mp hdisj hxD hxU
  · intro i D hDC hDX
    apply (hR i).retained_blocks_anticomplete D hDC
    intro x hxD
    by_contra hxU
    have hxX : x ∈ X i :=
      mem_sdiff.mpr ⟨hH i (C.subset_ambient D hDC hxD), hxU⟩
    exact Finset.disjoint_left.mp hDX hxD hxX
  · intro D hDH i
    exact hDH.mono_right (hXH i)
  · intro i x hx
    have hr := hXres i hx
    rw [reserveUnion, mem_biUnion] at hr
    exact hr

omit [DecidableEq I] [Fintype I] in

lemma PerColorExtensionConclusion.whole_blocks_deleted_of_restriction
    {A H : Finset V} {k : ℕ}
    {C : ProtectedFamily G H k} {E : ExtensionCertificate G H k C}
    {Atilde : I → Finset V}
    (R : PerColorExtensionConclusion C E Atilde)
    (C₀ : ProtectedFamily G A k)
    (hwhole : C₀.WholeBlocks H)
    (hblocks : ∀ D, D ∈ C.blocks ↔ D ∈ C₀.blocks ∧ D ⊆ H) :
    ∀ i D, D ∈ C₀.blocks → D ⊆ R.X i ∨ Disjoint D (R.X i) := by
  intro i D hD
  rcases hwhole D hD with hDH | hDH
  · exact R.whole_blocks_deleted i D ((hblocks D).2 ⟨hD, hDH⟩)
  · exact Or.inr (hDH.mono_right (R.X_subset_H i))

section PopularScratch

variable {V Block Scope : Type*}
variable [Fintype V] [DecidableEq V]
variable [DecidableEq Block]
variable [DecidableEq Scope]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def currentUncoloredIndices
    (C : List (Finset V)) (phi : PartialColoring V k) (ell : ℕ) : Finset ℕ := by
  classical
  exact (Dyadic.levelIndices ell).filter fun r ↦
    BlockUncolored phi (C.getD r ∅)

omit [DecidableEq V] [Fintype V] in
@[simp] lemma card_currentUncoloredIndices
    (C : List (Finset V)) (phi : PartialColoring V k) (ell : ℕ) :
    (currentUncoloredIndices C phi ell).card =
      uncoloredBlockCount C phi ell := by
  rfl

def blockIndicesAdjacentTo
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : List (Finset V)) (U : Finset ℕ) (s : V) : Finset ℕ :=
  U.filter fun r ↦ ∃ v ∈ C.getD r ∅, G.Adj s v

def scopeNeed (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (k : ℕ) (s : V) : ℕ :=
  k + 1 - degreeOn G H s

lemma scopeNeed_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (k : ℕ) (s : V) : scopeNeed G H k s ≤ k + 1 := by
  exact Nat.sub_le _ _

noncomputable def selectedScope
    (adjacent : Scope → Finset Block) (need : Scope → ℕ)
    (s : Scope) : Finset Block := by
  classical
  exact Classical.choose
    (Finset.exists_subset_card_eq
      (s := adjacent s) (n := min (adjacent s).card (need s))
      (Nat.min_le_left _ _))

omit [DecidableEq Block] [DecidableEq Scope] in
lemma selectedScope_subset
    (adjacent : Scope → Finset Block) (need : Scope → ℕ) (s : Scope) :
    selectedScope adjacent need s ⊆ adjacent s := by
  classical
  exact (Classical.choose_spec
    (Finset.exists_subset_card_eq
      (s := adjacent s) (n := min (adjacent s).card (need s))
      (Nat.min_le_left _ _))).1

omit [DecidableEq Block] [DecidableEq Scope] in
lemma card_selectedScope
    (adjacent : Scope → Finset Block) (need : Scope → ℕ) (s : Scope) :
    (selectedScope adjacent need s).card = min (adjacent s).card (need s) := by
  classical
  exact (Classical.choose_spec
    (Finset.exists_subset_card_eq
      (s := adjacent s) (n := min (adjacent s).card (need s))
      (Nat.min_le_left _ _))).2

omit [DecidableEq Block] [DecidableEq Scope] in
lemma card_selectedScope_le_need
    (adjacent : Scope → Finset Block) (need : Scope → ℕ) (s : Scope) :
    (selectedScope adjacent need s).card ≤ need s := by
  rw [card_selectedScope]
  exact Nat.min_le_right _ _

omit [DecidableEq Block] [DecidableEq Scope] in
lemma selectedScope_eq_adjacent_of_card_lt_need
    (adjacent : Scope → Finset Block) (need : Scope → ℕ) (s : Scope)
    (h : (adjacent s).card < need s) :
    selectedScope adjacent need s = adjacent s := by
  classical
  apply Finset.eq_of_subset_of_card_le (selectedScope_subset adjacent need s)
  rw [card_selectedScope, Nat.min_eq_left (Nat.le_of_lt h)]

def scopeFrequency (S : Finset Scope) (scope : Scope → Finset Block)
    (D : Block) : ℕ :=
  (S.filter fun s ↦ D ∈ scope s).card

def IsPopular (S : Finset Scope) (scope : Scope → Finset Block)
    (D : Block) : Prop :=
  200 < scopeFrequency S scope D

instance instDecidablePredIsPopular
    (S : Finset Scope) (scope : Scope → Finset Block) :
    DecidablePred (IsPopular S scope) := by
  intro D
  unfold IsPopular scopeFrequency
  infer_instance

def popularBlocks (U : Finset Block) (S : Finset Scope)
    (scope : Scope → Finset Block) : Finset Block :=
  U.filter fun D ↦ IsPopular S scope D

def nonpopularBlocks (U : Finset Block) (S : Finset Scope)
    (scope : Scope → Finset Block) : Finset Block :=
  U \ popularBlocks U S scope

omit [DecidableEq Scope] in
lemma sum_card_scope_eq_sum_frequency
    (U : Finset Block) (S : Finset Scope) (scope : Scope → Finset Block)
    (hscope : ∀ s ∈ S, scope s ⊆ U) :
    ∑ s ∈ S, (scope s).card =
      ∑ D ∈ U, scopeFrequency S scope D := by
  classical
  calc
    ∑ s ∈ S, (scope s).card =
        ∑ s ∈ S, ∑ D ∈ U, if D ∈ scope s then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      have hi : U ∩ scope s = scope s :=
        Finset.inter_eq_right.mpr (hscope s hs)
      simp [hi]
    _ = ∑ D ∈ U, ∑ s ∈ S, if D ∈ scope s then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ D ∈ U, scopeFrequency S scope D := by
      apply Finset.sum_congr rfl
      intro D hDU
      rw [← Finset.sum_filter]
      simp [scopeFrequency]

omit [DecidableEq Scope] in
lemma popular_frequency_lower
    (U : Finset Block) (S : Finset Scope) (scope : Scope → Finset Block) :
    201 * (popularBlocks U S scope).card ≤
      ∑ D ∈ U, scopeFrequency S scope D := by
  classical
  calc
    201 * (popularBlocks U S scope).card =
        ∑ D ∈ popularBlocks U S scope, 201 := by
      simp [Nat.mul_comm]
    _ ≤ ∑ D ∈ popularBlocks U S scope, scopeFrequency S scope D := by
      apply Finset.sum_le_sum
      intro D hD
      have hp : IsPopular S scope D := by
        exact (Finset.mem_filter.mp (by simpa [popularBlocks] using hD)).2
      exact Nat.succ_le_iff.mpr hp
    _ ≤ ∑ D ∈ U, scopeFrequency S scope D := by
      apply Finset.sum_le_sum_of_subset
      intro D hD
      exact (Finset.mem_filter.mp (by simpa [popularBlocks] using hD)).1

omit [DecidableEq Scope] in
lemma four_mul_card_popular_le
    (U : Finset Block) (S : Finset Scope) (scope : Scope → Finset Block)
    (hscope : ∀ s ∈ S, scope s ⊆ U)
    (hsum : ∑ s ∈ S, (scope s).card ≤ 48 * U.card) :
    4 * (popularBlocks U S scope).card ≤ U.card := by
  have hlower := popular_frequency_lower U S scope
  rw [← sum_card_scope_eq_sum_frequency U S scope hscope] at hlower
  omega

omit [DecidableEq Block] [DecidableEq Scope] in
lemma sum_card_selectedScope_le
    (U : Finset Block) (S' S : Finset Scope)
    (adjacent : Scope → Finset Block) (need : Scope → ℕ)
    (hS : S' ⊆ S)
    (hneed : ∑ s ∈ S, need s ≤ 48 * U.card) :
    ∑ s ∈ S', (selectedScope adjacent need s).card ≤ 48 * U.card := by
  calc
    ∑ s ∈ S', (selectedScope adjacent need s).card ≤
        ∑ s ∈ S', need s := by
      exact Finset.sum_le_sum fun s hs ↦ card_selectedScope_le_need adjacent need s
    _ ≤ ∑ s ∈ S, need s := by
      exact Finset.sum_le_sum_of_subset hS
    _ ≤ 48 * U.card := hneed

def activeScopes (S : Finset Scope) (adjacent : Scope → Finset Block) :
    Finset Scope :=
  S.filter fun s ↦ (adjacent s).Nonempty

omit [DecidableEq Block] [DecidableEq Scope] in
lemma activeScopes_subset (S : Finset Scope) (adjacent : Scope → Finset Block) :
    activeScopes S adjacent ⊆ S :=
  Finset.filter_subset _ _

omit [DecidableEq Scope] in
theorem four_mul_card_popular_selectedScope_le
    (U : Finset Block) (S' S : Finset Scope)
    (adjacent : Scope → Finset Block) (need : Scope → ℕ)
    (hS : S' ⊆ S)
    (hadjacent : ∀ s ∈ S', adjacent s ⊆ U)
    (hneed : ∑ s ∈ S, need s ≤ 48 * U.card) :
    4 * (popularBlocks U S' (selectedScope adjacent need)).card ≤ U.card := by
  apply four_mul_card_popular_le U S' (selectedScope adjacent need)
  · intro s hs
    exact (selectedScope_subset adjacent need s).trans (hadjacent s hs)
  · exact sum_card_selectedScope_le U S' S adjacent need hS hneed

noncomputable def activeDeficitVertices
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : List (Finset V)) (U : Finset ℕ)
    (S : Finset V) : Finset V :=
  activeScopes S (blockIndicesAdjacentTo G C U)

noncomputable def vertexScope
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (C : List (Finset V)) (U : Finset ℕ)
    (k : ℕ) (s : V) : Finset ℕ :=
  selectedScope (blockIndicesAdjacentTo G C U) (scopeNeed G H k) s

lemma vertexScope_subset_adjacent
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (C : List (Finset V)) (U : Finset ℕ)
    (k : ℕ) (s : V) :
    vertexScope G H C U k s ⊆ blockIndicesAdjacentTo G C U s :=
  selectedScope_subset _ _ _

lemma vertexScope_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (C : List (Finset V)) (U : Finset ℕ)
    (k : ℕ) (s : V) : vertexScope G H C U k s ⊆ U := by
  exact (vertexScope_subset_adjacent G H C U k s).trans (Finset.filter_subset _ _)

lemma card_vertexScope
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (C : List (Finset V)) (U : Finset ℕ)
    (k : ℕ) (s : V) :
    (vertexScope G H C U k s).card =
      min (blockIndicesAdjacentTo G C U s).card (scopeNeed G H k s) :=
  card_selectedScope _ _ _

lemma card_vertexScope_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (C : List (Finset V)) (U : Finset ℕ)
    (k : ℕ) (s : V) : (vertexScope G H C U k s).card ≤ k + 1 := by
  exact (card_selectedScope_le_need _ _ _).trans (scopeNeed_le G H k s)

lemma vertexScope_eq_adjacent_of_card_lt_need
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (C : List (Finset V)) (U : Finset ℕ)
    (k : ℕ) (s : V)
    (h : (blockIndicesAdjacentTo G C U s).card < scopeNeed G H k s) :
    vertexScope G H C U k s = blockIndicesAdjacentTo G C U s :=
  selectedScope_eq_adjacent_of_card_lt_need _ _ _ h

def neighborColors (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    (phi : PartialColoring V k) (s : V) : Finset (Color k) :=
  Finset.univ.filter fun i ↦ ∃ v ∈ A, G.Adj s v ∧ phi v = some i

noncomputable def selectedNeighborColors
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (phi : PartialColoring V k)
    (s : V) : Finset (Color k) := by
  classical
  exact Classical.choose
    (Finset.exists_subset_card_eq
      (s := neighborColors G A phi s)
      (n := min (neighborColors G A phi s).card k)
      (Nat.min_le_left _ _))

omit [DecidableEq V] [Fintype V] in
lemma selectedNeighborColors_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (phi : PartialColoring V k)
    (s : V) :
    selectedNeighborColors G A phi s ⊆ neighborColors G A phi s := by
  classical
  exact (Classical.choose_spec
    (Finset.exists_subset_card_eq
      (s := neighborColors G A phi s)
      (n := min (neighborColors G A phi s).card k)
      (Nat.min_le_left _ _))).1

omit [DecidableEq V] [Fintype V] in
lemma card_selectedNeighborColors
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (phi : PartialColoring V k)
    (s : V) :
    (selectedNeighborColors G A phi s).card =
      min (neighborColors G A phi s).card k := by
  classical
  exact (Classical.choose_spec
    (Finset.exists_subset_card_eq
      (s := neighborColors G A phi s)
      (n := min (neighborColors G A phi s).card k)
      (Nat.min_le_left _ _))).2

omit [DecidableEq V] [Fintype V] in
lemma card_selectedNeighborColors_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (phi : PartialColoring V k)
    (s : V) :
    (selectedNeighborColors G A phi s).card ≤ k := by
  classical
  rw [card_selectedNeighborColors]
  exact Nat.min_le_right _ _

omit [DecidableEq V] [Fintype V] in
lemma selectedNeighborColors_eq_of_card_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (phi : PartialColoring V k)
    (s : V) (h : (neighborColors G A phi s).card ≤ k) :
    selectedNeighborColors G A phi s = neighborColors G A phi s := by
  classical
  apply Finset.eq_of_subset_of_card_le (selectedNeighborColors_subset G A phi s)
  rw [selectedNeighborColors]
  have hs := (Classical.choose_spec
    (Finset.exists_subset_card_eq
      (s := neighborColors G A phi s)
      (n := min (neighborColors G A phi s).card k)
      (Nat.min_le_left _ _))).2
  rw [hs, Nat.min_eq_left h]

section FiniteGreedy

def nonpopularScope
    (P : Finset Block) (S : Finset Scope) (scope : Scope → Finset Block)
    (s : Scope) : Finset {D // D ∈ P} :=
  Finset.univ.filter fun D ↦ s ∈ S ∧ (D : Block) ∈ scope s

lemma card_nonpopularScope_le
    (P : Finset Block) (S : Finset Scope) (scope : Scope → Finset Block)
    (s : Scope) :
    (nonpopularScope P S scope s).card ≤ (scope s).card := by
  classical
  let f : {D // D ∈ P} → Block := fun D ↦ D
  have hinj : Set.InjOn f (nonpopularScope P S scope s : Set {D // D ∈ P}) :=
    fun _ _ _ _ h ↦ Subtype.ext h
  have hcard : (nonpopularScope P S scope s).card =
      ((nonpopularScope P S scope s).image f).card := by
    rw [Finset.card_image_iff.mpr]
    intro x hx y hy hxy
    exact Subtype.ext hxy
  rw [hcard]
  apply Finset.card_le_card
  intro D hD
  rw [Finset.mem_image] at hD
  obtain ⟨x, hx, rfl⟩ := hD
  exact (Finset.mem_filter.mp hx).2.2

variable [Finite Scope]

theorem exists_nonpopular_scope_coloring
    {k : ℕ} (hk : 0 < k)
    (U : Finset Block) (S : Finset Scope) (scope : Scope → Finset Block)
    (avoid : Scope → Finset (Color k))
    (_hscopeU : ∀ s ∈ S, scope s ⊆ U)
    (hscope : ∀ s ∈ S, (scope s).card ≤ k + 1)
    (havoid : ∀ s, (avoid s).card ≤ k) :
    ∃ color : {D // D ∈ nonpopularBlocks U S scope} → Color k,
      (∀ s : Scope, Set.InjOn color
        (nonpopularScope (nonpopularBlocks U S scope) S scope s :
          Set {D // D ∈ nonpopularBlocks U S scope})) ∧
      (∀ s : Scope, ∀ D ∈
        nonpopularScope (nonpopularBlocks U S scope) S scope s,
        color D ∉ avoid s) := by
  classical
  let := Fintype.ofFinite Scope
  apply exists_erdos814_scope_coloring hk
  · intro D
    have hnonpop : ¬ IsPopular S scope (D : Block) := by
      have hD := D.property
      change (D : Block) ∈ U \ popularBlocks U S scope at hD
      rw [Finset.mem_sdiff] at hD
      exact fun hp ↦ hD.2 (by
        simpa [popularBlocks] using (Finset.mem_filter.mpr ⟨hD.1, hp⟩))
    have heq :
        (Finset.univ.filter fun s : Scope ↦
          D ∈ nonpopularScope (nonpopularBlocks U S scope) S scope s) =
        S.filter fun s ↦ (D : Block) ∈ scope s := by
      ext s
      simp [nonpopularScope]
    rw [heq]
    simpa [IsPopular, scopeFrequency] using (Nat.le_of_not_gt hnonpop)
  · intro s
    by_cases hs : s ∈ S
    · exact (card_nonpopularScope_le _ _ _ s).trans (hscope s hs)
    · simp [nonpopularScope, hs]
  · exact havoid

omit [DecidableEq V] [Fintype V] in
theorem exists_nonpopular_scope_coloring_with_neighbor_lists
    {k : ℕ} (hk : 0 < k)
    (U : Finset Block) (S : Finset Scope) (scope : Scope → Finset Block)
    (A : Finset V) (phi : PartialColoring V k) (atVertex : Scope → V)
    (hscopeU : ∀ s ∈ S, scope s ⊆ U)
    (hscope : ∀ s ∈ S, (scope s).card ≤ k + 1) :
    ∃ color : {D // D ∈ nonpopularBlocks U S scope} → Color k,
      (∀ s : Scope, Set.InjOn color
        (nonpopularScope (nonpopularBlocks U S scope) S scope s :
          Set {D // D ∈ nonpopularBlocks U S scope})) ∧
      (∀ s : Scope, ∀ D ∈
        nonpopularScope (nonpopularBlocks U S scope) S scope s,
        color D ∉ selectedNeighborColors G A phi (atVertex s)) := by
  exact exists_nonpopular_scope_coloring hk U S scope
    (fun s ↦ selectedNeighborColors G A phi (atVertex s))
    hscopeU hscope (fun s ↦ card_selectedNeighborColors_le G A phi (atVertex s))

end FiniteGreedy

end PopularScratch

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] [Fintype V] in
lemma adjacent_cut_of_connectedOn
    {A D : Finset V} (hconn : ConnectedOn G A)
    (hD : D.Nonempty) (hDA : D ⊆ A) (hcomp : (A \ D).Nonempty) :
    AdjacentSets G D (A \ D) := by
  classical
  obtain ⟨u, huD⟩ := hD
  obtain ⟨v, hvAD⟩ := hcomp
  have huA : u ∈ A := hDA huD
  have hvA : v ∈ A := (mem_sdiff.mp hvAD).1
  let uA : (↑A : Set V) := ⟨u, huA⟩
  let vA : (↑A : Set V) := ⟨v, hvA⟩
  change (G.induce (↑A : Set V)).Connected at hconn
  obtain ⟨p⟩ := hconn.preconnected uA vA
  obtain ⟨d, _hdp, hdD, hdnotD⟩ :=
    p.exists_boundary_dart {x : (↑A : Set V) | (x : V) ∈ D}
      (by simpa [uA] using huD) (by simpa [vA] using (mem_sdiff.mp hvAD).2)
  refine ⟨(d.toProd.1 : V), hdD, (d.toProd.2 : V), ?_, ?_⟩
  · exact mem_sdiff.mpr ⟨d.toProd.2.property, hdnotD⟩
  · exact d.adj

lemma deficitResidual_nonempty
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hellJ : ell < J)
    (hlarge : 2 ^ ell < 4 * uncoloredBlockCount C phi ell) :
    (deficitResidual A C phi (ell + 1)).Nonempty := by
  classical
  have hpow : 0 < 2 ^ ell := pow_pos (by omega) ell
  have hcount : 0 < uncoloredBlockCount C phi ell := by omega
  have hindices : (uncoloredCurrentIndices C phi ell).Nonempty := by
    simpa [uncoloredCurrentIndices, uncoloredBlockCount] using hcount
  obtain ⟨r, hrU⟩ := hindices
  have hrData : r ∈ Dyadic.levelIndices ell ∧
      BlockUncolored phi (C.getD r ∅) := by
    simpa [uncoloredCurrentIndices] using hrU
  have hrRange := (Dyadic.mem_levelIndices.mp hrData.1)
  have hellSuccJ : ell + 1 ≤ J := Nat.succ_le_iff.mpr hellJ
  have hrJ : r < Dyadic.levelStart J :=
    hrRange.2.trans_le (Dyadic.levelStart_mono hellSuccJ)
  let D := C.getD r ∅
  have hDne : D.Nonempty := S.block_nonempty r hrJ
  have hDA : D ⊆ A := S.block_subset r hrJ
  have hcomp : (A \ D).Nonempty := (S.block_complement_minDegree r hrJ).1
  obtain ⟨v, hvD, w, hwAD, hvw⟩ :=
    adjacent_cut_of_connectedOn (G := G) S.connected hDne hDA hcomp
  have hwA : w ∈ A := (mem_sdiff.mp hwAD).1
  have hwD : w ∉ D := (mem_sdiff.mp hwAD).2
  have hwnone : phi w = none :=
    hphi.future r hrRange.1 hrJ hrData.2 v hvD w hwA hvw
  refine ⟨w, mem_sdiff.mpr ⟨hwA, ?_⟩⟩
  rw [mem_union]
  push Not
  constructor
  · intro hwColored
    rw [mem_coloredVertices_iff] at hwColored
    obtain ⟨_, i, hi⟩ := hwColored
    rw [hwnone] at hi
    contradiction
  · intro hwPrefix
    rw [uncoloredPrefixUnion, mem_biUnion] at hwPrefix
    obtain ⟨s, hsPrefix, hws⟩ := hwPrefix
    have hsData : s ∈ Finset.range (Dyadic.levelStart (ell + 1)) ∧
        BlockUncolored phi (C.getD s ∅) := by
      simpa [uncoloredPrefixIndices] using hsPrefix
    have hsJ : s < Dyadic.levelStart J :=
      (mem_range.mp hsData.1).trans_le (Dyadic.levelStart_mono hellSuccJ)
    by_cases hrs : r = s
    · subst s
      exact hwD hws
    · exact S.blocks_anticomplete r hrJ s hsJ hrs ⟨v, hvD, w, hws, hvw⟩

noncomputable def residualFutureIndices
    (A : Finset V) (C : List (Finset V))
    (phi : PartialColoring V k) (ell J : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico (Dyadic.levelStart (ell + 1)) (Dyadic.levelStart J)).filter
    fun r ↦ C.getD r ∅ ⊆ deficitResidual A C phi (ell + 1)

omit [Fintype V] in
lemma blockUncolored_of_subset_deficitResidual
    {A D : Finset V} {C : List (Finset V)} {phi : PartialColoring V k}
    {ell : ℕ} (hD : D ⊆ deficitResidual A C phi (ell + 1)) :
    BlockUncolored phi D := by
  intro v hv
  have hvH := hD hv
  have hvA : v ∈ A := (mem_sdiff.mp hvH).1
  have hvnotColored : v ∉ coloredVertices A phi := by
    intro hvColored
    exact (mem_sdiff.mp hvH).2 (mem_union_left _ hvColored)
  cases hphi : phi v with
  | none => rfl
  | some i =>
      exact False.elim <| hvnotColored <|
        mem_coloredVertices_iff.mpr ⟨hvA, i, hphi⟩

lemma future_block_neighbor_closed_in_deficitResidual
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J r : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hrStart : Dyadic.levelStart (ell + 1) ≤ r)
    (hrJ : r < Dyadic.levelStart J)
    (hD : C.getD r ∅ ⊆ deficitResidual A C phi (ell + 1)) :
    ∀ {x}, x ∈ C.getD r ∅ → ∀ {y}, y ∈ A → G.Adj x y →
      y ∈ deficitResidual A C phi (ell + 1) := by
  classical
  have hrun : BlockUncolored phi (C.getD r ∅) :=
    blockUncolored_of_subset_deficitResidual hD
  intro x hx y hyA hxy
  have hynone : phi y = none :=
    hphi.future r (Dyadic.levelStart_le_succ ell |>.trans hrStart) hrJ hrun
      x hx y hyA hxy
  refine mem_sdiff.mpr ⟨hyA, ?_⟩
  rw [mem_union]
  push Not
  constructor
  · intro hyColored
    rw [mem_coloredVertices_iff] at hyColored
    obtain ⟨_, i, hi⟩ := hyColored
    rw [hynone] at hi
    contradiction
  · intro hyPrefix
    rw [uncoloredPrefixUnion, mem_biUnion] at hyPrefix
    obtain ⟨s, hsPrefix, hys⟩ := hyPrefix
    have hsData : s ∈ Finset.range (Dyadic.levelStart (ell + 1)) ∧
        BlockUncolored phi (C.getD s ∅) := by
      simpa [uncoloredPrefixIndices] using hsPrefix
    have hslt : s < Dyadic.levelStart (ell + 1) := mem_range.mp hsData.1
    have hsJ : s < Dyadic.levelStart J :=
      hslt.trans_le (hrStart.trans hrJ.le)
    have hrs : r ≠ s := by omega
    exact S.blocks_anticomplete r hrJ s hsJ hrs ⟨x, hx, y, hys, hxy⟩

noncomputable def residualProtectedFamily
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi) :
    ProtectedFamily G (deficitResidual A C phi (ell + 1)) k := by
  classical
  let H := deficitResidual A C phi (ell + 1)
  let R := residualFutureIndices A C phi ell J
  let block : ℕ → Finset V := fun r ↦ C.getD r ∅
  refine
    { blocks := R.image block
      nonempty := ?_
      subset_ambient := ?_
      pairwise_disjoint := ?_
      high_degree := ?_
      incident_le := ?_ }
  · intro D hD
    rw [mem_image] at hD
    obtain ⟨r, hrR, rfl⟩ := hD
    have hrIco : r ∈ Finset.Ico (Dyadic.levelStart (ell + 1))
        (Dyadic.levelStart J) := (mem_filter.mp hrR).1
    exact S.block_nonempty r (mem_Ico.mp hrIco).2
  · intro D hD
    rw [mem_image] at hD
    obtain ⟨r, hrR, rfl⟩ := hD
    exact (mem_filter.mp hrR).2
  · intro D hD E hE hDE
    rw [mem_image] at hD hE
    obtain ⟨r, hrR, rfl⟩ := hD
    obtain ⟨s, hsR, rfl⟩ := hE
    have hrIco := mem_Ico.mp (mem_filter.mp hrR).1
    have hsIco := mem_Ico.mp (mem_filter.mp hsR).1
    have hrs : r ≠ s := by
      intro hrs
      subst s
      exact hDE rfl
    exact S.blocks_disjoint r hrIco.2 s hsIco.2 hrs
  · intro D hD x hx
    rw [mem_image] at hD
    obtain ⟨r, hrR, rfl⟩ := hD
    have hrIco := mem_Ico.mp (mem_filter.mp hrR).1
    have hDsub : C.getD r ∅ ⊆ H := (mem_filter.mp hrR).2
    have hclosed : ∀ {z}, z ∈ C.getD r ∅ → ∀ {y}, y ∈ A → G.Adj z y → y ∈ H :=
      future_block_neighbor_closed_in_deficitResidual
        S hphi hrIco.1 hrIco.2 hDsub
    have hdegEq : degreeOn G H x = degreeOn G A x := by
      unfold degreeOn
      congr 1
      ext y
      simp only [mem_inter, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨hxy, hyH⟩
        exact ⟨hxy, sdiff_subset hyH⟩
      · rintro ⟨hxy, hyA⟩
        exact ⟨hxy, hclosed hx hyA hxy⟩
    change k ≤ degreeOn G H x
    rw [hdegEq]
    exact S.minDegree.2 x (sdiff_subset (hDsub hx))
  · intro D hD
    rw [mem_image] at hD
    obtain ⟨r, hrR, rfl⟩ := hD
    have hrIco := mem_Ico.mp (mem_filter.mp hrR).1
    exact (incidentCount_ambient_mono (G := G) (A := H) (B := A)
      sdiff_subset).trans (S.block_incident r hrIco.2)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

def selectedBlockUnion (C : List (Finset V)) (N : Finset ℕ)
    (psi : ℕ → Color k) (i : Color k) : Finset V :=
  (N.filter fun r ↦ psi r = i).biUnion fun r ↦ C.getD r ∅

def assembledNewClass (C : List (Finset V)) (N : Finset ℕ)
    (psi : ℕ → Color k) (X : Color k → Finset V) (i : Color k) : Finset V :=
  selectedBlockUnion C N psi i ∪ X i

noncomputable def assembleColoring (phi : PartialColoring V k)
    (C : List (Finset V)) (N : Finset ℕ) (psi : ℕ → Color k)
    (X : Color k → Finset V) : PartialColoring V k :=
  fun v ↦
    if (phi v).isSome then phi v
    else if h : ∃ i, v ∈ assembledNewClass C N psi X i then
      some (Classical.choose h)
    else none

omit [Fintype V] in
@[simp] lemma assembleColoring_eq_some_of_old
    {phi : PartialColoring V k} {C : List (Finset V)} {N : Finset ℕ}
    {psi : ℕ → Color k} {X : Color k → Finset V} {v : V} {i : Color k}
    (h : phi v = some i) : assembleColoring phi C N psi X v = some i := by
  simp [assembleColoring, h]

omit [Fintype V] in
lemma assembleColoring_eq_none_of_old_none_of_new
    {phi : PartialColoring V k} {C : List (Finset V)} {N : Finset ℕ}
    {psi : ℕ → Color k} {X : Color k → Finset V} {v : V}
    (hphi : phi v = none)
    (hnew : ∀ i, v ∉ assembledNewClass C N psi X i) :
    assembleColoring phi C N psi X v = none := by
  simp [assembleColoring, hphi, hnew]

omit [Fintype V] in
lemma assembleColoring_eq_some_of_new
    {phi : PartialColoring V k} {C : List (Finset V)} {N : Finset ℕ}
    {psi : ℕ → Color k} {X : Color k → Finset V} {v : V} {i : Color k}
    (hphi : phi v = none)
    (hpair : ∀ i j, i ≠ j →
      Disjoint (assembledNewClass C N psi X i) (assembledNewClass C N psi X j))
    (hv : v ∈ assembledNewClass C N psi X i) :
    assembleColoring phi C N psi X v = some i := by
  have hex : ∃ j, v ∈ assembledNewClass C N psi X j := ⟨i, hv⟩
  have hvj : v ∈ assembledNewClass C N psi X (Classical.choose hex) :=
    Classical.choose_spec hex
  have hchoice : Classical.choose hex = i := by
    by_contra hne
    exact (Finset.disjoint_left.mp (hpair (Classical.choose hex) i hne)) hvj hv
  simp [assembleColoring, hphi, hex, hchoice]

omit [Fintype V] in
lemma assembleColoring_eq_some_iff
    {phi : PartialColoring V k} {C : List (Finset V)} {N : Finset ℕ}
    {psi : ℕ → Color k} {X : Color k → Finset V} {v : V} {i : Color k}
    (hpair : ∀ i j, i ≠ j →
      Disjoint (assembledNewClass C N psi X i) (assembledNewClass C N psi X j))
    (_huncolored : ∀ i, ∀ v ∈ assembledNewClass C N psi X i, phi v = none) :
    assembleColoring phi C N psi X v = some i ↔
      phi v = some i ∨ (phi v = none ∧ v ∈ assembledNewClass C N psi X i) := by
  constructor
  · intro hrho
    by_cases hp : phi v = none
    · right
      refine ⟨hp, ?_⟩
      by_cases h : ∃ j, v ∈ assembledNewClass C N psi X j
      · have hchoice : Classical.choose h = i := by
          have hs : some (Classical.choose h) = some i := by
            simpa [assembleColoring, hp, h] using hrho
          exact Option.some.inj hs
        simpa [hchoice] using Classical.choose_spec h
      · simp [assembleColoring, hp, h] at hrho
    · left
      obtain ⟨j, hj⟩ := Option.ne_none_iff_exists'.mp hp
      have hji : j = i := by
        have hs : some j = some i := by simpa [assembleColoring, hj] using hrho
        exact Option.some.inj hs
      simpa [hji] using hj
  · rintro (hold | ⟨hnone, hnew⟩)
    · exact assembleColoring_eq_some_of_old hold
    · exact assembleColoring_eq_some_of_new hnone hpair hnew

omit [Fintype V] in
lemma selectedBlock_subset_selectedBlockUnion
    {C : List (Finset V)} {N : Finset ℕ} {psi : ℕ → Color k}
    {r : ℕ} (hr : r ∈ N) :
    C.getD r ∅ ⊆ selectedBlockUnion C N psi (psi r) := by
  intro v hv
  rw [selectedBlockUnion, mem_biUnion]
  exact ⟨r, mem_filter.mpr ⟨hr, rfl⟩, hv⟩

omit [Fintype V] in
lemma selectedBlock_mono_assembleColoring
    {phi : PartialColoring V k} {C : List (Finset V)} {N : Finset ℕ}
    {psi : ℕ → Color k} {X : Color k → Finset V} {r : ℕ}
    (hr : r ∈ N)
    (hphi : BlockUncolored phi (C.getD r ∅))
    (hpair : ∀ i j, i ≠ j →
      Disjoint (assembledNewClass C N psi X i) (assembledNewClass C N psi X j)) :
    Monochromatic (assembleColoring phi C N psi X) (C.getD r ∅) (psi r) := by
  intro v hv
  apply assembleColoring_eq_some_of_new (hphi v hv) hpair
  exact mem_union_left _ (selectedBlock_subset_selectedBlockUnion hr hv)

structure AssemblyInput
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (C : List (Finset V))
    (J0 ell J : ℕ) (phi : PartialColoring V k) where
  Uidx : Finset ℕ
  N : Finset ℕ
  psi : ℕ → Color k
  X : Color k → Finset V
  Uidx_eq : Uidx = uncoloredCurrentIndices C phi ell
  N_subset_Uidx : N ⊆ Uidx
  selected_nonempty : ∀ r ∈ N, (C.getD r ∅).Nonempty
  new_pairwise : ∀ i j, i ≠ j →
    Disjoint (assembledNewClass C N psi X i)
      (assembledNewClass C N psi X j)
  new_subset : ∀ i, assembledNewClass C N psi X i ⊆ A
  new_uncolored : ∀ i, ∀ v ∈ assembledNewClass C N psi X i,
    phi v = none
  Z_X_disjoint : ∀ i, Disjoint (selectedBlockUnion C N psi i) (X i)
  whole_X : ∀ r < Dyadic.levelStart J, ∀ i,
    C.getD r ∅ ⊆ X i ∨ Disjoint (C.getD r ∅) (X i)
  unselected_disjoint_Z : ∀ r < Dyadic.levelStart J, r ∉ N → ∀ i,
    Disjoint (C.getD r ∅) (selectedBlockUnion C N psi i)
  early_disjoint_new : ∀ r < Dyadic.levelStart J0, ∀ i,
    Disjoint (C.getD r ∅) (assembledNewClass C N psi X i)
  quarter_bound : 4 * (Uidx.card - N.card) ≤ 2 ^ ell
  block_incidence : ∀ i,
    incidentCount G (A \ colorClass A phi i) (selectedBlockUnion C N psi i) ≤
      (k - 1) * (selectedBlockUnion C N psi i).card +
        (N.filter fun r ↦ psi r = i).card
  removed_incidence : ∀ i,
    incidentCount G ((A \ colorClass A phi i) \ selectedBlockUnion C N psi i)
        (X i) ≤ (k - 1) * (X i).card
  retained_core : ∀ i,
    HasMinDegreeOn G (A \ (colorClass A phi i ∪
      (selectedBlockUnion C N psi i ∪ X i))) k
  future_Z_anticomplete : ∀ r,
    Dyadic.levelStart (ell + 1) ≤ r → r < Dyadic.levelStart J → ∀ i,
      ¬ AdjacentSets G (C.getD r ∅) (selectedBlockUnion C N psi i)
  future_X_anticomplete : ∀ r,
    Dyadic.levelStart (ell + 1) ≤ r → r < Dyadic.levelStart J → ∀ i,
      BlockUncolored phi (C.getD r ∅) →
      Disjoint (C.getD r ∅) (X i) →
        ¬ AdjacentSets G (C.getD r ∅) (X i)

namespace AssemblyInput

variable {A : Finset V} {k J0 ell J : ℕ} {C : List (Finset V)}
variable {phi : PartialColoring V k}

abbrev Z (d : AssemblyInput G A k C J0 ell J phi) (i : Color k) : Finset V :=
  selectedBlockUnion C d.N d.psi i

abbrev newClass (d : AssemblyInput G A k C J0 ell J phi)
    (i : Color k) : Finset V := assembledNewClass C d.N d.psi d.X i

abbrev rho (d : AssemblyInput G A k C J0 ell J phi) : PartialColoring V k :=
  assembleColoring phi C d.N d.psi d.X

lemma refines (d : AssemblyInput G A k C J0 ell J phi) :
    Extends phi d.rho := by
  intro v i hvi
  exact assembleColoring_eq_some_of_old hvi

lemma rho_eq_some_iff (d : AssemblyInput G A k C J0 ell J phi)
    {v : V} {i : Color k} :
    d.rho v = some i ↔ phi v = some i ∨ (phi v = none ∧ v ∈ d.newClass i) :=
  assembleColoring_eq_some_iff d.new_pairwise d.new_uncolored

lemma class_eq (d : AssemblyInput G A k C J0 ell J phi) (i : Color k) :
    colorClass A d.rho i = colorClass A phi i ∪ (d.Z i ∪ d.X i) := by
  ext v
  simp only [colorClass, mem_filter, mem_union]
  constructor
  · rintro ⟨hvA, hv⟩
    rw [d.rho_eq_some_iff] at hv
    rcases hv with hold | ⟨_, hnew⟩
    · exact Or.inl ⟨hvA, hold⟩
    · right
      simpa [newClass, assembledNewClass, Z] using hnew
  · rintro (hold | hnew)
    · exact ⟨hold.1, assembleColoring_eq_some_of_old hold.2⟩
    · have hnew' : v ∈ d.newClass i := by
        simpa [newClass, assembledNewClass, Z] using hnew
      have hvA := d.new_subset i hnew'
      have hvnone := d.new_uncolored i v hnew'
      exact ⟨hvA, assembleColoring_eq_some_of_new hvnone d.new_pairwise hnew'⟩

lemma old_disjoint_new (d : AssemblyInput G A k C J0 ell J phi) (i : Color k) :
    Disjoint (colorClass A phi i) (d.newClass i) := by
  rw [Finset.disjoint_left]
  intro v hvold hvnew
  have hold : phi v = some i := (mem_filter.mp hvold).2
  have hnone : phi v = none := d.new_uncolored i v hvnew
  rw [hnone] at hold
  contradiction

lemma class_card (d : AssemblyInput G A k C J0 ell J phi) (i : Color k) :
    (colorClass A d.rho i).card =
      (colorClass A phi i).card + (d.Z i).card + (d.X i).card := by
  rw [d.class_eq i]
  change (colorClass A phi i ∪ d.newClass i).card =
    (colorClass A phi i).card + (d.Z i).card + (d.X i).card
  rw [Finset.card_union_of_disjoint (d.old_disjoint_new i)]
  have hzx : (d.newClass i).card = (d.Z i).card + (d.X i).card := by
    change (d.Z i ∪ d.X i).card = (d.Z i).card + (d.X i).card
    exact Finset.card_union_of_disjoint (d.Z_X_disjoint i)
  omega

lemma support (d : AssemblyInput G A k C J0 ell J phi)
    (hphi : Appropriate G A k C J0 ell J phi) :
    ∀ v, v ∉ A → d.rho v = none := by
  intro v hvA
  apply assembleColoring_eq_none_of_old_none_of_new (hphi.support v hvA)
  intro i hvi
  exact hvA (d.new_subset i hvi)

lemma selected_mono (d : AssemblyInput G A k C J0 ell J phi)
    {r : ℕ} (hr : r ∈ d.N) :
    Monochromatic d.rho (C.getD r ∅) (d.psi r) := by
  classical
  have hrU : r ∈ uncoloredCurrentIndices C phi ell := by
    rw [← d.Uidx_eq]
    exact d.N_subset_Uidx hr
  have hrun : BlockUncolored phi (C.getD r ∅) := by
    exact (mem_filter.mp hrU).2
  exact selectedBlock_mono_assembleColoring hr hrun d.new_pairwise

lemma block_status (d : AssemblyInput G A k C J0 ell J phi)
    (hphi : Appropriate G A k C J0 ell J phi) :
    ∀ r < Dyadic.levelStart J,
      IsMonochromatic d.rho (C.getD r ∅) ∨ BlockUncolored d.rho (C.getD r ∅) := by
  intro r hr
  rcases hphi.blocks r hr with ⟨i, hi⟩ | hu
  · left
    exact ⟨i, fun v hv ↦ d.refines v i (hi v hv)⟩
  · by_cases hrN : r ∈ d.N
    · exact Or.inl ⟨d.psi r, d.selected_mono hrN⟩
    · by_cases hcontained : ∃ i, C.getD r ∅ ⊆ d.X i
      · obtain ⟨i, hi⟩ := hcontained
        left
        refine ⟨i, ?_⟩
        intro v hv
        apply assembleColoring_eq_some_of_new (hu v hv) d.new_pairwise
        exact mem_union_right _ (hi hv)
      · right
        intro v hv
        apply assembleColoring_eq_none_of_old_none_of_new (hu v hv)
        intro i hvi
        rcases mem_union.mp hvi with hviZ | hviX
        · exact (Finset.disjoint_left.mp (d.unselected_disjoint_Z r hr hrN i)) hv hviZ
        · have hdisj : Disjoint (C.getD r ∅) (d.X i) :=
            (d.whole_X r hr i).resolve_left (fun hsub ↦ hcontained ⟨i, hsub⟩)
          exact (Finset.disjoint_left.mp hdisj) hv hviX

lemma early (d : AssemblyInput G A k C J0 ell J phi)
    (hphi : Appropriate G A k C J0 ell J phi) :
    ∀ r < Dyadic.levelStart J0, BlockUncolored d.rho (C.getD r ∅) := by
  intro r hr v hv
  apply assembleColoring_eq_none_of_old_none_of_new (hphi.early r hr v hv)
  intro i hvi
  exact (Finset.disjoint_left.mp (d.early_disjoint_new r hr i)) hv hvi

lemma quarter (d : AssemblyInput G A k C J0 ell J phi) :
    4 * uncoloredBlockCount C d.rho ell ≤ 2 ^ ell := by
  classical
  let R := (Dyadic.levelIndices ell).filter fun r ↦
    BlockUncolored d.rho (C.getD r ∅)
  have hsub : R ⊆ d.Uidx \ d.N := by
    intro r hr
    have hrdata := mem_filter.mp hr
    have hOld : BlockUncolored phi (C.getD r ∅) :=
      d.refines.blockUncolored hrdata.2
    have hrU : r ∈ d.Uidx := by
      rw [d.Uidx_eq]
      exact mem_filter.mpr ⟨hrdata.1, hOld⟩
    refine mem_sdiff.mpr ⟨hrU, ?_⟩
    intro hrN
    obtain ⟨v, hv⟩ := d.selected_nonempty r hrN
    have hm := d.selected_mono hrN v hv
    have hu := hrdata.2 v hv
    rw [hu] at hm
    contradiction
  have hc : R.card ≤ d.Uidx.card - d.N.card := by
    have := card_le_card hsub
    rwa [card_sdiff_of_subset d.N_subset_Uidx] at this
  have hfinal := (Nat.mul_le_mul_left 4 hc).trans d.quarter_bound
  simpa [R, uncoloredBlockCount] using hfinal

lemma block_count_gain (d : AssemblyInput G A k C J0 ell J phi)
    (i : Color k) :
    monochromaticBlockCount C phi ell i + (d.N.filter fun r ↦ d.psi r = i).card ≤
      monochromaticBlockCount C d.rho (ell + 1) i := by
  classical
  let M := (Finset.range (Dyadic.levelStart ell)).filter fun r ↦
    Monochromatic phi (C.getD r ∅) i
  let P := d.N.filter fun r ↦ d.psi r = i
  let M' := (Finset.range (Dyadic.levelStart (ell + 1))).filter fun r ↦
    Monochromatic d.rho (C.getD r ∅) i
  have hdisj : Disjoint M P := by
    rw [Finset.disjoint_left]
    intro r hrM hrP
    have hrM' := by
      simpa only [M] using (mem_filter.mp (show r ∈
        (Finset.range (Dyadic.levelStart ell)).filter fun r ↦
          Monochromatic phi (C.getD r ∅) i from hrM))
    have hrN : r ∈ d.N := (mem_filter.mp hrP).1
    have hrU : r ∈ uncoloredCurrentIndices C phi ell := by
      rw [← d.Uidx_eq]
      exact d.N_subset_Uidx hrN
    have hrlev := (mem_filter.mp hrU).1
    have hrlower := (Dyadic.mem_levelIndices.mp hrlev).1
    exact (Nat.not_lt_of_ge hrlower) (mem_range.mp hrM'.1)
  have hsub : M ∪ P ⊆ M' := by
    intro r hr
    rcases mem_union.mp hr with hrM | hrP
    · have hrM' := by
        simpa only [M] using (mem_filter.mp (show r ∈
          (Finset.range (Dyadic.levelStart ell)).filter fun r ↦
            Monochromatic phi (C.getD r ∅) i from hrM))
      refine mem_filter.mpr ⟨?_, ?_⟩
      · exact mem_range.mpr ((mem_range.mp hrM'.1).trans_le
          (Dyadic.levelStart_le_succ ell))
      · intro v hv
        exact d.refines v i (hrM'.2 v hv)
    · have hrP' := mem_filter.mp hrP
      have hrU : r ∈ uncoloredCurrentIndices C phi ell := by
        rw [← d.Uidx_eq]
        exact d.N_subset_Uidx hrP'.1
      have hrlev := (mem_filter.mp hrU).1
      refine mem_filter.mpr ⟨?_, ?_⟩
      · exact mem_range.mpr (Dyadic.mem_levelIndices.mp hrlev).2
      · simpa [hrP'.2] using d.selected_mono hrP'.1
  have hcard : M.card + P.card ≤ M'.card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact card_le_card hsub
  simpa [M, P, M', monochromaticBlockCount] using hcard

lemma future_anticomplete (d : AssemblyInput G A k C J0 ell J phi) :
    ∀ r, Dyadic.levelStart (ell + 1) ≤ r → r < Dyadic.levelStart J →
      BlockUncolored d.rho (C.getD r ∅) → ∀ i,
        ¬ AdjacentSets G (C.getD r ∅) (d.Z i ∪ d.X i) := by
  intro r hr hJ hrun i hadj
  have hrunOld : BlockUncolored phi (C.getD r ∅) :=
    d.refines.blockUncolored hrun
  have hdisjX : Disjoint (C.getD r ∅) (d.X i) := by
    rcases d.whole_X r hJ i with hsub | hdisj
    · obtain ⟨v, hv⟩ : (C.getD r ∅).Nonempty := by

        obtain ⟨v, hv, w, hw, hvw⟩ := hadj
        exact ⟨v, hv⟩
      have hm : d.rho v = some i :=
        assembleColoring_eq_some_of_new (hrunOld v hv) d.new_pairwise
          (mem_union_right _ (hsub hv))
      rw [hrun v hv] at hm
      contradiction
    · exact hdisj
  obtain ⟨v, hv, w, hw, hvw⟩ := hadj
  rcases mem_union.mp hw with hwZ | hwX
  · exact d.future_Z_anticomplete r hr hJ i ⟨v, hv, w, hwZ, hvw⟩
  · exact d.future_X_anticomplete r hr hJ i hrunOld hdisjX
      ⟨v, hv, w, hwX, hvw⟩

noncomputable def toSuccessorData
    (d : AssemblyInput G A k C J0 ell J phi)
    (hphi : Appropriate G A k C J0 ell J phi) :
    SuccessorData G A k C J0 ell J phi d.rho where
  Z := d.Z
  X := d.X
  newBlockCount := fun i ↦ (d.N.filter fun r ↦ d.psi r = i).card
  refines := d.refines
  support := d.support hphi
  block_status := d.block_status hphi
  class_eq := d.class_eq
  class_card := d.class_card
  block_incidence := d.block_incidence
  removed_incidence := d.removed_incidence
  block_count_gain := d.block_count_gain
  retained_core := fun i ↦ by simpa [d.class_eq i] using d.retained_core i
  early := d.early hphi
  quarter := d.quarter
  future_anticomplete := d.future_anticomplete

end AssemblyInput

end

namespace PopularScratch

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable def chooseMinSubset {α : Type*} [DecidableEq α]
    (s : Finset α) (d : ℕ) : Finset α :=
  Classical.choose (Finset.exists_subset_card_eq (Nat.min_le_left s.card d))

lemma chooseMinSubset_subset {α : Type*} [DecidableEq α]
    (s : Finset α) (d : ℕ) : chooseMinSubset s d ⊆ s :=
  (Classical.choose_spec
    (Finset.exists_subset_card_eq (Nat.min_le_left s.card d))).1

lemma card_chooseMinSubset {α : Type*} [DecidableEq α]
    (s : Finset α) (d : ℕ) : (chooseMinSubset s d).card = min s.card d :=
  (Classical.choose_spec
    (Finset.exists_subset_card_eq (Nat.min_le_left s.card d))).2

noncomputable def adjacentBlockIndices (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : List (Finset V))
    (Uidx : Finset ℕ) (s : V) : Finset ℕ := by
  classical
  exact Uidx.filter fun r => AdjacentSets G {s} (C.getD r ∅)

noncomputable def selectedScope (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V)
    (C : List (Finset V)) (Uidx : Finset ℕ) (k : ℕ) (s : V) : Finset ℕ := by
  classical
  exact chooseMinSubset (adjacentBlockIndices G C Uidx s)
    (k + 1 - degreeOn G H s)

lemma selectedScope_subset_adjacentBlockIndices
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (C : List (Finset V))
    (Uidx : Finset ℕ) (k : ℕ) (s : V) :
    selectedScope G H C Uidx k s ⊆ adjacentBlockIndices G C Uidx s := by
  classical
  exact chooseMinSubset_subset _ _

lemma selectedScope_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (C : List (Finset V))
    (Uidx : Finset ℕ) (k : ℕ) (s : V) :
    selectedScope G H C Uidx k s ⊆ Uidx := by
  classical
  apply (selectedScope_subset_adjacentBlockIndices G H C Uidx k s).trans
  intro r hr
  exact (Finset.mem_filter.mp hr).1

lemma mem_selectedScope_adjacent
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (C : List (Finset V))
    (Uidx : Finset ℕ) (k : ℕ) (s : V) {r : ℕ}
    (hr : r ∈ selectedScope G H C Uidx k s) :
    AdjacentSets G {s} (C.getD r ∅) := by
  classical
  have hr' := selectedScope_subset_adjacentBlockIndices G H C Uidx k s hr
  change r ∈ Uidx.filter (fun r => AdjacentSets G {s} (C.getD r ∅)) at hr'
  exact (Finset.mem_filter.mp hr').2

lemma card_selectedScope
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (C : List (Finset V))
    (Uidx : Finset ℕ) (k : ℕ) (s : V) :
    (selectedScope G H C Uidx k s).card =
      min (adjacentBlockIndices G C Uidx s).card (k + 1 - degreeOn G H s) := by
  classical
  exact card_chooseMinSubset _ _

lemma selectedScope_eq_adjacent_of_card_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset V) (C : List (Finset V))
    (Uidx : Finset ℕ) (k : ℕ) (s : V)
    (hcard : (adjacentBlockIndices G C Uidx s).card ≤
      k + 1 - degreeOn G H s) :
    selectedScope G H C Uidx k s = adjacentBlockIndices G C Uidx s := by
  classical
  apply Finset.eq_of_subset_of_card_le
    (selectedScope_subset_adjacentBlockIndices G H C Uidx k s)
  rw [card_selectedScope, Nat.min_eq_left hcard]

noncomputable def selectedVertices (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : List (Finset V))
    (Uidx : Finset ℕ) (S : Finset V) : Finset V := by
  classical
  exact S.filter fun s => (adjacentBlockIndices G C Uidx s).Nonempty

omit [DecidableEq V] [Fintype V] in
lemma selectedVertices_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : List (Finset V))
    (Uidx : Finset ℕ) (S : Finset V) : selectedVertices G C Uidx S ⊆ S := by
  classical
  exact Finset.filter_subset _ _

lemma certificate_deficit_sum_le_twenty_four
    {H : Finset V} {k : ℕ} {C0 : ProtectedFamily G H k}
    (E : ExtensionCertificate G H k C0) (Uidx : Finset ℕ)
    (hshort : shortage k G H ≤ (12 * Uidx.card : ℕ)) :
    E.S.sum (fun s => k - degreeOn G H s) ≤ 24 * Uidx.card := by
  have h := E.deficit_le
  have hcast : ((E.S.sum (fun s => k - degreeOn G H s) : ℕ) : ℤ) ≤
      ((24 * Uidx.card : ℕ) : ℤ) := by
    calc
      ((E.S.sum (fun s => k - degreeOn G H s) : ℕ) : ℤ) ≤
          2 * shortage k G H := h
      _ ≤ 2 * ((12 * Uidx.card : ℕ) : ℤ) :=
        mul_le_mul_of_nonneg_left hshort (by norm_num)
      _ = ((24 * Uidx.card : ℕ) : ℤ) := by push_cast; ring
  exact_mod_cast hcast

lemma certificate_card_le_twenty_four
    {H : Finset V} {k : ℕ} {C0 : ProtectedFamily G H k}
    (E : ExtensionCertificate G H k C0) (Uidx : Finset ℕ) (hk : 2 ≤ k)
    (hshort : shortage k G H ≤ (12 * Uidx.card : ℕ)) :
    E.S.card ≤ 24 * Uidx.card := by
  calc
    E.S.card = E.S.sum (fun _ => 1) := by simp
    _ ≤ E.S.sum (fun s => k - degreeOn G H s) := by
      apply Finset.sum_le_sum
      intro s hs
      have hsLow := E.S_subset_low hs
      rw [mem_lowVertices] at hsLow
      omega
    _ ≤ 24 * Uidx.card := certificate_deficit_sum_le_twenty_four E Uidx hshort

lemma certificate_scope_budget
    {H : Finset V} {k : ℕ} {C0 : ProtectedFamily G H k}
    (E : ExtensionCertificate G H k C0) (Uidx : Finset ℕ) (hk : 2 ≤ k)
    (hshort : shortage k G H ≤ (12 * Uidx.card : ℕ)) :
    E.S.sum (fun s => k + 1 - degreeOn G H s) ≤ 48 * Uidx.card := by
  have hdef := certificate_deficit_sum_le_twenty_four E Uidx hshort
  have hcard := certificate_card_le_twenty_four E Uidx hk hshort
  have heq : E.S.sum (fun s => k + 1 - degreeOn G H s) =
      E.S.sum (fun s => k - degreeOn G H s) + E.S.card := by
    calc
      E.S.sum (fun s => k + 1 - degreeOn G H s) =
          E.S.sum (fun s => (k - degreeOn G H s) + 1) := by
        apply Finset.sum_congr rfl
        intro s hs
        have hsLow := E.S_subset_low hs
        rw [mem_lowVertices] at hsLow
        omega
      _ = E.S.sum (fun s => k - degreeOn G H s) +
          E.S.sum (fun _ => 1) := Finset.sum_add_distrib
      _ = E.S.sum (fun s => k - degreeOn G H s) + E.S.card := by simp
  rw [heq]
  omega

lemma selectedScope_total_le
    {H : Finset V} {k : ℕ} {C0 : ProtectedFamily G H k}
    (E : ExtensionCertificate G H k C0) (C : List (Finset V))
    (Uidx : Finset ℕ) (hk : 2 ≤ k)
    (hshort : shortage k G H ≤ (12 * Uidx.card : ℕ)) :
    (selectedVertices G C Uidx E.S).sum
      (fun s => (selectedScope G H C Uidx k s).card) ≤ 48 * Uidx.card := by
  calc
    (selectedVertices G C Uidx E.S).sum
        (fun s => (selectedScope G H C Uidx k s).card) ≤
        (selectedVertices G C Uidx E.S).sum
          (fun s => k + 1 - degreeOn G H s) := by
      apply Finset.sum_le_sum
      intro s hs
      rw [card_selectedScope]
      exact Nat.min_le_right _ _
    _ ≤ E.S.sum (fun s => k + 1 - degreeOn G H s) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (selectedVertices_subset G C Uidx E.S) (by simp)
    _ ≤ 48 * Uidx.card := certificate_scope_budget E Uidx hk hshort

def scopeFrequency (S : Finset V) (scope : V -> Finset ℕ) (r : ℕ) : ℕ :=
  (S.filter fun s => r ∈ scope s).card

def popularIndices (Uidx : Finset ℕ) (S : Finset V)
    (scope : V -> Finset ℕ) : Finset ℕ :=
  Uidx.filter fun r => 200 < scopeFrequency S scope r

omit [DecidableEq V] [Fintype V] in
lemma sum_scopeFrequency_eq
    (Uidx : Finset ℕ) (S : Finset V) (scope : V -> Finset ℕ)
    (hscope : ∀ s ∈ S, scope s ⊆ Uidx) :
    Uidx.sum (scopeFrequency S scope) = S.sum fun s => (scope s).card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [scopeFrequency]
  | @insert s S hs ih =>
      have hscopeS : ∀ x ∈ S, scope x ⊆ Uidx := by
        intro x hx
        exact hscope x (Finset.mem_insert_of_mem hx)
      have hscopes : scope s ⊆ Uidx := hscope s (Finset.mem_insert_self s S)
      have hfreq : ∀ r,
          scopeFrequency (insert s S) scope r =
            scopeFrequency S scope r + if r ∈ scope s then 1 else 0 := by
        intro r
        by_cases hrs : r ∈ scope s
        · rw [scopeFrequency, scopeFrequency, Finset.filter_insert, if_pos hrs,
            Finset.card_insert_of_notMem]
          · simp only [if_pos hrs]
          · simp [hs]
        · rw [scopeFrequency, scopeFrequency, Finset.filter_insert, if_neg hrs]
          simp only [if_neg hrs, add_zero]
      have hindicator : Uidx.sum (fun r => if r ∈ scope s then 1 else 0) =
          (scope s).card := by
        rw [← Finset.sum_filter]
        have hfilter : Uidx.filter (fun r => r ∈ scope s) = scope s := by
          ext r
          simp only [Finset.mem_filter]
          constructor
          · exact fun h => h.2
          · exact fun h => ⟨hscopes h, h⟩
        rw [hfilter]
        simp
      rw [Finset.sum_insert hs, ← ih hscopeS]
      calc
        Uidx.sum (scopeFrequency (insert s S) scope) =
            Uidx.sum (fun r => scopeFrequency S scope r +
              if r ∈ scope s then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro r hr
          exact hfreq r
        _ = Uidx.sum (scopeFrequency S scope) +
            Uidx.sum (fun r => if r ∈ scope s then 1 else 0) :=
          Finset.sum_add_distrib
        _ = (scope s).card + Uidx.sum (scopeFrequency S scope) := by
          rw [hindicator, Nat.add_comm]

omit [DecidableEq V] [Fintype V] in
lemma popular_double_count
    (Uidx : Finset ℕ) (S : Finset V) (scope : V -> Finset ℕ)
    (hscope : ∀ s ∈ S, scope s ⊆ Uidx) :
    201 * (popularIndices Uidx S scope).card ≤ S.sum fun s => (scope s).card := by
  rw [← sum_scopeFrequency_eq Uidx S scope hscope]
  calc
    201 * (popularIndices Uidx S scope).card =
        (popularIndices Uidx S scope).sum (fun _ => 201) := by
      simp [Nat.mul_comm]
    _ ≤ (popularIndices Uidx S scope).sum (scopeFrequency S scope) := by
      apply Finset.sum_le_sum
      intro r hr
      have := (Finset.mem_filter.mp hr).2
      omega
    _ ≤ Uidx.sum (scopeFrequency S scope) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (by simp)

omit [DecidableEq V] [Fintype V] in
lemma four_mul_popular_le
    (Uidx : Finset ℕ) (S : Finset V) (scope : V -> Finset ℕ)
    (hscope : ∀ s ∈ S, scope s ⊆ Uidx)
    (hbudget : S.sum (fun s => (scope s).card) ≤ 48 * Uidx.card) :
    4 * (popularIndices Uidx S scope).card ≤ Uidx.card := by
  have hdc := (popular_double_count Uidx S scope hscope).trans hbudget
  omega

lemma selectedPopular_quarter
    {H : Finset V} {k : ℕ} {C0 : ProtectedFamily G H k}
    (E : ExtensionCertificate G H k C0) (C : List (Finset V))
    (Uidx : Finset ℕ) (hk : 2 ≤ k)
    (hshort : shortage k G H ≤ (12 * Uidx.card : ℕ)) :
    let S' := selectedVertices G C Uidx E.S
    let scope := fun s : V => selectedScope G H C Uidx k s
    4 * (popularIndices Uidx S' scope).card ≤ Uidx.card := by
  classical
  dsimp only
  apply four_mul_popular_le
  · intro s hs
    exact selectedScope_subset G H C Uidx k s
  · exact selectedScope_total_le E C Uidx hk hshort

omit [DecidableEq V] [Fintype V] in
lemma nonpopular_frequency_le
    (Uidx : Finset ℕ) (S : Finset V) (scope : V -> Finset ℕ) {r : ℕ}
    (hrU : r ∈ Uidx) (hr : r ∉ popularIndices Uidx S scope) :
    scopeFrequency S scope r ≤ 200 := by
  simp only [popularIndices, Finset.mem_filter, hrU, true_and] at hr
  omega

def nonpopularIndices (Uidx : Finset ℕ) (S : Finset V)
    (scope : V -> Finset ℕ) : Finset ℕ :=
  Uidx \ popularIndices Uidx S scope

noncomputable def restrictedScope
    (Uidx : Finset ℕ) (S : Finset V) (scope : V -> Finset ℕ)
    (s : {s // s ∈ S}) : Finset {r // r ∈ nonpopularIndices Uidx S scope} := by
  classical
  exact Finset.univ.filter fun r => (r : ℕ) ∈ scope (s : V)

noncomputable def neighborColorSet (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (phi : PartialColoring V k) (s : V) : Finset (Color k) := by
  classical
  exact Finset.univ.filter fun i => ∃ v ∈ A, G.Adj s v ∧ phi v = some i

noncomputable def neighborColorList (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (phi : PartialColoring V k) (s : V) : Finset (Color k) :=
  chooseMinSubset (neighborColorSet G A phi s) k

omit [DecidableEq V] [Fintype V] in
lemma neighborColorList_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (phi : PartialColoring V k) (s : V) :
    neighborColorList G A phi s ⊆ neighborColorSet G A phi s :=
  chooseMinSubset_subset _ _

omit [DecidableEq V] [Fintype V] in
lemma neighborColorList_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (phi : PartialColoring V k) (s : V) :
    (neighborColorList G A phi s).card ≤ k := by
  rw [neighborColorList, card_chooseMinSubset]
  exact Nat.min_le_right _ _

omit [DecidableEq V] [Fintype V] in
lemma restrictedScope_card_le_scope
    (Uidx : Finset ℕ) (S : Finset V) (scope : V -> Finset ℕ)
    (s : {s // s ∈ S}) :
    (restrictedScope Uidx S scope s).card ≤ (scope (s : V)).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun r :
    {r // r ∈ nonpopularIndices Uidx S scope} => (r : ℕ))
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro r hr q hq heq
    exact Subtype.ext heq

omit [DecidableEq V] [Fintype V] in
lemma restrictedScope_frequency_le
    (Uidx : Finset ℕ) (S : Finset V) (scope : V -> Finset ℕ)
    (_hscope : ∀ s ∈ S, scope s ⊆ Uidx)
    (r : {r // r ∈ nonpopularIndices Uidx S scope}) :
    ((Finset.univ.filter fun s : {s // s ∈ S} =>
      r ∈ restrictedScope Uidx S scope s).card) ≤ 200 := by
  classical
  have hcard :
      (Finset.univ.filter fun s : {s // s ∈ S} =>
        r ∈ restrictedScope Uidx S scope s).card ≤
      (S.filter fun s => (r : ℕ) ∈ scope s).card := by
    apply Finset.card_le_card_of_injOn (fun s : {s // s ∈ S} => (s : V))
    · intro s hs
      have hsScope : (r : ℕ) ∈ scope (s : V) := by
        have hrRestricted := (Finset.mem_filter.mp hs).2
        simpa only [restrictedScope, Finset.mem_filter, Finset.mem_univ, true_and]
          using hrRestricted
      exact Finset.mem_filter.mpr ⟨s.property, hsScope⟩
    · intro s hs q hq heq
      exact Subtype.ext heq
  have hrData := Finset.mem_sdiff.mp r.property
  exact hcard.trans (nonpopular_frequency_le Uidx S scope hrData.1 hrData.2)

theorem exists_selected_scope_coloring
    {H A : Finset V} {k : ℕ} {C0 : ProtectedFamily G H k}
    (E : ExtensionCertificate G H k C0) (C : List (Finset V))
    (Uidx : Finset ℕ) (phi : PartialColoring V k) (hk : 2 ≤ k)
    (_hshort : shortage k G H ≤ (12 * Uidx.card : ℕ)) :
    let S' := selectedVertices G C Uidx E.S
    let scope := fun s : V => selectedScope G H C Uidx k s
    let NP := nonpopularIndices Uidx S' scope
    ∃ color : {r // r ∈ NP} -> Color k,
      (∀ s : {s // s ∈ S'},
        Set.InjOn color (restrictedScope Uidx S' scope s :
          Set {r // r ∈ NP})) ∧
      (∀ s : {s // s ∈ S'}, ∀ r ∈ restrictedScope Uidx S' scope s,
        color r ∉ neighborColorList G A phi (s : V)) := by
  classical
  dsimp only
  let S' := selectedVertices G C Uidx E.S
  let scope : V -> Finset ℕ := fun s => selectedScope G H C Uidx k s
  let NP := nonpopularIndices Uidx S' scope
  let ScopeT := {s // s ∈ S'}
  let ItemT := {r // r ∈ NP}
  let scopeT : ScopeT -> Finset ItemT := fun s => restrictedScope Uidx S' scope s
  let avoidT : ScopeT -> Finset (Color k) :=
    fun s => neighborColorList G A phi (s : V)
  have hscopeSub : ∀ s ∈ S', scope s ⊆ Uidx := by
    intro s hs
    exact selectedScope_subset G H C Uidx k s
  have hfrequency : ∀ r : ItemT,
      (Finset.univ.filter fun s : ScopeT => r ∈ scopeT s).card ≤ 200 := by
    intro r
    exact restrictedScope_frequency_le Uidx S' scope hscopeSub r
  have hscopeCard : ∀ s : ScopeT, (scopeT s).card ≤ k + 1 := by
    intro s
    calc
      (scopeT s).card ≤ (scope (s : V)).card :=
        restrictedScope_card_le_scope Uidx S' scope s
      _ ≤ k + 1 := by
        dsimp [scope]
        rw [card_selectedScope]
        exact (Nat.min_le_right _ _).trans (Nat.sub_le _ _)
  have havoid : ∀ s : ScopeT, (avoidT s).card ≤ k := by
    intro s
    exact neighborColorList_card_le G A phi (s : V)
  have hkpos : 0 < k := by omega
  simpa [S', scope, NP, ScopeT, ItemT, scopeT, avoidT] using
    (exists_erdos814_scope_coloring (Item := ItemT) (Scope := ScopeT)
      hkpos scopeT avoidT hfrequency hscopeCard havoid)

end PopularScratch

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

lemma residual_card_add_earlyMass_le
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hJ0ell : J0 ≤ ell) :
    (deficitResidual A C phi (ell + 1)).card +
        Dyadic.retainedMass C J0 ≤ A.card := by
  classical
  let R := Finset.range (Dyadic.levelStart J0)
  let block : ℕ → Finset V := fun r ↦ C.getD r ∅
  let E := R.biUnion block
  let H := deficitResidual A C phi (ell + 1)
  have hJ0succ : J0 ≤ ell + 1 := hJ0ell.trans (Nat.le_succ ell)
  have hRprefix : R ⊆ uncoloredPrefixIndices C phi (ell + 1) := by
    intro r hr
    have hr0 : r < Dyadic.levelStart J0 := mem_range.mp hr
    rw [uncoloredPrefixIndices, mem_filter]
    exact ⟨mem_range.mpr (hr0.trans_le (Dyadic.levelStart_mono hJ0succ)),
      hphi.early r hr0⟩
  have hEprefix : E ⊆ uncoloredPrefixUnion C phi (ell + 1) := by
    intro v hv
    rw [show E = R.biUnion block by rfl, mem_biUnion] at hv
    obtain ⟨r, hrR, hvr⟩ := hv
    rw [uncoloredPrefixUnion, mem_biUnion]
    exact ⟨r, hRprefix hrR, hvr⟩
  have hEA : E ⊆ A := by
    intro v hv
    rw [show E = R.biUnion block by rfl, mem_biUnion] at hv
    obtain ⟨r, hrR, hvr⟩ := hv
    have hr0 : r < Dyadic.levelStart J0 := mem_range.mp hrR
    exact S.block_subset r
      (hr0.trans_le (Dyadic.levelStart_mono S.hJ)) hvr
  have hHA : H ⊆ A := sdiff_subset
  have hdisj : Disjoint H E := by
    rw [Finset.disjoint_left]
    intro v hvH hvE
    have hvprefix := hEprefix hvE
    exact (mem_sdiff.mp hvH).2 (mem_union_right _ hvprefix)
  have hpair : (R : Set ℕ).PairwiseDisjoint block := by
    intro r hr s hs hrs
    have hr0 : r < Dyadic.levelStart J0 := mem_range.mp hr
    have hs0 : s < Dyadic.levelStart J0 := mem_range.mp hs
    exact S.blocks_disjoint r
      (hr0.trans_le (Dyadic.levelStart_mono S.hJ)) s
      (hs0.trans_le (Dyadic.levelStart_mono S.hJ)) hrs
  have hEcard : E.card = Dyadic.retainedMass C J0 := by
    rw [show E = R.biUnion block by rfl, Finset.card_biUnion hpair]
    rfl
  have hunion : H ∪ E ⊆ A := union_subset hHA hEA
  have hc := card_le_card hunion
  rw [Finset.card_union_of_disjoint hdisj, hEcard] at hc
  exact hc

lemma noCore_deficitResidual
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hJ0ell : J0 ≤ ell) :
    ∀ X : Finset V, X ⊆ deficitResidual A C phi (ell + 1) →
      ¬ HasMinDegreeOn G X k := by
  intro X hXH hmin
  apply S.noSmallCore
  refine ⟨X, ?_⟩
  have hXA : X ⊆ A := hXH.trans sdiff_subset
  have hmass := residual_card_add_earlyMass_le S hphi hJ0ell
  have hXcard : X.card ≤ (deficitResidual A C phi (ell + 1)).card :=
    card_le_card hXH
  let q : ℕ := 100 * k
  have hq : 1 ≤ q := by
    dsimp [q]
    exact Nat.mul_pos (by decide) (lt_of_lt_of_le (by decide) S.hk)
  have hsmallq : q * X.card ≤ (q - 1) * A.card := by
    have hearly := S.early_mass
    have hqX : q * X.card ≤ q * (deficitResidual A C phi (ell + 1)).card :=
      Nat.mul_le_mul_left q hXcard
    have hmul := Nat.mul_le_mul_left q hmass
    rw [Nat.mul_add] at hmul
    have hchain : q * (deficitResidual A C phi (ell + 1)).card + A.card ≤
        q * A.card := by
      calc
        q * (deficitResidual A C phi (ell + 1)).card + A.card ≤
            q * (deficitResidual A C phi (ell + 1)).card +
              q * Dyadic.retainedMass C J0 := by
                exact Nat.add_le_add_left (by simpa [q] using hearly) _
        _ ≤ q * A.card := hmul
    have hdecomp : q * A.card = (q - 1) * A.card + A.card := by
      calc
        q * A.card = ((q - 1) + 1) * A.card := by rw [Nat.sub_add_cancel hq]
        _ = (q - 1) * A.card + A.card := by ring
    rw [hdecomp] at hchain
    omega
  have hqD : q ≤ uniformDen k := by
    have hk0 : k ≠ 0 := by omega
    have hkk : 1 ≤ k * k := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hk0 hk0)
    have hkpow : k ≤ k ^ 3 := by
      calc
        k = k * 1 := by simp
        _ ≤ k * (k * k) := Nat.mul_le_mul_left k hkk
        _ = k ^ 3 := by ring
    dsimp [q]
    simp only [uniformDen]
    calc
      100 * k ≤ 10000 * k := Nat.mul_le_mul_right k (by decide)
      _ ≤ 10000 * k ^ 3 := Nat.mul_le_mul_left 10000 hkpow
  exact (IsSmallCoreOn.mono_den hq hqD ⟨hXA, hmin, hsmallq⟩)

theorem exists_residualExtensionCertificate
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hJ0ell : J0 ≤ ell) :
    Nonempty (ExtensionCertificate G (deficitResidual A C phi (ell + 1)) k
      (residualProtectedFamily S hphi)) :=
  exists_extensionCertificate (residualProtectedFamily S hphi) S.hk
    (noCore_deficitResidual S hphi hJ0ell)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

private lemma sum_scopeNeed_certificate_le'
    {H : Finset V} {k u : ℕ} {CF : ProtectedFamily G H k}
    (E : ExtensionCertificate G H k CF) (hk : 2 ≤ k)
    (hshort : shortage k G H ≤ (12 * u : ℕ)) :
    ∑ s ∈ E.S, (k + 1 - degreeOn G H s) ≤ 48 * u := by
  have hdeg : ∀ s ∈ E.S, degreeOn G H s ≤ k - 1 := by
    intro s hs
    exact (mem_lowVertices.mp (E.S_subset_low hs)).2
  have hsplit :
      (∑ s ∈ E.S, (k + 1 - degreeOn G H s)) =
        E.S.card + ∑ s ∈ E.S, (k - degreeOn G H s) := by
    calc
      (∑ s ∈ E.S, (k + 1 - degreeOn G H s)) =
          ∑ s ∈ E.S, (1 + (k - degreeOn G H s)) := by
            apply Finset.sum_congr rfl
            intro s hs
            have := hdeg s hs
            omega
      _ = E.S.card + ∑ s ∈ E.S, (k - degreeOn G H s) := by
            simp [Finset.sum_add_distrib]
  have hcard : E.S.card ≤ ∑ s ∈ E.S, (k - degreeOn G H s) := by
    calc
      E.S.card = ∑ _s ∈ E.S, 1 := by simp
      _ ≤ ∑ s ∈ E.S, (k - degreeOn G H s) := by
        apply Finset.sum_le_sum
        intro s hs
        have := hdeg s hs
        omega
  have hdef := E.deficit_le
  have hdefnonneg : 0 ≤ shortage k G H := by
    have hsum_nonneg :
        (0 : ℤ) ≤ ((E.S.sum fun s ↦ k - degreeOn G H s : ℕ) : ℤ) := by omega
    omega
  have hgoalZ :
      (((∑ s ∈ E.S, (k + 1 - degreeOn G H s)) : ℕ) : ℤ) ≤
        ((48 * u : ℕ) : ℤ) := by
    rw [hsplit, Nat.cast_add]
    have hcardZ :
        (E.S.card : ℤ) ≤
          ((∑ s ∈ E.S, (k - degreeOn G H s) : ℕ) : ℤ) := by
      exact_mod_cast hcard
    have hshortZ : shortage k G H ≤ (12 * u : ℕ) := hshort
    omega
  exact_mod_cast hgoalZ

structure GreedyLevelData
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A H : Finset V) (k : ℕ) (C : List (Finset V))
    (phi : PartialColoring V k) (Eset : Finset V) (ell : ℕ) where
  Uidx : Finset ℕ
  active : Finset V
  scope : V → Finset ℕ
  N : Finset ℕ
  psi : ℕ → Color k
  Uidx_eq : Uidx = uncoloredCurrentIndices C phi ell
  active_eq : active = PopularScratch.selectedVertices G C Uidx Eset
  scope_eq : scope = fun s ↦ PopularScratch.selectedScope G H C Uidx k s
  N_eq : N = PopularScratch.nonpopularIndices Uidx active scope
  N_subset : N ⊆ Uidx
  quarter : 4 * (Uidx.card - N.card) ≤ 2 ^ ell
  injective_scope : ∀ s ∈ active, ∀ r ∈ scope s, r ∈ N →
    ∀ q ∈ scope s, q ∈ N → psi r = psi q → r = q
  avoids : ∀ s ∈ active, ∀ r ∈ scope s, r ∈ N →
    psi r ∉ PopularScratch.neighborColorList G A phi s

theorem exists_greedyLevelData
    {A H : Finset V} {k ell : ℕ} {C : List (Finset V)}
    {phi : PartialColoring V k} {CF : ProtectedFamily G H k}
    (E : ExtensionCertificate G H k CF)
    (hk : 2 ≤ k)
    (hshort : shortage k G H ≤
      (12 * uncoloredBlockCount C phi ell : ℕ)) :
    Nonempty (GreedyLevelData G A H k C phi E.S ell) := by
  classical
  let U := currentUncoloredIndices C phi ell
  let Sact := PopularScratch.selectedVertices G C U E.S
  let scope : V → Finset ℕ := fun s ↦
    PopularScratch.selectedScope G H C U k s
  let N := PopularScratch.nonpopularIndices U Sact scope
  have hshortU : shortage k G H ≤ (12 * U.card : ℕ) := by
    simpa [U] using hshort
  obtain ⟨color, hinj, havoid⟩ :=
    PopularScratch.exists_selected_scope_coloring
      (G := G) E C U phi hk hshortU
  let fallback : Color k := ⟨0, by
    have hkpos : 0 < k := by omega
    exact Nat.mul_pos (by decide) hkpos⟩
  let psi : ℕ → Color k := fun r ↦
    if hr : r ∈ N then color ⟨r, hr⟩ else fallback
  have hNsub : N ⊆ U := sdiff_subset
  have hpopular := PopularScratch.selectedPopular_quarter
    (G := G) E C U hk hshortU
  have hquarter : 4 * (U.card - N.card) ≤ 2 ^ ell := by
    have hNcard : U.card - N.card =
        (PopularScratch.popularIndices U Sact scope).card := by
      change U.card - (U \ PopularScratch.popularIndices U Sact scope).card =
        (PopularScratch.popularIndices U Sact scope).card
      unfold PopularScratch.popularIndices
      have hpopularCard :
          (U.filter fun r ↦ 200 < PopularScratch.scopeFrequency Sact scope r).card ≤
            U.card := card_le_card (Finset.filter_subset _ _)
      rw [card_sdiff_of_subset (Finset.filter_subset _ _)]
      omega
    rw [hNcard]
    have hpopU : 4 * (PopularScratch.popularIndices U Sact scope).card ≤ U.card := by
      simpa [Sact, scope] using hpopular
    have hUlevel : U.card ≤ 2 ^ ell := by
      dsimp [U]
      rw [card_currentUncoloredIndices]
      unfold uncoloredBlockCount
      simpa only [Dyadic.card_levelIndices] using
        card_le_card (Finset.filter_subset
          (fun r ↦ BlockUncolored phi (C.getD r ∅)) (Dyadic.levelIndices ell))
    exact hpopU.trans hUlevel
  refine ⟨{
    Uidx := U
    active := Sact
    scope := scope
    N := N
    psi := psi
    Uidx_eq := rfl
    active_eq := rfl
    scope_eq := rfl
    N_eq := rfl
    N_subset := hNsub
    quarter := hquarter
    injective_scope := ?_
    avoids := ?_ }⟩
  · intro s hs r hrs hrN q hqs hqN heq
    let ss : {s // s ∈ Sact} := ⟨s, hs⟩
    let rr : {r // r ∈ N} := ⟨r, hrN⟩
    let qq : {r // r ∈ N} := ⟨q, hqN⟩
    have hrr : rr ∈ PopularScratch.restrictedScope U Sact scope ss := by
      simp [rr, ss, PopularScratch.restrictedScope, hrs]
    have hqq : qq ∈ PopularScratch.restrictedScope U Sact scope ss := by
      simp [qq, ss, PopularScratch.restrictedScope, hqs]
    have hc : color rr = color qq := by
      simpa [psi, hrN, hqN, rr, qq] using heq
    exact congrArg Subtype.val (hinj ss hrr hqq hc)
  · intro s hs r hrs hrN
    let ss : {s // s ∈ Sact} := ⟨s, hs⟩
    let rr : {r // r ∈ N} := ⟨r, hrN⟩
    have hrr : rr ∈ PopularScratch.restrictedScope U Sact scope ss := by
      simp [rr, ss, PopularScratch.restrictedScope, hrs]
    simpa [psi, hrN, rr, ss] using havoid ss rr hrr

end

namespace ExtensionApplyScratch

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

def redBlockIndices (U : Finset ℕ) (blockColor : ℕ → Option I)
    (i : I) : Finset ℕ :=
  U.filter fun r ↦ blockColor r = some i

def redBlockUnion (C : List (Finset V)) (U : Finset ℕ)
    (blockColor : ℕ → Option I) (i : I) : Finset V :=
  (redBlockIndices U blockColor i).biUnion fun r ↦ C.getD r ∅

omit [DecidableRel G.Adj] [Fintype I] [Fintype V] in

lemma adjacent_block_of_adjacent_redBlockUnion
    (C : List (Finset V)) (U : Finset ℕ)
    (blockColor : ℕ → Option I) (i : I) {v : V}
    (h : AdjacentSets G {v} (redBlockUnion C U blockColor i)) :
    ∃ r ∈ U, blockColor r = some i ∧
      AdjacentSets G {v} (C.getD r ∅) := by
  rcases h with ⟨x, hx, y, hy, hxy⟩
  have hxv : x = v := by simpa using hx
  subst x
  rw [redBlockUnion, mem_biUnion] at hy
  obtain ⟨r, hr, hyr⟩ := hy
  rw [redBlockIndices, mem_filter] at hr
  exact ⟨r, hr.1, hr.2, v, by simp, y, hyr, hxy⟩

lemma adjacent_of_low_after_delete
    {B Z : Finset V} {k : ℕ} {v : V}
    (hk : 2 ≤ k) (hZB : Z ⊆ B) (_hv : v ∈ B \ Z)
    (hhigh : k ≤ degreeOn G B v)
    (hlow : degreeOn G (B \ Z) v ≤ k - 1) :
    AdjacentSets G {v} Z := by
  by_contra hnot
  have heq := degreeOn_sdiff_eq_of_not_adjacent (G := G) hZB hnot
  rw [heq] at hlow
  omega

lemma lowVertices_after_red_delete_subset_residual
    {A O Z P : Finset V} {k : ℕ}
    (phi : PartialColoring V k)
    (hk : 2 ≤ k)
    (hZ : Z ⊆ A \ O)
    (hmin : HasMinDegreeOn G (A \ O) k)
    (hneigh_uncolored : ∀ v ∈ A,
      AdjacentSets G {v} Z → phi v = none)
    (hprefix_anti : ∀ v ∈ P, ¬ AdjacentSets G {v} Z) :
    lowVertices G ((A \ O) \ Z) k ⊆
      A \ (coloredVertices A phi ∪ P) := by
  intro v hv
  have hvdata := mem_lowVertices.mp hv
  have hvB : v ∈ A \ O := (mem_sdiff.mp hvdata.1).1
  have hadj : AdjacentSets G {v} Z :=
    adjacent_of_low_after_delete (G := G) hk hZ hvdata.1
      (hmin.2 v hvB) hvdata.2
  have hvnone : phi v = none := hneigh_uncolored v (mem_sdiff.mp hvB).1 hadj
  refine mem_sdiff.mpr ⟨(mem_sdiff.mp hvB).1, ?_⟩
  intro hvbad
  rcases mem_union.mp hvbad with hvcolored | hvP
  · rw [mem_coloredVertices_iff] at hvcolored
    obtain ⟨_, i, hi⟩ := hvcolored
    rw [hvnone] at hi
    contradiction
  · exact hprefix_anti v hvP hadj

lemma lowVertices_after_red_delete_subset_residual'
    {A O Z P : Finset V} {k : ℕ}
    (phi : PartialColoring V k)
    (hk : 2 ≤ k)
    (hZ : Z ⊆ A \ O)
    (hmin : HasMinDegreeOn G (A \ O) k)
    (hneigh_uncolored : ∀ v ∈ A,
      AdjacentSets G {v} Z → phi v = none)
    (hprefix : ∀ v ∈ P,
      v ∈ Z ∨ ¬ AdjacentSets G {v} Z) :
    lowVertices G ((A \ O) \ Z) k ⊆
      A \ (coloredVertices A phi ∪ P) := by
  intro v hv
  have hvdata := mem_lowVertices.mp hv
  have hvB : v ∈ A \ O := (mem_sdiff.mp hvdata.1).1
  have hvnotZ : v ∉ Z := (mem_sdiff.mp hvdata.1).2
  have hadj : AdjacentSets G {v} Z :=
    adjacent_of_low_after_delete (G := G) hk hZ hvdata.1
      (hmin.2 v hvB) hvdata.2
  have hvnone : phi v = none := hneigh_uncolored v (mem_sdiff.mp hvB).1 hadj
  refine mem_sdiff.mpr ⟨(mem_sdiff.mp hvB).1, ?_⟩
  intro hvbad
  rcases mem_union.mp hvbad with hvcolored | hvP
  · rw [mem_coloredVertices_iff] at hvcolored
    obtain ⟨_, i, hi⟩ := hvcolored
    rw [hvnone] at hi
    contradiction
  · rcases hprefix v hvP with hvZ | hanti
    · exact hvnotZ hvZ
    · exact hanti hadj

lemma lowVertices_currentColor_subset_deficitResidual
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hellJ : ell < J)
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (blockColor : ℕ → Option (Color k)) (i : Color k) :
    lowVertices G
        ((A \ colorClass A phi i) \ redBlockUnion C N blockColor i) k ⊆
      deficitResidual A C phi ell := by
  classical
  let Z := redBlockUnion C N blockColor i
  have hellSuccJ : ell + 1 ≤ J := Nat.succ_le_iff.mpr hellJ
  have selected_data : ∀ r, r ∈ N →
      Dyadic.levelStart ell ≤ r ∧
      r < Dyadic.levelStart (ell + 1) ∧
      BlockUncolored phi (C.getD r ∅) := by
    intro r hr
    have hr' := hN hr
    rw [uncoloredCurrentIndices, mem_filter, Dyadic.mem_levelIndices] at hr'
    exact ⟨hr'.1.1, hr'.1.2, hr'.2⟩
  have selected_lt_J : ∀ r, r ∈ N → r < Dyadic.levelStart J := by
    intro r hr
    exact (selected_data r hr).2.1.trans_le
      (Dyadic.levelStart_mono hellSuccJ)
  have hZA : Z ⊆ A \ colorClass A phi i := by
    intro v hv
    change v ∈ redBlockUnion C N blockColor i at hv
    rw [redBlockUnion, mem_biUnion] at hv
    obtain ⟨r, hr, hvr⟩ := hv
    have hrN : r ∈ N := (mem_filter.mp hr).1
    have hrlt := selected_lt_J r hrN
    have hvA := S.block_subset r hrlt hvr
    refine mem_sdiff.mpr ⟨hvA, ?_⟩
    intro hvclass
    have hvcolor : phi v = some i := (mem_filter.mp hvclass).2
    have hvnone := (selected_data r hrN).2.2 v hvr
    rw [hvnone] at hvcolor
    contradiction
  have hneigh : ∀ v ∈ A, AdjacentSets G {v} Z → phi v = none := by
    intro v hvA hvZ
    obtain ⟨r, hrN, hcolor, hadj⟩ :=
      adjacent_block_of_adjacent_redBlockUnion C N blockColor i hvZ
    have hd := selected_data r hrN
    have hfut := hphi.future r hd.1 (selected_lt_J r hrN) hd.2.2
    rcases hadj with ⟨x, hx, y, hy, hxy⟩
    have hxv : x = v := by simpa using hx
    subst x
    exact hfut y hy v hvA hxy.symm
  have hprefix : ∀ v ∈ uncoloredPrefixUnion C phi ell,
      ¬ AdjacentSets G {v} Z := by
    intro v hvP hvZ
    rw [uncoloredPrefixUnion, mem_biUnion] at hvP
    obtain ⟨r, hrP, hvr⟩ := hvP
    have hrP' : r ∈ Finset.range (Dyadic.levelStart ell) ∧
        BlockUncolored phi (C.getD r ∅) := by
      simpa [uncoloredPrefixIndices] using hrP
    have hrltell : r < Dyadic.levelStart ell := mem_range.mp hrP'.1
    obtain ⟨s, hsN, hcolor, hadj⟩ :=
      adjacent_block_of_adjacent_redBlockUnion C N blockColor i hvZ
    have hsdata := selected_data s hsN
    have hrs : r ≠ s := by omega
    have hrJ : r < Dyadic.levelStart J :=
      hrltell.trans_le (Dyadic.levelStart_mono hellJ.le)
    have hsJ := selected_lt_J s hsN
    apply S.blocks_anticomplete r hrJ s hsJ hrs
    rcases hadj with ⟨x, hx, y, hy, hxy⟩
    have hxv : x = v := by simpa using hx
    subst x
    exact ⟨v, hvr, y, hy, hxy⟩
  have hres := lowVertices_after_red_delete_subset_residual
    (G := G) phi S.hk hZA (hphi.minDegree i) hneigh hprefix
  simpa [Z, deficitResidual] using hres

lemma lowVertices_currentColor_subset_deficitResidual_succ
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hellJ : ell < J)
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (blockColor : ℕ → Option (Color k)) (i : Color k) :
    lowVertices G
        ((A \ colorClass A phi i) \ redBlockUnion C N blockColor i) k ⊆
      deficitResidual A C phi (ell + 1) := by
  classical
  let Z := redBlockUnion C N blockColor i
  have hellSuccJ : ell + 1 ≤ J := Nat.succ_le_iff.mpr hellJ
  have selected_data : ∀ r, r ∈ N →
      Dyadic.levelStart ell ≤ r ∧
      r < Dyadic.levelStart (ell + 1) ∧
      BlockUncolored phi (C.getD r ∅) := by
    intro r hr
    have hr' := hN hr
    rw [uncoloredCurrentIndices, mem_filter, Dyadic.mem_levelIndices] at hr'
    exact ⟨hr'.1.1, hr'.1.2, hr'.2⟩
  have selected_lt_J : ∀ r, r ∈ N → r < Dyadic.levelStart J := by
    intro r hr
    exact (selected_data r hr).2.1.trans_le
      (Dyadic.levelStart_mono hellSuccJ)
  have hZA : Z ⊆ A \ colorClass A phi i := by
    intro v hv
    change v ∈ redBlockUnion C N blockColor i at hv
    rw [redBlockUnion, mem_biUnion] at hv
    obtain ⟨r, hr, hvr⟩ := hv
    have hrN : r ∈ N := (mem_filter.mp hr).1
    have hvA := S.block_subset r (selected_lt_J r hrN) hvr
    refine mem_sdiff.mpr ⟨hvA, ?_⟩
    intro hvclass
    have hvcolor : phi v = some i := (mem_filter.mp hvclass).2
    have hvnone := (selected_data r hrN).2.2 v hvr
    rw [hvnone] at hvcolor
    contradiction
  have hneigh : ∀ v ∈ A, AdjacentSets G {v} Z → phi v = none := by
    intro v hvA hvZ
    obtain ⟨r, hrN, hcolor, hadj⟩ :=
      adjacent_block_of_adjacent_redBlockUnion C N blockColor i hvZ
    have hd := selected_data r hrN
    have hfut := hphi.future r hd.1 (selected_lt_J r hrN) hd.2.2
    rcases hadj with ⟨x, hx, y, hy, hxy⟩
    have hxv : x = v := by simpa using hx
    subst x
    exact hfut y hy v hvA hxy.symm
  have hprefix : ∀ v ∈ uncoloredPrefixUnion C phi (ell + 1),
      v ∈ Z ∨ ¬ AdjacentSets G {v} Z := by
    intro v hvP
    rw [uncoloredPrefixUnion, mem_biUnion] at hvP
    obtain ⟨r, hrP, hvr⟩ := hvP
    have hrP' : r ∈ Finset.range (Dyadic.levelStart (ell + 1)) ∧
        BlockUncolored phi (C.getD r ∅) := by
      simpa [uncoloredPrefixIndices] using hrP
    by_cases hvZ : v ∈ Z
    · exact Or.inl hvZ
    · right
      intro hadj
      obtain ⟨s, hsN, hcolor, hadjS⟩ :=
        adjacent_block_of_adjacent_redBlockUnion C N blockColor i hadj
      have hrs : r ≠ s := by
        intro hrs
        subst s
        apply hvZ
        change v ∈ redBlockUnion C N blockColor i
        rw [redBlockUnion, mem_biUnion]
        refine ⟨r, ?_, hvr⟩
        rw [redBlockIndices, mem_filter]
        exact ⟨hsN, hcolor⟩
      have hrJ : r < Dyadic.levelStart J :=
        (mem_range.mp hrP'.1).trans_le (Dyadic.levelStart_mono hellSuccJ)
      have hsJ := selected_lt_J s hsN
      apply S.blocks_anticomplete r hrJ s hsJ hrs
      rcases hadjS with ⟨x, hx, y, hy, hxy⟩
      have hxv : x = v := by simpa using hx
      subst x
      exact ⟨v, hvr, y, hy, hxy⟩
  have hres := lowVertices_after_red_delete_subset_residual'
    (G := G) phi S.hk hZA (hphi.minDegree i) hneigh hprefix
  simpa [Z, deficitResidual] using hres

omit [Fintype I] [Fintype V] in

lemma redBlockUnion_subset_uncoloredPrefixUnion_succ
    {k ell : ℕ} {C : List (Finset V)} {phi : PartialColoring V k}
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (blockColor : ℕ → Option I) (i : I) :
    redBlockUnion C N blockColor i ⊆
      uncoloredPrefixUnion C phi (ell + 1) := by
  classical
  intro v hv
  rw [redBlockUnion, mem_biUnion] at hv
  obtain ⟨r, hr, hvr⟩ := hv
  have hrN : r ∈ N := (mem_filter.mp hr).1
  have hrU := hN hrN
  rw [uncoloredCurrentIndices, mem_filter] at hrU
  rw [uncoloredPrefixUnion, mem_biUnion]
  refine ⟨r, ?_, hvr⟩
  rw [uncoloredPrefixIndices, mem_filter]
  exact ⟨mem_range.mpr ((Dyadic.mem_levelIndices.mp hrU.1).2), hrU.2⟩

omit [Fintype V] in

lemma deficitResidual_subset_currentColorAmbient
    {A : Finset V} {k ell : ℕ} {C : List (Finset V)}
    {phi : PartialColoring V k}
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (blockColor : ℕ → Option (Color k)) (i : Color k) :
    deficitResidual A C phi (ell + 1) ⊆
      (A \ colorClass A phi i) \ redBlockUnion C N blockColor i := by
  classical
  intro v hv
  rw [deficitResidual, mem_sdiff] at hv
  refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hv.1, ?_⟩, ?_⟩
  · intro hvclass
    apply hv.2
    exact mem_union_left _ (colorClass_subset_coloredVertices A phi i hvclass)
  · intro hvZ
    apply hv.2
    exact mem_union_right _
      (redBlockUnion_subset_uncoloredPrefixUnion_succ
        N hN blockColor i hvZ)

lemma redBlockUnion_subset_oldColorComplement
    {A : Finset V} {k ell J : ℕ} {C : List (Finset V)}
    {phi : PartialColoring V k} {t : ℤ} {J0 : ℕ}
    (S : ColoringSystem G A k t C J0 J)
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (hellJ : ell < J)
    (blockColor : ℕ → Option (Color k)) (i : Color k) :
    redBlockUnion C N blockColor i ⊆ A \ colorClass A phi i := by
  classical
  intro v hv
  rw [redBlockUnion, mem_biUnion] at hv
  obtain ⟨r, hr, hvr⟩ := hv
  have hrN : r ∈ N := (mem_filter.mp hr).1
  have hrU := hN hrN
  rw [uncoloredCurrentIndices, mem_filter, Dyadic.mem_levelIndices] at hrU
  have hrJ : r < Dyadic.levelStart J := hrU.1.2.trans_le
    (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ))
  have hvA := S.block_subset r hrJ hvr
  refine mem_sdiff.mpr ⟨hvA, ?_⟩
  intro hvclass
  have hvcolor : phi v = some i := (mem_filter.mp hvclass).2
  have hvnone := hrU.2 v hvr
  rw [hvnone] at hvcolor
  contradiction

lemma futureBlock_neighbor_mem_deficitResidual_succ
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J r : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hr : Dyadic.levelStart (ell + 1) ≤ r)
    (hrJ : r < Dyadic.levelStart J)
    (hu : BlockUncolored phi (C.getD r ∅))
    {x v : V} (hx : x ∈ C.getD r ∅) (hvA : v ∈ A)
    (hxv : G.Adj x v) :
    v ∈ deficitResidual A C phi (ell + 1) := by
  classical
  have hrell : Dyadic.levelStart ell ≤ r :=
    (Dyadic.levelStart_le_succ ell).trans hr
  have hvnone : phi v = none := hphi.future r hrell hrJ hu x hx v hvA hxv
  rw [deficitResidual, mem_sdiff]
  refine ⟨hvA, ?_⟩
  intro hvbad
  rcases mem_union.mp hvbad with hvcolored | hvprefix
  · rw [mem_coloredVertices_iff] at hvcolored
    obtain ⟨_, i, hi⟩ := hvcolored
    rw [hvnone] at hi
    contradiction
  · rw [uncoloredPrefixUnion, mem_biUnion] at hvprefix
    obtain ⟨s, hs, hvs⟩ := hvprefix
    have hs' : s ∈ Finset.range (Dyadic.levelStart (ell + 1)) ∧
        BlockUncolored phi (C.getD s ∅) := by
      simpa [uncoloredPrefixIndices] using hs
    have hslt : s < Dyadic.levelStart (ell + 1) := mem_range.mp hs'.1
    have hsr : s ≠ r := by omega
    have hsJ : s < Dyadic.levelStart J := (hslt.trans_le hr).trans hrJ
    apply S.blocks_anticomplete s hsJ r hrJ hsr
    exact ⟨v, hvs, x, hx, hxv.symm⟩

lemma extensionDiff_anticomplete_futureBlock
    {A Atilde H : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J r : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hAtilde : Atilde ⊆ A)
    (hH : H = deficitResidual A C phi (ell + 1))
    (hr : Dyadic.levelStart (ell + 1) ≤ r)
    (hrJ : r < Dyadic.levelStart J)
    (hu : BlockUncolored phi (C.getD r ∅)) :
    Anticomplete G (Atilde \ H) (C.getD r ∅) := by
  intro hadj
  rcases hadj with ⟨v, hv, x, hx, hvx⟩
  have hvres := futureBlock_neighbor_mem_deficitResidual_succ
    S hphi hr hrJ hu hx (hAtilde (mem_sdiff.mp hv).1) hvx.symm
  exact (mem_sdiff.mp hv).2 (by simpa [hH] using hvres)

omit [DecidableEq I] [Fintype I] in

lemma extensionDiff_anticomplete_protectedFutureFamily
    {A H : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (CH : ProtectedFamily G H k)
    (hH : H = deficitResidual A C phi (ell + 1))
    (Atilde : I → Finset V) (hAtilde : ∀ i, Atilde i ⊆ A)
    (hfuture : ∀ D ∈ CH.blocks, ∃ r,
      Dyadic.levelStart (ell + 1) ≤ r ∧
      r < Dyadic.levelStart J ∧
      BlockUncolored phi (C.getD r ∅) ∧ D = C.getD r ∅) :
    ∀ i D, D ∈ CH.blocks → Anticomplete G (Atilde i \ H) D := by
  intro i D hD
  obtain ⟨r, hr, hrJ, hu, rfl⟩ := hfuture D hD
  exact extensionDiff_anticomplete_futureBlock S hphi (hAtilde i) hH
    hr hrJ hu

lemma degreeOn_add_card_le_of_outward_neighbor_supply
    {H A W : Finset V} {s : V}
    (hHA : H ⊆ A) (hWA : W ⊆ A) (hWH : Disjoint W H)
    (hWnbr : ∀ w ∈ W, G.Adj s w) :
    degreeOn G H s + W.card ≤ degreeOn G A s := by
  classical
  let NH := G.neighborFinset s ∩ H
  have hNHcard : NH.card = degreeOn G H s := rfl
  have hdisj : Disjoint NH W := by
    rw [Finset.disjoint_left]
    intro x hxNH hxW
    exact Finset.disjoint_left.mp hWH hxW (mem_inter.mp hxNH).2
  have hsub : NH ∪ W ⊆ G.neighborFinset s ∩ A := by
    intro x hx
    rcases mem_union.mp hx with hxNH | hxW
    · exact mem_inter.mpr ⟨(mem_inter.mp hxNH).1,
        hHA (mem_inter.mp hxNH).2⟩
    · exact mem_inter.mpr ⟨by simpa using hWnbr x hxW, hWA hxW⟩
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hdisj, hNHcard] at hc
  exact hc

omit [DecidableRel G.Adj] [Fintype V] in

lemma exists_neighborRepresentatives_of_pairwiseDisjoint
    {Q : Finset ℕ} {block : ℕ → Finset V} {s : V}
    (hpair : (Q : Set ℕ).PairwiseDisjoint block)
    (hadj : ∀ r ∈ Q, AdjacentSets G {s} (block r)) :
    ∃ W : Finset V, W.card = Q.card ∧
      W ⊆ Q.biUnion block ∧ ∀ w ∈ W, G.Adj s w := by
  classical
  have hex : ∀ r : ℕ, r ∈ Q → ∃ w ∈ block r, G.Adj s w := by
    intro r hr
    rcases hadj r hr with ⟨x, hx, w, hw, hxw⟩
    have hxs : x = s := by simpa using hx
    subst x
    exact ⟨w, hw, hxw⟩
  let pick : {r // r ∈ Q} → V := fun r ↦ Classical.choose (hex r r.property)
  have pick_mem : ∀ r : {r // r ∈ Q}, pick r ∈ block r := by
    intro r
    exact (Classical.choose_spec (hex r r.property)).1
  have pick_adj : ∀ r : {r // r ∈ Q}, G.Adj s (pick r) := by
    intro r
    exact (Classical.choose_spec (hex r r.property)).2
  have hinj : Function.Injective pick := by
    intro r q heq
    apply Subtype.ext
    by_contra hrq
    have hd := hpair r.property q.property hrq
    exact Finset.disjoint_left.mp hd (pick_mem r) (heq ▸ pick_mem q)
  refine ⟨Q.attach.image pick, ?_, ?_, ?_⟩
  · rw [Finset.card_image_iff.mpr (fun r _ q _ h ↦ hinj h)]
    exact Finset.card_attach
  · intro w hw
    rw [mem_image] at hw
    obtain ⟨r, hr, rfl⟩ := hw
    exact mem_biUnion.mpr ⟨r, r.property, pick_mem r⟩
  · intro w hw
    rw [mem_image] at hw
    obtain ⟨r, hr, rfl⟩ := hw
    exact pick_adj r

lemma colorSet_card_le_degreeOn
    {A : Finset V} {k : ℕ} (phi : PartialColoring V k)
    {L : Finset (Color k)} {s : V}
    (hneigh : ∀ i ∈ L, ∃ v ∈ A, G.Adj s v ∧ phi v = some i) :
    L.card ≤ degreeOn G A s := by
  classical
  have hex : ∀ i : Color k, i ∈ L →
      ∃ v ∈ A, G.Adj s v ∧ phi v = some i := hneigh
  let pick : {i // i ∈ L} → V := fun i ↦ Classical.choose (hex i i.property)
  have pick_mem : ∀ i : {i // i ∈ L}, pick i ∈ A := by
    intro i
    exact (Classical.choose_spec (hex i i.property)).1
  have pick_adj : ∀ i : {i // i ∈ L}, G.Adj s (pick i) := by
    intro i
    exact (Classical.choose_spec (hex i i.property)).2.1
  have pick_color : ∀ i : {i // i ∈ L}, phi (pick i) = some i := by
    intro i
    exact (Classical.choose_spec (hex i i.property)).2.2
  have hinj : Function.Injective pick := by
    intro i j heq
    apply Subtype.ext
    exact Option.some.inj ((pick_color i).symm.trans (heq ▸ pick_color j))
  have himage : L.attach.image pick ⊆ G.neighborFinset s ∩ A := by
    intro v hv
    rw [mem_image] at hv
    obtain ⟨i, hi, rfl⟩ := hv
    exact mem_inter.mpr ⟨by simpa using pick_adj i, pick_mem i⟩
  have hc := card_le_card himage
  rw [Finset.card_image_iff.mpr (fun i _ j _ h ↦ hinj h), Finset.card_attach] at hc
  exact hc

lemma degreeOn_eq_of_adjacent_membership_iff
    {A B : Finset V} {s : V}
    (h : ∀ v, G.Adj s v → (v ∈ A ↔ v ∈ B)) :
    degreeOn G A s = degreeOn G B s := by
  unfold degreeOn
  congr 1
  ext v
  simp only [mem_inter, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨hsv, hvA⟩
    exact ⟨hsv, (h v hsv).mp hvA⟩
  · rintro ⟨hsv, hvB⟩
    exact ⟨hsv, (h v hsv).mpr hvB⟩

omit [DecidableEq V] [Fintype V] in
lemma PopularScratch.neighborColorList_eq_of_card_le
    {A : Finset V} {k : ℕ} (phi : PartialColoring V k) (s : V)
    (hcard : (PopularScratch.neighborColorSet G A phi s).card ≤ k) :
    PopularScratch.neighborColorList G A phi s =
      PopularScratch.neighborColorSet G A phi s := by
  classical
  apply Finset.eq_of_subset_of_card_le
    (PopularScratch.neighborColorList_subset G A phi s)
  rw [PopularScratch.neighborColorList,
    PopularScratch.card_chooseMinSubset, Nat.min_eq_left hcard]

lemma certificateVertex_degree_ge_of_greedy_cases
    {H B Z Atilde : Finset V} {k : ℕ}
    (phi : PartialColoring V k)
    (_hk : 2 ≤ k) (hHtilde : H ⊆ Atilde) (hZB : Z ⊆ B)
    (hAtilde : Atilde = B \ Z) (hminB : HasMinDegreeOn G B k)
    {s : V} (hsH : s ∈ H) (_hslow : degreeOn G H s ≤ k - 1)
    (hcases :
      ¬ AdjacentSets G {s} Z ∨
      (∃ W : Finset V, W ⊆ Atilde ∧ Disjoint W H ∧
        (∀ w ∈ W, G.Adj s w) ∧
        k - degreeOn G H s ≤ W.card) ∨
      (∃ L : Finset (Color k), k ≤ L.card ∧
        ∀ i ∈ L, ∃ v ∈ Atilde, G.Adj s v ∧
          phi v = some i) ∨
      (∃ AminusD : Finset V, s ∈ AminusD ∧
        HasMinDegreeOn G AminusD k ∧
        degreeOn G Atilde s = degreeOn G AminusD s)) :
    k ≤ degreeOn G Atilde s := by
  rcases hcases with hno | hfull | hold | hshort
  · have hsAtilde : s ∈ Atilde := hHtilde hsH
    have hsBZ : s ∈ B \ Z := by simpa [hAtilde] using hsAtilde
    have hsB : s ∈ B := (mem_sdiff.mp hsBZ).1
    have heq := degreeOn_sdiff_eq_of_not_adjacent (G := G) hZB hno
    rw [hAtilde, heq]
    exact hminB.2 s hsB
  · obtain ⟨W, hWA, hWH, hWnbr, hcard⟩ := hfull
    have hsupply := degreeOn_add_card_le_of_outward_neighbor_supply
      (G := G) hHtilde hWA hWH hWnbr
    omega
  · obtain ⟨L, hLcard, hL⟩ := hold
    have hc : L.card ≤ degreeOn G Atilde s := by
      apply colorSet_card_le_degreeOn (G := G) (phi := phi)
      intro i hi
      exact hL i hi
    omega
  · obtain ⟨AminusD, hsD, hminD, heq⟩ := hshort
    rw [heq]
    exact hminD.2 s hsD

lemma lowVertex_currentBlock_color_description
    {A H : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hellJ : ell < J)
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (blockColor : ℕ → Option (Color k))
    (CH : ProtectedFamily G H k)
    (E : ExtensionCertificate G H k CH)
    (hH : H = deficitResidual A C phi (ell + 1))
    (hprotect : ∀ i s, s ∈ E.S →
      s ∈ ((A \ colorClass A phi i) \ redBlockUnion C N blockColor i) →
      k ≤ degreeOn G
        ((A \ colorClass A phi i) \ redBlockUnion C N blockColor i) s)
    (i : Color k) (v : V)
    (hv : v ∈ lowVertices G
      ((A \ colorClass A phi i) \ redBlockUnion C N blockColor i) k) :
    (∃ r ∈ N, blockColor r = some i ∧
      AdjacentSets G {v} (C.getD r ∅)) ∧
    (∀ q ∈ uncoloredCurrentIndices C phi ell,
      AdjacentSets G {v} (C.getD q ∅) → blockColor q = some i) := by
  classical
  let Z := redBlockUnion C N blockColor i
  let B := A \ colorClass A phi i
  let At := B \ Z
  have hZB : Z ⊆ B := by
    simpa [Z, B] using redBlockUnion_subset_oldColorComplement
      S N hN hellJ blockColor i
  have hvdata : v ∈ At ∧ degreeOn G At v ≤ k - 1 := by
    simpa [At, B, Z] using (mem_lowVertices.mp hv)
  have hadjZ : AdjacentSets G {v} Z :=
    adjacent_of_low_after_delete (G := G) S.hk hZB hvdata.1
      (by simpa [B] using
        (hphi.minDegree i).2 v (mem_sdiff.mp hvdata.1).1) hvdata.2
  have hfirst : ∃ r ∈ N, blockColor r = some i ∧
      AdjacentSets G {v} (C.getD r ∅) := by
    exact adjacent_block_of_adjacent_redBlockUnion C N blockColor i hadjZ
  refine ⟨hfirst, ?_⟩
  have hinside := lowVertices_currentColor_subset_deficitResidual_succ
    S hphi hellJ N hN blockColor i hv
  have hvH : v ∈ H := by simpa [hH] using hinside
  have hHAt : H ⊆ At := by
    intro x hx
    have hx' : x ∈ deficitResidual A C phi (ell + 1) := by simpa [hH] using hx
    simpa [At, B, Z] using
      (deficitResidual_subset_currentColorAmbient N hN blockColor i hx')
  have hdegHle : degreeOn G H v ≤ k - 1 :=
    (degreeOn_mono G hHAt v).trans hvdata.2
  have hvnotS : v ∉ E.S := by
    intro hvS
    have hhigh := hprotect i v hvS (by simpa [At, B, Z] using hvdata.1)
    change k ≤ degreeOn G At v at hhigh
    have hlow := hvdata.2
    have hbad : k ≤ k - 1 := hhigh.trans hlow
    have hk := S.hk
    omega
  have hdegH : degreeOn G H v = k - 1 := by
    have hnvery : v ∉ veryLowVertices G H k := by
      intro hvery
      exact hvnotS (E.veryLow_subset_S hvery)
    have hlower : k - 1 ≤ degreeOn G H v := by
      by_contra hnot
      apply hnvery
      rw [mem_veryLowVertices]
      exact ⟨hvH, by omega⟩
    omega
  have hdegAt : degreeOn G At v = k - 1 := by
    have hmono := degreeOn_mono G hHAt v
    omega
  intro q hqU hadjq
  by_contra hqcolor
  have hqData : q ∈ Dyadic.levelIndices ell ∧
      BlockUncolored phi (C.getD q ∅) := by
    simpa [uncoloredCurrentIndices] using hqU
  have hqRange := Dyadic.mem_levelIndices.mp hqData.1
  have hellSuccJ : ell + 1 ≤ J := Nat.succ_le_iff.mpr hellJ
  have hqJ : q < Dyadic.levelStart J := hqRange.2.trans_le
    (Dyadic.levelStart_mono hellSuccJ)
  rcases hadjq with ⟨x, hx, y, hy, hxy⟩
  have hxv : x = v := by simpa using hx
  subst x
  have hyAt : y ∈ At := by
    have hyA := S.block_subset q hqJ hy
    have hyB : y ∈ B := by
      refine mem_sdiff.mpr ⟨hyA, ?_⟩
      intro hyclass
      have hycolor : phi y = some i := (mem_filter.mp hyclass).2
      have hynone := hqData.2 y hy
      rw [hynone] at hycolor
      contradiction
    refine mem_sdiff.mpr ⟨hyB, ?_⟩
    intro hyZ
    change y ∈ redBlockUnion C N blockColor i at hyZ
    rw [redBlockUnion, mem_biUnion] at hyZ
    obtain ⟨r, hr, hyr⟩ := hyZ
    have hrN : r ∈ N := (mem_filter.mp hr).1
    have hrcolor : blockColor r = some i := (mem_filter.mp hr).2
    have hrU := hN hrN
    have hrData : r ∈ Dyadic.levelIndices ell ∧
        BlockUncolored phi (C.getD r ∅) := by
      simpa [uncoloredCurrentIndices] using hrU
    have hrRange := Dyadic.mem_levelIndices.mp hrData.1
    have hrJ : r < Dyadic.levelStart J := hrRange.2.trans_le
      (Dyadic.levelStart_mono hellSuccJ)
    by_cases hqr : q = r
    · subst r
      exact hqcolor hrcolor
    · exact Finset.disjoint_left.mp
        (S.blocks_disjoint q hqJ r hrJ hqr) hy hyr
  have hyNotH : y ∉ H := by
    intro hyH
    have hyRes : y ∈ deficitResidual A C phi (ell + 1) := by simpa [hH] using hyH
    rw [deficitResidual, mem_sdiff] at hyRes
    apply hyRes.2
    apply mem_union_right
    rw [uncoloredPrefixUnion, mem_biUnion]
    refine ⟨q, ?_, hy⟩
    rw [uncoloredPrefixIndices, mem_filter]
    exact ⟨mem_range.mpr hqRange.2, hqData.2⟩
  have hsupply : degreeOn G H v + 1 ≤ degreeOn G At v := by
    have h := degreeOn_add_card_le_of_outward_neighbor_supply
      (G := G) hHAt (W := {y}) (A := At)
      (by simpa using hyAt)
      (by simp [hyNotH])
      (by
        intro w hw
        have hwy : w = y := by simpa using hw
        subst w
        exact hxy)
    simpa using h
  omega

structure PerColorExtensionConclusion
    (C : ProtectedFamily G H k) (E : ExtensionCertificate G H k C)
    (Atilde : I → Finset V) where
  retained : I → Finset V
  X : I → Finset V
  deleted_eq : ∀ i, X i = Atilde i \ retained i
  retained_eq : ∀ i, retained i = Atilde i \ X i
  X_subset_H : ∀ i, X i ⊆ H
  X_subset_reserves : ∀ i, X i ⊆ reserveUnion E.reserve G (Atilde i) k
  incidence : ∀ i,
    incidentCount G (Atilde i) (X i) ≤ (k - 1) * (X i).card
  minDegree : ∀ i, HasMinDegreeOn G (retained i) k
  whole_blocks_deleted : ∀ i D, D ∈ C.blocks →
    D ⊆ X i ∨ Disjoint D (X i)
  retained_blocks_anticomplete : ∀ i D, D ∈ C.blocks →
    Disjoint D (X i) → Anticomplete G D (X i)
  disjoint_from_old : ∀ D, Disjoint D H → ∀ i, Disjoint D (X i)
  low_index_description : ∀ i x, x ∈ X i →
    ∃ v ∈ lowVertices G (Atilde i) k,
      x ∈ E.reserve v
  pairwise_X : ∀ i j, i ≠ j → Disjoint (X i) (X j)

omit [DecidableEq I] [Fintype I] in

theorem apply_extension_per_color
    {H : Finset V} {k : ℕ}
    (C : ProtectedFamily G H k) (E : ExtensionCertificate G H k C)
    (hk : 2 ≤ k)
    (Atilde : I → Finset V)
    (hH : ∀ i, H ⊆ Atilde i)
    (hproper : ∀ i, H ⊂ Atilde i)
    (hinside : ∀ i, lowVertices G (Atilde i) k ⊆ H)
    (hprotect : ∀ i s, s ∈ E.S → s ∈ Atilde i →
      k ≤ degreeOn G (Atilde i) s)
    (hnew : ∀ i D, D ∈ C.blocks →
      Anticomplete G (Atilde i \ H) D)
    (selectedBlocks : Finset (Finset V))
    (blockColor : Finset V → Option I)
    (hred : ∀ i v, v ∈ lowVertices G (Atilde i) k →
      (∃ D ∈ selectedBlocks, AdjacentSets G {v} D) ∧
      (∀ D ∈ selectedBlocks, AdjacentSets G {v} D →
        blockColor D = some i)) :
    Nonempty (PerColorExtensionConclusion C E Atilde) := by
  classical
  have hlow : ∀ i,
      lowVertices G (Atilde i) k ⊆ lowVertices G H k \ E.S := by
    intro i v hv
    have hvdata := mem_lowVertices.mp hv
    have hvH : v ∈ H := hinside i hv
    have hvlowH : degreeOn G H v ≤ k - 1 :=
      (degreeOn_mono G (hH i) v).trans hvdata.2
    refine mem_sdiff.mpr ⟨mem_lowVertices.mpr ⟨hvH, hvlowH⟩, ?_⟩
    intro hvS
    have hhigh := hprotect i v hvS hvdata.1
    omega
  have hext : ∀ i, ∃ U' : Finset V, ExtensionConclusion C E.reserve (Atilde i) U' := by
    intro i
    exact E.extension (Atilde i) (hproper i) (hlow i) (hnew i)
  let U' : I → Finset V := fun i ↦ Classical.choose (hext i)
  have hR : ∀ i, ExtensionConclusion C E.reserve (Atilde i) (U' i) :=
    fun i ↦ Classical.choose_spec (hext i)
  let X : I → Finset V := fun i ↦ Atilde i \ U' i
  have hret : ∀ i, U' i = Atilde i \ X i := by
    intro i
    ext x
    constructor
    · intro hx
      exact mem_sdiff.mpr ⟨(hR i).subset_extension hx, by
        intro hxX
        exact (mem_sdiff.mp hxX).2 hx⟩
    · intro hx
      rw [mem_sdiff] at hx
      by_contra hxU
      exact hx.2 (mem_sdiff.mpr ⟨hx.1, hxU⟩)
  have hXH : ∀ i, X i ⊆ H := fun i ↦ (hR i).deleted_subset_old
  have hXres : ∀ i, X i ⊆ reserveUnion E.reserve G (Atilde i) k :=
    fun i ↦ (hR i).deleted_subset_reserves
  have hindex_unique : ∀ i j v,
      v ∈ lowVertices G (Atilde i) k →
      v ∈ lowVertices G (Atilde j) k → i = j := by
    intro i j v hvi hvj
    obtain ⟨D, hDB, hvD⟩ := (hred i v hvi).1
    have hi := (hred i v hvi).2 D hDB hvD
    have hj := (hred j v hvj).2 D hDB hvD
    exact Option.some.inj (hi.symm.trans hj)
  have hpair : ∀ i j, i ≠ j → Disjoint (X i) (X j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    have hri := hXres i hxi
    have hrj := hXres j hxj
    rw [reserveUnion, mem_biUnion] at hri hrj
    obtain ⟨v, hvi, hxv⟩ := hri
    obtain ⟨w, hwj, hxw⟩ := hrj
    have hviOld := hlow i hvi
    have hwjOld := hlow j hwj
    have hvw : v = w := by
      by_contra hvw
      have hd := E.reserve_pairwise v hviOld w hwjOld hvw
      exact (Finset.disjoint_left.mp hd) hxv hxw
    subst w
    exact hij (hindex_unique i j v hvi hwj)
  refine ⟨{
    retained := U'
    X := X
    deleted_eq := fun _ ↦ rfl
    retained_eq := hret
    X_subset_H := hXH
    X_subset_reserves := hXres
    incidence := ?_
    minDegree := fun i ↦ (hR i).minDegree
    whole_blocks_deleted := ?_
    retained_blocks_anticomplete := ?_
    disjoint_from_old := ?_
    low_index_description := ?_
    pairwise_X := hpair }⟩
  · intro i
    exact incidentCount_deleted_le_of_shortage_le
      (hR i).subset_extension (hR i).shortage_le
  · intro i D hDC
    rcases (hR i).blocks_whole D hDC with hDU | hdisj
    · right
      rw [Finset.disjoint_left]
      intro x hxD hxX
      exact (mem_sdiff.mp hxX).2 (hDU hxD)
    · left
      intro x hxD
      refine mem_sdiff.mpr ⟨hH i (C.subset_ambient D hDC hxD), ?_⟩
      exact fun hxU ↦ Finset.disjoint_left.mp hdisj hxD hxU
  · intro i D hDC hDX
    apply (hR i).retained_blocks_anticomplete D hDC
    intro x hxD
    by_contra hxU
    have hxX : x ∈ X i :=
      mem_sdiff.mpr ⟨hH i (C.subset_ambient D hDC hxD), hxU⟩
    exact Finset.disjoint_left.mp hDX hxD hxX
  · intro D hDH i
    exact hDH.mono_right (hXH i)
  · intro i x hx
    have hr := hXres i hx
    rw [reserveUnion, mem_biUnion] at hr
    exact hr

omit [DecidableEq I] [Fintype I] in

theorem apply_extension_per_color_of_unique
    {H : Finset V} {k : ℕ}
    (C : ProtectedFamily G H k) (E : ExtensionCertificate G H k C)
    (hk : 2 ≤ k)
    (Atilde : I → Finset V)
    (hH : ∀ i, H ⊆ Atilde i)
    (hproper : ∀ i, H ⊂ Atilde i)
    (hinside : ∀ i, lowVertices G (Atilde i) k ⊆ H)
    (hprotect : ∀ i s, s ∈ E.S → s ∈ Atilde i →
      k ≤ degreeOn G (Atilde i) s)
    (hnew : ∀ i D, D ∈ C.blocks → Anticomplete G (Atilde i \ H) D)
    (hunique : ∀ i j v,
      v ∈ lowVertices G (Atilde i) k →
      v ∈ lowVertices G (Atilde j) k → i = j) :
    Nonempty (PerColorExtensionConclusion C E Atilde) := by
  classical
  have hlow : ∀ i,
      lowVertices G (Atilde i) k ⊆ lowVertices G H k \ E.S := by
    intro i v hv
    have hvdata := mem_lowVertices.mp hv
    have hvH : v ∈ H := hinside i hv
    have hvlowH : degreeOn G H v ≤ k - 1 :=
      (degreeOn_mono G (hH i) v).trans hvdata.2
    refine mem_sdiff.mpr ⟨mem_lowVertices.mpr ⟨hvH, hvlowH⟩, ?_⟩
    intro hvS
    have hhigh := hprotect i v hvS hvdata.1
    omega
  have hext : ∀ i, ∃ U' : Finset V,
      ExtensionConclusion C E.reserve (Atilde i) U' := by
    intro i
    exact E.extension (Atilde i) (hproper i) (hlow i) (hnew i)
  let U' : I → Finset V := fun i ↦ Classical.choose (hext i)
  have hR : ∀ i, ExtensionConclusion C E.reserve (Atilde i) (U' i) :=
    fun i ↦ Classical.choose_spec (hext i)
  let X : I → Finset V := fun i ↦ Atilde i \ U' i
  have hret : ∀ i, U' i = Atilde i \ X i := by
    intro i
    ext x
    constructor
    · intro hx
      exact mem_sdiff.mpr ⟨(hR i).subset_extension hx, by
        intro hxX
        exact (mem_sdiff.mp hxX).2 hx⟩
    · intro hx
      rw [mem_sdiff] at hx
      by_contra hxU
      exact hx.2 (mem_sdiff.mpr ⟨hx.1, hxU⟩)
  have hXH : ∀ i, X i ⊆ H := fun i ↦ (hR i).deleted_subset_old
  have hXres : ∀ i, X i ⊆ reserveUnion E.reserve G (Atilde i) k :=
    fun i ↦ (hR i).deleted_subset_reserves
  have hpair : ∀ i j, i ≠ j → Disjoint (X i) (X j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    have hri := hXres i hxi
    have hrj := hXres j hxj
    rw [reserveUnion, mem_biUnion] at hri hrj
    obtain ⟨v, hvi, hxv⟩ := hri
    obtain ⟨w, hwj, hxw⟩ := hrj
    have hviOld := hlow i hvi
    have hwjOld := hlow j hwj
    have hvw : v = w := by
      by_contra hvw
      have hd := E.reserve_pairwise v hviOld w hwjOld hvw
      exact (Finset.disjoint_left.mp hd) hxv hxw
    subst w
    exact hij (hunique i j v hvi hwj)
  refine ⟨{
    retained := U'
    X := X
    deleted_eq := fun _ ↦ rfl
    retained_eq := hret
    X_subset_H := hXH
    X_subset_reserves := hXres
    incidence := ?_
    minDegree := fun i ↦ (hR i).minDegree
    whole_blocks_deleted := ?_
    retained_blocks_anticomplete := ?_
    disjoint_from_old := ?_
    low_index_description := ?_
    pairwise_X := hpair }⟩
  · intro i
    exact incidentCount_deleted_le_of_shortage_le
      (hR i).subset_extension (hR i).shortage_le
  · intro i D hDC
    rcases (hR i).blocks_whole D hDC with hDU | hdisj
    · right
      rw [Finset.disjoint_left]
      intro x hxD hxX
      exact (mem_sdiff.mp hxX).2 (hDU hxD)
    · left
      intro x hxD
      refine mem_sdiff.mpr ⟨hH i (C.subset_ambient D hDC hxD), ?_⟩
      exact fun hxU ↦ Finset.disjoint_left.mp hdisj hxD hxU
  · intro i D hDC hDX
    apply (hR i).retained_blocks_anticomplete D hDC
    intro x hxD
    by_contra hxU
    have hxX : x ∈ X i :=
      mem_sdiff.mpr ⟨hH i (C.subset_ambient D hDC hxD), hxU⟩
    exact Finset.disjoint_left.mp hDX hxD hxX
  · intro D hDH i
    exact hDH.mono_right (hXH i)
  · intro i x hx
    have hr := hXres i hx
    rw [reserveUnion, mem_biUnion] at hr
    exact hr

omit [DecidableEq I] [Fintype I] in

theorem apply_extension_per_color_indices
    {H : Finset V} {k : ℕ}
    (C : ProtectedFamily G H k) (E : ExtensionCertificate G H k C)
    (hk : 2 ≤ k) (blocks : List (Finset V))
    (Atilde : I → Finset V)
    (hH : ∀ i, H ⊆ Atilde i)
    (hproper : ∀ i, H ⊂ Atilde i)
    (hinside : ∀ i, lowVertices G (Atilde i) k ⊆ H)
    (hprotect : ∀ i s, s ∈ E.S → s ∈ Atilde i →
      k ≤ degreeOn G (Atilde i) s)
    (hnew : ∀ i D, D ∈ C.blocks → Anticomplete G (Atilde i \ H) D)
    (Uidx : Finset ℕ) (blockColor : ℕ → Option I)
    (hred : ∀ i v, v ∈ lowVertices G (Atilde i) k →
      (∃ r ∈ Uidx, blockColor r = some i ∧
        AdjacentSets G {v} (blocks.getD r ∅)) ∧
      (∀ r ∈ Uidx, AdjacentSets G {v} (blocks.getD r ∅) →
        blockColor r = some i)) :
    Nonempty (PerColorExtensionConclusion C E Atilde) := by
  apply apply_extension_per_color_of_unique C E hk Atilde hH hproper hinside
    hprotect hnew
  intro i j v hvi hvj
  obtain ⟨⟨r, hr, hri, hadj⟩, halli⟩ := hred i v hvi
  have hrj := (hred j v hvj).2 r hr hadj
  exact Option.some.inj (hri.symm.trans hrj)

omit [DecidableEq I] [Fintype I] in

lemma PerColorExtensionConclusion.whole_blocks_deleted_of_restriction
    {A H : Finset V} {k : ℕ}
    {C : ProtectedFamily G H k} {E : ExtensionCertificate G H k C}
    {Atilde : I → Finset V}
    (R : PerColorExtensionConclusion C E Atilde)
    (C₀ : ProtectedFamily G A k)
    (hwhole : C₀.WholeBlocks H)
    (hblocks : ∀ D, D ∈ C.blocks ↔ D ∈ C₀.blocks ∧ D ⊆ H) :
    ∀ i D, D ∈ C₀.blocks → D ⊆ R.X i ∨ Disjoint D (R.X i) := by
  intro i D hD
  rcases hwhole D hD with hDH | hDH
  · exact R.whole_blocks_deleted i D ((hblocks D).2 ⟨hD, hDH⟩)
  · exact Or.inr (hDH.mono_right (R.X_subset_H i))

end ExtensionApplyScratch

noncomputable section

lemma selectedBlockUnion_incidence
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (hellJ : ell < J) (psi : ℕ → Color k) (i : Color k) :
    incidentCount G (A \ colorClass A phi i)
        (selectedBlockUnion C N psi i) ≤
      (k - 1) * (selectedBlockUnion C N psi i).card +
        (N.filter fun r ↦ psi r = i).card := by
  classical
  let R := N.filter fun r ↦ psi r = i
  let D : ℕ → Finset V := fun r ↦ C.getD r ∅
  have hellSuccJ : ell + 1 ≤ J := Nat.succ_le_iff.mpr hellJ
  have hrJ : ∀ r ∈ R, r < Dyadic.levelStart J := by
    intro r hr
    have hrN := hN (mem_filter.mp hr).1
    have hrlev : r ∈ Dyadic.levelIndices ell := by
      simpa [uncoloredCurrentIndices] using (mem_filter.mp hrN).1
    exact (Dyadic.mem_levelIndices.mp hrlev).2.trans_le
      (Dyadic.levelStart_mono hellSuccJ)
  have hpair : (R : Set ℕ).PairwiseDisjoint D := by
    intro r hr s hs hrs
    exact S.blocks_disjoint r (hrJ r hr) s (hrJ s hs) hrs
  have hsum := incidentCount_biUnion_le_sum (G := G)
    (A \ colorClass A phi i) R D
  calc
    incidentCount G (A \ colorClass A phi i)
        (selectedBlockUnion C N psi i) =
        incidentCount G (A \ colorClass A phi i) (R.biUnion D) := by rfl
    _ ≤ ∑ r ∈ R, incidentCount G (A \ colorClass A phi i) (D r) := hsum
    _ ≤ ∑ r ∈ R, ((k - 1) * (D r).card + 1) := by
      apply Finset.sum_le_sum
      intro r hr
      exact (incidentCount_ambient_mono (G := G)
        (A := A \ colorClass A phi i) (B := A) sdiff_subset).trans
          (S.block_incident r (hrJ r hr))
    _ = (k - 1) * (R.biUnion D).card + R.card := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.card_biUnion hpair]
      simp
    _ = (k - 1) * (selectedBlockUnion C N psi i).card +
        (N.filter fun r ↦ psi r = i).card := by rfl

lemma selectedBlockUnion_subset_A
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (hellJ : ell < J) (psi : ℕ → Color k) (i : Color k) :
    selectedBlockUnion C N psi i ⊆ A := by
  classical
  intro v hv
  rw [selectedBlockUnion, mem_biUnion] at hv
  obtain ⟨r, hr, hvr⟩ := hv
  have hrN := hN (mem_filter.mp hr).1
  have hrlev : r ∈ Dyadic.levelIndices ell := by
    simpa [uncoloredCurrentIndices] using (mem_filter.mp hrN).1
  have hrJ := (Dyadic.mem_levelIndices.mp hrlev).2.trans_le
    (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ))
  exact S.block_subset r hrJ hvr

omit [Fintype V] in
lemma selectedBlockUnion_uncolored
    {k ell : ℕ} {C : List (Finset V)} {phi : PartialColoring V k}
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (psi : ℕ → Color k) (i : Color k) :
    ∀ v ∈ selectedBlockUnion C N psi i, phi v = none := by
  classical
  intro v hv
  rw [selectedBlockUnion, mem_biUnion] at hv
  obtain ⟨r, hr, hvr⟩ := hv
  have hrN := hN (mem_filter.mp hr).1
  exact (mem_filter.mp hrN).2 v hvr

lemma selectedBlockUnion_pairwise
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (hellJ : ell < J) (psi : ℕ → Color k) :
    ∀ i j, i ≠ j →
      Disjoint (selectedBlockUnion C N psi i)
        (selectedBlockUnion C N psi j) := by
  classical
  intro i j hij
  rw [Finset.disjoint_left]
  intro v hvi hvj
  rw [selectedBlockUnion, mem_biUnion] at hvi hvj
  obtain ⟨r, hr, hvr⟩ := hvi
  obtain ⟨s, hs, hvs⟩ := hvj
  have hrN := hN (mem_filter.mp hr).1
  have hsN := hN (mem_filter.mp hs).1
  have hrlev : r ∈ Dyadic.levelIndices ell := by
    simpa [uncoloredCurrentIndices] using (mem_filter.mp hrN).1
  have hslev : s ∈ Dyadic.levelIndices ell := by
    simpa [uncoloredCurrentIndices] using (mem_filter.mp hsN).1
  have hrJ := (Dyadic.mem_levelIndices.mp hrlev).2.trans_le
    (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ))
  have hsJ := (Dyadic.mem_levelIndices.mp hslev).2.trans_le
    (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ))
  by_cases hrs : r = s
  · subst s
    exact hij ((mem_filter.mp hr).2.symm.trans (mem_filter.mp hs).2)
  · exact Finset.disjoint_left.mp
      (S.blocks_disjoint r hrJ s hsJ hrs) hvr hvs

omit [Fintype V] in
lemma selectedBlockUnion_disjoint_residual
    {A : Finset V} {k ell : ℕ} {C : List (Finset V)}
    {phi : PartialColoring V k}
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (psi : ℕ → Color k) (i : Color k) :
    Disjoint (selectedBlockUnion C N psi i)
      (deficitResidual A C phi (ell + 1)) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvZ hvH
  have hvPrefix : v ∈ uncoloredPrefixUnion C phi (ell + 1) := by
    rw [selectedBlockUnion, mem_biUnion] at hvZ
    obtain ⟨r, hr, hvr⟩ := hvZ
    have hrU := hN (mem_filter.mp hr).1
    rw [uncoloredPrefixUnion, mem_biUnion]
    refine ⟨r, ?_, hvr⟩
    rw [uncoloredPrefixIndices, mem_filter]
    exact ⟨mem_range.mpr (Dyadic.mem_levelIndices.mp (mem_filter.mp hrU).1).2,
      (mem_filter.mp hrU).2⟩
  exact (mem_sdiff.mp hvH).2 (mem_union_right _ hvPrefix)

lemma block_whole_deficitResidual
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J r : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hrJ : r < Dyadic.levelStart J) :
    C.getD r ∅ ⊆ deficitResidual A C phi (ell + 1) ∨
      Disjoint (C.getD r ∅) (deficitResidual A C phi (ell + 1)) := by
  classical
  rcases hphi.blocks r hrJ with ⟨i, hmono⟩ | hun
  · right
    rw [Finset.disjoint_left]
    intro v hvD hvH
    have hvA := S.block_subset r hrJ hvD
    have hvcol : v ∈ coloredVertices A phi :=
      mem_coloredVertices_iff.mpr ⟨hvA, i, hmono v hvD⟩
    exact (mem_sdiff.mp hvH).2 (mem_union_left _ hvcol)
  · by_cases hr : r < Dyadic.levelStart (ell + 1)
    · right
      rw [Finset.disjoint_left]
      intro v hvD hvH
      have hvprefix : v ∈ uncoloredPrefixUnion C phi (ell + 1) := by
        rw [uncoloredPrefixUnion, mem_biUnion]
        refine ⟨r, ?_, hvD⟩
        rw [uncoloredPrefixIndices, mem_filter]
        exact ⟨mem_range.mpr hr, hun⟩
      exact (mem_sdiff.mp hvH).2 (mem_union_right _ hvprefix)
    · left
      intro v hvD
      have hvA := S.block_subset r hrJ hvD
      refine mem_sdiff.mpr ⟨hvA, ?_⟩
      intro hvbad
      rcases mem_union.mp hvbad with hvcol | hvprefix
      · rw [mem_coloredVertices_iff] at hvcol
        obtain ⟨_, i, hi⟩ := hvcol
        have hn := hun v hvD
        rw [hn] at hi
        contradiction
      · rw [uncoloredPrefixUnion, mem_biUnion] at hvprefix
        obtain ⟨s, hs, hvs⟩ := hvprefix
        have hsData : s < Dyadic.levelStart (ell + 1) := by
          rw [uncoloredPrefixIndices, mem_filter] at hs
          exact mem_range.mp hs.1
        have hsJ : s < Dyadic.levelStart J :=
          (hsData.trans_le (Nat.le_of_not_gt hr)).trans hrJ
        have hrs : r ≠ s := by omega
        exact Finset.disjoint_left.mp
          (S.blocks_disjoint r hrJ s hsJ hrs) hvD hvs

lemma future_uncolored_block_subset_residual
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J r : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (_hphi : Appropriate G A k C J0 ell J phi)
    (hr : Dyadic.levelStart (ell + 1) ≤ r)
    (hrJ : r < Dyadic.levelStart J)
    (hun : BlockUncolored phi (C.getD r ∅)) :
    C.getD r ∅ ⊆ deficitResidual A C phi (ell + 1) := by
  classical
  intro v hvD
  have hvA := S.block_subset r hrJ hvD
  refine mem_sdiff.mpr ⟨hvA, ?_⟩
  intro hvbad
  rcases mem_union.mp hvbad with hvcol | hvprefix
  · rw [mem_coloredVertices_iff] at hvcol
    obtain ⟨_, i, hi⟩ := hvcol
    have hn := hun v hvD
    rw [hn] at hi
    contradiction
  · rw [uncoloredPrefixUnion, mem_biUnion] at hvprefix
    obtain ⟨s, hs, hvs⟩ := hvprefix
    have hslt : s < Dyadic.levelStart (ell + 1) := by
      rw [uncoloredPrefixIndices, mem_filter] at hs
      exact mem_range.mp hs.1
    have hsJ : s < Dyadic.levelStart J := hslt.trans_le (hr.trans hrJ.le)
    have hrs : r ≠ s := by omega
    exact Finset.disjoint_left.mp
      (S.blocks_disjoint r hrJ s hsJ hrs) hvD hvs

lemma block_subset_residual_is_future
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J r : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hrJ : r < Dyadic.levelStart J)
    (hsub : C.getD r ∅ ⊆ deficitResidual A C phi (ell + 1)) :
    Dyadic.levelStart (ell + 1) ≤ r := by
  classical
  by_contra hnot
  have hr : r < Dyadic.levelStart (ell + 1) := Nat.lt_of_not_ge hnot
  obtain ⟨v, hv⟩ := S.block_nonempty r hrJ
  have hvH := hsub hv
  rcases hphi.blocks r hrJ with ⟨i, hmono⟩ | hun
  · have hvA := S.block_subset r hrJ hv
    have hvcol : v ∈ coloredVertices A phi :=
      mem_coloredVertices_iff.mpr ⟨hvA, i, hmono v hv⟩
    exact (mem_sdiff.mp hvH).2 (mem_union_left _ hvcol)
  · have hvprefix : v ∈ uncoloredPrefixUnion C phi (ell + 1) := by
      rw [uncoloredPrefixUnion, mem_biUnion]
      refine ⟨r, ?_, hv⟩
      rw [uncoloredPrefixIndices, mem_filter]
      exact ⟨mem_range.mpr hr, hun⟩
    exact (mem_sdiff.mp hvH).2 (mem_union_right _ hvprefix)

lemma unselectedBlock_disjoint_selectedBlockUnion
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J r : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (hrJ : r < Dyadic.levelStart J) (hrN : r ∉ N)
    (hellJ : ell < J) (psi : ℕ → Color k) (i : Color k) :
    Disjoint (C.getD r ∅) (selectedBlockUnion C N psi i) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvr hvZ
  rw [selectedBlockUnion, mem_biUnion] at hvZ
  obtain ⟨s, hs, hvs⟩ := hvZ
  have hsN := (mem_filter.mp hs).1
  have hsU := hN hsN
  have hslev : s ∈ Dyadic.levelIndices ell := (mem_filter.mp hsU).1
  have hsJ := (Dyadic.mem_levelIndices.mp hslev).2.trans_le
    (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ))
  have hrs : r ≠ s := fun hrs ↦ hrN (hrs ▸ hsN)
  exact Finset.disjoint_left.mp (S.blocks_disjoint r hrJ s hsJ hrs) hvr hvs

lemma futureBlock_anticomplete_selectedBlockUnion
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J r : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (hr : Dyadic.levelStart (ell + 1) ≤ r)
    (hrJ : r < Dyadic.levelStart J) (hellJ : ell < J)
    (psi : ℕ → Color k) (i : Color k) :
    Anticomplete G (C.getD r ∅) (selectedBlockUnion C N psi i) := by
  classical
  intro hadj
  rcases hadj with ⟨v, hvr, w, hwZ, hvw⟩
  rw [selectedBlockUnion, mem_biUnion] at hwZ
  obtain ⟨s, hs, hws⟩ := hwZ
  have hsN := (mem_filter.mp hs).1
  have hsU := hN hsN
  have hslev : s ∈ Dyadic.levelIndices ell := (mem_filter.mp hsU).1
  have hsrange := Dyadic.mem_levelIndices.mp hslev
  have hsJ := hsrange.2.trans_le
    (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ))
  have hrs : r ≠ s := by omega
  exact S.blocks_anticomplete r hrJ s hsJ hrs ⟨v, hvr, w, hws, hvw⟩

lemma deficitResidual_ssubset_selectedColorAmbient
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hJ0ell : J0 ≤ ell) (hellJ : ell < J)
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (psi : ℕ → Color k) (i : Color k) :
    deficitResidual A C phi (ell + 1) ⊂
      (A \ colorClass A phi i) \ selectedBlockUnion C N psi i := by
  classical
  let H := deficitResidual A C phi (ell + 1)
  let Z := selectedBlockUnion C N psi i
  let B := (A \ colorClass A phi i) \ Z
  have hHB : H ⊆ B := by
    intro v hvH
    have hvA := (mem_sdiff.mp hvH).1
    refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hvA, ?_⟩, ?_⟩
    · intro hvclass
      exact (mem_sdiff.mp hvH).2 (mem_union_left _
        (colorClass_subset_coloredVertices A phi i hvclass))
    · intro hvZ
      exact Finset.disjoint_left.mp
        (selectedBlockUnion_disjoint_residual N hN psi i) hvZ hvH
  have hellpos : 0 < ell := S.hJ0.trans_le hJ0ell
  have hzeroJ : 0 < Dyadic.levelStart J := by
    have hJne : J ≠ 0 := Nat.ne_of_gt (hellpos.trans hellJ)
    simp [Dyadic.levelStart, hJne]
  obtain ⟨v, hvD⟩ := S.block_nonempty 0 hzeroJ
  have hvA := S.block_subset 0 hzeroJ hvD
  have hzeroEarly : 0 < Dyadic.levelStart J0 := by
    have hJ0ne : J0 ≠ 0 := Nat.ne_of_gt S.hJ0
    simp [Dyadic.levelStart, hJ0ne]
  have hvnone := hphi.early 0 hzeroEarly v hvD
  have hzeroN : 0 ∉ N := by
    intro hzN
    have hzU := hN hzN
    have hzlev : 0 ∈ Dyadic.levelIndices ell := (mem_filter.mp hzU).1
    have hzlow := (Dyadic.mem_levelIndices.mp hzlev).1
    have : 0 < Dyadic.levelStart ell := by
      have hellne : ell ≠ 0 := Nat.ne_of_gt hellpos
      simp [Dyadic.levelStart, hellne]
    omega
  have hDZ : Disjoint (C.getD 0 ∅) Z := by
    exact unselectedBlock_disjoint_selectedBlockUnion S N hN hzeroJ
      hzeroN hellJ psi i
  have hvB : v ∈ B := by
    refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hvA, ?_⟩, ?_⟩
    · intro hvclass
      have hi := (mem_filter.mp hvclass).2
      rw [hvnone] at hi
      contradiction
    · exact fun hvZ ↦ Finset.disjoint_left.mp hDZ hvD hvZ
  have hvNotH : v ∉ H := by
    intro hvH
    have hvprefix : v ∈ uncoloredPrefixUnion C phi (ell + 1) := by
      rw [uncoloredPrefixUnion, mem_biUnion]
      refine ⟨0, ?_, hvD⟩
      rw [uncoloredPrefixIndices, mem_filter]
      exact ⟨mem_range.mpr (hzeroEarly.trans_le
        (Dyadic.levelStart_mono (hJ0ell.trans (Nat.le_succ ell)))),
        hphi.early 0 hzeroEarly⟩
    exact (mem_sdiff.mp hvH).2 (mem_union_right _ hvprefix)
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hHB, ?_⟩
  intro heq
  have hvH : v ∈ H := by
    change v ∈ deficitResidual A C phi (ell + 1)
    rw [heq]
    simpa [B, Z] using hvB
  exact hvNotH hvH

theorem successorData_of_greedy_and_extensions
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hJ0ell : J0 ≤ ell) (hellJ : ell < J)
    (E : ExtensionCertificate G (deficitResidual A C phi (ell + 1)) k
      (residualProtectedFamily S hphi))
    (d : GreedyLevelData G A (deficitResidual A C phi (ell + 1))
      k C phi E.S ell)
    (R : ExtensionApplyScratch.PerColorExtensionConclusion
      (residualProtectedFamily S hphi) E
      (fun i ↦ (A \ colorClass A phi i) \
        selectedBlockUnion C d.N d.psi i)) :
    ∃ rho, Nonempty (SuccessorData G A k C J0 ell J phi rho) := by
  classical
  let H := deficitResidual A C phi (ell + 1)
  let CH := residualProtectedFamily S hphi
  let At : Color k → Finset V := fun i ↦
    (A \ colorClass A phi i) \ selectedBlockUnion C d.N d.psi i
  have hN : d.N ⊆ uncoloredCurrentIndices C phi ell := by
    intro r hr
    rw [← d.Uidx_eq]
    exact d.N_subset hr
  have hZX : ∀ i,
      Disjoint (selectedBlockUnion C d.N d.psi i) (R.X i) := by
    intro i
    exact (selectedBlockUnion_disjoint_residual d.N hN d.psi i).mono_right
      (R.X_subset_H i)
  have hnewPair : ∀ i j, i ≠ j →
      Disjoint (assembledNewClass C d.N d.psi R.X i)
        (assembledNewClass C d.N d.psi R.X j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro v hvi hvj
    rcases mem_union.mp hvi with hviZ | hviX
    · rcases mem_union.mp hvj with hvjZ | hvjX
      · exact Finset.disjoint_left.mp
          (selectedBlockUnion_pairwise S d.N hN hellJ d.psi i j hij) hviZ hvjZ
      · exact Finset.disjoint_left.mp
          ((selectedBlockUnion_disjoint_residual d.N hN d.psi i).mono_right
            (R.X_subset_H j)) hviZ hvjX
    · rcases mem_union.mp hvj with hvjZ | hvjX
      · exact Finset.disjoint_left.mp
          (((selectedBlockUnion_disjoint_residual d.N hN d.psi j).mono_right
            (R.X_subset_H i)).symm) hviX hvjZ
      · exact Finset.disjoint_left.mp (R.pairwise_X i j hij) hviX hvjX
  have hwholeX : ∀ r < Dyadic.levelStart J, ∀ i,
      C.getD r ∅ ⊆ R.X i ∨ Disjoint (C.getD r ∅) (R.X i) := by
    intro r hrJ i
    rcases block_whole_deficitResidual S hphi hrJ with hDH | hdisj
    · have hrfuture := block_subset_residual_is_future S hphi hrJ hDH
      have hrR : r ∈ residualFutureIndices A C phi ell J := by
        rw [residualFutureIndices, mem_filter, mem_Ico]
        exact ⟨⟨hrfuture, hrJ⟩, hDH⟩
      have hmem : C.getD r ∅ ∈ CH.blocks := by
        change C.getD r ∅ ∈
          (residualFutureIndices A C phi ell J).image (fun q ↦ C.getD q ∅)
        exact mem_image.mpr ⟨r, hrR, rfl⟩
      exact R.whole_blocks_deleted i _ hmem
    · exact Or.inr (hdisj.mono_right (R.X_subset_H i))
  have hnewSubset : ∀ i, assembledNewClass C d.N d.psi R.X i ⊆ A := by
    intro i v hv
    rcases mem_union.mp hv with hvZ | hvX
    · exact selectedBlockUnion_subset_A S d.N hN hellJ d.psi i hvZ
    · exact sdiff_subset (R.X_subset_H i hvX)
  have hnewUncolored : ∀ i, ∀ v ∈ assembledNewClass C d.N d.psi R.X i,
      phi v = none := by
    intro i v hv
    rcases mem_union.mp hv with hvZ | hvX
    · exact selectedBlockUnion_uncolored d.N hN d.psi i v hvZ
    · have hvH := R.X_subset_H i hvX
      have hvNotColored : v ∉ coloredVertices A phi := by
        intro hvcol
        exact (mem_sdiff.mp hvH).2 (mem_union_left _ hvcol)
      cases hp : phi v with
      | none => rfl
      | some j =>
          exact False.elim (hvNotColored
            (mem_coloredVertices_iff.mpr
              ⟨(mem_sdiff.mp hvH).1, j, hp⟩))
  have hearlyDisj : ∀ r < Dyadic.levelStart J0, ∀ i,
      Disjoint (C.getD r ∅) (assembledNewClass C d.N d.psi R.X i) := by
    intro r hr0 i
    have hrJ : r < Dyadic.levelStart J :=
      hr0.trans_le (Dyadic.levelStart_mono S.hJ)
    have hrN : r ∉ d.N := by
      intro hrN
      have hrU := hN hrN
      have hrlower := (Dyadic.mem_levelIndices.mp (mem_filter.mp hrU).1).1
      exact (Nat.not_lt_of_ge
        (Dyadic.levelStart_mono hJ0ell |>.trans hrlower)) hr0
    have hDZ := unselectedBlock_disjoint_selectedBlockUnion S d.N hN
      hrJ hrN hellJ d.psi i
    have hDH : Disjoint (C.getD r ∅) H := by
      rcases block_whole_deficitResidual S hphi hrJ with hsub | hdisj
      · have hfut := block_subset_residual_is_future S hphi hrJ hsub
        exact False.elim ((Nat.not_lt_of_ge
          ((Dyadic.levelStart_mono (hJ0ell.trans (Nat.le_succ ell))).trans hfut)) hr0)
      · exact hdisj
    rw [Finset.disjoint_left]
    intro v hvD hvnew
    rcases mem_union.mp hvnew with hvZ | hvX
    · exact Finset.disjoint_left.mp hDZ hvD hvZ
    · exact Finset.disjoint_left.mp
        (hDH.mono_right (R.X_subset_H i)) hvD hvX
  have hfutureX : ∀ r,
      Dyadic.levelStart (ell + 1) ≤ r → r < Dyadic.levelStart J → ∀ i,
      BlockUncolored phi (C.getD r ∅) → Disjoint (C.getD r ∅) (R.X i) →
        ¬ AdjacentSets G (C.getD r ∅) (R.X i) := by
    intro r hr hrJ i hun hdisj
    have hDH := future_uncolored_block_subset_residual S hphi hr hrJ hun
    have hrR : r ∈ residualFutureIndices A C phi ell J := by
      rw [residualFutureIndices, mem_filter, mem_Ico]
      exact ⟨⟨hr, hrJ⟩, hDH⟩
    have hmem : C.getD r ∅ ∈ CH.blocks := by
      change C.getD r ∅ ∈
        (residualFutureIndices A C phi ell J).image (fun q ↦ C.getD q ∅)
      exact mem_image.mpr ⟨r, hrR, rfl⟩
    exact R.retained_blocks_anticomplete i _ hmem hdisj
  let ai : AssemblyInput G A k C J0 ell J phi :=
    { Uidx := d.Uidx
      N := d.N
      psi := d.psi
      X := R.X
      Uidx_eq := d.Uidx_eq
      N_subset_Uidx := d.N_subset
      selected_nonempty := by
        intro r hr
        have hrU := hN hr
        have hrlev := (mem_filter.mp hrU).1
        exact S.block_nonempty r
          ((Dyadic.mem_levelIndices.mp hrlev).2.trans_le
            (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ)))
      new_pairwise := hnewPair
      new_subset := hnewSubset
      new_uncolored := hnewUncolored
      Z_X_disjoint := hZX
      whole_X := hwholeX
      unselected_disjoint_Z := by
        intro r hrJ hrN i
        exact unselectedBlock_disjoint_selectedBlockUnion S d.N hN
          hrJ hrN hellJ d.psi i
      early_disjoint_new := hearlyDisj
      quarter_bound := d.quarter
      block_incidence := fun i ↦
        selectedBlockUnion_incidence S d.N hN hellJ d.psi i
      removed_incidence := fun i ↦ by
        simpa [At] using R.incidence i
      retained_core := fun i ↦ by
        have hmin := R.minDegree i
        rw [R.retained_eq i] at hmin
        have heq : At i \ R.X i =
            A \ (colorClass A phi i ∪
              (selectedBlockUnion C d.N d.psi i ∪ R.X i)) := by
          ext v
          simp [At]
          tauto
        rwa [heq] at hmin
      future_Z_anticomplete := by
        intro r hr hrJ i
        exact futureBlock_anticomplete_selectedBlockUnion S d.N hN
          hr hrJ hellJ d.psi i
      future_X_anticomplete := hfutureX }
  exact ⟨ai.rho, ⟨ai.toSuccessorData hphi⟩⟩

omit [Fintype V] in
lemma currentUncoloredBlock_disjoint_deficitResidual
    {A : Finset V} {k ell : ℕ} {C : List (Finset V)}
    {phi : PartialColoring V k} {r : ℕ}
    (hr : r ∈ uncoloredCurrentIndices C phi ell) :
    Disjoint (C.getD r ∅) (deficitResidual A C phi (ell + 1)) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvD hvH
  have hvPrefix : v ∈ uncoloredPrefixUnion C phi (ell + 1) := by
    rw [uncoloredPrefixUnion, mem_biUnion]
    refine ⟨r, ?_, hvD⟩
    rw [uncoloredPrefixIndices, mem_filter]
    exact ⟨mem_range.mpr (Dyadic.mem_levelIndices.mp (mem_filter.mp hr).1).2,
      (mem_filter.mp hr).2⟩
  exact (mem_sdiff.mp hvH).2 (mem_union_right _ hvPrefix)

lemma currentUncoloredBlock_subset_selectedColorAmbient
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J r : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (N : Finset ℕ) (hN : N ⊆ uncoloredCurrentIndices C phi ell)
    (hellJ : ell < J) (psi : ℕ → Color k) (i : Color k)
    (hrU : r ∈ uncoloredCurrentIndices C phi ell)
    (hrSurvives : ¬ (r ∈ N ∧ psi r = i)) :
    C.getD r ∅ ⊆
      (A \ colorClass A phi i) \ selectedBlockUnion C N psi i := by
  classical
  have hrLev : r ∈ Dyadic.levelIndices ell := (mem_filter.mp hrU).1
  have hrJ : r < Dyadic.levelStart J :=
    (Dyadic.mem_levelIndices.mp hrLev).2.trans_le
      (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ))
  intro v hvD
  refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨S.block_subset r hrJ hvD, ?_⟩, ?_⟩
  · intro hvclass
    have hvColor := (mem_filter.mp hvclass).2
    have hvNone := (mem_filter.mp hrU).2 v hvD
    rw [hvNone] at hvColor
    contradiction
  · intro hvZ
    rw [selectedBlockUnion, mem_biUnion] at hvZ
    obtain ⟨q, hq, hvq⟩ := hvZ
    have hqN : q ∈ N := (mem_filter.mp hq).1
    have hqU := hN hqN
    have hqLev : q ∈ Dyadic.levelIndices ell := (mem_filter.mp hqU).1
    have hqJ : q < Dyadic.levelStart J :=
      (Dyadic.mem_levelIndices.mp hqLev).2.trans_le
        (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ))
    by_cases hrq : r = q
    · subst q
      exact hrSurvives ⟨hqN, (mem_filter.mp hq).2⟩
    · exact Finset.disjoint_left.mp
        (S.blocks_disjoint r hrJ q hqJ hrq) hvD hvq

lemma greedyLevel_certificate_protected
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hJ0ell : J0 ≤ ell) (hellJ : ell < J)
    (E : ExtensionCertificate G (deficitResidual A C phi (ell + 1)) k
      (residualProtectedFamily S hphi))
    (d : GreedyLevelData G A (deficitResidual A C phi (ell + 1))
      k C phi E.S ell) :
    ∀ i s, s ∈ E.S →
      s ∈ ((A \ colorClass A phi i) \
        selectedBlockUnion C d.N d.psi i) →
      k ≤ degreeOn G ((A \ colorClass A phi i) \
        selectedBlockUnion C d.N d.psi i) s := by
  classical
  intro i s hsS hsAt
  let H := deficitResidual A C phi (ell + 1)
  let B := A \ colorClass A phi i
  let Z := selectedBlockUnion C d.N d.psi i
  let At := B \ Z
  have hN : d.N ⊆ uncoloredCurrentIndices C phi ell := by
    intro r hr
    rw [← d.Uidx_eq]
    exact d.N_subset hr
  have hHAt : H ⊆ At :=
    (deficitResidual_ssubset_selectedColorAmbient S hphi hJ0ell hellJ
      d.N hN d.psi i).subset
  have hZB : Z ⊆ B := by
    intro v hvZ
    exact mem_sdiff.mpr ⟨selectedBlockUnion_subset_A S d.N hN hellJ d.psi i hvZ,
      fun hvclass ↦ by
        have hvColor := (mem_filter.mp hvclass).2
        have hvNone := selectedBlockUnion_uncolored d.N hN d.psi i v hvZ
        rw [hvNone] at hvColor
        contradiction⟩
  have hsH : s ∈ H := (mem_lowVertices.mp (E.S_subset_low hsS)).1
  have hsLow : degreeOn G H s ≤ k - 1 :=
    (mem_lowVertices.mp (E.S_subset_low hsS)).2
  apply ExtensionApplyScratch.certificateVertex_degree_ge_of_greedy_cases
    (G := G) phi S.hk hHAt hZB rfl (hphi.minDegree i) hsH hsLow
  change s ∈ At at hsAt
  by_cases hno : ¬ AdjacentSets G {s} Z
  · exact Or.inl hno
  right
  have hred : ∃ r ∈ d.N, d.psi r = i ∧
      AdjacentSets G {s} (C.getD r ∅) := by
    have hadj : AdjacentSets G {s} Z := Classical.not_not.mp hno
    rcases hadj with ⟨x, hx, y, hy, hxy⟩
    have hxs : x = s := by simpa using hx
    subst x
    change y ∈ selectedBlockUnion C d.N d.psi i at hy
    rw [selectedBlockUnion, mem_biUnion] at hy
    obtain ⟨r, hr, hyr⟩ := hy
    exact ⟨r, (mem_filter.mp hr).1, (mem_filter.mp hr).2,
      s, by simp, y, hyr, hxy⟩
  obtain ⟨rred, hrredN, hrredColor, hrredAdj⟩ := hred
  have hrredU := hN hrredN
  have hsActive : s ∈ d.active := by
    rw [d.active_eq, PopularScratch.selectedVertices, mem_filter]
    refine ⟨hsS, ?_⟩
    refine ⟨rred, ?_⟩
    rw [PopularScratch.adjacentBlockIndices, mem_filter]
    exact ⟨by rw [d.Uidx_eq]; exact hrredU, hrredAdj⟩
  let Adj := PopularScratch.adjacentBlockIndices G C d.Uidx s
  let need := k + 1 - degreeOn G H s
  by_cases hfull : need ≤ Adj.card
  · left
    have hscopeCard : (d.scope s).card = need := by
      rw [congrFun d.scope_eq s, PopularScratch.card_selectedScope]
      exact Nat.min_eq_right hfull
    by_cases hex : ∃ q ∈ d.scope s, q ∈ d.N ∧ d.psi q = i
    · obtain ⟨qred, hqredScope, hqredN, hqredColor⟩ := hex
      let Q := (d.scope s).erase qred
      have hQcard : Q.card = need - 1 := by
        dsimp [Q]
        rw [Finset.card_erase_of_mem hqredScope, hscopeCard]
      have hQsurvive : ∀ q ∈ Q, ¬ (q ∈ d.N ∧ d.psi q = i) := by
        intro q hqQ hqbad
        have hqScope := (mem_erase.mp hqQ).2
        have heq := d.injective_scope s hsActive q hqScope hqbad.1
          qred hqredScope hqredN (hqbad.2.trans hqredColor.symm)
        exact (mem_erase.mp hqQ).1 heq
      have hQpair : (Q : Set ℕ).PairwiseDisjoint (fun q ↦ C.getD q ∅) := by
        intro q hqQ p hpQ hqp
        have hqScope := (mem_erase.mp hqQ).2
        have hpScope := (mem_erase.mp hpQ).2
        have hqU : q ∈ d.Uidx := by
          rw [congrFun d.scope_eq s] at hqScope
          exact PopularScratch.selectedScope_subset G H C d.Uidx k s hqScope
        have hpU : p ∈ d.Uidx := by
          rw [congrFun d.scope_eq s] at hpScope
          exact PopularScratch.selectedScope_subset G H C d.Uidx k s hpScope
        have hqU' : q ∈ uncoloredCurrentIndices C phi ell := by
          rw [← d.Uidx_eq]; exact hqU
        have hpU' : p ∈ uncoloredCurrentIndices C phi ell := by
          rw [← d.Uidx_eq]; exact hpU
        have hqJ := (Dyadic.mem_levelIndices.mp (mem_filter.mp hqU').1).2.trans_le
          (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ))
        have hpJ := (Dyadic.mem_levelIndices.mp (mem_filter.mp hpU').1).2.trans_le
          (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ))
        exact S.blocks_disjoint q hqJ p hpJ hqp
      have hQadj : ∀ q ∈ Q, AdjacentSets G {s} (C.getD q ∅) := by
        intro q hqQ
        have hqScope := (mem_erase.mp hqQ).2
        rw [congrFun d.scope_eq s] at hqScope
        exact PopularScratch.mem_selectedScope_adjacent G H C d.Uidx k s hqScope
      obtain ⟨W, hWcard, hWsub, hWadj⟩ :=
        ExtensionApplyScratch.exists_neighborRepresentatives_of_pairwiseDisjoint
          (G := G) hQpair hQadj
      refine ⟨W, ?_, ?_, hWadj, ?_⟩
      · intro w hw
        obtain ⟨q, hqQ, hwq⟩ := mem_biUnion.mp (hWsub hw)
        have hqScope := (mem_erase.mp hqQ).2
        have hqU : q ∈ d.Uidx := by
          rw [congrFun d.scope_eq s] at hqScope
          exact PopularScratch.selectedScope_subset G H C d.Uidx k s hqScope
        have hqU' : q ∈ uncoloredCurrentIndices C phi ell := by
          rw [← d.Uidx_eq]; exact hqU
        exact currentUncoloredBlock_subset_selectedColorAmbient S d.N hN hellJ
          d.psi i hqU' (hQsurvive q hqQ) hwq
      · rw [Finset.disjoint_left]
        intro w hwW hwH
        obtain ⟨q, hqQ, hwq⟩ := mem_biUnion.mp (hWsub hwW)
        have hqScope := (mem_erase.mp hqQ).2
        have hqU : q ∈ d.Uidx := by
          rw [congrFun d.scope_eq s] at hqScope
          exact PopularScratch.selectedScope_subset G H C d.Uidx k s hqScope
        have hqU' : q ∈ uncoloredCurrentIndices C phi ell := by
          rw [← d.Uidx_eq]; exact hqU
        exact Finset.disjoint_left.mp
          (currentUncoloredBlock_disjoint_deficitResidual hqU') hwq hwH
      · rw [hWcard, hQcard]
        dsimp [need]
        omega
    · let Q := d.scope s
      have hQsurvive : ∀ q ∈ Q, ¬ (q ∈ d.N ∧ d.psi q = i) := by
        intro q hqQ hqbad
        exact hex ⟨q, hqQ, hqbad⟩
      have hQpair : (Q : Set ℕ).PairwiseDisjoint (fun q ↦ C.getD q ∅) := by
        intro q hqQ p hpQ hqp
        change q ∈ d.scope s at hqQ
        change p ∈ d.scope s at hpQ
        have hqU : q ∈ d.Uidx := by
          rw [congrFun d.scope_eq s] at hqQ
          exact PopularScratch.selectedScope_subset G H C d.Uidx k s hqQ
        have hpU : p ∈ d.Uidx := by
          rw [congrFun d.scope_eq s] at hpQ
          exact PopularScratch.selectedScope_subset G H C d.Uidx k s hpQ
        have hqU' : q ∈ uncoloredCurrentIndices C phi ell := by
          rw [← d.Uidx_eq]; exact hqU
        have hpU' : p ∈ uncoloredCurrentIndices C phi ell := by
          rw [← d.Uidx_eq]; exact hpU
        have hqJ := (Dyadic.mem_levelIndices.mp (mem_filter.mp hqU').1).2.trans_le
          (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ))
        have hpJ := (Dyadic.mem_levelIndices.mp (mem_filter.mp hpU').1).2.trans_le
          (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ))
        exact S.blocks_disjoint q hqJ p hpJ hqp
      have hQadj : ∀ q ∈ Q, AdjacentSets G {s} (C.getD q ∅) := by
        intro q hqQ
        change q ∈ d.scope s at hqQ
        rw [congrFun d.scope_eq s] at hqQ
        exact PopularScratch.mem_selectedScope_adjacent G H C d.Uidx k s hqQ
      obtain ⟨W, hWcard, hWsub, hWadj⟩ :=
        ExtensionApplyScratch.exists_neighborRepresentatives_of_pairwiseDisjoint
          (G := G) hQpair hQadj
      refine ⟨W, ?_, ?_, hWadj, ?_⟩
      · intro w hw
        obtain ⟨q, hqQ, hwq⟩ := mem_biUnion.mp (hWsub hw)
        change q ∈ d.scope s at hqQ
        have hqU : q ∈ d.Uidx := by
          rw [congrFun d.scope_eq s] at hqQ
          exact PopularScratch.selectedScope_subset G H C d.Uidx k s hqQ
        have hqU' : q ∈ uncoloredCurrentIndices C phi ell := by
          rw [← d.Uidx_eq]; exact hqU
        exact currentUncoloredBlock_subset_selectedColorAmbient S d.N hN hellJ
          d.psi i hqU' (hQsurvive q hqQ) hwq
      · rw [Finset.disjoint_left]
        intro w hwW hwH
        obtain ⟨q, hqQ, hwq⟩ := mem_biUnion.mp (hWsub hwW)
        change q ∈ d.scope s at hqQ
        have hqU : q ∈ d.Uidx := by
          rw [congrFun d.scope_eq s] at hqQ
          exact PopularScratch.selectedScope_subset G H C d.Uidx k s hqQ
        have hqU' : q ∈ uncoloredCurrentIndices C phi ell := by
          rw [← d.Uidx_eq]; exact hqU
        exact Finset.disjoint_left.mp
          (currentUncoloredBlock_disjoint_deficitResidual hqU') hwq hwH
      · rw [hWcard]
        change k - degreeOn G H s ≤ (d.scope s).card
        rw [hscopeCard]
        dsimp [need]
        omega
  · right
    have hAdjLe : Adj.card ≤ need := Nat.le_of_lt (Nat.lt_of_not_ge hfull)
    have hscopeEq : d.scope s = Adj := by
      rw [congrFun d.scope_eq s]
      exact PopularScratch.selectedScope_eq_adjacent_of_card_le
        G H C d.Uidx k s hAdjLe
    have hrredScope : rred ∈ d.scope s := by
      rw [hscopeEq]
      change rred ∈
        (d.Uidx.filter fun r ↦ AdjacentSets G {s} (C.getD r ∅))
      rw [mem_filter]
      exact ⟨by rw [d.Uidx_eq]; exact hrredU, hrredAdj⟩
    have hiAvoid : i ∉ PopularScratch.neighborColorList G A phi s := by
      have := d.avoids s hsActive rred hrredScope hrredN
      simpa [hrredColor] using this
    by_cases hmany : k ≤ (PopularScratch.neighborColorSet G A phi s).card
    · left
      let L := PopularScratch.neighborColorList G A phi s
      have hLcard : k ≤ L.card := by
        change k ≤ (PopularScratch.neighborColorList G A phi s).card
        rw [PopularScratch.neighborColorList,
          PopularScratch.card_chooseMinSubset, Nat.min_eq_right hmany]
      refine ⟨L, hLcard, ?_⟩
      intro j hj
      have hjSet := PopularScratch.neighborColorList_subset G A phi s hj
      rw [PopularScratch.neighborColorSet, mem_filter] at hjSet
      obtain ⟨v, hvA, hsv, hvColor⟩ := hjSet.2
      refine ⟨v, ?_, hsv, hvColor⟩
      refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hvA, ?_⟩, ?_⟩
      · intro hvI
        have : j = i := Option.some.inj (hvColor.symm.trans (mem_filter.mp hvI).2)
        subst j
        exact hiAvoid hj
      · intro hvZ
        have hvNone := selectedBlockUnion_uncolored d.N hN d.psi i v hvZ
        rw [hvNone] at hvColor
        contradiction
    · right
      refine ⟨A \ C.getD rred ∅, ?_, ?_, ?_⟩
      · have hsA : s ∈ A := (mem_sdiff.mp (mem_sdiff.mp hsAt).1).1
        refine mem_sdiff.mpr ⟨hsA, ?_⟩
        intro hsD
        exact Finset.disjoint_left.mp
          (currentUncoloredBlock_disjoint_deficitResidual hrredU) hsD hsH
      · have hrLev := (mem_filter.mp hrredU).1
        have hrJ := (Dyadic.mem_levelIndices.mp hrLev).2.trans_le
          (Dyadic.levelStart_mono (Nat.succ_le_iff.mpr hellJ))
        exact S.block_complement_minDegree rred hrJ
      · apply ExtensionApplyScratch.degreeOn_eq_of_adjacent_membership_iff
        intro v hsv
        constructor
        · intro hvAt
          change v ∈ (A \ colorClass A phi i) \
            selectedBlockUnion C d.N d.psi i at hvAt
          have hvB : v ∈ A \ colorClass A phi i := (mem_sdiff.mp hvAt).1
          have hvA : v ∈ A := (mem_sdiff.mp hvB).1
          refine mem_sdiff.mpr ⟨hvA, ?_⟩
          intro hvRed
          have hvZ : v ∈ Z := by
            change v ∈ selectedBlockUnion C d.N d.psi i
            rw [selectedBlockUnion, mem_biUnion]
            exact ⟨rred, mem_filter.mpr ⟨hrredN, hrredColor⟩, hvRed⟩
          exact (mem_sdiff.mp hvAt).2 hvZ
        · intro hvComp
          have hvA := (mem_sdiff.mp hvComp).1
          refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hvA, ?_⟩, ?_⟩
          · intro hvClass
            have hiOld : i ∈ PopularScratch.neighborColorSet G A phi s := by
              rw [PopularScratch.neighborColorSet, mem_filter]
              exact ⟨by simp, v, hvA, hsv, (mem_filter.mp hvClass).2⟩
            have hcardLe : (PopularScratch.neighborColorSet G A phi s).card ≤ k := by
              omega
            have hlistEq := ExtensionApplyScratch.PopularScratch.neighborColorList_eq_of_card_le
              (G := G) phi s hcardLe
            exact hiAvoid (hlistEq.symm ▸ hiOld)
          · intro hvZ
            change v ∈ selectedBlockUnion C d.N d.psi i at hvZ
            rw [selectedBlockUnion, mem_biUnion] at hvZ
            obtain ⟨q, hq, hvq⟩ := hvZ
            have hqN := (mem_filter.mp hq).1
            have hqColor := (mem_filter.mp hq).2
            have hqU := hN hqN
            have hqAdj : AdjacentSets G {s} (C.getD q ∅) :=
              ⟨s, by simp, v, hvq, hsv⟩
            have hqScope : q ∈ d.scope s := by
              rw [hscopeEq]
              change q ∈
                (d.Uidx.filter fun r ↦ AdjacentSets G {s} (C.getD r ∅))
              rw [mem_filter]
              exact ⟨by rw [d.Uidx_eq]; exact hqU, hqAdj⟩
            have hqr := d.injective_scope s hsActive q hqScope hqN
              rred hrredScope hrredN (hqColor.trans hrredColor.symm)
            subst q
            exact (mem_sdiff.mp hvComp).2 hvq

theorem exists_perColorExtensionConclusion_of_greedyLevel
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hJ0ell : J0 ≤ ell) (hellJ : ell < J)
    (E : ExtensionCertificate G (deficitResidual A C phi (ell + 1)) k
      (residualProtectedFamily S hphi))
    (d : GreedyLevelData G A (deficitResidual A C phi (ell + 1))
      k C phi E.S ell) :
    Nonempty (ExtensionApplyScratch.PerColorExtensionConclusion
      (residualProtectedFamily S hphi) E
      (fun i ↦ (A \ colorClass A phi i) \
        selectedBlockUnion C d.N d.psi i)) := by
  classical
  let H := deficitResidual A C phi (ell + 1)
  let CH := residualProtectedFamily S hphi
  let blockColor : ℕ → Option (Color k) := fun r ↦ some (d.psi r)
  let At : Color k → Finset V := fun i ↦
    (A \ colorClass A phi i) \ selectedBlockUnion C d.N d.psi i
  have hN : d.N ⊆ uncoloredCurrentIndices C phi ell := by
    intro r hr
    rw [← d.Uidx_eq]
    exact d.N_subset hr
  have hZeq : ∀ i, ExtensionApplyScratch.redBlockUnion C d.N blockColor i =
      selectedBlockUnion C d.N d.psi i := by
    intro i
    ext v
    simp only [ExtensionApplyScratch.redBlockUnion,
      ExtensionApplyScratch.redBlockIndices, selectedBlockUnion,
      mem_biUnion, mem_filter]
    constructor
    · rintro ⟨r, ⟨hrN, hrColor⟩, hvr⟩
      exact ⟨r, ⟨hrN, Option.some.inj hrColor⟩, hvr⟩
    · rintro ⟨r, ⟨hrN, hrColor⟩, hvr⟩
      exact ⟨r, ⟨hrN, congrArg some hrColor⟩, hvr⟩
  have hHAt : ∀ i, H ⊆ At i := by
    intro i
    exact (deficitResidual_ssubset_selectedColorAmbient S hphi hJ0ell hellJ
      d.N hN d.psi i).subset
  have hproper : ∀ i, H ⊂ At i := by
    intro i
    exact deficitResidual_ssubset_selectedColorAmbient S hphi hJ0ell hellJ
      d.N hN d.psi i
  have hinside : ∀ i, lowVertices G (At i) k ⊆ H := by
    intro i
    have h := ExtensionApplyScratch.lowVertices_currentColor_subset_deficitResidual_succ
      S hphi hellJ d.N hN blockColor i
    simpa [At, H, hZeq i] using h
  have hprotect : ∀ i s, s ∈ E.S → s ∈ At i →
      k ≤ degreeOn G (At i) s := by
    intro i s hsS hsAt
    exact greedyLevel_certificate_protected S hphi hJ0ell hellJ E d i s hsS
      (by simpa [At] using hsAt)
  have hAtA : ∀ i, At i ⊆ A := by
    intro i
    exact sdiff_subset.trans sdiff_subset
  have hfuture : ∀ D ∈ CH.blocks, ∃ r,
      Dyadic.levelStart (ell + 1) ≤ r ∧
      r < Dyadic.levelStart J ∧
      BlockUncolored phi (C.getD r ∅) ∧ D = C.getD r ∅ := by
    intro D hD
    change D ∈
      (residualFutureIndices A C phi ell J).image (fun r ↦ C.getD r ∅) at hD
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hD
    have hrIco := mem_Ico.mp (mem_filter.mp hr).1
    have hrSub := (mem_filter.mp hr).2
    exact ⟨r, hrIco.1, hrIco.2,
      blockUncolored_of_subset_deficitResidual hrSub, rfl⟩
  have hnew : ∀ i D, D ∈ CH.blocks → Anticomplete G (At i \ H) D :=
    ExtensionApplyScratch.extensionDiff_anticomplete_protectedFutureFamily
      S hphi CH rfl At hAtA hfuture
  have hred : ∀ i v, v ∈ lowVertices G (At i) k →
      (∃ r ∈ uncoloredCurrentIndices C phi ell,
        blockColor r = some i ∧ AdjacentSets G {v} (C.getD r ∅)) ∧
      (∀ r ∈ uncoloredCurrentIndices C phi ell,
        AdjacentSets G {v} (C.getD r ∅) → blockColor r = some i) := by
    intro i v hv
    have hraw := ExtensionApplyScratch.lowVertex_currentBlock_color_description
      S hphi hellJ d.N hN blockColor CH E rfl
      (by
        intro j s hsS hsMem
        have hp := hprotect j s hsS
        have hsAt : s ∈ At j := by simpa [At, hZeq j] using hsMem
        simpa [At, hZeq j] using hp hsAt)
      i v
      (by simpa [At, hZeq i] using hv)
    refine ⟨?_, hraw.2⟩
    obtain ⟨r, hrN, hrColor, hrAdj⟩ := hraw.1
    exact ⟨r, hN hrN, hrColor, hrAdj⟩
  have hR := ExtensionApplyScratch.apply_extension_per_color_indices
    CH E S.hk C At hHAt hproper hinside hprotect hnew
    (uncoloredCurrentIndices C phi ell) blockColor hred
  simpa [At] using hR

theorem successorData_of_greedyLevel
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hJ0ell : J0 ≤ ell) (hellJ : ell < J)
    (E : ExtensionCertificate G (deficitResidual A C phi (ell + 1)) k
      (residualProtectedFamily S hphi))
    (d : GreedyLevelData G A (deficitResidual A C phi (ell + 1))
      k C phi E.S ell) :
    ∃ rho, Nonempty (SuccessorData G A k C J0 ell J phi rho) := by
  obtain ⟨R⟩ := exists_perColorExtensionConclusion_of_greedyLevel
    S hphi hJ0ell hellJ E d
  exact successorData_of_greedy_and_extensions S hphi hJ0ell hellJ E d R

theorem exists_successorData_of_large_uncoloredLevel
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hJ0ell : J0 ≤ ell) (hellJ : ell < J)
    (hlarge : 2 ^ ell < 4 * uncoloredBlockCount C phi ell) :
    ∃ rho, Nonempty (SuccessorData G A k C J0 ell J phi rho) := by
  obtain ⟨E⟩ := exists_residualExtensionCertificate S hphi hJ0ell
  have hshort := shortage_deficitResidual_le_twelve
    S hphi hJ0ell hellJ hlarge
  obtain ⟨d⟩ := exists_greedyLevelData E S.hk hshort
  exact successorData_of_greedyLevel S hphi hJ0ell hellJ E d

end

theorem exists_appropriateColoring_succ
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 ell J : ℕ}
    {phi : PartialColoring V k}
    (S : ColoringSystem G A k t C J0 J)
    (hphi : Appropriate G A k C J0 ell J phi)
    (hJ0ell : J0 ≤ ell) (hellJ : ell < J) :
    ∃ rho, Appropriate G A k C J0 (ell + 1) J rho := by
  by_cases hquarter :
      4 * uncoloredBlockCount C phi ell ≤ 2 ^ ell
  · exact ⟨phi, hphi.advance_without_change hquarter⟩
  · have hlarge : 2 ^ ell < 4 * uncoloredBlockCount C phi ell := by omega
    exact appropriateColoring_succ hphi
      (exists_successorData_of_large_uncoloredLevel
        S hphi hJ0ell hellJ hlarge)

theorem exists_finalAppropriate
    {A : Finset V} {k : ℕ} {t : ℤ}
    {C : List (Finset V)} {J0 J : ℕ}
    (S : ColoringSystem G A k t C J0 J) :
    ∃ phi, Appropriate G A k C J0 J J phi := by
  let P : (ell : ℕ) → J0 ≤ ell → Prop := fun ell _ ↦
    ell ≤ J → ∃ phi, Appropriate G A k C J0 ell J phi
  have hbase : P J0 (Nat.le_refl J0) := by
    intro _
    exact ⟨fun _ ↦ none, appropriate_uncolored S.minDegree⟩
  have hstep : ∀ (ell : ℕ) (hJ0ell : J0 ≤ ell), P ell hJ0ell →
      P (ell + 1) (Nat.le_succ_of_le hJ0ell) := by
    intro ell hJ0ell ih hell1J
    have hellJ : ell ≤ J := (Nat.le_succ ell).trans hell1J
    have hellLtJ : ell < J := Nat.lt_of_succ_le hell1J
    obtain ⟨phi, hphi⟩ := ih hellJ
    exact exists_appropriateColoring_succ S hphi hJ0ell hellLtJ
  exact Nat.le_induction (P := P) hbase hstep J S.hJ (Nat.le_refl J)

theorem exists_small_core_of_localExpansion
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (t : ℤ) (hk : 2 ≤ k) (ht : t + 1 ≤ Tmax k)
    (A : Finset V) (hcard : k - 1 ≤ A.card)
    (hshort : shortage k G A ≤ t)
    (hlocal : LocalExpansion G A k)
    (hmin : HasMinDegreeOn G A k)
    (hconn : ConnectedOn G A) :
    ∃ W, IsSmallCoreOn G A k (uniformDen k) W := by
  classical
  by_contra hno
  have hno' : NoSmallCoreOn G A k (uniformDen k) := hno
  obtain ⟨C, J0, J, S⟩ := exists_coloringSystem G k t hk ht A hcard
    hshort hlocal hmin hconn hno'
  obtain ⟨phi, hphi⟩ := exists_finalAppropriate S
  exact hno' (smallCore_of_appropriate_and_colored hk hphi
    (final_colored_mass S hphi))

end P814

end

section
open Finset SimpleGraph

namespace P814

variable {V : Type*} [Fintype V] [DecidableEq V]

def SignedDensity (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (t : ℤ) (A : Finset V) : Prop :=
  shortage k G A ≤ t

def SmallCoreExists (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (A : Finset V) : Prop :=
  ∃ U : Finset V, U ⊆ A ∧ U.Nonempty ∧ HasMinDegreeOn G U k ∧
    uniformDen k * U.card ≤ (uniformDen k - 1) * A.card

lemma SmallCoreExists.of_isSmallCoreOn
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ} {A U : Finset V}
    (hU : IsSmallCoreOn G A k (uniformDen k) U) :
    SmallCoreExists G k A := by
  rcases hU with ⟨hUA, hmin, hsmall⟩
  exact ⟨U, hUA, hmin.1, hmin, hsmall⟩

lemma SmallCoreExists.mono_ambient
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ} {B A : Finset V}
    (hBA : B ⊆ A) (h : SmallCoreExists G k B) : SmallCoreExists G k A := by
  rcases h with ⟨U, hUB, hUne, hUmin, hsmall⟩
  refine ⟨U, hUB.trans hBA, hUne, hUmin, ?_⟩
  exact hsmall.trans (Nat.mul_le_mul_left (uniformDen k - 1) (card_le_card hBA))

lemma problemT_eq_Tmax_sub_one (k : ℕ) : problemT k = Tmax k - 1 := by
  rfl

lemma le_problemT_of_add_one_le_Tmax {k : ℕ} {t : ℤ}
    (ht : t + 1 ≤ Tmax k) : t ≤ problemT k := by
  rw [problemT_eq_Tmax_sub_one]
  omega

lemma edgeThreshold_le_of_signedDensity
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (t : ℤ) (hk : 2 ≤ k) (ht : t + 1 ≤ Tmax k)
    (A : Finset V) (hcard : k - 1 ≤ A.card)
    (hedge : SignedDensity G k t A) :
    edgeThreshold k A.card ≤ edgeCount G A := by
  have ht' : t ≤ problemT k := le_problemT_of_add_one_le_Tmax ht
  have hshort : shortage k G A ≤ problemT k := hedge.trans ht'
  have hcast := edgeThreshold_cast_eq k A.card hk hcard
  have hmulcast :
      ((((k - 1) * A.card : ℕ) : ℤ)) =
        (((k - 1 : ℕ) : ℤ) * (A.card : ℤ)) := by
    push_cast
    rfl
  have hcastle : (edgeThreshold k A.card : ℤ) ≤ (edgeCount G A : ℤ) := by
    rw [hcast, hmulcast]
    simpa [SignedDensity, shortage, add_comm] using hshort
  exact_mod_cast hcastle

lemma card_ge_succ_of_signedDensity
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (t : ℤ) (hk : 2 ≤ k) (ht : t + 1 ≤ Tmax k)
    (A : Finset V) (hcard : k - 1 ≤ A.card)
    (hedge : SignedDensity G k t A) :
    k + 1 ≤ A.card := by
  exact card_ge_succ_of_edgeThreshold_le G k hk hcard
    (edgeThreshold_le_of_signedDensity G k t hk ht A hcard hedge)

def SmallerCoreHypothesis
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (t : ℤ) (A : Finset V) : Prop :=
  ∀ B : Finset V, B ⊂ A → k - 1 ≤ B.card →
    SignedDensity G k t B → SmallCoreExists G k B

lemma localExpansion_of_smallerCoreHypothesis
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (t : ℤ) (hk : 2 ≤ k) (A : Finset V)
    (hcard : k - 1 ≤ A.card) (hlarge : k + 1 ≤ A.card)
    (hedge : SignedDensity G k t A)
    (hsmaller : SmallerCoreHypothesis G k t A)
    (hnosmall : ¬ SmallCoreExists G k A) :
    LocalExpansion G A k := by
  intro X hXne hXA hXcard
  by_contra hinc
  have hinc' : incidentCount G A X ≤ (k - 1) * X.card := by omega
  let B := A \ X
  have hBcard_eq : B.card = A.card - X.card := by
    simp [B, card_sdiff_of_subset hXA]
  have hBcard : k - 1 ≤ B.card := by
    have hrewrite : A.card - k + 1 = A.card - (k - 1) := by omega
    rw [hrewrite] at hXcard
    rw [hBcard_eq]
    omega
  have hBssub : B ⊂ A := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset, ?_⟩
    intro hBA
    obtain ⟨x, hxX⟩ := hXne
    have hxA := hXA hxX
    have hxB : x ∈ B := hBA.symm ▸ hxA
    exact (mem_sdiff.mp hxB).2 hxX
  have hpot : 0 ≤ deletionPotential k G A X := by
    unfold deletionPotential
    have hincZ : (incidentCount G A X : ℤ) ≤
        (((k - 1 : ℕ) : ℤ) * (X.card : ℤ)) := by
      exact_mod_cast hinc'
    exact sub_nonneg.mpr hincZ
  have hBshort : SignedDensity G k t B := by
    have hs := shortage_sdiff k G hXA
    change shortage k G B ≤ t
    calc
      shortage k G B = shortage k G A - deletionPotential k G A X := hs
      _ ≤ shortage k G A := sub_le_self _ hpot
      _ ≤ t := hedge
  exact hnosmall <| SmallCoreExists.mono_ambient hBssub.subset
    (hsmaller B hBssub hBcard hBshort)

lemma hasMinDegreeOn_of_localExpansion
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (A : Finset V) (hcard : k + 1 ≤ A.card)
    (hlocal : LocalExpansion G A k) :
    HasMinDegreeOn G A k := by
  have hAne : A.Nonempty := by
    apply card_pos.mp
    omega
  refine ⟨hAne, ?_⟩
  intro v hvA
  have hsingle : ({v} : Finset V).Nonempty := singleton_nonempty v
  have hsingleSub : ({v} : Finset V) ⊆ A := singleton_subset_iff.mpr hvA
  have hsingleCard : ({v} : Finset V).card ≤ A.card - k + 1 := by
    simp
  have h := hlocal {v} hsingle hsingleSub hsingleCard
  have hincident : incidentCount G A {v} = degreeOn G A v := by
    have hdel := edgeCount_sdiff_add_incidentCount G A {v}
    have herase := edgeCount_erase_add_degreeOn G hvA
    have hs : A \ {v} = A.erase v := by ext x; simp [and_comm]
    rw [hs] at hdel
    omega
  rw [hincident] at h
  simp only [card_singleton, Nat.mul_one] at h
  omega

def CounterexampleStep
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ (k : ℕ) (t : ℤ), 2 ≤ k → t + 1 ≤ Tmax k →
    ∀ A : Finset V, k - 1 ≤ A.card → SignedDensity G k t A →
      LocalExpansion G A k → HasMinDegreeOn G A k → ConnectedOn G A →
      SmallCoreExists G k A

theorem sauermann_uniform_on_of_step
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hstep : CounterexampleStep G)
    (k : ℕ) (t : ℤ) (hk : 2 ≤ k) (ht : t + 1 ≤ Tmax k)
    (A : Finset V) (hcard : k - 1 ≤ A.card)
    (hedge : SignedDensity G k t A) :
    SmallCoreExists G k A := by
  revert hcard hedge
  refine Finset.strongInductionOn A ?_
  intro A ih hcard hedge
  by_contra hnosmall
  have hsmaller : SmallerCoreHypothesis G k t A := by
    intro B hBA hBcard hBedge
    exact ih B hBA hBcard hBedge
  have hlarge := card_ge_succ_of_signedDensity G k t hk ht A hcard hedge
  have hlocal := localExpansion_of_smallerCoreHypothesis G k t hk A
    hcard hlarge hedge hsmaller hnosmall
  have hmin := hasMinDegreeOn_of_localExpansion G k A hlarge hlocal
  have hD : 2 ≤ uniformDen k := by
    simp only [uniformDen]
    have : 0 < k ^ 3 := pow_pos (by omega) _
    nlinarith
  have hnoCore : NoSmallCoreOn G A k (uniformDen k) := by
    intro h
    rcases h with ⟨U, hUA, hUmin, hsmall⟩
    exact hnosmall ⟨U, hUA, hUmin.1, hUmin, hsmall⟩
  have hconn := connectedOn_of_noSmallCoreOn G hD hmin hnoCore
  exact hnosmall (hstep k t hk ht A hcard hedge hlocal hmin hconn)

theorem sauermann_uniform_on
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {t : ℤ} (hk : 2 ≤ k) (ht : t + 1 ≤ Tmax k)
    (A : Finset V) (hcard : k - 1 ≤ A.card)
    (hshort : shortage k G A ≤ t) :
    ∃ U : Finset V, U ⊆ A ∧ U.Nonempty ∧ HasMinDegreeOn G U k ∧
      uniformDen k * U.card ≤ (uniformDen k - 1) * A.card := by
  have hstep : CounterexampleStep G := by
    intro k t hk ht A hcard hshort hlocal hmin hconn
    obtain ⟨U, hU⟩ := exists_small_core_of_localExpansion G k t hk ht A hcard
      hshort hlocal hmin hconn
    exact SmallCoreExists.of_isSmallCoreOn hU
  have hDensity : SignedDensity G k t A := hshort
  simpa only [SmallCoreExists] using
    sauermann_uniform_on_of_step G hstep k t hk ht A hcard hDensity

end P814

end

section
open Finset SimpleGraph

namespace P814

def Erdos814AtLeastStatement : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, k - 1 ≤ n →
        ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          edgeThreshold k n ≤ G.edgeFinset.card →
            ∃ S : Finset (Fin n),
              S.Nonempty ∧
              (S.card : ℝ) ≤ (1 - c) * (n : ℝ) ∧
              k ≤ (G.induce (↑S : Set (Fin n))).minDegree

def Erdos814Statement : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, k - 1 ≤ n →
        ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          G.edgeFinset.card = edgeThreshold k n →
            ∃ S : Finset (Fin n),
              S.Nonempty ∧
              (S.card : ℝ) ≤ (1 - c) * (n : ℝ) ∧
              k ≤ (G.induce (↑S : Set (Fin n))).minDegree

theorem erdos_814_atLeast : Erdos814AtLeastStatement := by
  intro k hk
  refine ⟨1 / (10000 * (k : ℝ) ^ 3), ?_, ?_⟩
  · positivity
  intro n hn G _ hEdges
  have hEdgesInt : (edgeThreshold k n : ℤ) ≤ (G.edgeFinset.card : ℤ) := by
    exact_mod_cast hEdges
  have hThreshold := edgeThreshold_cast_eq k n hk hn
  have hshort : shortage k G (Finset.univ : Finset (Fin n)) ≤ problemT k := by
    simp only [shortage, edgeCount_univ, Finset.card_univ, Fintype.card_fin]
    rw [hThreshold] at hEdgesInt
    push_cast at hEdgesInt ⊢
    omega
  obtain ⟨S, -, hSnonempty, hSmin, hSsmall⟩ :=
    sauermann_uniform_on G (k := k) (t := problemT k) hk
      (problemT_add_one_le_Tmax k) (Finset.univ : Finset (Fin n))
      (by simpa using hn) hshort
  refine ⟨S, hSnonempty, card_le_one_sub_inv_mul k S.card n hk ?_, ?_⟩
  · simpa using hSsmall
  · exact (hasMinDegreeOn_iff_induce_minDegree G S k).mp hSmin |>.2

theorem erdos_814 : (∀ k : ℕ, 2 ≤ k →
  ∃ c : ℝ, 0 < c ∧
    ∀ n : ℕ, k - 1 ≤ n →
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        G.edgeFinset.card = P814.edgeThreshold k n →
          ∃ S : Finset (Fin n),
            S.Nonempty ∧
            (S.card : ℝ) ≤ (1 - c) * (n : ℝ) ∧
            k ≤ (G.induce (↑S : Set (Fin n))).minDegree) := by
  refine Iff.mp ?_ trivial
  constructor
  · intro _ k hk
    obtain ⟨c, hc, hstrong⟩ := erdos_814_atLeast k hk
    refine ⟨c, hc, ?_⟩
    intro n hn G _ hEdges
    exact hstrong n hn G hEdges.symm.le
  · intro _
    trivial

end P814

end

namespace P814

theorem sauermann_explicit (k : ℕ) (hk : 2 ≤ k) (n : ℕ) (hn : k - 1 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hEdges : edgeThreshold k n ≤ G.edgeFinset.card) :
    ∃ S : Finset (Fin n), S.Nonempty ∧
      (S.card : ℝ) ≤ (1 - 1 / (10000 * (k : ℝ) ^ 3)) * (n : ℝ) ∧
      k ≤ (G.induce (↑S : Set (Fin n))).minDegree := by
  have hEdgesInt : (edgeThreshold k n : ℤ) ≤ (G.edgeFinset.card : ℤ) := by
    exact_mod_cast hEdges
  have hThreshold := edgeThreshold_cast_eq k n hk hn
  have hshort : shortage k G (Finset.univ : Finset (Fin n)) ≤ problemT k := by
    simp only [shortage, edgeCount_univ, Finset.card_univ, Fintype.card_fin]
    rw [hThreshold] at hEdgesInt
    push_cast at hEdgesInt ⊢
    omega
  obtain ⟨S, -, hSnonempty, hSmin, hSsmall⟩ :=
    sauermann_uniform_on G (k := k) (t := problemT k) hk
      (problemT_add_one_le_Tmax k) (Finset.univ : Finset (Fin n))
      (by simpa using hn) hshort
  refine ⟨S, hSnonempty, card_le_one_sub_inv_mul k S.card n hk ?_, ?_⟩
  · simpa using hSsmall
  · exact (hasMinDegreeOn_iff_induce_minDegree G S k).mp hSmin |>.2

end P814

theorem OMA.solution : type_of% @Erdos814.erdos_814.variants.sauermann := by
  classical
  refine ⟨1 / 10000, by norm_num, ?_⟩
  intro k hk n hn G hE
  obtain ⟨S, hS, hcard, hmin⟩ := P814.sauermann_explicit k hk n hn G (by unfold P814.edgeThreshold; convert hE)
  refine ⟨S, hS, ?_, by convert hmin⟩
  have hk0 : (0 : ℝ) < (k : ℝ) ^ 3 := by
    have : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    positivity
  have heq : (1 : ℝ) / 10000 / (k : ℝ) ^ 3 = 1 / (10000 * (k : ℝ) ^ 3) := by
    field_simp
  calc (S.card : ℝ) ≤ (1 - 1 / (10000 * (k : ℝ) ^ 3)) * (n : ℝ) := hcard
    _ = (1 - 1 / 10000 / (k : ℝ) ^ 3) * (n : ℝ) := by rw [heq]
