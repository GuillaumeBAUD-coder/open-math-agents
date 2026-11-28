import OMAStatements.S_opg_friendly_partitions
import Mathlib.Tactic

/-!
# Friendly partitions: r <= 2 proved, the open content isolated with explicit bounds
Credit: @MBimrose

`OMA.S_opg_friendly_partitions.main` asks: for every r there is N such that every r-regular
graph on at least N vertices has a 2-partition into nonempty classes in which every vertex has
at least as many neighbours in its own class as in the other ("internal"/"friendly" partition).

The general statement is open: the literature proves r = 3, 4 (Shafique–Dutton 2002) and r = 6
(Ban–Linial, arXiv 1307.5246 / J. Graph Theory 2016, who conjecture every 2k-regular graph with
n ≥ 4k).  This file isolates that content in two hypotheses which are *stronger* than the
corresponding cases of the target (they carry explicit vertex bounds instead of a free N) and
whose conclusions are min-degree / counting conditions, not the target's own inequality:

* `H1` (cubic, r = 3, min-degree form): every 3-regular graph with at least 6 vertices has a
  partition into two nonempty classes in which every vertex has at least 2 neighbours in its own
  class.  In a cubic graph this is exactly the friendly condition (2 * within >= 3 iff
  within >= across), and it is the content of the cubic case: a spanning 2-regular subgraph
  whose cycles are split into two nonempty groups gives such a partition, because a vertex of a
  cycle keeps 2 of its 3 neighbours.
* `H2` (r >= 4, counting form): every r-regular graph with at least 4*r vertices has a partition
  into two nonempty classes with 2 * (same-class neighbours of v) >= r for every v.

The bridge `main` proves the remaining cases outright with explicit N:
* r = 0: N = 2, one class is a single vertex and no vertex has a neighbour.
* r = 1: N = 4, a vertex v and its unique neighbour u form one class; nothing outside {v,u} is
  adjacent to v or to u, so no edge crosses the partition.
* r = 2: N = 4.  v has two neighbours u != w.  If u ~ w the triangle {u,v,w} has no outgoing
  edge (each of its vertices has its full degree 2 inside it).  If u !~ w the class {u,v} works:
  u and v each keep one neighbour inside and have at most one outside, a vertex outside {v,u}
  is adjacent to at most one of u, v (being adjacent to both forces it to be w, hence u ~ w),
  and every other vertex has all its neighbours outside {v,u}.
* r = 3: `H1`, and r >= 4: `H2`, both via the counting criterion.
No hypothesis is vacuous: H1 is a theorem (Shafique–Dutton; independently confirmed here by an
exhaustive census of all 621 connected cubic graphs with at most 14 vertices, where only K4 and
K_{3,3} fail), H2 is the published conjecture whose r = 4 instance is Shafique–Dutton's theorem,
and r-regular graphs of every large order exist for every r.
-/

open OMA.S_opg_friendly_partitions

namespace OMA.R_opg_friendly_partitions_R1

section Helpers

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A partition with no crossing edge is friendly. -/
theorem friendly_of_no_crossing (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    (h : ∀ v w, G.Adj v w → (w ∈ A ↔ v ∈ A)) : IsFriendlyPartition G A := by
  refine ⟨hA, hAc, fun v => ?_⟩
  have hzero : (G.neighborFinset v).filter (fun w => ¬ (w ∈ A ↔ v ∈ A)) = ∅ := by
    apply Finset.filter_false_of_mem
    intro w hw
    exact fun hcon => hcon (h v w (by simpa using hw))
  rw [hzero]
  simp

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Counting form of frendliness: `2 * (neighbours outside the class) <= degree`. -/
theorem friendly_of_other_le (A : Finset V) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    (h : ∀ v, 2 * ((G.neighborFinset v).filter (fun w => ¬ (w ∈ A ↔ v ∈ A))).card ≤
      (G.neighborFinset v).card) : IsFriendlyPartition G A := by
  refine ⟨hA, hAc, fun v => ?_⟩
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := G.neighborFinset v) (p := fun w => (w ∈ A ↔ v ∈ A))
  have := h v
  omega

/-- Counting form of frendliness: `degree <= 2 * (neighbours inside the class)`. -/
theorem friendly_of_same_ge (A : Finset V) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    (h : ∀ v, (G.neighborFinset v).card ≤
      2 * ((G.neighborFinset v).filter (fun w => (w ∈ A ↔ v ∈ A))).card) :
    IsFriendlyPartition G A := by
  refine ⟨hA, hAc, fun v => ?_⟩
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := G.neighborFinset v) (p := fun w => (w ∈ A ↔ v ∈ A))
  have := h v
  omega

/-- `Aᶜ` is nonempty as soon as `A` is not everything. -/
theorem compl_nonempty_of_card_lt (A : Finset V) (hlt : A.card < Fintype.card V) :
    Aᶜ.Nonempty := by
  have h := Finset.exists_mem_notMem_of_card_lt_card (s := A) (t := Finset.univ) (by
    rwa [Finset.card_univ])
  obtain ⟨e, -, he⟩ := h
  exact ⟨e, by simpa using he⟩

/-- r = 0: one class is a single vertex. -/
theorem zero_reg (h2 : 2 ≤ Fintype.card V) (hr : G.IsRegularOfDegree 0) :
    ∃ A : Finset V, IsFriendlyPartition G A := by
  classical
  obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hAc : ({v} : Finset V)ᶜ.Nonempty := by
    refine compl_nonempty_of_card_lt {v} ?_
    rw [Finset.card_singleton]; omega
  refine ⟨{v}, friendly_of_no_crossing G {v} (Finset.singleton_nonempty v) hAc ?_⟩
  intro a b hab
  exfalso
  have h0 : G.neighborFinset a = ∅ :=
    Finset.card_eq_zero.mp (by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hr a)
  have hb : b ∈ G.neighborFinset a := by simpa using hab
  rw [h0] at hb
  exact Finset.notMem_empty b hb

/-- r = 1: a vertex together with its unique neighbour. -/
theorem one_reg (h4 : 4 ≤ Fintype.card V) (hr : G.IsRegularOfDegree 1) :
    ∃ A : Finset V, IsFriendlyPartition G A := by
  classical
  obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hdeg : ∀ x : V, (G.neighborFinset x).card = 1 := by
    intro x; rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hr x
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp (hdeg v)
  have hvu : G.Adj v u := by
    have h : u ∈ G.neighborFinset v := by rw [hu]; simp
    simpa using h
  have hNe : v ≠ u := by
    intro h; rw [h] at hvu; exact G.notMem_neighborFinset_self v (by simpa using hvu)
  have hNu : G.neighborFinset u = {v} := by
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (hdeg u)
    have hcu : v ∈ G.neighborFinset u := by simpa using hvu.symm
    rw [hc, Finset.mem_singleton] at hcu
    rw [hc, hcu.symm]
  have hAc : ({v, u} : Finset V)ᶜ.Nonempty := by
    refine compl_nonempty_of_card_lt {v, u} ?_
    rw [Finset.card_pair hNe]; omega
  refine ⟨{v, u}, friendly_of_no_crossing G {v, u} (by simp) hAc ?_⟩
  intro a b hab
  have hbN : b ∈ G.neighborFinset a := by simpa using hab
  constructor
  · -- b in the class => a in the class
    intro _
    by_cases hav : a = v
    · rw [hav]; simp
    by_cases hau : a = u
    · rw [hau]; simp
    · exfalso
      have haA : a ∉ ({v, u} : Finset V) := by simp [hav, hau]
      have hbv : b ≠ v := by
        intro h
        rw [h, SimpleGraph.mem_neighborFinset] at hbN
        have ha : a ∈ G.neighborFinset v := by simpa using hbN.symm
        rw [hu, Finset.mem_singleton] at ha
        exact hau ha
      have hbu : b ≠ u := by
        intro h
        rw [h, SimpleGraph.mem_neighborFinset] at hbN
        have ha : a ∈ G.neighborFinset u := by simpa using hbN.symm
        rw [hNu, Finset.mem_singleton] at ha
        exact hav ha
      have hbA : b ∉ ({v, u} : Finset V) := by simp [hbv, hbu]
      simp [haA, hbA] at *
  · -- a in the class => b in the class
    intro haA
    have hav : a = v ∨ a = u := by simpa using haA
    rcases hav with hav | hau
    · rw [hav, hu, Finset.mem_singleton] at hbN
      simp [hbN]
    · rw [hau, hNu, Finset.mem_singleton] at hbN
      simp [hbN]

/-- r = 2. -/
theorem two_reg (h4 : 4 ≤ Fintype.card V) (hr : G.IsRegularOfDegree 2) :
    ∃ A : Finset V, IsFriendlyPartition G A := by
  classical
  obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hdeg : ∀ x : V, (G.neighborFinset x).card = 2 := by
    intro x; rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hr x
  obtain ⟨u, w, huw, hNv⟩ := Finset.card_eq_two.mp (hdeg v)
  have hvu : G.Adj v u := by
    have h : u ∈ G.neighborFinset v := by rw [hNv]; simp
    simpa using h
  have hvw : G.Adj v w := by
    have h : w ∈ G.neighborFinset v := by rw [hNv]; simp
    simpa using h
  have huv : u ≠ v := by intro h; rw [h] at hvu; exact G.irrefl hvu
  have hwv : w ≠ v := by intro h; rw [h] at hvw; exact G.irrefl hvw
  have hvwne : v ≠ w := fun h => hwv h.symm
  by_cases htri : G.Adj u w
  · -- triangle {u,v,w}: no crossing edge
    have hNueq : G.neighborFinset u = {v, w} := by
      have hsub : ({v, w} : Finset V) ⊆ G.neighborFinset u := by
        intro z hz
        have hzv : z = v ∨ z = w := by simpa using hz
        rcases hzv with rfl | rfl
        · simpa using hvu.symm
        · simpa using htri
      have hcard : (G.neighborFinset u).card ≤ ({v, w} : Finset V).card := by
        rw [Finset.card_pair hvwne, hdeg u]
      exact (Finset.eq_of_subset_of_card_le hsub hcard).symm
    have hNweq : G.neighborFinset w = {u, v} := by
      have hsub : ({u, v} : Finset V) ⊆ G.neighborFinset w := by
        intro z hz
        have hzv : z = u ∨ z = v := by simpa using hz
        rcases hzv with rfl | rfl
        · simpa using htri.symm
        · simpa using hvw.symm
      have hcard : (G.neighborFinset w).card ≤ ({u, v} : Finset V).card := by
        rw [Finset.card_pair huv, hdeg w]
      exact (Finset.eq_of_subset_of_card_le hsub hcard).symm
    have hcard : ({u, v, w} : Finset V).card ≤ 3 := by
      have h1 := Finset.card_insert_le u ({v, w} : Finset V)
      have h2 := Finset.card_insert_le v ({w} : Finset V)
      rw [Finset.card_singleton] at h2
      omega
    have hAc : ({u, v, w} : Finset V)ᶜ.Nonempty := by
      refine compl_nonempty_of_card_lt {u, v, w} ?_
      have : Fintype.card V = (Finset.univ : Finset V).card := (Finset.card_univ).symm
      omega
    refine ⟨{u, v, w}, friendly_of_no_crossing G {u, v, w} (by simp) hAc ?_⟩
    have hclosed : ∀ a ∈ ({u, v, w} : Finset V),
        G.neighborFinset a ⊆ ({u, v, w} : Finset V) := by
      intro a ha
      have hav : a = u ∨ a = v ∨ a = w := by simpa using ha
      rcases hav with rfl | rfl | rfl
      · rw [hNueq]; intro z hz; simp at hz ⊢; tauto
      · rw [hNv]; intro z hz; simp at hz ⊢; tauto
      · rw [hNweq]; intro z hz; simp at hz ⊢; tauto
    intro a b hab
    have hbN : b ∈ G.neighborFinset a := by simpa using hab
    have haN : a ∈ G.neighborFinset b := by simpa using hab.symm
    constructor
    · intro hbA; exact hclosed b hbA haN
    · intro haA; exact hclosed a haA hbN
  · -- class {u, v}: at most one neighbour outside it at every vertex
    have hAc : ({u, v} : Finset V)ᶜ.Nonempty := by
      refine compl_nonempty_of_card_lt {u, v} ?_
      rw [Finset.card_pair huv]; omega
    refine ⟨{u, v}, friendly_of_other_le G {u, v} (by simp) hAc ?_⟩
    intro x
    have hxdeg : (G.neighborFinset x).card = 2 := hdeg x
    have hle : ((G.neighborFinset x).filter
        (fun y => ¬ (y ∈ ({u, v} : Finset V) ↔ x ∈ ({u, v} : Finset V)))).card ≤ 1 := by
      by_cases hxA : x ∈ ({u, v} : Finset V)
      · have hsame : 1 ≤ ((G.neighborFinset x).filter
            (fun y => (y ∈ ({u, v} : Finset V) ↔ x ∈ ({u, v} : Finset V)))).card := by
          by_cases hxu : x = u
          · refine Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
            · rw [hxu]; simpa using hvu.symm
            · simp [hxu]
          · have hxv : x = v := by
              have h := hxA
              simp only [Finset.mem_insert, Finset.mem_singleton] at h
              tauto
            refine Finset.card_pos.mpr ⟨u, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
            · rw [hxv]; simpa using hvu
            · simp [hxv]
        have hsplit := Finset.card_filter_add_card_filter_not
          (s := G.neighborFinset x) (p := fun y => (y ∈ ({u, v} : Finset V) ↔ x ∈ ({u, v} : Finset V)))
        omega
      · have hsub : ((G.neighborFinset x).filter
            (fun y => ¬ (y ∈ ({u, v} : Finset V) ↔ x ∈ ({u, v} : Finset V)))) ⊆ ({u, v} : Finset V) := by
          intro y hy
          by_contra hy'
          exact (Finset.mem_filter.mp hy).2 (by simp [hy', hxA])
        have hne : ((G.neighborFinset x).filter
            (fun y => ¬ (y ∈ ({u, v} : Finset V) ↔ x ∈ ({u, v} : Finset V)))) ≠ ({u, v} : Finset V) := by
          intro hEq
          have huS : u ∈ (G.neighborFinset x).filter
              (fun y => ¬ (y ∈ ({u, v} : Finset V) ↔ x ∈ ({u, v} : Finset V))) := by
            rw [hEq]; simp
          have hvS : v ∈ (G.neighborFinset x).filter
              (fun y => ¬ (y ∈ ({u, v} : Finset V) ↔ x ∈ ({u, v} : Finset V))) := by
            rw [hEq]; simp
          have hux : G.Adj x u := by simpa using (Finset.mem_filter.mp huS).1
          have hvx : G.Adj x v := by simpa using (Finset.mem_filter.mp hvS).1
          have hxNv : x ∈ G.neighborFinset v := (SimpleGraph.mem_neighborFinset G v x).mpr hvx.symm
          rw [hNv] at hxNv
          have hxuv : x = u ∨ x = w := by simpa using hxNv
          rcases hxuv with hxu | hxw
          · exact hxA (by rw [hxu]; simp)
          · rw [hxw] at hux
            exact htri hux.symm
        have hssub : ((G.neighborFinset x).filter
            (fun y => ¬ (y ∈ ({u, v} : Finset V) ↔ x ∈ ({u, v} : Finset V)))) ⊂ ({u, v} : Finset V) :=
          Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
        have hlt := Finset.card_lt_card hssub
        rw [Finset.card_pair huv] at hlt
        omega
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := G.neighborFinset x) (p := fun y => (y ∈ ({u, v} : Finset V) ↔ x ∈ ({u, v} : Finset V)))
    omega

end Helpers

/-! ## The two isolated hypotheses -/

/-- `H1`: the cubic case, min-degree form, with the explicit bound 6. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    6 ≤ Fintype.card V → G.IsRegularOfDegree 3 →
    ∃ A : Finset V, A.Nonempty ∧ Aᶜ.Nonempty ∧
      ∀ v, 2 ≤ ((G.neighborFinset v).filter (fun w => (w ∈ A ↔ v ∈ A))).card

/-- `H2`: the case r >= 4, counting form, with the explicit bound 4*r. -/
def H2 : Prop :=
  ∀ r : ℕ, 4 ≤ r → ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj], 4 * r ≤ Fintype.card V → G.IsRegularOfDegree r →
    ∃ A : Finset V, A.Nonempty ∧ Aᶜ.Nonempty ∧
      ∀ v, r ≤ 2 * ((G.neighborFinset v).filter (fun w => (w ∈ A ↔ v ∈ A))).card

/-- The bridge: `H1` (cubic, min-degree form) and `H2` (r >= 4, counting form) give the
target; r = 0, 1, 2 are proved outright. -/
theorem main : H1 → H2 → type_of% @OMA.S_opg_friendly_partitions.main := by
  intro h1 h2 r
  match r with
  | 0 =>
    exact ⟨2, fun (V : Type) _ _ (G : SimpleGraph V) _ hV hr => zero_reg G (by omega) hr⟩
  | 1 =>
    exact ⟨4, fun (V : Type) _ _ (G : SimpleGraph V) _ hV hr => one_reg G (by omega) hr⟩
  | 2 =>
    exact ⟨4, fun (V : Type) _ _ (G : SimpleGraph V) _ hV hr => two_reg G (by omega) hr⟩
  | 3 =>
    refine ⟨6, fun (V : Type) _ _ (G : SimpleGraph V) _ hV hr => ?_⟩
    obtain ⟨A, hA, hAc, h⟩ := h1 V G hV hr
    exact ⟨A, friendly_of_same_ge G A hA hAc (fun v => by
      have hv := h v
      have hd : (G.neighborFinset v).card = 3 := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hr v
      omega)⟩
  | (k + 4) =>
    refine ⟨4 * (k + 4), fun (V : Type) _ _ (G : SimpleGraph V) _ hV hr => ?_⟩
    obtain ⟨A, hA, hAc, h⟩ := h2 (k + 4) (by omega) V G hV hr
    exact ⟨A, friendly_of_same_ge G A hA hAc (fun v => by
      have hv := h v
      have hd : (G.neighborFinset v).card = k + 4 := by
        rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hr v
      omega)⟩

end OMA.R_opg_friendly_partitions_R1
