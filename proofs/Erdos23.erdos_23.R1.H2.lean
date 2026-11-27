import OMAReductions.R_Erdos23_erdos_23_R1
import Mathlib

-- Step Erdos23.erdos_23.R1.H2: hypothesis H2 of reduction Erdos23.erdos_23.R1
-- Credit: @ivillar. Averaging over all 2^n vertex subsets: toggling one endpoint swaps same-side and split partitions of an edge, so each edge is same-side for exactly 2^(n-1) subsets; hence some subset has at most |E|/2 same-side edges. Uses the reduction's lemma same_mk (PR #9853).

/-! Step Erdos23.erdos_23.R1.H2. -/

namespace P8Erdos23

open Finset

/-- Toggle membership of `u`. -/
def toggle {V : Type} [DecidableEq V] (u : V) (S : Finset V) : Finset V :=
  if u ∈ S then S.erase u else insert u S

lemma mem_toggle_self {V : Type} [DecidableEq V] (u : V) (S : Finset V) :
    u ∈ toggle u S ↔ u ∉ S := by
  unfold toggle
  split_ifs with h <;> simp [h]

lemma mem_toggle_ne {V : Type} [DecidableEq V] {u w : V} (S : Finset V) (h : w ≠ u) :
    w ∈ toggle u S ↔ w ∈ S := by
  unfold toggle
  split_ifs with hu <;> simp [h]

lemma toggle_toggle {V : Type} [DecidableEq V] (u : V) (S : Finset V) :
    toggle u (toggle u S) = S := by
  by_cases h : u ∈ S
  · have h1 : toggle u S = S.erase u := if_pos h
    have h2 : u ∉ S.erase u := by simp
    rw [h1, toggle, if_neg h2, Finset.insert_erase h]
  · have h1 : toggle u S = insert u S := if_neg h
    have h2 : u ∈ insert u S := Finset.mem_insert_self u S
    rw [h1, toggle, if_pos h2, Finset.erase_insert h]

lemma half_count {V : Type} [Fintype V] [DecidableEq V] {u v : V} (huv : u ≠ v) :
    ((univ : Finset (Finset V)).filter (fun S => (u ∈ S ↔ v ∈ S))).card * 2 =
      2 ^ Fintype.card V := by
  have hvu : v ≠ u := fun h => huv h.symm
  have hAB : ((univ : Finset (Finset V)).filter (fun S => (u ∈ S ↔ v ∈ S))).card =
      ((univ : Finset (Finset V)).filter (fun S => ¬ (u ∈ S ↔ v ∈ S))).card := by
    apply Finset.card_nbij' (toggle u) (toggle u)
    · intro S hS
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hS ⊢
      rw [mem_toggle_self, mem_toggle_ne S hvu]
      tauto
    · intro S hS
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hS ⊢
      rw [mem_toggle_self, mem_toggle_ne S hvu]
      tauto
    · intro S _
      exact toggle_toggle u S
    · intro S _
      exact toggle_toggle u S
  have htot := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Finset V)))
    (fun S => (u ∈ S ↔ v ∈ S))
  rw [Finset.card_univ, Fintype.card_finset] at htot
  omega

lemma key {V : Type} [Fintype V] [DecidableEq V] (E : Finset (Sym2 V))
    (hE : ∀ e ∈ E, ¬ e.IsDiag)
    (P : Finset V → Sym2 V → Prop) [∀ S, DecidablePred (P S)] [∀ e, DecidablePred (fun S => P S e)]
    (hP : ∀ S u v, P S s(u, v) ↔ (u ∈ S ↔ v ∈ S)) :
    ∃ S : Finset V, (E.filter (P S)).card ≤ E.card / 2 := by
  by_contra hcon
  have hall : ∀ S : Finset V, E.card + 1 ≤ 2 * (E.filter (P S)).card := by
    intro S
    have := not_le.mp (fun h => hcon ⟨S, h⟩)
    omega
  have hcount : ∀ e ∈ E,
      ((univ : Finset (Finset V)).filter (fun S => P S e)).card * 2 = 2 ^ Fintype.card V := by
    intro e he
    have hd := hE e he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : u ≠ v := fun h => hd (Sym2.mk_isDiag_iff.mpr h)
      rw [← half_count huv]
      congr 2
      ext S
      simp [hP]
  have hsum : ∑ S : Finset V, (E.filter (P S)).card =
      ∑ e ∈ E, ((univ : Finset (Finset V)).filter (fun S => P S e)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have h2 : (∑ S : Finset V, (E.filter (P S)).card) * 2 = E.card * 2 ^ Fintype.card V := by
    rw [hsum, Finset.sum_mul, Finset.sum_congr rfl hcount, Finset.sum_const, smul_eq_mul]
  have h4 : ∑ _S : Finset V, (E.card + 1) ≤ ∑ S : Finset V, 2 * (E.filter (P S)).card :=
    Finset.sum_le_sum (fun S _ => hall S)
  rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_finset,
    smul_eq_mul] at h4
  have hpos : 0 < 2 ^ Fintype.card V := by positivity
  nlinarith

theorem maxcut : OMA.R_Erdos23_erdos_23_R1.H2 := by
  intro V _ G
  classical
  obtain ⟨S, hS⟩ := key G.edgeFinset
    (fun e he => G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp he))
    (fun S e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))
    (fun S u v => OMA.R_Erdos23_erdos_23_R1.same_mk S u v)
  exact ⟨S, by convert hS⟩

end P8Erdos23

theorem OMA.solution : OMA.R_Erdos23_erdos_23_R1.H2 :=
  P8Erdos23.maxcut
