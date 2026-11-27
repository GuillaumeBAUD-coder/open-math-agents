import FormalConjectures.Paper.ClaudesCycles
import Mathlib

/-! The cube has twelve directed Hamiltonian cycles when marked at the origin.
The eight entries in a direction table give the outgoing coordinate at the eight
vertices, in binary order. The first finite check exhausts the 3^8 tables.
The second checks that every triple of the twelve cycles shares a directed arc.
The previous proof in project PR 224 is credited to @TheWaler. -/

namespace CubeArcCheck

open ClaudesCycles

abbrev Directions := Fin 8 → Fin 3

def vertices : Fin 8 → Vertex 2 :=
  ![![0, 0, 0],
    ![1, 0, 0],
    ![0, 1, 0],
    ![1, 1, 0],
    ![0, 0, 1],
    ![1, 0, 1],
    ![0, 1, 1],
    ![1, 1, 1]]

def neighbor : Fin 8 → Fin 3 → Fin 8 :=
  ![![1, 2, 4],
    ![0, 3, 5],
    ![3, 0, 6],
    ![2, 1, 7],
    ![5, 6, 0],
    ![4, 7, 1],
    ![7, 4, 2],
    ![6, 5, 3]]

lemma neighbor_correct : ∀ (x : Fin 8) (b : Fin 3),
    vertices (neighbor x b) = bumpAt b (vertices x) := by decide

lemma origin_unique : ∀ x : Fin 8, vertices x = vertices 0 → x = 0 := by decide

def walk (t : Directions) : ℕ → Fin 8
  | 0 => 0
  | k + 1 => neighbor (walk t k) (t (walk t k))

def cycles : List Directions :=
  [![0, 1, 1, 2, 1, 0, 2, 1],
   ![0, 1, 2, 0, 2, 0, 0, 1],
   ![0, 2, 1, 0, 1, 0, 0, 2],
   ![0, 2, 2, 0, 2, 1, 1, 2],
   ![1, 0, 0, 2, 0, 2, 1, 0],
   ![1, 0, 2, 1, 0, 1, 1, 2],
   ![1, 2, 0, 1, 2, 1, 1, 0],
   ![1, 2, 2, 1, 2, 0, 0, 2],
   ![2, 0, 0, 1, 0, 1, 2, 0],
   ![2, 0, 0, 2, 1, 2, 2, 1],
   ![2, 1, 1, 0, 1, 2, 0, 1],
   ![2, 1, 1, 2, 0, 2, 2, 0]]

/-- Returning at step eight but not at step four forces the orbit length to be eight. -/
def traverses (t : Directions) : Prop := walk t 8 = 0 ∧ walk t 4 ≠ 0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 12000000 in
lemma complete (t : Directions) (ht : traverses t) : t ∈ cycles := by
  have checked : ∀ a b c d e f g h : Fin 3,
      let u : Directions := ![a, b, c, d, e, f, g, h]
      traverses u → u ∈ cycles := by
    unfold traverses
    decide
  have he : (![t 0, t 1, t 2, t 3, t 4, t 5, t 6, t 7] : Directions) = t := by
    funext i
    fin_cases i <;> rfl
  have hv := checked (t 0) (t 1) (t 2) (t 3) (t 4) (t 5) (t 6) (t 7)
  dsimp only at hv
  rw [he] at hv
  exact hv ht

def overlaps (a b c : Directions) : Bool :=
  decide (∃ x, a x = b x ∨ a x = c x ∨ b x = c x)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma conflict {a b c : Directions} (ha : a ∈ cycles) (hb : b ∈ cycles) (hc : c ∈ cycles) :
    ∃ x, a x = b x ∨ a x = c x ∨ b x = c x := by
  have h : cycles.all (fun i => cycles.all (fun j => cycles.all (overlaps i j))) = true := by
    decide
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h a ha) b hb) c hc)

lemma lift_walk {σ : Equiv.Perm (Vertex 2)} {t : Directions}
    (h : ∀ x, σ (vertices x) = vertices (neighbor x (t x))) (k : ℕ) :
    vertices (walk t k) = (σ ^ k) (vertices 0) := by
  induction k with
  | zero => simp [walk]
  | succ k ih => rw [walk, ← h, ih, pow_succ', Equiv.Perm.mul_apply]

lemma in_table {σ : Equiv.Perm (Vertex 2)} {t : Directions}
    (h : ∀ x, σ (vertices x) = vertices (neighbor x (t x)))
    (hcyc : IsDirectedHamiltonianCycle (cubeAdj (m := 2)) σ) : t ∈ cycles := by
  have hord : orderOf σ = 8 := by
    rw [hcyc.2.1.orderOf, hcyc.2.2, Finset.card_univ]
    decide
  have h8 : σ ^ 8 = 1 := hord ▸ pow_orderOf_eq_one σ
  have h4 : vertices 0 ∈ (σ ^ 4).support := by
    rw [hcyc.2.1.support_pow_of_pos_of_lt_orderOf (by decide) (by omega), hcyc.2.2]
    exact Finset.mem_univ _
  apply complete
  constructor
  · apply origin_unique
    rw [lift_walk h 8, h8]
    rfl
  · intro ret
    have hr := lift_walk h 4
    rw [ret] at hr
    exact (Equiv.Perm.mem_support.mp h4) hr.symm

end CubeArcCheck

theorem OMA.solution : type_of% @ClaudesCycles.cube_hamiltonian_arc_decomposition_impossible_m2 := by
  rintro ⟨σ, hcyc, hcover⟩
  let t (i : Fin 3) (x : Fin 8) := ((hcyc i).1 (CubeArcCheck.vertices x)).choose
  have hstep (i : Fin 3) (x : Fin 8) :
      σ i (CubeArcCheck.vertices x) = ClaudesCycles.bumpAt (t i x) (CubeArcCheck.vertices x) :=
    ((hcyc i).1 (CubeArcCheck.vertices x)).choose_spec.symm
  have htab (i : Fin 3) : t i ∈ CubeArcCheck.cycles := by
    apply CubeArcCheck.in_table (σ := σ i) _ (hcyc i)
    intro x
    rw [CubeArcCheck.neighbor_correct, hstep]
  have unique {i j : Fin 3} (x : Fin 8) (h : t i x = t j x) : i = j := by
    obtain ⟨c, _, huniq⟩ := hcover (CubeArcCheck.vertices x) (t i x)
    exact (huniq i (hstep i x)).trans (huniq j (h ▸ hstep j x)).symm
  obtain ⟨x, h | h | h⟩ := CubeArcCheck.conflict (htab 0) (htab 1) (htab 2)
  · exact (by decide : (0 : Fin 3) ≠ 1) (unique x h)
  · exact (by decide : (0 : Fin 3) ≠ 2) (unique x h)
  · exact (by decide : (1 : Fin 3) ≠ 2) (unique x h)
