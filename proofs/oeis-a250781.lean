import OMAStatements.S_oeis_a250781
import Mathlib

-- Proof of the formulas of OEIS A250781 (statement by @ivillar).
-- Idea: the conditions only involve consecutive lines, so the count is a walk count on lines (transfer matrix).
-- The lines are grouped into 35 classes such that the number of successors in each class depends only on the class
-- (checked by decide); the class counts V n c then satisfy an explicit linear system, from which the recurrence
-- follows by linear algebra, and the g.f. and the closed form follow from the recurrence and initial values.

namespace OMAA250781Helpers

open OMA.S_oeis_a250781

/-- The lines of the array (the states of the transfer matrix). -/
abbrev R := Fin 7 → Fin 2

instance (u v : R) : Decidable (BlockOK u v) := by unfold BlockOK; infer_instance

abbrev ok (_r : R) : Prop := True

abbrev ini (_r : R) : Prop := True

abbrev compat (r s : R) : Prop := BlockOK r s

abbrev Walk {n : ℕ} (x : Fin (n + 1) → R) : Prop :=
  (∀ i, ok (x i)) ∧ ∀ i : Fin n, compat (x i.castSucc) (x i.succ)

theorem walk_cons (n : ℕ) (r : R) (y : Fin (n + 1) → R) :
    Walk (Fin.cons r y : Fin (n + 2) → R) ↔ ok r ∧ compat r (y 0) ∧ Walk y := by
  simp only [Walk, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero,
    ← Fin.succ_castSucc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨h1, ?_, h2, h4⟩
    simpa using h3
  · rintro ⟨h1, h3, h2, h4⟩
    refine ⟨⟨h1, h2⟩, ?_, h4⟩
    simpa using h3

def F (n : ℕ) (s : R) : ℕ := ∑ y : Fin (n + 1) → R, if Walk y ∧ y 0 = s then 1 else 0

theorem F_zero (s : R) : F 0 s = if ok s then 1 else 0 := by
  unfold F
  rw [← (Equiv.funUnique (Fin 1) R).symm.sum_comp]
  have h : ∀ r : R, (if Walk ((Equiv.funUnique (Fin 1) R).symm r) ∧
      (Equiv.funUnique (Fin 1) R).symm r 0 = s then 1 else 0) = if r = s then (if ok s then 1 else 0) else 0 := by
    intro r
    simp only [Equiv.funUnique_symm_apply, Walk, IsEmpty.forall_iff, and_true]
    by_cases hr : r = s
    · subst hr; simp
    · simp [hr]
  rw [Finset.sum_congr rfl (fun r _ => h r), Finset.sum_ite_eq']
  simp

theorem F_succ (n : ℕ) (s : R) :
    F (n + 1) s = ∑ t : R, if ok s ∧ compat s t then F n t else 0 := by
  have lhs : F (n + 1) s = ∑ y : Fin (n + 1) → R, if ok s ∧ compat s (y 0) ∧ Walk y then 1 else 0 := by
    unfold F
    rw [← (Fin.consEquiv (fun _ : Fin (n + 2) => R)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    have h : ∀ r : R, (if Walk ((Fin.consEquiv (fun _ : Fin (n + 2) => R)) (r, y)) ∧
        (Fin.consEquiv (fun _ : Fin (n + 2) => R)) (r, y) 0 = s then 1 else 0) =
        if r = s then (if ok s ∧ compat s (y 0) ∧ Walk y then 1 else 0) else 0 := by
      intro r
      rw [show (Fin.consEquiv (fun _ : Fin (n + 2) => R)) (r, y) = (Fin.cons r y : Fin (n + 2) → R)
        from rfl]
      simp only [walk_cons, Fin.cons_zero]
      by_cases hr : r = s
      · subst hr
        rw [if_pos rfl]
        exact if_congr ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩ rfl rfl
      · rw [if_neg hr, if_neg (show ¬((ok r ∧ compat r (y 0) ∧ Walk y) ∧ r = s) from fun h => hr h.2)]
    rw [Finset.sum_congr rfl (fun r _ => h r), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  rw [lhs]
  unfold F
  have h2 : ∀ t : R, (if ok s ∧ compat s t then
      ∑ y : Fin (n + 1) → R, (if Walk y ∧ y 0 = t then 1 else 0) else 0) =
      ∑ y : Fin (n + 1) → R, if y 0 = t then (if ok s ∧ compat s (y 0) ∧ Walk y then 1 else 0) else 0 := by
    intro t
    split_ifs with ht
    · apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y 0 = t
      · subst hy
        rw [if_pos (rfl : y 0 = y 0)]
        exact if_congr ⟨fun h => ⟨ht.1, ht.2, h.1⟩, fun h => ⟨h.2.2, rfl⟩⟩ rfl rfl
      · rw [if_neg hy, if_neg (show ¬(Walk y ∧ y 0 = t) from fun h => hy h.2)]
    · symm
      apply Finset.sum_eq_zero
      intro y _
      by_cases hy : y 0 = t
      · subst hy; rw [if_pos rfl, if_neg (fun h => ht ⟨h.1, h.2.1⟩)]
      · rw [if_neg hy]
  rw [Finset.sum_congr rfl (fun t _ => h2 t), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

theorem good_iff (n : ℕ) (x : Fin (n + 1) → R) : Good x ↔ Walk x ∧ ini (x 0) := by
  unfold Good
  constructor
  · intro h2
    exact ⟨⟨fun _ => trivial, fun i => h2 i.castSucc i.succ (by simp)⟩, trivial⟩
  · rintro ⟨⟨-, h2⟩, -⟩
    intro i j hij
    have hi : (i : ℕ) < n := by have := j.isLt; omega
    have e1 : (⟨i, hi⟩ : Fin n).castSucc = i := Fin.ext rfl
    have e2 : (⟨i, hi⟩ : Fin n).succ = j := Fin.ext (by simp [hij])
    have := h2 ⟨i, hi⟩
    rw [e1, e2] at this
    exact this

/-- The class table, indexed by the entries of a line. -/
def clsT : List (List (List (List (List (List (List ℕ)))))) :=
  [[[[[[[0, 1], [2, 3]], [[4, 5], [6, 3]]], [[[7, 8], [9, 3]], [[10, 11], [6, 3]]]], [[[[12, 13], [14, 3]], [[15, 16], [6, 3]]], [[[17, 18], [10, 3]], [[10, 11], [6, 3]]]]], [[[[[19, 20], [21, 3]], [[22, 23], [6, 3]]], [[[24, 25], [26, 3]], [[10, 11], [6, 3]]]], [[[[27, 28], [29, 3]], [[17, 18], [6, 3]]], [[[17, 18], [10, 3]], [[10, 11], [6, 3]]]]]], [[[[[[0, 1], [2, 3]], [[4, 5], [6, 3]]], [[[7, 8], [9, 3]], [[10, 11], [6, 3]]]], [[[[12, 13], [14, 3]], [[15, 16], [6, 3]]], [[[17, 18], [10, 3]], [[10, 11], [6, 3]]]]], [[[[[30, 31], [32, 3]], [[33, 34], [6, 3]]], [[[27, 28], [29, 3]], [[10, 11], [6, 3]]]], [[[[27, 28], [29, 3]], [[17, 18], [6, 3]]], [[[17, 18], [10, 3]], [[10, 11], [6, 3]]]]]]]

/-- The class of a line: lines of the same class have the same number of successors in each class. -/
def cls (r : R) : ℕ := (((((((clsT).getD (r 0 : ℕ) []).getD (r 1 : ℕ) []).getD (r 2 : ℕ) []).getD (r 3 : ℕ) []).getD (r 4 : ℕ) []).getD (r 5 : ℕ) []).getD (r 6 : ℕ) 0

/-- Mt i j: the number of successors in class j of a line of class i. -/
def Mt (i j : ℕ) : ℕ :=
  (([[1, 1, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 1, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 5, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 5, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 4, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    [0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1],
    [0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]] : List (List ℕ)).getD i []).getD j 0

/-- V n c: the number of walks of n + 1 lines starting at a given line of class c. -/
def V : ℕ → ℕ → ℕ
  | 0, c => ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℕ).getD c 0
  | n + 1, 0 => 0 + 1 * V n 0 + 1 * V n 1 + 0 * V n 2 + 6 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 1 => 0 + 0 * V n 0 + 1 * V n 1 + 1 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 5 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 2 => 0 + 0 * V n 0 + 0 * V n 1 + 1 * V n 2 + 1 * V n 3 + 0 * V n 4 + 1 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 4 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 3 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 1 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 4 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 5 * V n 3 + 1 * V n 4 + 1 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 5 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 1 * V n 5 + 1 * V n 6 + 0 * V n 7 + 0 * V n 8 + 1 * V n 9 + 3 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 6 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 1 * V n 3 + 0 * V n 4 + 0 * V n 5 + 1 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 7 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 5 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 1 * V n 7 + 1 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 8 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 4 * V n 6 + 0 * V n 7 + 1 * V n 8 + 1 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 9 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 1 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 1 * V n 9 + 0 * V n 10 + 1 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 1 * V n 16 + 0 * V n 17 + 2 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 10 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 1 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 1 * V n 10 + 1 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 11 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 1 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 1 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 12 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 5 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 1 * V n 12 + 1 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 13 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 4 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 1 * V n 13 + 1 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 14 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 1 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 3 * V n 11 + 0 * V n 12 + 0 * V n 13 + 1 * V n 14 + 0 * V n 15 + 1 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 15 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 4 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 1 * V n 15 + 1 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 16 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 1 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 1 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 1 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 1 * V n 26 + 0 * V n 27 + 0 * V n 28 + 1 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 17 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 2 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 1 * V n 17 + 1 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 18 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 1 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 1 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 1 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 19 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 5 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 1 * V n 19 + 1 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 20 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 4 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 1 * V n 20 + 1 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 21 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 1 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 3 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 1 * V n 21 + 0 * V n 22 + 1 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 22 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 4 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 1 * V n 22 + 1 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 23 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 1 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 2 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 1 * V n 23 + 0 * V n 24 + 0 * V n 25 + 1 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 24 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 4 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 1 * V n 24 + 1 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 25 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 3 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 1 * V n 25 + 1 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 26 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 1 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 1 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 1 * V n 16 + 0 * V n 17 + 1 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 1 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 27 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 3 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 1 * V n 27 + 1 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 28 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 2 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 1 * V n 28 + 1 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 29 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 1 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 1 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 1 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 1 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 30 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 4 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 1 * V n 30 + 1 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 31 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 3 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 1 * V n 31 + 1 * V n 32 + 0 * V n 33 + 0 * V n 34
  | n + 1, 32 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 1 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 2 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 1 * V n 32 + 0 * V n 33 + 1 * V n 34
  | n + 1, 33 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 3 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 1 * V n 33 + 1 * V n 34
  | n + 1, 34 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 1 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 1 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 1 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 1 * V n 34
  | _ + 1, _ => 0

theorem cls_lt : ∀ t : R, cls t < 35 := by decide +kernel

theorem sum_cls (g : ℕ → ℕ) (P : R → Prop) [DecidablePred P] :
    (∑ t : R, if P t then g (cls t) else 0) =
      ∑ c ∈ Finset.range 35, (Finset.univ.filter (fun t : R => cls t = c ∧ P t)).card * g c := by
  have h1 : ∀ t : R, (if P t then g (cls t) else 0) =
      ∑ c ∈ Finset.range 35, if cls t = c ∧ P t then g c else 0 := by
    intro t
    rw [Finset.sum_eq_single (cls t)]
    · by_cases hp : P t <;> simp [hp]
    · intro c _ hc
      rw [if_neg]
      exact fun h => hc h.1.symm
    · intro h
      exact absurd (Finset.mem_range.mpr (cls_lt t)) h
  rw [Finset.sum_congr rfl (fun t _ => h1 t), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]

/-- The lines, numbered by their base-2 digits. -/
abbrev E : R ≃ Fin (2 ^ 7) := finFunctionFinEquiv

theorem cntN_0 : ∀ a : Fin (2 ^ 7), (a : ℕ) / 6 = 0 → ∀ c < 35,
    (Finset.univ.filter (fun x : Fin (2 ^ 7) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_1 : ∀ a : Fin (2 ^ 7), (a : ℕ) / 6 = 1 → ∀ c < 35,
    (Finset.univ.filter (fun x : Fin (2 ^ 7) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_2 : ∀ a : Fin (2 ^ 7), (a : ℕ) / 6 = 2 → ∀ c < 35,
    (Finset.univ.filter (fun x : Fin (2 ^ 7) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_3 : ∀ a : Fin (2 ^ 7), (a : ℕ) / 6 = 3 → ∀ c < 35,
    (Finset.univ.filter (fun x : Fin (2 ^ 7) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_4 : ∀ a : Fin (2 ^ 7), (a : ℕ) / 6 = 4 → ∀ c < 35,
    (Finset.univ.filter (fun x : Fin (2 ^ 7) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_5 : ∀ a : Fin (2 ^ 7), (a : ℕ) / 6 = 5 → ∀ c < 35,
    (Finset.univ.filter (fun x : Fin (2 ^ 7) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_6 : ∀ a : Fin (2 ^ 7), (a : ℕ) / 6 = 6 → ∀ c < 35,
    (Finset.univ.filter (fun x : Fin (2 ^ 7) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_7 : ∀ a : Fin (2 ^ 7), (a : ℕ) / 6 = 7 → ∀ c < 35,
    (Finset.univ.filter (fun x : Fin (2 ^ 7) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_8 : ∀ a : Fin (2 ^ 7), (a : ℕ) / 6 = 8 → ∀ c < 35,
    (Finset.univ.filter (fun x : Fin (2 ^ 7) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_9 : ∀ a : Fin (2 ^ 7), (a : ℕ) / 6 = 9 → ∀ c < 35,
    (Finset.univ.filter (fun x : Fin (2 ^ 7) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_10 : ∀ a : Fin (2 ^ 7), (a : ℕ) / 6 = 10 → ∀ c < 35,
    (Finset.univ.filter (fun x : Fin (2 ^ 7) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_11 : ∀ a : Fin (2 ^ 7), (a : ℕ) / 6 = 11 → ∀ c < 35,
    (Finset.univ.filter (fun x : Fin (2 ^ 7) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_12 : ∀ a : Fin (2 ^ 7), (a : ℕ) / 6 = 12 → ∀ c < 35,
    (Finset.univ.filter (fun x : Fin (2 ^ 7) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_13 : ∀ a : Fin (2 ^ 7), (a : ℕ) / 6 = 13 → ∀ c < 35,
    (Finset.univ.filter (fun x : Fin (2 ^ 7) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_14 : ∀ a : Fin (2 ^ 7), (a : ℕ) / 6 = 14 → ∀ c < 35,
    (Finset.univ.filter (fun x : Fin (2 ^ 7) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_15 : ∀ a : Fin (2 ^ 7), (a : ℕ) / 6 = 15 → ∀ c < 35,
    (Finset.univ.filter (fun x : Fin (2 ^ 7) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_16 : ∀ a : Fin (2 ^ 7), (a : ℕ) / 6 = 16 → ∀ c < 35,
    (Finset.univ.filter (fun x : Fin (2 ^ 7) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_17 : ∀ a : Fin (2 ^ 7), (a : ℕ) / 6 = 17 → ∀ c < 35,
    (Finset.univ.filter (fun x : Fin (2 ^ 7) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_18 : ∀ a : Fin (2 ^ 7), (a : ℕ) / 6 = 18 → ∀ c < 35,
    (Finset.univ.filter (fun x : Fin (2 ^ 7) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_19 : ∀ a : Fin (2 ^ 7), (a : ℕ) / 6 = 19 → ∀ c < 35,
    (Finset.univ.filter (fun x : Fin (2 ^ 7) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_20 : ∀ a : Fin (2 ^ 7), (a : ℕ) / 6 = 20 → ∀ c < 35,
    (Finset.univ.filter (fun x : Fin (2 ^ 7) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_21 : ∀ a : Fin (2 ^ 7), (a : ℕ) / 6 = 21 → ∀ c < 35,
    (Finset.univ.filter (fun x : Fin (2 ^ 7) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem chunk_lt : ∀ a : Fin (2 ^ 7), (a : ℕ) / 6 < 22 := by decide +kernel

theorem cntN (a : Fin (2 ^ 7)) : ∀ c < 35,
    (Finset.univ.filter (fun x : Fin (2 ^ 7) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  have h := chunk_lt a
  generalize hq : (a : ℕ) / 6 = q at h
  interval_cases q
  · exact cntN_0 a hq
  · exact cntN_1 a hq
  · exact cntN_2 a hq
  · exact cntN_3 a hq
  · exact cntN_4 a hq
  · exact cntN_5 a hq
  · exact cntN_6 a hq
  · exact cntN_7 a hq
  · exact cntN_8 a hq
  · exact cntN_9 a hq
  · exact cntN_10 a hq
  · exact cntN_11 a hq
  · exact cntN_12 a hq
  · exact cntN_13 a hq
  · exact cntN_14 a hq
  · exact cntN_15 a hq
  · exact cntN_16 a hq
  · exact cntN_17 a hq
  · exact cntN_18 a hq
  · exact cntN_19 a hq
  · exact cntN_20 a hq
  · exact cntN_21 a hq

theorem cnt (s : R) (c : ℕ) (hc : c < 35) :
    (Finset.univ.filter (fun t : R => cls t = c ∧ (ok s ∧ compat s t))).card = Mt (cls s) c := by
  have h := cntN (E s) c hc
  simp only [Equiv.symm_apply_apply] at h
  rw [← h, Finset.card_filter, Finset.card_filter]
  exact (Equiv.sum_comp E.symm (fun t : R => if cls t = c ∧ (ok s ∧ compat s t) then 1 else 0)).symm


theorem cnt0 : ∀ s : R, (if ok s then 1 else 0) = V 0 (cls s) := by decide +kernel

theorem tcnt : ∀ c < 35, (Finset.univ.filter (fun t : R => cls t = c ∧ ini t)).card =
    ([2, 2, 2, 32, 2, 2, 16, 2, 2, 2, 12, 8, 2, 2, 2, 2, 2, 6, 6, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1] : List ℕ).getD c 0 := by decide +kernel

theorem step (n : ℕ) : ∀ i < 35, (∑ c ∈ Finset.range 35, Mt i c * V n c) = V (n + 1) i := by
  intro i hi
  interval_cases i <;> (simp only [Finset.sum_range_succ, Finset.sum_range_zero]; rfl)

theorem F_eq (n : ℕ) : ∀ s : R, F n s = V n (cls s) := by
  induction n with
  | zero => intro s; rw [F_zero]; exact cnt0 s
  | succ n ih =>
    intro s
    rw [F_succ]
    simp only [ih]
    rw [sum_cls (V n) (fun t => ok s ∧ compat s t), ← step n (cls s) (cls_lt s)]
    apply Finset.sum_congr rfl
    intro c hc
    rw [cnt s c (Finset.mem_range.mp hc)]

/-- U n: the number of arrays with n + 1 lines. -/
def U (n : ℕ) : ℕ := 0 + 2 * V n 0 + 2 * V n 1 + 2 * V n 2 + 32 * V n 3 + 2 * V n 4 + 2 * V n 5 + 16 * V n 6 + 2 * V n 7 + 2 * V n 8 + 2 * V n 9 + 12 * V n 10 + 8 * V n 11 + 2 * V n 12 + 2 * V n 13 + 2 * V n 14 + 2 * V n 15 + 2 * V n 16 + 6 * V n 17 + 6 * V n 18 + 1 * V n 19 + 1 * V n 20 + 1 * V n 21 + 1 * V n 22 + 1 * V n 23 + 1 * V n 24 + 1 * V n 25 + 1 * V n 26 + 3 * V n 27 + 3 * V n 28 + 3 * V n 29 + 1 * V n 30 + 1 * V n 31 + 1 * V n 32 + 1 * V n 33 + 1 * V n 34

theorem usum (n : ℕ) : (∑ c ∈ Finset.range 35, ([2, 2, 2, 32, 2, 2, 16, 2, 2, 2, 12, 8, 2, 2, 2, 2, 2, 6, 6, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1] : List ℕ).getD c 0 * V n c) = U n := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rfl

theorem a_eq (n : ℕ) : a n = U n := by
  unfold a
  rw [Nat.card_congr (Equiv.subtypeEquivRight (good_iff n)), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_filter]
  have h1 : (∑ x : Fin (n + 1) → R, if Walk x ∧ ini (x 0) then 1 else 0) =
      ∑ s : R, if ini s then F n s else 0 := by
    unfold F
    have h2 : ∀ s : R, (if ini s then ∑ y : Fin (n + 1) → R, (if Walk y ∧ y 0 = s then 1 else 0)
        else 0) = ∑ y : Fin (n + 1) → R, if y 0 = s then (if Walk y ∧ ini (y 0) then 1 else 0)
          else 0 := by
      intro s
      split_ifs with hs
      · apply Finset.sum_congr rfl
        intro y _
        by_cases hy : y 0 = s
        · subst hy; simp [hs]
        · simp [hy]
      · symm
        apply Finset.sum_eq_zero
        intro y _
        by_cases hy : y 0 = s
        · subst hy; rw [if_pos rfl, if_neg (fun h => hs h.2)]
        · rw [if_neg hy]
    rw [Finset.sum_congr rfl (fun s _ => h2 s), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_ite_eq]
    simp
  rw [h1]
  simp only [F_eq]
  rw [sum_cls (V n) (fun t => ini t), ← usum n]
  apply Finset.sum_congr rfl
  intro c hc
  rw [tcnt c (Finset.mem_range.mp hc)]

theorem up0 (n : ℕ) : U n = 2 * V n 0 + 2 * V n 1 + 2 * V n 2 + 32 * V n 3 + 2 * V n 4 + 2 * V n 5 + 16 * V n 6 + 2 * V n 7 + 2 * V n 8 + 2 * V n 9 + 12 * V n 10 + 8 * V n 11 + 2 * V n 12 + 2 * V n 13 + 2 * V n 14 + 2 * V n 15 + 2 * V n 16 + 6 * V n 17 + 6 * V n 18 + V n 19 + V n 20 + V n 21 + V n 22 + V n 23 + V n 24 + V n 25 + V n 26 + 3 * V n 27 + 3 * V n 28 + 3 * V n 29 + V n 30 + V n 31 + V n 32 + V n 33 + V n 34 := by
  unfold U
  ring

theorem up1 (n : ℕ) : U (n + 1) = 2 * V n 0 + 4 * V n 1 + 4 * V n 2 + 163 * V n 3 + 2 * V n 4 + 6 * V n 5 + 78 * V n 6 + 2 * V n 7 + 4 * V n 8 + 6 * V n 9 + 29 * V n 10 + 45 * V n 11 + 2 * V n 12 + 4 * V n 13 + 4 * V n 14 + 2 * V n 15 + 9 * V n 16 + 6 * V n 17 + 20 * V n 18 + V n 19 + 2 * V n 20 + 2 * V n 21 + V n 22 + 3 * V n 23 + V n 24 + 2 * V n 25 + 5 * V n 26 + 3 * V n 27 + 6 * V n 28 + 9 * V n 29 + V n 30 + 2 * V n 31 + 2 * V n 32 + V n 33 + 3 * V n 34 := by
  rw [up0 (n + 1)]
  simp only [V]
  ring

theorem up2 (n : ℕ) : U (n + 2) = 2 * V n 0 + 6 * V n 1 + 8 * V n 2 + 393 * V n 3 + 2 * V n 4 + 12 * V n 5 + 248 * V n 6 + 2 * V n 7 + 6 * V n 8 + 16 * V n 9 + 85 * V n 10 + 132 * V n 11 + 2 * V n 12 + 6 * V n 13 + 8 * V n 14 + 2 * V n 15 + 26 * V n 16 + 6 * V n 17 + 52 * V n 18 + V n 19 + 3 * V n 20 + 4 * V n 21 + V n 22 + 6 * V n 23 + V n 24 + 3 * V n 25 + 19 * V n 26 + 3 * V n 27 + 9 * V n 28 + 27 * V n 29 + V n 30 + 3 * V n 31 + 4 * V n 32 + V n 33 + 6 * V n 34 := by
  rw [show n + 2 = (n + 1) + 1 from rfl, up1 (n + 1)]
  simp only [V]
  ring

theorem up3 (n : ℕ) : U (n + 3) = 2 * V n 0 + 8 * V n 1 + 14 * V n 2 + 903 * V n 3 + 2 * V n 4 + 22 * V n 5 + 608 * V n 6 + 2 * V n 7 + 8 * V n 8 + 34 * V n 9 + 217 * V n 10 + 355 * V n 11 + 2 * V n 12 + 8 * V n 13 + 14 * V n 14 + 2 * V n 15 + 71 * V n 16 + 6 * V n 17 + 136 * V n 18 + V n 19 + 4 * V n 20 + 7 * V n 21 + V n 22 + 11 * V n 23 + V n 24 + 4 * V n 25 + 54 * V n 26 + 3 * V n 27 + 12 * V n 28 + 68 * V n 29 + V n 30 + 4 * V n 31 + 7 * V n 32 + V n 33 + 11 * V n 34 := by
  rw [show n + 3 = (n + 1) + 2 from rfl, up2 (n + 1)]
  simp only [V]
  ring

theorem up4 (n : ℕ) : U (n + 4) = 2 * V n 0 + 10 * V n 1 + 22 * V n 2 + 2017 * V n 3 + 2 * V n 4 + 38 * V n 5 + 1382 * V n 6 + 2 * V n 7 + 10 * V n 8 + 64 * V n 9 + 523 * V n 10 + 861 * V n 11 + 2 * V n 12 + 10 * V n 13 + 22 * V n 14 + 2 * V n 15 + 175 * V n 16 + 6 * V n 17 + 332 * V n 18 + V n 19 + 5 * V n 20 + 11 * V n 21 + V n 22 + 19 * V n 23 + V n 24 + 5 * V n 25 + 140 * V n 26 + 3 * V n 27 + 15 * V n 28 + 162 * V n 29 + V n 30 + 5 * V n 31 + 11 * V n 32 + V n 33 + 19 * V n 34 := by
  rw [show n + 4 = (n + 1) + 3 from rfl, up3 (n + 1)]
  simp only [V]
  ring

theorem up5 (n : ℕ) : U (n + 5) = 2 * V n 0 + 12 * V n 1 + 32 * V n 2 + 4445 * V n 3 + 2 * V n 4 + 62 * V n 5 + 3036 * V n 6 + 2 * V n 7 + 12 * V n 8 + 112 * V n 9 + 1201 * V n 10 + 1959 * V n 11 + 2 * V n 12 + 12 * V n 13 + 32 * V n 14 + 2 * V n 15 + 403 * V n 16 + 6 * V n 17 + 768 * V n 18 + V n 19 + 6 * V n 20 + 16 * V n 21 + V n 22 + 31 * V n 23 + V n 24 + 6 * V n 25 + 339 * V n 26 + 3 * V n 27 + 18 * V n 28 + 371 * V n 29 + V n 30 + 6 * V n 31 + 16 * V n 32 + V n 33 + 31 * V n 34 := by
  rw [show n + 5 = (n + 1) + 4 from rfl, up4 (n + 1)]
  simp only [V]
  ring

theorem up6 (n : ℕ) : U (n + 6) = 2 * V n 0 + 14 * V n 1 + 44 * V n 2 + 9691 * V n 3 + 2 * V n 4 + 96 * V n 5 + 6542 * V n 6 + 2 * V n 7 + 14 * V n 8 + 186 * V n 9 + 2651 * V n 10 + 4286 * V n 11 + 2 * V n 12 + 14 * V n 13 + 44 * V n 14 + 2 * V n 15 + 888 * V n 16 + 6 * V n 17 + 1708 * V n 18 + V n 19 + 7 * V n 20 + 22 * V n 21 + V n 22 + 48 * V n 23 + V n 24 + 7 * V n 25 + 779 * V n 26 + 3 * V n 27 + 21 * V n 28 + 823 * V n 29 + V n 30 + 7 * V n 31 + 22 * V n 32 + V n 33 + 48 * V n 34 := by
  rw [show n + 6 = (n + 1) + 5 from rfl, up5 (n + 1)]
  simp only [V]
  ring

theorem up7 (n : ℕ) : U (n + 7) = 2 * V n 0 + 16 * V n 1 + 58 * V n 2 + 20895 * V n 3 + 2 * V n 4 + 142 * V n 5 + 13910 * V n 6 + 2 * V n 7 + 16 * V n 8 + 296 * V n 9 + 5679 * V n 10 + 9143 * V n 11 + 2 * V n 12 + 16 * V n 13 + 58 * V n 14 + 2 * V n 15 + 1899 * V n 16 + 6 * V n 17 + 3688 * V n 18 + V n 19 + 8 * V n 20 + 29 * V n 21 + V n 22 + 71 * V n 23 + V n 24 + 8 * V n 25 + 1722 * V n 26 + 3 * V n 27 + 24 * V n 28 + 1780 * V n 29 + V n 30 + 8 * V n 31 + 29 * V n 32 + V n 33 + 71 * V n 34 := by
  rw [show n + 7 = (n + 1) + 6 from rfl, up6 (n + 1)]
  simp only [V]
  ring

theorem up8 (n : ℕ) : U (n + 8) = 2 * V n 0 + 18 * V n 1 + 74 * V n 2 + 44547 * V n 3 + 2 * V n 4 + 202 * V n 5 + 29260 * V n 6 + 2 * V n 7 + 18 * V n 8 + 454 * V n 9 + 11905 * V n 10 + 19171 * V n 11 + 2 * V n 12 + 18 * V n 13 + 74 * V n 14 + 2 * V n 15 + 3977 * V n 16 + 6 * V n 17 + 7788 * V n 18 + V n 19 + 9 * V n 20 + 37 * V n 21 + V n 22 + 101 * V n 23 + V n 24 + 9 * V n 25 + 3700 * V n 26 + 3 * V n 27 + 27 * V n 28 + 3774 * V n 29 + V n 30 + 9 * V n 31 + 37 * V n 32 + V n 33 + 101 * V n 34 := by
  rw [show n + 8 = (n + 1) + 7 from rfl, up7 (n + 1)]
  simp only [V]
  ring

theorem up9 (n : ℕ) : U (n + 9) = 2 * V n 0 + 20 * V n 1 + 92 * V n 2 + 93953 * V n 3 + 2 * V n 4 + 278 * V n 5 + 60978 * V n 6 + 2 * V n 7 + 20 * V n 8 + 674 * V n 9 + 24579 * V n 10 + 39707 * V n 11 + 2 * V n 12 + 20 * V n 13 + 92 * V n 14 + 2 * V n 15 + 8207 * V n 16 + 6 * V n 17 + 16176 * V n 18 + V n 19 + 10 * V n 20 + 46 * V n 21 + V n 22 + 139 * V n 23 + V n 24 + 10 * V n 25 + 7787 * V n 26 + 3 * V n 27 + 30 * V n 28 + 7879 * V n 29 + V n 30 + 10 * V n 31 + 46 * V n 32 + V n 33 + 139 * V n 34 := by
  rw [show n + 9 = (n + 1) + 8 from rfl, up8 (n + 1)]
  simp only [V]
  ring

theorem up10 (n : ℕ) : U (n + 10) = 2 * V n 0 + 22 * V n 1 + 112 * V n 2 + 196217 * V n 3 + 2 * V n 4 + 372 * V n 5 + 126044 * V n 6 + 2 * V n 7 + 22 * V n 8 + 972 * V n 9 + 50213 * V n 10 + 81500 * V n 11 + 2 * V n 12 + 22 * V n 13 + 112 * V n 14 + 2 * V n 15 + 16762 * V n 16 + 6 * V n 17 + 33196 * V n 18 + V n 19 + 11 * V n 20 + 56 * V n 21 + V n 22 + 186 * V n 23 + V n 24 + 11 * V n 25 + 16143 * V n 26 + 3 * V n 27 + 33 * V n 28 + 16255 * V n 29 + V n 30 + 11 * V n 31 + 56 * V n 32 + V n 33 + 186 * V n 34 := by
  rw [show n + 10 = (n + 1) + 9 from rfl, up9 (n + 1)]
  simp only [V]
  ring

theorem a_v1 : a 1 = 436 := by
  rw [a_eq]; decide +kernel

theorem a_v2 : a 2 = 1106 := by
  rw [a_eq]; decide +kernel

theorem a_v3 : a 3 = 2604 := by
  rw [a_eq]; decide +kernel

theorem a_v4 : a 4 = 5882 := by
  rw [a_eq]; decide +kernel

theorem a_v5 : a 5 = 12950 := by
  rw [a_eq]; decide +kernel

theorem a_v6 : a 6 = 27986 := by
  rw [a_eq]; decide +kernel

theorem a_v7 : a 7 = 59590 := by
  rw [a_eq]; decide +kernel

theorem a_v8 : a 8 = 125334 := by
  rw [a_eq]; decide +kernel

theorem a_v9 : a 9 = 260916 := by
  rw [a_eq]; decide +kernel

theorem a_rec : ∀ m : ℕ, 10 ≤ m → (a m : ℤ) = 10 * (a (m - 1) : ℤ) - 44 * (a (m - 2) : ℤ) + 112 * (a (m - 3) : ℤ) - 182 * (a (m - 4) : ℤ) + 196 * (a (m - 5) : ℤ) - 140 * (a (m - 6) : ℤ) + 64 * (a (m - 7) : ℤ) - 17 * (a (m - 8) : ℤ) + 2 * (a (m - 9) : ℤ) := by
  intro m hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 10 := ⟨m - 10, by omega⟩
  rw [show k + 10 - 1 = k + 9 by omega, show k + 10 - 2 = k + 8 by omega, show k + 10 - 3 = k + 7 by omega, show k + 10 - 4 = k + 6 by omega, show k + 10 - 5 = k + 5 by omega, show k + 10 - 6 = k + 4 by omega, show k + 10 - 7 = k + 3 by omega, show k + 10 - 8 = k + 2 by omega, show k + 10 - 9 = k + 1 by omega]
  rw [a_eq (k + 10), a_eq (k + 9), a_eq (k + 8), a_eq (k + 7), a_eq (k + 6), a_eq (k + 5), a_eq (k + 4), a_eq (k + 3), a_eq (k + 2), a_eq (k + 1)]
  rw [up10 k, up9 k, up8 k, up7 k, up6 k, up5 k, up4 k, up3 k, up2 k, up1 k]
  push_cast
  ring

theorem gf_eq : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
  have e1 : F' * ((1 - PowerSeries.X) ^ 8 * (1 - 2 * PowerSeries.X)) = F' - PowerSeries.C (10 : ℚ) * (PowerSeries.X ^ 1 * F') + PowerSeries.C (44 : ℚ) * (PowerSeries.X ^ 2 * F') - PowerSeries.C (112 : ℚ) * (PowerSeries.X ^ 3 * F') + PowerSeries.C (182 : ℚ) * (PowerSeries.X ^ 4 * F') - PowerSeries.C (196 : ℚ) * (PowerSeries.X ^ 5 * F') + PowerSeries.C (140 : ℚ) * (PowerSeries.X ^ 6 * F') - PowerSeries.C (64 : ℚ) * (PowerSeries.X ^ 7 * F') + PowerSeries.C (17 : ℚ) * (PowerSeries.X ^ 8 * F') - PowerSeries.C (2 : ℚ) * (PowerSeries.X ^ 9 * F') := by
    simp only [map_ofNat]
    ring
  have e2 : (2 * PowerSeries.X * (218 - 1627 * PowerSeries.X + 5364 * PowerSeries.X ^ 2 - 10163 * PowerSeries.X ^ 3 + 12093 * PowerSeries.X ^ 4 - 9259 * PowerSeries.X ^ 5 + 4469 * PowerSeries.X ^ 6 - 1253 * PowerSeries.X ^ 7 + 160 * PowerSeries.X ^ 8) : PowerSeries ℚ) = PowerSeries.C (436 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (3254 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (10728 : ℚ) * PowerSeries.X ^ 3 - PowerSeries.C (20326 : ℚ) * PowerSeries.X ^ 4 + PowerSeries.C (24186 : ℚ) * PowerSeries.X ^ 5 - PowerSeries.C (18518 : ℚ) * PowerSeries.X ^ 6 + PowerSeries.C (8938 : ℚ) * PowerSeries.X ^ 7 - PowerSeries.C (2506 : ℚ) * PowerSeries.X ^ 8 + PowerSeries.C (320 : ℚ) * PowerSeries.X ^ 9 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [F', map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
  by_cases hn : n ≤ 9
  · interval_cases n <;> norm_num [a_v1, a_v2, a_v3, a_v4, a_v5, a_v6, a_v7, a_v8, a_v9]
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 10 := ⟨n - 10, by omega⟩
    have h := a_rec (j + 10) (by omega)
    rw [show j + 10 - 1 = j + 9 by omega, show j + 10 - 2 = j + 8 by omega, show j + 10 - 3 = j + 7 by omega, show j + 10 - 4 = j + 6 by omega, show j + 10 - 5 = j + 5 by omega, show j + 10 - 6 = j + 4 by omega, show j + 10 - 7 = j + 3 by omega, show j + 10 - 8 = j + 2 by omega, show j + 10 - 9 = j + 1 by omega] at h
    have q : (a (j + 10) : ℚ) = 10 * (a (j + 9) : ℚ) - 44 * (a (j + 8) : ℚ) + 112 * (a (j + 7) : ℚ) - 182 * (a (j + 6) : ℚ) + 196 * (a (j + 5) : ℚ) - 140 * (a (j + 4) : ℚ) + 64 * (a (j + 3) : ℚ) - 17 * (a (j + 2) : ℚ) + 2 * (a (j + 1) : ℚ) := by exact_mod_cast h
    simp
    linear_combination q

theorem closed0 : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (2520 * (289 * (2 : ℚ) ^ n - 209) - 314796 * (n : ℚ) - 41972 * (n : ℚ) ^ 2 - 23779 * (n : ℚ) ^ 3 + 385 * (n : ℚ) ^ 4 - 364 * (n : ℚ) ^ 5 + 7 * (n : ℚ) ^ 6 - (n : ℚ) ^ 7) / 1260 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < 10
    · interval_cases n <;> norm_num [a_v1, a_v2, a_v3, a_v4, a_v5, a_v6, a_v7, a_v8, a_v9]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
      have h1 := ih (k + 9) (by omega) (by omega)
      have h2 := ih (k + 8) (by omega) (by omega)
      have h3 := ih (k + 7) (by omega) (by omega)
      have h4 := ih (k + 6) (by omega) (by omega)
      have h5 := ih (k + 5) (by omega) (by omega)
      have h6 := ih (k + 4) (by omega) (by omega)
      have h7 := ih (k + 3) (by omega) (by omega)
      have h8 := ih (k + 2) (by omega) (by omega)
      have h9 := ih (k + 1) (by omega) (by omega)
      have hr := a_rec (k + 10) (by omega)
      rw [show k + 10 - 1 = k + 9 by omega, show k + 10 - 2 = k + 8 by omega, show k + 10 - 3 = k + 7 by omega, show k + 10 - 4 = k + 6 by omega, show k + 10 - 5 = k + 5 by omega, show k + 10 - 6 = k + 4 by omega, show k + 10 - 7 = k + 3 by omega, show k + 10 - 8 = k + 2 by omega, show k + 10 - 9 = k + 1 by omega] at hr
      have q : (a (k + 10) : ℚ) = 10 * (a (k + 9) : ℚ) - 44 * (a (k + 8) : ℚ) + 112 * (a (k + 7) : ℚ) - 182 * (a (k + 6) : ℚ) + 196 * (a (k + 5) : ℚ) - 140 * (a (k + 4) : ℚ) + 64 * (a (k + 3) : ℚ) - 17 * (a (k + 2) : ℚ) + 2 * (a (k + 1) : ℚ) := by exact_mod_cast hr
      rw [q, h1, h2, h3, h4, h5, h6, h7, h8, h9]
      push_cast
      ring

end OMAA250781Helpers

open OMA.S_oeis_a250781 OMAA250781Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a250781.main :=
  ⟨a_rec, gf_eq, closed0⟩
