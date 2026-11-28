import OMAStatements.S_oeis_a250893
import Mathlib

-- Proof of the formulas of OEIS A250893 (statement by @ivillar).
-- Idea: the conditions only involve consecutive lines, so the count is a walk count on lines (transfer matrix).
-- The lines are grouped into 42 classes such that the number of successors in each class depends only on the class
-- (checked by decide); the class counts V n c then satisfy an explicit linear system, from which the recurrence
-- follows by linear algebra, and the g.f. and the closed form follow from the recurrence and initial values.

namespace OMAA250893Helpers

open OMA.S_oeis_a250893

/-- The lines of the array (the states of the transfer matrix). -/
abbrev R := Fin 4 → Fin 3

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
def clsT : List (List (List (List ℕ))) :=
  [[[[0, 1, 2], [3, 1, 2], [4, 5, 2]], [[6, 1, 2], [3, 1, 2], [4, 5, 2]], [[7, 8, 2], [9, 8, 2], [4, 5, 2]]], [[[10, 11, 2], [12, 11, 2], [4, 5, 2]], [[13, 14, 2], [15, 16, 17], [18, 19, 17]], [[20, 21, 2], [22, 23, 17], [18, 19, 17]]], [[[24, 25, 2], [26, 25, 2], [4, 5, 2]], [[27, 28, 2], [29, 30, 31], [32, 33, 31]], [[34, 35, 2], [36, 37, 38], [39, 40, 41]]]]

/-- The class of a line: lines of the same class have the same number of successors in each class. -/
def cls (r : R) : ℕ := ((((clsT).getD (r 0 : ℕ) []).getD (r 1 : ℕ) []).getD (r 2 : ℕ) []).getD (r 3 : ℕ) 0

/-- Mt i j: the number of successors in class j of a line of class i. -/
def Mt (i j : ℕ) : ℕ :=
  (([[1, 3, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    [0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 3, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 2, 5, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 3, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 2, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 6, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 3, 0, 0, 2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 5, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 4, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1],
    [0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 1, 3, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    [1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 2, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1],
    [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1],
    [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 1],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]] : List (List ℕ)).getD i []).getD j 0

/-- V n c: the number of walks of n + 1 lines starting at a given line of class c. -/
def V : ℕ → ℕ → ℕ
  | 0, c => ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℕ).getD c 0
  | n + 1, 0 => 0 + 1 * V n 0 + 3 * V n 1 + 6 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 1 * V n 16 + 3 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 1 * V n 41
  | n + 1, 1 => 0 + 0 * V n 0 + 1 * V n 1 + 3 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 1 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 0 * V n 41
  | n + 1, 2 => 0 + 0 * V n 0 + 0 * V n 1 + 1 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 0 * V n 41
  | n + 1, 3 => 0 + 0 * V n 0 + 1 * V n 1 + 3 * V n 2 + 1 * V n 3 + 0 * V n 4 + 2 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 1 * V n 17 + 0 * V n 18 + 1 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 0 * V n 41
  | n + 1, 4 => 0 + 0 * V n 0 + 0 * V n 1 + 1 * V n 2 + 0 * V n 3 + 1 * V n 4 + 1 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 0 * V n 41
  | n + 1, 5 => 0 + 0 * V n 0 + 0 * V n 1 + 1 * V n 2 + 0 * V n 3 + 0 * V n 4 + 1 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 0 * V n 41
  | n + 1, 6 => 0 + 0 * V n 0 + 2 * V n 1 + 5 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 1 * V n 6 + 0 * V n 7 + 1 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 2 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 1 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 0 * V n 41
  | n + 1, 7 => 0 + 0 * V n 0 + 0 * V n 1 + 3 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 1 * V n 7 + 2 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 0 * V n 41
  | n + 1, 8 => 0 + 0 * V n 0 + 0 * V n 1 + 2 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 1 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 0 * V n 41
  | n + 1, 9 => 0 + 0 * V n 0 + 0 * V n 1 + 2 * V n 2 + 0 * V n 3 + 0 * V n 4 + 1 * V n 5 + 0 * V n 6 + 0 * V n 7 + 1 * V n 8 + 1 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 0 * V n 41
  | n + 1, 10 => 0 + 0 * V n 0 + 1 * V n 1 + 6 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 1 * V n 10 + 2 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 1 * V n 16 + 3 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 1 * V n 30 + 2 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 1 * V n 41
  | n + 1, 11 => 0 + 0 * V n 0 + 0 * V n 1 + 3 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 1 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 1 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 1 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 0 * V n 41
  | n + 1, 12 => 0 + 0 * V n 0 + 0 * V n 1 + 3 * V n 2 + 0 * V n 3 + 0 * V n 4 + 2 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 1 * V n 11 + 1 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 1 * V n 17 + 0 * V n 18 + 1 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 1 * V n 31 + 0 * V n 32 + 1 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 0 * V n 41
  | n + 1, 13 => 0 + 0 * V n 0 + 1 * V n 1 + 5 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 1 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 1 * V n 13 + 1 * V n 14 + 0 * V n 15 + 1 * V n 16 + 4 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 1 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 1 * V n 37 + 1 * V n 38 + 0 * V n 39 + 0 * V n 40 + 1 * V n 41
  | n + 1, 14 => 0 + 0 * V n 0 + 0 * V n 1 + 3 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 1 * V n 14 + 0 * V n 15 + 0 * V n 16 + 2 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 1 * V n 38 + 0 * V n 39 + 0 * V n 40 + 0 * V n 41
  | n + 1, 15 => 0 + 0 * V n 0 + 1 * V n 1 + 3 * V n 2 + 0 * V n 3 + 0 * V n 4 + 2 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 1 * V n 15 + 1 * V n 16 + 3 * V n 17 + 0 * V n 18 + 2 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 1 * V n 40 + 1 * V n 41
  | n + 1, 16 => 0 + 1 * V n 0 + 0 * V n 1 + 3 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 1 * V n 16 + 3 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 1 * V n 41
  | n + 1, 17 => 0 + 0 * V n 0 + 1 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 1 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 0 * V n 41
  | n + 1, 18 => 0 + 0 * V n 0 + 1 * V n 1 + 1 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 1 * V n 17 + 1 * V n 18 + 1 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 0 * V n 41
  | n + 1, 19 => 0 + 0 * V n 0 + 0 * V n 1 + 1 * V n 2 + 1 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 1 * V n 17 + 0 * V n 18 + 1 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 0 * V n 41
  | n + 1, 20 => 0 + 0 * V n 0 + 1 * V n 1 + 3 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 2 * V n 17 + 0 * V n 18 + 0 * V n 19 + 1 * V n 20 + 1 * V n 21 + 0 * V n 22 + 1 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 0 * V n 41
  | n + 1, 21 => 0 + 0 * V n 0 + 0 * V n 1 + 2 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 1 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 1 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 0 * V n 41
  | n + 1, 22 => 0 + 0 * V n 0 + 1 * V n 1 + 2 * V n 2 + 0 * V n 3 + 0 * V n 4 + 1 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 2 * V n 17 + 0 * V n 18 + 1 * V n 19 + 0 * V n 20 + 0 * V n 21 + 1 * V n 22 + 1 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 0 * V n 41
  | n + 1, 23 => 0 + 0 * V n 0 + 0 * V n 1 + 2 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 1 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 2 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 1 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 0 * V n 41
  | n + 1, 24 => 0 + 0 * V n 0 + 0 * V n 1 + 4 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 1 * V n 16 + 3 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 1 * V n 24 + 2 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 1 * V n 30 + 2 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 1 * V n 41
  | n + 1, 25 => 0 + 0 * V n 0 + 0 * V n 1 + 2 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 1 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 1 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 1 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 0 * V n 41
  | n + 1, 26 => 0 + 0 * V n 0 + 0 * V n 1 + 2 * V n 2 + 0 * V n 3 + 0 * V n 4 + 1 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 1 * V n 17 + 0 * V n 18 + 1 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 1 * V n 25 + 1 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 1 * V n 31 + 0 * V n 32 + 1 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 0 * V n 41
  | n + 1, 27 => 0 + 0 * V n 0 + 0 * V n 1 + 3 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 1 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 2 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 1 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 1 * V n 27 + 1 * V n 28 + 0 * V n 29 + 1 * V n 30 + 2 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 1 * V n 37 + 1 * V n 38 + 0 * V n 39 + 0 * V n 40 + 1 * V n 41
  | n + 1, 28 => 0 + 0 * V n 0 + 0 * V n 1 + 2 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 1 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 1 * V n 28 + 0 * V n 29 + 0 * V n 30 + 1 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 1 * V n 38 + 0 * V n 39 + 0 * V n 40 + 0 * V n 41
  | n + 1, 29 => 0 + 0 * V n 0 + 0 * V n 1 + 2 * V n 2 + 0 * V n 3 + 0 * V n 4 + 1 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 1 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 1 * V n 17 + 0 * V n 18 + 1 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 1 * V n 29 + 1 * V n 30 + 2 * V n 31 + 0 * V n 32 + 1 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 1 * V n 40 + 1 * V n 41
  | n + 1, 30 => 0 + 0 * V n 0 + 0 * V n 1 + 2 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 1 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 1 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 1 * V n 30 + 2 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 1 * V n 41
  | n + 1, 31 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 1 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 1 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 0 * V n 41
  | n + 1, 32 => 0 + 0 * V n 0 + 0 * V n 1 + 1 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 1 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 1 * V n 31 + 1 * V n 32 + 1 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 0 * V n 41
  | n + 1, 33 => 0 + 0 * V n 0 + 0 * V n 1 + 1 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 1 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 1 * V n 31 + 0 * V n 32 + 1 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 0 * V n 41
  | n + 1, 34 => 0 + 0 * V n 0 + 0 * V n 1 + 2 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 1 * V n 16 + 2 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 1 * V n 34 + 1 * V n 35 + 0 * V n 36 + 1 * V n 37 + 1 * V n 38 + 0 * V n 39 + 0 * V n 40 + 1 * V n 41
  | n + 1, 35 => 0 + 0 * V n 0 + 0 * V n 1 + 1 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 1 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 1 * V n 35 + 0 * V n 36 + 0 * V n 37 + 1 * V n 38 + 0 * V n 39 + 0 * V n 40 + 0 * V n 41
  | n + 1, 36 => 0 + 0 * V n 0 + 0 * V n 1 + 1 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 1 * V n 14 + 0 * V n 15 + 0 * V n 16 + 1 * V n 17 + 0 * V n 18 + 1 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 1 * V n 36 + 1 * V n 37 + 1 * V n 38 + 0 * V n 39 + 1 * V n 40 + 1 * V n 41
  | n + 1, 37 => 0 + 0 * V n 0 + 0 * V n 1 + 1 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 1 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 1 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 1 * V n 37 + 1 * V n 38 + 0 * V n 39 + 0 * V n 40 + 1 * V n 41
  | n + 1, 38 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 1 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 1 * V n 38 + 0 * V n 39 + 0 * V n 40 + 0 * V n 41
  | n + 1, 39 => 0 + 0 * V n 0 + 0 * V n 1 + 1 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 1 * V n 16 + 1 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 1 * V n 39 + 1 * V n 40 + 1 * V n 41
  | n + 1, 40 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 1 * V n 15 + 0 * V n 16 + 1 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 1 * V n 40 + 1 * V n 41
  | n + 1, 41 => 0 + 1 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 1 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30 + 0 * V n 31 + 0 * V n 32 + 0 * V n 33 + 0 * V n 34 + 0 * V n 35 + 0 * V n 36 + 0 * V n 37 + 0 * V n 38 + 0 * V n 39 + 0 * V n 40 + 1 * V n 41
  | _ + 1, _ => 0

theorem cls_lt : ∀ t : R, cls t < 42 := by decide +kernel

theorem sum_cls (g : ℕ → ℕ) (P : R → Prop) [DecidablePred P] :
    (∑ t : R, if P t then g (cls t) else 0) =
      ∑ c ∈ Finset.range 42, (Finset.univ.filter (fun t : R => cls t = c ∧ P t)).card * g c := by
  have h1 : ∀ t : R, (if P t then g (cls t) else 0) =
      ∑ c ∈ Finset.range 42, if cls t = c ∧ P t then g c else 0 := by
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

/-- The lines, numbered by their base-3 digits. -/
abbrev E : R ≃ Fin (3 ^ 4) := finFunctionFinEquiv

theorem cntN_0 : ∀ a : Fin (3 ^ 4), (a : ℕ) / 8 = 0 → ∀ c < 42,
    (Finset.univ.filter (fun x : Fin (3 ^ 4) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_1 : ∀ a : Fin (3 ^ 4), (a : ℕ) / 8 = 1 → ∀ c < 42,
    (Finset.univ.filter (fun x : Fin (3 ^ 4) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_2 : ∀ a : Fin (3 ^ 4), (a : ℕ) / 8 = 2 → ∀ c < 42,
    (Finset.univ.filter (fun x : Fin (3 ^ 4) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_3 : ∀ a : Fin (3 ^ 4), (a : ℕ) / 8 = 3 → ∀ c < 42,
    (Finset.univ.filter (fun x : Fin (3 ^ 4) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_4 : ∀ a : Fin (3 ^ 4), (a : ℕ) / 8 = 4 → ∀ c < 42,
    (Finset.univ.filter (fun x : Fin (3 ^ 4) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_5 : ∀ a : Fin (3 ^ 4), (a : ℕ) / 8 = 5 → ∀ c < 42,
    (Finset.univ.filter (fun x : Fin (3 ^ 4) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_6 : ∀ a : Fin (3 ^ 4), (a : ℕ) / 8 = 6 → ∀ c < 42,
    (Finset.univ.filter (fun x : Fin (3 ^ 4) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_7 : ∀ a : Fin (3 ^ 4), (a : ℕ) / 8 = 7 → ∀ c < 42,
    (Finset.univ.filter (fun x : Fin (3 ^ 4) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_8 : ∀ a : Fin (3 ^ 4), (a : ℕ) / 8 = 8 → ∀ c < 42,
    (Finset.univ.filter (fun x : Fin (3 ^ 4) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_9 : ∀ a : Fin (3 ^ 4), (a : ℕ) / 8 = 9 → ∀ c < 42,
    (Finset.univ.filter (fun x : Fin (3 ^ 4) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem cntN_10 : ∀ a : Fin (3 ^ 4), (a : ℕ) / 8 = 10 → ∀ c < 42,
    (Finset.univ.filter (fun x : Fin (3 ^ 4) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  decide +kernel

theorem chunk_lt : ∀ a : Fin (3 ^ 4), (a : ℕ) / 8 < 11 := by decide +kernel

theorem cntN (a : Fin (3 ^ 4)) : ∀ c < 42,
    (Finset.univ.filter (fun x : Fin (3 ^ 4) => cls (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm x)))).card = Mt (cls (E.symm a)) c := by
  have h := chunk_lt a
  generalize hq : (a : ℕ) / 8 = q at h
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

theorem cnt (s : R) (c : ℕ) (hc : c < 42) :
    (Finset.univ.filter (fun t : R => cls t = c ∧ (ok s ∧ compat s t))).card = Mt (cls s) c := by
  have h := cntN (E s) c hc
  simp only [Equiv.symm_apply_apply] at h
  rw [← h, Finset.card_filter, Finset.card_filter]
  exact (Equiv.sum_comp E.symm (fun t : R => if cls t = c ∧ (ok s ∧ compat s t) then 1 else 0)).symm


theorem cnt0 : ∀ s : R, (if ok s then 1 else 0) = V 0 (cls s) := by decide +kernel

theorem tcnt : ∀ c < 42, (Finset.univ.filter (fun t : R => cls t = c ∧ ini t)).card =
    ([1, 4, 19, 2, 5, 5, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℕ).getD c 0 := by decide +kernel

theorem step (n : ℕ) : ∀ i < 42, (∑ c ∈ Finset.range 42, Mt i c * V n c) = V (n + 1) i := by
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
def U (n : ℕ) : ℕ := 0 + 1 * V n 0 + 4 * V n 1 + 19 * V n 2 + 2 * V n 3 + 5 * V n 4 + 5 * V n 5 + 1 * V n 6 + 1 * V n 7 + 2 * V n 8 + 1 * V n 9 + 1 * V n 10 + 2 * V n 11 + 1 * V n 12 + 1 * V n 13 + 1 * V n 14 + 1 * V n 15 + 1 * V n 16 + 4 * V n 17 + 2 * V n 18 + 2 * V n 19 + 1 * V n 20 + 1 * V n 21 + 1 * V n 22 + 1 * V n 23 + 1 * V n 24 + 2 * V n 25 + 1 * V n 26 + 1 * V n 27 + 1 * V n 28 + 1 * V n 29 + 1 * V n 30 + 2 * V n 31 + 1 * V n 32 + 1 * V n 33 + 1 * V n 34 + 1 * V n 35 + 1 * V n 36 + 1 * V n 37 + 1 * V n 38 + 1 * V n 39 + 1 * V n 40 + 1 * V n 41

theorem usum (n : ℕ) : (∑ c ∈ Finset.range 42, ([1, 4, 19, 2, 5, 5, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℕ).getD c 0 * V n c) = U n := by
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

theorem up0 (n : ℕ) : U n = V n 0 + 4 * V n 1 + 19 * V n 2 + 2 * V n 3 + 5 * V n 4 + 5 * V n 5 + V n 6 + V n 7 + 2 * V n 8 + V n 9 + V n 10 + 2 * V n 11 + V n 12 + V n 13 + V n 14 + V n 15 + V n 16 + 4 * V n 17 + 2 * V n 18 + 2 * V n 19 + V n 20 + V n 21 + V n 22 + V n 23 + V n 24 + 2 * V n 25 + V n 26 + V n 27 + V n 28 + V n 29 + V n 30 + 2 * V n 31 + V n 32 + V n 33 + V n 34 + V n 35 + V n 36 + V n 37 + V n 38 + V n 39 + V n 40 + V n 41 := by
  unfold U
  ring

theorem up1 (n : ℕ) : U (n + 1) = 3 * V n 0 + 22 * V n 1 + 136 * V n 2 + 4 * V n 3 + 5 * V n 4 + 22 * V n 5 + 2 * V n 6 + V n 7 + 7 * V n 8 + V n 9 + 2 * V n 10 + 10 * V n 11 + 2 * V n 12 + 2 * V n 13 + 4 * V n 14 + 2 * V n 15 + 9 * V n 16 + 62 * V n 17 + 2 * V n 18 + 13 * V n 19 + V n 20 + 2 * V n 21 + V n 22 + 6 * V n 23 + V n 24 + 5 * V n 25 + V n 26 + V n 27 + 2 * V n 28 + V n 29 + 5 * V n 30 + 21 * V n 31 + V n 32 + 5 * V n 33 + V n 34 + 2 * V n 35 + V n 36 + 5 * V n 37 + 9 * V n 38 + V n 39 + 5 * V n 40 + 15 * V n 41 := by
  rw [up0 (n + 1)]
  simp only [V]
  ring

theorem up2 (n : ℕ) : U (n + 2) = 27 * V n 0 + 111 * V n 1 + 479 * V n 2 + 17 * V n 3 + 5 * V n 4 + 47 * V n 5 + 8 * V n 6 + V n 7 + 14 * V n 8 + V n 9 + 7 * V n 10 + 40 * V n 11 + 7 * V n 12 + 7 * V n 13 + 16 * V n 14 + 7 * V n 15 + 36 * V n 16 + 236 * V n 17 + 2 * V n 18 + 29 * V n 19 + V n 20 + 3 * V n 21 + V n 22 + 13 * V n 23 + V n 24 + 8 * V n 25 + V n 26 + V n 27 + 3 * V n 28 + V n 29 + 10 * V n 30 + 67 * V n 31 + V n 32 + 10 * V n 33 + V n 34 + 3 * V n 35 + V n 36 + 10 * V n 37 + 27 * V n 38 + V n 39 + 10 * V n 40 + 54 * V n 41 := by
  rw [show n + 2 = (n + 1) + 1 from rfl, up1 (n + 1)]
  simp only [V]
  ring

theorem up3 (n : ℕ) : U (n + 3) = 117 * V n 0 + 486 * V n 1 + 1694 * V n 2 + 46 * V n 3 + 5 * V n 4 + 118 * V n 5 + 21 * V n 6 + V n 7 + 32 * V n 8 + V n 9 + 17 * V n 10 + 131 * V n 11 + 17 * V n 12 + 17 * V n 13 + 51 * V n 14 + 17 * V n 15 + 141 * V n 16 + 837 * V n 17 + 2 * V n 18 + 73 * V n 19 + V n 20 + 4 * V n 21 + V n 22 + 31 * V n 23 + V n 24 + 11 * V n 25 + V n 26 + V n 27 + 4 * V n 28 + V n 29 + 20 * V n 30 + 177 * V n 31 + V n 32 + 20 * V n 33 + V n 34 + 4 * V n 35 + V n 36 + 20 * V n 37 + 69 * V n 38 + V n 39 + 20 * V n 40 + 174 * V n 41 := by
  rw [show n + 3 = (n + 1) + 2 from rfl, up2 (n + 1)]
  simp only [V]
  ring

theorem up4 (n : ℕ) : U (n + 4) = 432 * V n 0 + 1817 * V n 1 + 5827 * V n 2 + 119 * V n 3 + 5 * V n 4 + 287 * V n 5 + 52 * V n 6 + V n 7 + 73 * V n 8 + V n 9 + 37 * V n 10 + 362 * V n 11 + 37 * V n 12 + 37 * V n 13 + 138 * V n 14 + 37 * V n 15 + 486 * V n 16 + 2840 * V n 17 + 2 * V n 18 + 176 * V n 19 + V n 20 + 5 * V n 21 + V n 22 + 72 * V n 23 + V n 24 + 14 * V n 25 + V n 26 + V n 27 + 5 * V n 28 + V n 29 + 40 * V n 30 + 442 * V n 31 + V n 32 + 40 * V n 33 + V n 34 + 5 * V n 35 + V n 36 + 40 * V n 37 + 168 * V n 38 + V n 39 + 40 * V n 40 + 549 * V n 41 := by
  rw [show n + 4 = (n + 1) + 3 from rfl, up3 (n + 1)]
  simp only [V]
  ring

theorem up5 (n : ℕ) : U (n + 5) = 1467 * V n 0 + 6291 * V n 1 + 19073 * V n 2 + 295 * V n 3 + 5 * V n 4 + 682 * V n 5 + 124 * V n 6 + V n 7 + 165 * V n 8 + V n 9 + 77 * V n 10 + 918 * V n 11 + 77 * V n 12 + 77 * V n 13 + 344 * V n 14 + 77 * V n 15 + 1581 * V n 16 + 9165 * V n 17 + 2 * V n 18 + 412 * V n 19 + V n 20 + 6 * V n 21 + V n 22 + 164 * V n 23 + V n 24 + 17 * V n 25 + V n 26 + V n 27 + 6 * V n 28 + V n 29 + 80 * V n 30 + 1062 * V n 31 + V n 32 + 80 * V n 33 + V n 34 + 6 * V n 35 + V n 36 + 80 * V n 37 + 396 * V n 38 + V n 39 + 80 * V n 40 + 1704 * V n 41 := by
  rw [show n + 5 = (n + 1) + 4 from rfl, up4 (n + 1)]
  simp only [V]
  ring

theorem up6 (n : ℕ) : U (n + 6) = 4752 * V n 0 + 20635 * V n 1 + 60260 * V n 2 + 707 * V n 3 + 5 * V n 4 + 1589 * V n 5 + 288 * V n 6 + V n 7 + 369 * V n 8 + V n 9 + 157 * V n 10 + 2214 * V n 11 + 157 * V n 12 + 157 * V n 13 + 818 * V n 14 + 157 * V n 15 + 4986 * V n 16 + 28628 * V n 17 + 2 * V n 18 + 944 * V n 19 + V n 20 + 7 * V n 21 + V n 22 + 368 * V n 23 + V n 24 + 20 * V n 25 + V n 26 + V n 27 + 7 * V n 28 + V n 29 + 160 * V n 30 + 2482 * V n 31 + V n 32 + 160 * V n 33 + V n 34 + 7 * V n 35 + V n 36 + 160 * V n 37 + 912 * V n 38 + V n 39 + 160 * V n 40 + 5229 * V n 41 := by
  rw [show n + 6 = (n + 1) + 5 from rfl, up5 (n + 1)]
  simp only [V]
  ring

theorem up7 (n : ℕ) : U (n + 7) = 14967 * V n 0 + 65277 * V n 1 + 185716 * V n 2 + 1651 * V n 3 + 5 * V n 4 + 3640 * V n 5 + 656 * V n 6 + V n 7 + 817 * V n 8 + V n 9 + 317 * V n 10 + 5170 * V n 11 + 317 * V n 12 + 317 * V n 13 + 1888 * V n 14 + 317 * V n 15 + 15441 * V n 16 + 87555 * V n 17 + 2 * V n 18 + 2128 * V n 19 + V n 20 + 8 * V n 21 + V n 22 + 816 * V n 23 + V n 24 + 23 * V n 25 + V n 26 + V n 27 + 8 * V n 28 + V n 29 + 320 * V n 30 + 5682 * V n 31 + V n 32 + 320 * V n 33 + V n 34 + 8 * V n 35 + V n 36 + 320 * V n 37 + 2064 * V n 38 + V n 39 + 320 * V n 40 + 15924 * V n 41 := by
  rw [show n + 7 = (n + 1) + 6 from rfl, up6 (n + 1)]
  simp only [V]
  ring

theorem up8 (n : ℕ) : U (n + 8) = 46332 * V n 0 + 201651 * V n 1 + 562901 * V n 2 + 3779 * V n 3 + 5 * V n 4 + 8219 * V n 5 + 1472 * V n 6 + V n 7 + 1793 * V n 8 + V n 9 + 637 * V n 10 + 11806 * V n 11 + 637 * V n 12 + 637 * V n 13 + 4270 * V n 14 + 637 * V n 15 + 47286 * V n 16 + 264236 * V n 17 + 2 * V n 18 + 4736 * V n 19 + V n 20 + 9 * V n 21 + V n 22 + 1792 * V n 23 + V n 24 + 26 * V n 25 + V n 26 + V n 27 + 9 * V n 28 + V n 29 + 640 * V n 30 + 12802 * V n 31 + V n 32 + 640 * V n 33 + V n 34 + 9 * V n 35 + V n 36 + 640 * V n 37 + 4608 * V n 38 + V n 39 + 640 * V n 40 + 48249 * V n 41 := by
  rw [show n + 8 = (n + 1) + 7 from rfl, up7 (n + 1)]
  simp only [V]
  ring

theorem up9 (n : ℕ) : U (n + 9) = 141867 * V n 0 + 613521 * V n 1 + 1688273 * V n 2 + 8515 * V n 3 + 5 * V n 4 + 18334 * V n 5 + 3264 * V n 6 + V n 7 + 3905 * V n 8 + V n 9 + 1277 * V n 10 + 26522 * V n 11 + 1277 * V n 12 + 1277 * V n 13 + 9516 * V n 14 + 1277 * V n 15 + 143781 * V n 16 + 791127 * V n 17 + 2 * V n 18 + 10432 * V n 19 + V n 20 + 10 * V n 21 + V n 22 + 3904 * V n 23 + V n 24 + 29 * V n 25 + V n 26 + V n 27 + 10 * V n 28 + V n 29 + 1280 * V n 30 + 28482 * V n 31 + V n 32 + 1280 * V n 33 + V n 34 + 10 * V n 35 + V n 36 + 1280 * V n 37 + 10176 * V n 38 + V n 39 + 1280 * V n 40 + 145704 * V n 41 := by
  rw [show n + 9 = (n + 1) + 8 from rfl, up8 (n + 1)]
  simp only [V]
  ring

theorem up10 (n : ℕ) : U (n + 10) = 431352 * V n 0 + 1849127 * V n 1 + 5032714 * V n 2 + 18947 * V n 3 + 5 * V n 4 + 40481 * V n 5 + 7168 * V n 6 + V n 7 + 8449 * V n 8 + V n 9 + 2557 * V n 10 + 58838 * V n 11 + 2557 * V n 12 + 2557 * V n 13 + 20970 * V n 14 + 2557 * V n 15 + 435186 * V n 16 + 2358392 * V n 17 + 2 * V n 18 + 22784 * V n 19 + V n 20 + 11 * V n 21 + V n 22 + 8448 * V n 23 + V n 24 + 32 * V n 25 + V n 26 + V n 27 + 11 * V n 28 + V n 29 + 2560 * V n 30 + 62722 * V n 31 + V n 32 + 2560 * V n 33 + V n 34 + 11 * V n 35 + V n 36 + 2560 * V n 37 + 22272 * V n 38 + V n 39 + 2560 * V n 40 + 439029 * V n 41 := by
  rw [show n + 10 = (n + 1) + 9 from rfl, up9 (n + 1)]
  simp only [V]
  ring

theorem a_v1 : a 1 = 403 := by
  rw [a_eq]; decide +kernel

theorem a_v2 : a 2 = 1325 := by
  rw [a_eq]; decide +kernel

theorem a_v3 : a 3 = 4388 := by
  rw [a_eq]; decide +kernel

theorem a_v4 : a 4 = 14196 := by
  rw [a_eq]; decide +kernel

theorem a_v5 : a 5 = 44525 := by
  rw [a_eq]; decide +kernel

theorem a_v6 : a 6 = 136509 := by
  rw [a_eq]; decide +kernel

theorem a_v7 : a 7 = 412006 := by
  rw [a_eq]; decide +kernel

theorem a_v8 : a 8 = 1231112 := by
  rw [a_eq]; decide +kernel

theorem a_v9 : a 9 = 3657629 := by
  rw [a_eq]; decide +kernel

theorem a_rec : ∀ m : ℕ, 10 ≤ m → (a m : ℤ) = 12 * (a (m - 1) : ℤ) - 60 * (a (m - 2) : ℤ) + 162 * (a (m - 3) : ℤ) - 255 * (a (m - 4) : ℤ) + 234 * (a (m - 5) : ℤ) - 116 * (a (m - 6) : ℤ) + 24 * (a (m - 7) : ℤ) := by
  intro m hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 10 := ⟨m - 10, by omega⟩
  rw [show k + 10 - 1 = k + 9 by omega, show k + 10 - 2 = k + 8 by omega, show k + 10 - 3 = k + 7 by omega, show k + 10 - 4 = k + 6 by omega, show k + 10 - 5 = k + 5 by omega, show k + 10 - 6 = k + 4 by omega, show k + 10 - 7 = k + 3 by omega]
  rw [a_eq (k + 10), a_eq (k + 9), a_eq (k + 8), a_eq (k + 7), a_eq (k + 6), a_eq (k + 5), a_eq (k + 4), a_eq (k + 3)]
  rw [up10 k, up9 k, up8 k, up7 k, up6 k, up5 k, up4 k, up3 k]
  push_cast
  ring

theorem gf_eq : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
  have e1 : F' * ((1 - PowerSeries.X) ^ 3 * (1 - 2 * PowerSeries.X) ^ 3 * (1 - 3 * PowerSeries.X)) = F' - PowerSeries.C (12 : ℚ) * (PowerSeries.X ^ 1 * F') + PowerSeries.C (60 : ℚ) * (PowerSeries.X ^ 2 * F') - PowerSeries.C (162 : ℚ) * (PowerSeries.X ^ 3 * F') + PowerSeries.C (255 : ℚ) * (PowerSeries.X ^ 4 * F') - PowerSeries.C (234 : ℚ) * (PowerSeries.X ^ 5 * F') + PowerSeries.C (116 : ℚ) * (PowerSeries.X ^ 6 * F') - PowerSeries.C (24 : ℚ) * (PowerSeries.X ^ 7 * F') := by
    simp only [map_ofNat]
    ring
  have e2 : (PowerSeries.X * (403 - 3511 * PowerSeries.X + 12668 * PowerSeries.X ^ 2 - 24246 * PowerSeries.X ^ 3 + 25568 * PowerSeries.X ^ 4 - 13314 * PowerSeries.X ^ 5 + 1284 * PowerSeries.X ^ 6 + 1746 * PowerSeries.X ^ 7 - 594 * PowerSeries.X ^ 8) : PowerSeries ℚ) = PowerSeries.C (403 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (3511 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (12668 : ℚ) * PowerSeries.X ^ 3 - PowerSeries.C (24246 : ℚ) * PowerSeries.X ^ 4 + PowerSeries.C (25568 : ℚ) * PowerSeries.X ^ 5 - PowerSeries.C (13314 : ℚ) * PowerSeries.X ^ 6 + PowerSeries.C (1284 : ℚ) * PowerSeries.X ^ 7 + PowerSeries.C (1746 : ℚ) * PowerSeries.X ^ 8 - PowerSeries.C (594 : ℚ) * PowerSeries.X ^ 9 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [F', map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
  by_cases hn : n ≤ 9
  · interval_cases n <;> norm_num [a_v1, a_v2, a_v3, a_v4, a_v5, a_v6, a_v7, a_v8, a_v9]
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 10 := ⟨n - 10, by omega⟩
    have h := a_rec (j + 10) (by omega)
    rw [show j + 10 - 1 = j + 9 by omega, show j + 10 - 2 = j + 8 by omega, show j + 10 - 3 = j + 7 by omega, show j + 10 - 4 = j + 6 by omega, show j + 10 - 5 = j + 5 by omega, show j + 10 - 6 = j + 4 by omega, show j + 10 - 7 = j + 3 by omega] at h
    have q : (a (j + 10) : ℚ) = 12 * (a (j + 9) : ℚ) - 60 * (a (j + 8) : ℚ) + 162 * (a (j + 7) : ℚ) - 255 * (a (j + 6) : ℚ) + 234 * (a (j + 5) : ℚ) - 116 * (a (j + 4) : ℚ) + 24 * (a (j + 3) : ℚ) := by exact_mod_cast h
    simp
    linear_combination q

theorem closed0 : ∀ n : ℕ, 3 ≤ n → (a n : ℚ) = (-8 * (179 + 223 * (2 : ℚ) ^ n - 25 * (3 : ℚ) ^ (3 + n)) + (1104 - 845 * (2 : ℚ) ^ n) * (n : ℚ) + (32 + 375 * (2 : ℚ) ^ n) * (n : ℚ) ^ 2) / 32 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < 10
    · interval_cases n <;> norm_num [a_v3, a_v4, a_v5, a_v6, a_v7, a_v8, a_v9]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
      have h1 := ih (k + 9) (by omega) (by omega)
      have h2 := ih (k + 8) (by omega) (by omega)
      have h3 := ih (k + 7) (by omega) (by omega)
      have h4 := ih (k + 6) (by omega) (by omega)
      have h5 := ih (k + 5) (by omega) (by omega)
      have h6 := ih (k + 4) (by omega) (by omega)
      have h7 := ih (k + 3) (by omega) (by omega)
      have hr := a_rec (k + 10) (by omega)
      rw [show k + 10 - 1 = k + 9 by omega, show k + 10 - 2 = k + 8 by omega, show k + 10 - 3 = k + 7 by omega, show k + 10 - 4 = k + 6 by omega, show k + 10 - 5 = k + 5 by omega, show k + 10 - 6 = k + 4 by omega, show k + 10 - 7 = k + 3 by omega] at hr
      have q : (a (k + 10) : ℚ) = 12 * (a (k + 9) : ℚ) - 60 * (a (k + 8) : ℚ) + 162 * (a (k + 7) : ℚ) - 255 * (a (k + 6) : ℚ) + 234 * (a (k + 5) : ℚ) - 116 * (a (k + 4) : ℚ) + 24 * (a (k + 3) : ℚ) := by exact_mod_cast hr
      rw [q, h1, h2, h3, h4, h5, h6, h7]
      push_cast
      ring

end OMAA250893Helpers

open OMA.S_oeis_a250893 OMAA250893Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a250893.main :=
  ⟨a_rec, gf_eq, closed0⟩
