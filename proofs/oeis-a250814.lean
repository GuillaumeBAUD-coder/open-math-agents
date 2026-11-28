import OMAStatements.S_oeis_a250814
import Mathlib

-- Proof of the statement oeis-a250814 (statement by @schulzee; proof by @ivillar).
-- Idea: the block condition involves only consecutive columns, so the count is a walk count on columns (transfer
-- matrix). For each column s, the number α(n, s) of walks with n steps starting at s is tabulated for n < 5; the
-- tables satisfy the transfer relation (checked by kernel computation on verified adjacency lists) and a linear
-- recurrence of order 5. Sequences with the same recurrence and initial values agree, which gives the first terms,
-- the recurrence and the closed form.

namespace OMAA250814Helpers

open OMA.S_oeis_a250814

abbrev R := Fin 3 → Fin 3

instance (a b c d : Fin 3) : Decidable (Blk a b c d) := by unfold Blk; infer_instance


abbrev ok (_r : R) : Prop := True

abbrev compat (r s : R) : Prop := ∀ i : Fin 2, Blk (r i.castSucc) (s i.castSucc) (r i.succ) (s i.succ)


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

theorem sum_F (n : ℕ) : (∑ x : Fin (n + 1) → R, if Walk x then 1 else 0) = ∑ s : R, F n s := by
  unfold F
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  have hh : ∀ s : R, (if Walk y ∧ y 0 = s then 1 else 0) = if y 0 = s then (if Walk y then 1 else 0) else 0 := by
    intro s
    by_cases h : y 0 = s
    · rw [if_pos h]; exact if_congr ⟨fun hh => hh.1, fun hh => ⟨hh, h⟩⟩ rfl rfl
    · rw [if_neg h, if_neg (show ¬(Walk y ∧ y 0 = s) from fun hh => h hh.2)]
  rw [Finset.sum_congr rfl (fun s _ => hh s), Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

theorem forall_vecCons {k : ℕ} {β : Type} (P : (Fin (k + 1) → β) → Prop) :
    (∀ s, P s) ↔ ∀ a t, P (Matrix.vecCons a t) :=
  ⟨fun h a t => h _, fun h s => by rw [← Matrix.cons_head_tail s]; exact h _ _⟩

theorem forall_vecEmpty {β : Type} (P : (Fin 0 → β) → Prop) : (∀ s, P s) ↔ P ![] :=
  ⟨fun h => h _, fun h s => by rw [Subsingleton.elim s ![]]; exact h⟩

theorem sum_vecCons {k : ℕ} {β : Type} [Fintype β] (f : (Fin (k + 1) → β) → ℤ) :
    ∑ s, f s = ∑ a, ∑ t, f (Matrix.vecCons a t) := by
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => β)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem sum_vecEmpty {β : Type} [Fintype β] (f : (Fin 0 → β) → ℤ) : ∑ s, f s = f ![] := by
  rw [Fintype.sum_unique]
  congr 1

def look (l : List (List (List (ℤ)))) (s : R) : ℤ := (((l).getD (s 0).val []).getD (s 1).val []).getD (s 2).val 0

def tab0 : List (List (List (ℤ))) := [[[1, 1, 1], [1, 1, 1], [1, 1, 1]], [[1, 1, 1], [1, 1, 1], [1, 1, 1]], [[1, 1, 1], [1, 1, 1], [1, 1, 1]]]

def tab1 : List (List (List (ℤ))) := [[[10, 4, 1], [7, 4, 1], [3, 2, 1]], [[15, 7, 2], [7, 4, 1], [3, 2, 1]], [[18, 9, 3], [10, 6, 2], [3, 2, 1]]]

def tab2 : List (List (List (ℤ))) := [[[28, 7, 1], [18, 7, 1], [6, 3, 1]], [[60, 18, 3], [18, 7, 1], [6, 3, 1]], [[90, 30, 6], [36, 15, 3], [6, 3, 1]]]

def tab3 : List (List (List (ℤ))) := [[[55, 10, 1], [34, 10, 1], [10, 4, 1]], [[154, 34, 4], [34, 10, 1], [10, 4, 1]], [[280, 70, 10], [88, 28, 4], [10, 4, 1]]]

def tab4 : List (List (List (ℤ))) := [[[91, 13, 1], [55, 13, 1], [15, 5, 1]], [[315, 55, 5], [55, 13, 1], [15, 5, 1]], [[675, 135, 15], [175, 45, 5], [15, 5, 1]]]

def α : ℕ → R → ℤ
  | 0, s => look tab0 s
  | 1, s => look tab1 s
  | 2, s => look tab2 s
  | 3, s => look tab3 s
  | 4, s => look tab4 s
  | n + 5, s => 1 * α n s - 5 * α (n + 1) s + 10 * α (n + 2) s - 10 * α (n + 3) s + 5 * α (n + 4) s

theorem α_rec (n : ℕ) (s : R) : α (n + 5) s = 1 * α n s - 5 * α (n + 1) s + 10 * α (n + 2) s - 10 * α (n + 3) s + 5 * α (n + 4) s := by
  rw [α]

theorem uniqP {K : Type} [CommRing K] (u v : ℕ → K)
    (hu : ∀ n, u (n + 5) = 1 * u n - 5 * u (n + 1) + 10 * u (n + 2) - 10 * u (n + 3) + 5 * u (n + 4))
    (hv : ∀ n, v (n + 5) = 1 * v n - 5 * v (n + 1) + 10 * v (n + 2) - 10 * v (n + 3) + 5 * v (n + 4))
    (h0 : u 0 = v 0) (h1 : u 1 = v 1) (h2 : u 2 = v 2) (h3 : u 3 = v 3) (h4 : u 4 = v 4) : ∀ n, u n = v n := by
  have key : ∀ n, u n = v n ∧ u (n + 1) = v (n + 1) ∧ u (n + 2) = v (n + 2) ∧ u (n + 3) = v (n + 3) ∧ u (n + 4) = v (n + 4) := by
    intro n
    induction n with
    | zero => exact ⟨h0, h1, h2, h3, h4⟩
    | succ n ih =>
      obtain ⟨a0, a1, a2, a3, a4⟩ := ih
      refine ⟨a1, a2, a3, a4, ?_⟩
      rw [show n + 1 + 4 = n + 5 from rfl, hu, hv, a0, a1, a2, a3, a4]
  exact fun n => (key n).1

def adjT : List (List (List (List R))) := [[[[![0, 0, 0], ![0, 0, 1], ![0, 0, 2], ![0, 1, 1], ![0, 1, 2], ![0, 2, 2], ![1, 1, 1], ![1, 1, 2], ![1, 2, 2], ![2, 2, 2]], [![0, 0, 1], ![0, 0, 2], ![0, 1, 2], ![1, 1, 2]], [![0, 0, 2]]], [[![0, 1, 0], ![0, 1, 1], ![0, 1, 2], ![0, 2, 1], ![0, 2, 2], ![1, 2, 1], ![1, 2, 2]], [![0, 1, 1], ![0, 1, 2], ![0, 2, 2], ![1, 2, 2]], [![0, 1, 2]]], [[![0, 2, 0], ![0, 2, 1], ![0, 2, 2]], [![0, 2, 1], ![0, 2, 2]], [![0, 2, 2]]]], [[[![0, 0, 0], ![0, 0, 1], ![0, 0, 2], ![0, 1, 1], ![0, 1, 2], ![0, 2, 2], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 1, 1], ![1, 1, 2], ![1, 2, 2], ![2, 1, 1], ![2, 1, 2], ![2, 2, 2]], [![0, 0, 1], ![0, 0, 2], ![0, 1, 2], ![1, 0, 1], ![1, 0, 2], ![1, 1, 2], ![2, 1, 2]], [![0, 0, 2], ![1, 0, 2]]], [[![1, 1, 0], ![1, 1, 1], ![1, 1, 2], ![1, 2, 1], ![1, 2, 2], ![2, 2, 1], ![2, 2, 2]], [![1, 1, 1], ![1, 1, 2], ![1, 2, 2], ![2, 2, 2]], [![1, 1, 2]]], [[![1, 2, 0], ![1, 2, 1], ![1, 2, 2]], [![1, 2, 1], ![1, 2, 2]], [![1, 2, 2]]]], [[[![0, 0, 0], ![0, 0, 1], ![0, 0, 2], ![0, 1, 1], ![0, 1, 2], ![0, 2, 2], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 1, 1], ![1, 1, 2], ![1, 2, 2], ![2, 0, 0], ![2, 0, 1], ![2, 0, 2], ![2, 1, 1], ![2, 1, 2], ![2, 2, 2]], [![0, 0, 1], ![0, 0, 2], ![0, 1, 2], ![1, 0, 1], ![1, 0, 2], ![1, 1, 2], ![2, 0, 1], ![2, 0, 2], ![2, 1, 2]], [![0, 0, 2], ![1, 0, 2], ![2, 0, 2]]], [[![1, 1, 0], ![1, 1, 1], ![1, 1, 2], ![1, 2, 1], ![1, 2, 2], ![2, 1, 0], ![2, 1, 1], ![2, 1, 2], ![2, 2, 1], ![2, 2, 2]], [![1, 1, 1], ![1, 1, 2], ![1, 2, 2], ![2, 1, 1], ![2, 1, 2], ![2, 2, 2]], [![1, 1, 2], ![2, 1, 2]]], [[![2, 2, 0], ![2, 2, 1], ![2, 2, 2]], [![2, 2, 1], ![2, 2, 2]], [![2, 2, 2]]]]]

def adjL (s : R) : List R := (((adjT).getD (s 0).val []).getD (s 1).val []).getD (s 2).val []

def AP (s : R) : Prop := ∀ t : R, (ok s ∧ compat s t) ↔ t ∈ adjL s

theorem ADJ : ∀ s : R, AP s := by
  simp only [AP, forall_vecCons, forall_vecEmpty]
  decide +kernel

theorem ND : ∀ s : R, (adjL s).Nodup := by
  simp only [forall_vecCons, forall_vecEmpty]
  decide +kernel

theorem sum_adj (s : R) (f : R → ℤ) :
    (∑ t : R, if ok s ∧ compat s t then f t else 0) = ((adjL s).map f).sum := by
  have h1 : ∀ t, (if ok s ∧ compat s t then f t else 0) = if t ∈ adjL s then f t else 0 :=
    fun t => if_congr (ADJ s t) rfl rfl
  rw [Finset.sum_congr rfl (fun t _ => h1 t), ← Finset.sum_filter, ← List.sum_toFinset f (ND s)]
  congr 1
  ext t
  simp

def TP (j : ℕ) (s : R) : Prop := ((adjL s).map (α j)).sum = α (j + 1) s

theorem TL0 : ∀ s : R, TP 0 s := by
  simp only [TP, forall_vecCons, forall_vecEmpty]
  decide +kernel

theorem T0 (s : R) : (∑ t : R, if ok s ∧ compat s t then α 0 t else 0) = α 1 s := by
  rw [sum_adj]
  exact TL0 s

theorem TL1 : ∀ s : R, TP 1 s := by
  simp only [TP, forall_vecCons, forall_vecEmpty]
  decide +kernel

theorem T1 (s : R) : (∑ t : R, if ok s ∧ compat s t then α 1 t else 0) = α 2 s := by
  rw [sum_adj]
  exact TL1 s

theorem TL2 : ∀ s : R, TP 2 s := by
  simp only [TP, forall_vecCons, forall_vecEmpty]
  decide +kernel

theorem T2 (s : R) : (∑ t : R, if ok s ∧ compat s t then α 2 t else 0) = α 3 s := by
  rw [sum_adj]
  exact TL2 s

theorem TL3 : ∀ s : R, TP 3 s := by
  simp only [TP, forall_vecCons, forall_vecEmpty]
  decide +kernel

theorem T3 (s : R) : (∑ t : R, if ok s ∧ compat s t then α 3 t else 0) = α 4 s := by
  rw [sum_adj]
  exact TL3 s

theorem TL4 : ∀ s : R, TP 4 s := by
  simp only [TP, forall_vecCons, forall_vecEmpty]
  decide +kernel

theorem T4 (s : R) : (∑ t : R, if ok s ∧ compat s t then α 4 t else 0) = α 5 s := by
  rw [sum_adj]
  exact TL4 s

theorem T (s : R) : ∀ n, (∑ t : R, if ok s ∧ compat s t then α n t else 0) = α (n + 1) s := by
  apply uniqP (fun n => ∑ t : R, if ok s ∧ compat s t then α n t else 0) (fun n => α (n + 1) s)
  · intro n
    simp only [α_rec, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> ring
  · intro n
    exact α_rec (n + 1) s
  · exact T0 s
  · exact T1 s
  · exact T2 s
  · exact T3 s
  · exact T4 s

theorem B0 : ∀ s : R, α 0 s = if ok s then 1 else 0 := by
  simp only [forall_vecCons, forall_vecEmpty]
  decide +kernel

theorem F_eq (n : ℕ) : ∀ s : R, (F n s : ℤ) = α n s := by
  induction n with
  | zero =>
    intro s
    rw [F_zero, B0]
    split_ifs <;> simp
  | succ n ih =>
    intro s
    rw [F_succ, ← T s n]
    push_cast
    apply Finset.sum_congr rfl
    intro t _
    split_ifs
    · exact ih t
    · rfl

def A : ℕ → ℤ
  | 0 => 27
  | 1 => 129
  | 2 => 379
  | 3 => 873
  | 4 => 1731
  | n + 5 => 1 * A n - 5 * A (n + 1) + 10 * A (n + 2) - 10 * A (n + 3) + 5 * A (n + 4)

theorem A_rec (n : ℕ) : A (n + 5) = 1 * A n - 5 * A (n + 1) + 10 * A (n + 2) - 10 * A (n + 3) + 5 * A (n + 4) := by
  rw [A]

theorem U0 : (∑ s : R, if True then α 0 s else 0) = A 0 := by
  simp only [sum_vecCons, sum_vecEmpty]
  decide +kernel

theorem U1 : (∑ s : R, if True then α 1 s else 0) = A 1 := by
  simp only [sum_vecCons, sum_vecEmpty]
  decide +kernel

theorem U2 : (∑ s : R, if True then α 2 s else 0) = A 2 := by
  simp only [sum_vecCons, sum_vecEmpty]
  decide +kernel

theorem U3 : (∑ s : R, if True then α 3 s else 0) = A 3 := by
  simp only [sum_vecCons, sum_vecEmpty]
  decide +kernel

theorem U4 : (∑ s : R, if True then α 4 s else 0) = A 4 := by
  simp only [sum_vecCons, sum_vecEmpty]
  decide +kernel

theorem U : ∀ n, (∑ s : R, if True then α n s else 0) = A n := by
  apply uniqP (fun n => ∑ s : R, if True then α n s else 0) A
  · intro n
    simp only [α_rec, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> ring
  · exact A_rec
  · exact U0
  · exact U1
  · exact U2
  · exact U3
  · exact U4

theorem N_eq (n : ℕ) : (a n : ℤ) = A n := by
  unfold a
  rw [Nat.card_congr ((Equiv.piComm (fun (_ : Fin 3) (_ : Fin (n + 1)) => Fin 3)).subtypeEquiv
      (p := fun x : Fin 3 → Fin (n + 1) → Fin 3 => Good n x)
      (q := fun y : Fin (n + 1) → R => Walk y)
      (fun x => ⟨fun h => ⟨fun _ => trivial, fun j i => h i j⟩, fun h i j => h.2 j i⟩)), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_filter, sum_F, ← U n]
  push_cast
  apply Finset.sum_congr rfl
  intro s _
  exact F_eq n s

def C : ℕ → ℤ
  | 0 => 129
  | 1 => 379
  | 2 => 873
  | 3 => 1731
  | 4 => 3097
  | n + 5 => 1 * C n - 5 * C (n + 1) + 10 * C (n + 2) - 10 * C (n + 3) + 5 * C (n + 4)

theorem C_rec (n : ℕ) : C (n + 5) = 1 * C n - 5 * C (n + 1) + 10 * C (n + 2) - 10 * C (n + 3) + 5 * C (n + 4) := by
  rw [C]

theorem C_P (n : ℕ) : C (n + 5) = 1 * C n - 5 * C (n + 1) + 10 * C (n + 2) - 10 * C (n + 3) + 5 * C (n + 4) := by
  have h0 : C (n + 5) = 1 * C n - 5 * C (n + 1) + 10 * C (n + 2) - 10 * C (n + 3) + 5 * C (n + 4) := C_rec (n)
  linear_combination (1) * h0

theorem A_C : ∀ n, A (n + 1) = 1 * C n := by
  apply uniqP (fun n => A (n + 1)) (fun n => 1 * C n)
  · intro n
    exact A_rec (n + 1)
  · intro n
    rw [C_P]
    ring
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem aC (n : ℕ) : (a (n + 1) : ℤ) = C n := by
  rw [N_eq, A_C]
  ring

theorem uniqp {K : Type} [CommRing K] (u v : ℕ → K)
    (hu : ∀ n, u (n + 5) = 1 * u n - 5 * u (n + 1) + 10 * u (n + 2) - 10 * u (n + 3) + 5 * u (n + 4))
    (hv : ∀ n, v (n + 5) = 1 * v n - 5 * v (n + 1) + 10 * v (n + 2) - 10 * v (n + 3) + 5 * v (n + 4))
    (h0 : u 0 = v 0) (h1 : u 1 = v 1) (h2 : u 2 = v 2) (h3 : u 3 = v 3) (h4 : u 4 = v 4) : ∀ n, u n = v n := by
  have key : ∀ n, u n = v n ∧ u (n + 1) = v (n + 1) ∧ u (n + 2) = v (n + 2) ∧ u (n + 3) = v (n + 3) ∧ u (n + 4) = v (n + 4) := by
    intro n
    induction n with
    | zero => exact ⟨h0, h1, h2, h3, h4⟩
    | succ n ih =>
      obtain ⟨a0, a1, a2, a3, a4⟩ := ih
      refine ⟨a1, a2, a3, a4, ?_⟩
      rw [show n + 1 + 4 = n + 5 from rfl, hu, hv, a0, a1, a2, a3, a4]
  exact fun n => (key n).1

theorem a_v1 : a 1 = 129 := by
  have h := N_eq 1
  rw [show A 1 = 129 from by decide +kernel] at h
  exact_mod_cast h

theorem a_v2 : a 2 = 379 := by
  have h := N_eq 2
  rw [show A 2 = 379 from by decide +kernel] at h
  exact_mod_cast h

theorem a_v3 : a 3 = 873 := by
  have h := N_eq 3
  rw [show A 3 = 873 from by decide +kernel] at h
  exact_mod_cast h

theorem a_v4 : a 4 = 1731 := by
  have h := N_eq 4
  rw [show A 4 = 1731 from by decide +kernel] at h
  exact_mod_cast h

theorem a_v5 : a 5 = 3097 := by
  have h := N_eq 5
  rw [show A 5 = 3097 from by decide +kernel] at h
  exact_mod_cast h

theorem closedC : ∀ m : ℕ, 1 * C m = (fun n : ℕ => ((n : ℤ) ^ 4 + 10 * n ^ 3 + 37 * n ^ 2 + 54 * n + 27 : ℤ)) (m + 1) := by
  apply uniqp (fun m : ℕ => 1 * C m) (fun m : ℕ => (fun n : ℕ => ((n : ℤ) ^ 4 + 10 * n ^ 3 + 37 * n ^ 2 + 54 * n + 27 : ℤ)) (m + 1))
  · intro m
    show 1 * C (m + 5) = _
    rw [C_rec]
    ring
  · intro m
    show (fun n : ℕ => ((n : ℤ) ^ 4 + 10 * n ^ 3 + 37 * n ^ 2 + 54 * n + 27 : ℤ)) (m + 5 + 1) = _
    simp only []
    push_cast
    ring
  · show 1 * C 0 = (fun n : ℕ => ((n : ℤ) ^ 4 + 10 * n ^ 3 + 37 * n ^ 2 + 54 * n + 27 : ℤ)) (0 + 1)
    rw [show C 0 = 129 from by decide +kernel]
    norm_num
  · show 1 * C 1 = (fun n : ℕ => ((n : ℤ) ^ 4 + 10 * n ^ 3 + 37 * n ^ 2 + 54 * n + 27 : ℤ)) (1 + 1)
    rw [show C 1 = 379 from by decide +kernel]
    norm_num
  · show 1 * C 2 = (fun n : ℕ => ((n : ℤ) ^ 4 + 10 * n ^ 3 + 37 * n ^ 2 + 54 * n + 27 : ℤ)) (2 + 1)
    rw [show C 2 = 873 from by decide +kernel]
    norm_num
  · show 1 * C 3 = (fun n : ℕ => ((n : ℤ) ^ 4 + 10 * n ^ 3 + 37 * n ^ 2 + 54 * n + 27 : ℤ)) (3 + 1)
    rw [show C 3 = 1731 from by decide +kernel]
    norm_num
  · show 1 * C 4 = (fun n : ℕ => ((n : ℤ) ^ 4 + 10 * n ^ 3 + 37 * n ^ 2 + 54 * n + 27 : ℤ)) (4 + 1)
    rw [show C 4 = 3097 from by decide +kernel]
    norm_num

end OMAA250814Helpers

open OMA.S_oeis_a250814 OMAA250814Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a250814.main := by
  refine ⟨a_v1, a_v2, a_v3, a_v4, a_v5, fun n hn => ?_, fun n hn => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have e0 : (a (k + 1) : ℤ) = C k := aC k
    have e1 : (a (k + 1 + 1) : ℤ) = C (k + 1) := aC (k + 1)
    have e2 : (a (k + 1 + 2) : ℤ) = C (k + 2) := aC (k + 2)
    have e3 : (a (k + 1 + 3) : ℤ) = C (k + 3) := aC (k + 3)
    have e4 : (a (k + 1 + 4) : ℤ) = C (k + 4) := aC (k + 4)
    have e5 : (a (k + 1 + 5) : ℤ) = C (k + 5) := aC (k + 5)
    linear_combination e5 - (5) * e4 - (-10) * e3 - (10) * e2 - (-5) * e1 - (1) * e0 + C_rec k
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [aC k]
    exact closedC k
