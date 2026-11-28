import OMAStatements.S_oeis_a250780
import Mathlib

-- Proof of the conjectures in OEIS A250780 (statement by @ivillar).
-- Idea: the conditions only involve 2 X 2 blocks, so the count is a walk count on the rows of the
-- array (transfer matrix). The 64 states are lumped into 22 classes with constant numbers of successors in
-- each class (checked by decide), which gives a linear system for the class counts W n c. The recurrence
-- of order 8 follows from explicit row vectors orthogonal to all W n (an invariant subspace of the
-- transposed class matrix), and the generating function and closed forms follow from the recurrence
-- and the first values.

namespace OMAA250780Helpers

open OMA.S_oeis_a250780

instance (p q r s : ℕ) : Decidable (Blk p q r s) := by
  unfold Blk; infer_instance

/-- The states of the transfer matrix: the rows of the array, encoded as numbers in base 2
(digit j of the code is entry j). -/
abbrev R := Fin (2 ^ 6)

/-- Digit j of the code a in base 2. -/
def dig (a j : ℕ) : ℕ := a / 2 ^ j % 2

/-- Consecutive rows u, v: all the 2 X 2 blocks they form satisfy the condition. -/
abbrev BlockOK (u v : Fin 6 → Fin 2) : Prop :=
  ∀ j : Fin 5, Blk (u j.castSucc) (u j.succ) (v j.castSucc) (v j.succ)

/-- The truth table of `Blk` on entries below 2: bit ((p * 2 + q) * 2 + r) * 2 + s. -/
def blkTab : ℕ := 36459

/-- `Blk` read off the truth table. -/
def blkB (p q r s : ℕ) : Bool := Nat.testBit blkTab (((p * 2 + q) * 2 + r) * 2 + s)

theorem blk_iff : ∀ p q r s : Fin 2, blkB p q r s = true ↔ Blk p q r s := by decide +kernel

/-- The same condition on codes. -/
def compatB (r s : ℕ) : Bool :=
  blkB (dig r 0) (dig r 1) (dig s 0) (dig s 1) &&
    (blkB (dig r 1) (dig r 2) (dig s 1) (dig s 2) &&
    (blkB (dig r 2) (dig r 3) (dig s 2) (dig s 3) &&
    (blkB (dig r 3) (dig r 4) (dig s 3) (dig s 4) &&
    (blkB (dig r 4) (dig r 5) (dig s 4) (dig s 5)))))

abbrev compatN (r s : ℕ) : Prop := compatB r s = true

/-- States are unconstrained. -/
abbrev ok (_r : R) : Prop := True

/-- Every state may start a walk. -/
abbrev init (_r : R) : Prop := True

/-- Compatibility of consecutive states. -/
abbrev compat (r s : R) : Prop := compatN r.val s.val

theorem dig_enc (u : Fin 6 → Fin 2) (i : Fin 6) : dig ((finFunctionFinEquiv (m := 2) (n := 6)) u).val i.val = (u i).val :=
  congrArg Fin.val (congrFun (Equiv.symm_apply_apply (finFunctionFinEquiv (m := 2) (n := 6)) u) i)

theorem dig_e0 (u : Fin 6 → Fin 2) : dig ((finFunctionFinEquiv (m := 2) (n := 6)) u).val 0 = (u 0).val := dig_enc u 0

theorem dig_e1 (u : Fin 6 → Fin 2) : dig ((finFunctionFinEquiv (m := 2) (n := 6)) u).val 1 = (u 1).val := dig_enc u 1

theorem dig_e2 (u : Fin 6 → Fin 2) : dig ((finFunctionFinEquiv (m := 2) (n := 6)) u).val 2 = (u 2).val := dig_enc u 2

theorem dig_e3 (u : Fin 6 → Fin 2) : dig ((finFunctionFinEquiv (m := 2) (n := 6)) u).val 3 = (u 3).val := dig_enc u 3

theorem dig_e4 (u : Fin 6 → Fin 2) : dig ((finFunctionFinEquiv (m := 2) (n := 6)) u).val 4 = (u 4).val := dig_enc u 4

theorem dig_e5 (u : Fin 6 → Fin 2) : dig ((finFunctionFinEquiv (m := 2) (n := 6)) u).val 5 = (u 5).val := dig_enc u 5


theorem blockOK_iff (u v : Fin 6 → Fin 2) :
    BlockOK u v ↔
      (Blk (u 0) (u 1) (v 0) (v 1) ∧
      (Blk (u 1) (u 2) (v 1) (v 2) ∧
      (Blk (u 2) (u 3) (v 2) (v 3) ∧
      (Blk (u 3) (u 4) (v 3) (v 4) ∧
      (Blk (u 4) (u 5) (v 4) (v 5)))))) := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ j
    fin_cases j <;>
      first
        | exact h0
        | exact h1
        | exact h2
        | exact h3
        | exact h4

theorem compat_enc (u v : Fin 6 → Fin 2) :
    compat ((finFunctionFinEquiv (m := 2) (n := 6)) u) ((finFunctionFinEquiv (m := 2) (n := 6)) v) ↔ BlockOK u v := by
  rw [blockOK_iff]
  simp only [compat, compatN, compatB, Bool.and_eq_true, dig_e0, dig_e1, dig_e2, dig_e3, dig_e4, dig_e5, blk_iff]

/-- Arrays as sequences of encoded rows. -/
def enc (n : ℕ) : (Fin (n + 1) → Fin 6 → Fin 2) ≃ (Fin (n + 1) → R) where
  toFun := fun x i => (finFunctionFinEquiv (m := 2) (n := 6)) (x i)
  invFun := fun y i => (finFunctionFinEquiv (m := 2) (n := 6)).symm (y i)
  left_inv := fun x => by funext i; exact Equiv.symm_apply_apply _ _
  right_inv := fun y => by funext i; exact Equiv.apply_symm_apply _ _

abbrev Walk {n : ℕ} (x : Fin (n + 1) → R) : Prop :=
  (∀ i, ok (x i)) ∧ ∀ i : Fin n, compat (x i.castSucc) (x i.succ)

theorem walk_cons (n : ℕ) (r : R) (y : Fin (n + 1) → R) :
    Walk (Fin.cons r y : Fin (n + 2) → R) ↔ ok r ∧ compat r (y 0) ∧ Walk y := by
  simp only [Walk, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero,
    Fin.succ_zero_eq_one, ← Fin.succ_castSucc]
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

/-- The classes of the states, one byte per state. -/
def clsTab : ℕ := 157738916822854083524400294096539366206875739260441100848973122442602279199926271270924344120058538043334772679004814057244754589530832804145431524933632

/-- The class of a code (states of one class have the same numbers of successors in each class). -/
def clsF (a : ℕ) : Fin 22 := ⟨(clsTab >>> (8 * a)) % 256 % 22, Nat.mod_lt _ (by norm_num)⟩

/-- The class of a state. -/
def cls (t : R) : Fin 22 := clsF t.val

/-- The codes of the states of each class. -/
def mem : Fin 22 → List ℕ :=
  ![[0, 1], [32, 33], [16, 17], [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], [8, 9], [40, 41], [24, 25, 26, 27, 28, 29, 30, 31], [4, 5], [36, 37], [20, 21], [12, 13, 14, 15, 22, 23], [44, 45, 46, 47], [2], [34], [18], [10], [42], [6, 7, 11], [38, 39, 43], [3], [35], [19]]

/-- Mat c d: the number of successors of class d of a state of class c. -/
def Mat : Fin 22 → Fin 22 → ℤ :=
  ![![1, 1, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 4, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 4, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 3, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1]]

/-- W n c: the number of walks with n steps starting at a given state of class c. -/
def W : ℕ → Fin 22 → ℤ
  | 0 => fun _ => 1
  | n + 1 => fun c => ∑ d, Mat c d * W n d

theorem hmem_0 : ∀ c : Fin 22, 0 ≤ c.val → c.val < 15 →
    mem c = (List.range (2 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem_1 : ∀ c : Fin 22, 15 ≤ c.val → c.val < 22 →
    mem c = (List.range (2 ^ 6)).filter (fun a => clsF a = c) := by decide +kernel

theorem hmem : ∀ c : Fin 22, mem c = (List.range (2 ^ 6)).filter (fun a => clsF a = c) := fun c =>
  if h1 : c.val < 15 then
    hmem_0 c (Nat.zero_le _) h1
  else
    hmem_1 c (Nat.le_of_not_lt h1) c.isLt

theorem cntN_0 : ∀ s : R, 0 ≤ s.val → s.val < 18 → ∀ c : Fin 22,
    (((mem c).filter (fun a => compatB s.val a)).length : ℤ) = Mat (cls s) c := by
  decide +kernel

theorem cntN_1 : ∀ s : R, 18 ≤ s.val → s.val < 36 → ∀ c : Fin 22,
    (((mem c).filter (fun a => compatB s.val a)).length : ℤ) = Mat (cls s) c := by
  decide +kernel

theorem cntN_2 : ∀ s : R, 36 ≤ s.val → s.val < 54 → ∀ c : Fin 22,
    (((mem c).filter (fun a => compatB s.val a)).length : ℤ) = Mat (cls s) c := by
  decide +kernel

theorem cntN_3 : ∀ s : R, 54 ≤ s.val → s.val < 2 ^ 6 → ∀ c : Fin 22,
    (((mem c).filter (fun a => compatB s.val a)).length : ℤ) = Mat (cls s) c := by
  decide +kernel

theorem cntN : ∀ s : R, ∀ c : Fin 22,
    (((mem c).filter (fun a => compatB s.val a)).length : ℤ) = Mat (cls s) c := fun s c =>
  if h2 : s.val < 36 then
    if h1 : s.val < 18 then
      cntN_0 s (Nat.zero_le _) h1 c
    else
      cntN_1 s (Nat.le_of_not_lt h1) h2 c
  else
    if h3 : s.val < 54 then
      cntN_2 s (Nat.le_of_not_lt h2) h3 c
    else
      cntN_3 s (Nat.le_of_not_lt h3) s.isLt c

/-- U i: the row vector (class sizes) * Mat^i. -/
def U : Fin 9 → Fin 22 → ℤ :=
  ![![2, 2, 2, 16, 2, 2, 8, 2, 2, 2, 6, 4, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1],
    ![2, 4, 4, 78, 2, 6, 37, 2, 4, 7, 14, 21, 1, 2, 2, 1, 5, 3, 9, 1, 2, 2],
    ![2, 6, 8, 186, 2, 12, 116, 2, 6, 22, 40, 60, 1, 3, 4, 1, 15, 3, 21, 1, 3, 4],
    ![2, 8, 14, 422, 2, 22, 281, 2, 8, 55, 100, 158, 1, 4, 7, 1, 42, 3, 50, 1, 4, 7],
    ![2, 10, 22, 928, 2, 38, 629, 2, 10, 127, 236, 376, 1, 5, 11, 1, 105, 3, 115, 1, 5, 11],
    ![2, 12, 32, 2006, 2, 62, 1358, 2, 12, 280, 532, 838, 1, 6, 16, 1, 244, 3, 256, 1, 6, 16],
    ![2, 14, 44, 4282, 2, 96, 2872, 2, 14, 598, 1156, 1794, 1, 7, 22, 1, 541, 3, 555, 1, 7, 22],
    ![2, 16, 58, 9038, 2, 142, 5991, 2, 16, 1249, 2444, 3746, 1, 8, 29, 1, 1162, 3, 1178, 1, 8, 29],
    ![2, 18, 74, 18880, 2, 202, 12371, 2, 18, 2569, 5068, 7700, 1, 9, 37, 1, 2441, 3, 2459, 1, 9, 37]]

theorem totN : ∀ c : Fin 22, ((mem c).length : ℤ) = U 0 c := by decide +kernel

theorem card_cls (c : Fin 22) (P : ℕ → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun t : R => cls t = c ∧ P t.val)).card = ((mem c).filter (fun a => P a)).length := by
  have key : (Finset.univ.filter (fun t : R => cls t = c ∧ P t.val)).map Fin.valEmbedding =
      ((mem c).filter (fun a => P a)).toFinset := by
    ext a
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    rw [hmem c]
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
      exact ⟨⟨t.isLt, h1⟩, h2⟩
    · rintro ⟨⟨ha, hc⟩, h2⟩
      exact ⟨⟨a, ha⟩, ⟨hc, h2⟩, rfl⟩
  have hnd : (mem c).Nodup := by
    rw [hmem c]
    exact List.Nodup.filter _ (by first | exact List.nodup_range | exact List.nodup_range _)
  rw [← Finset.card_map Fin.valEmbedding, key, List.toFinset_card_of_nodup (hnd.filter _)]

theorem cnt : ∀ s : R, ∀ c : Fin 22,
    ((Finset.univ.filter (fun t : R => cls t = c ∧ (ok s ∧ compat s t))).card : ℤ) = Mat (cls s) c := by
  intro s c
  have h2 : Finset.univ.filter (fun t : R => cls t = c ∧ (ok s ∧ compat s t)) =
      Finset.univ.filter (fun t : R => cls t = c ∧ compatN s.val t.val) :=
    Finset.filter_congr (fun t _ => ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, trivial, h.2⟩⟩)
  rw [h2, card_cls c (fun a => compatN s.val a)]
  have h3 : (mem c).filter (fun a => decide (compatN s.val a)) = (mem c).filter (fun a => compatB s.val a) :=
    List.filter_congr (fun a _ => by simp only [compatN, Bool.decide_eq_true])
  first
    | (rw [h3]; exact cntN s c)
    | (simpa [compatN] using cntN s c)

theorem tot : ∀ c : Fin 22,
    ((Finset.univ.filter (fun t : R => cls t = c ∧ init t)).card : ℤ) = U 0 c := by
  intro c
  have h2 : Finset.univ.filter (fun t : R => cls t = c ∧ init t) =
      Finset.univ.filter (fun t : R => cls t = c ∧ (fun _ : ℕ => True) t.val) :=
    Finset.filter_congr (fun t _ => Iff.rfl)
  rw [h2, card_cls c (fun _ : ℕ => True)]
  simpa using totN c

theorem hU : ∀ (i : Fin 8) (d : Fin 22), ∑ c, U i.castSucc c * Mat c d = U i.succ d := by
  decide +kernel

/-- Coefficients of the recurrence. -/
def L : Fin 9 → ℤ := ![0, -2, 13, -36, 55, -50, 27, -8, 1]

/-- Row vectors orthogonal to all the vectors W n. -/
def Rm : Fin 1 → Fin 22 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def Am : Fin 1 → Fin 1 → ℤ :=
  ![![0]]

theorem hRA : ∀ (l : Fin 1) (d : Fin 22), ∑ c, Rm l c * Mat c d = ∑ l', Am l l' * Rm l' d := by
  decide +kernel

theorem hR0 : ∀ l : Fin 1, ∑ c, Rm l c = 0 := by decide +kernel

theorem hL : ∀ c : Fin 22, ∑ i, L i * U i c = Rm 0 c := by decide +kernel

/-- The first values. -/
def vals : Fin 9 → ℤ := ![64, 209, 518, 1194, 2640, 5688, 12036, 25126, 51904]

theorem hV : ∀ i : Fin 9, ∑ c, U i c = vals i := by decide +kernel

theorem sum_cls (g : Fin 22 → ℤ) (P : R → Prop) [DecidablePred P] :
    (∑ t : R, if P t then g (cls t) else 0) =
      ∑ c : Fin 22, ((Finset.univ.filter (fun t => cls t = c ∧ P t)).card : ℤ) * g c := by
  rw [← Finset.sum_fiberwise Finset.univ cls]
  apply Finset.sum_congr rfl
  intro c _
  have h : ∑ t ∈ Finset.univ.filter (fun t => cls t = c), (if P t then g (cls t) else 0) =
      ∑ t ∈ Finset.univ.filter (fun t => cls t = c), (if P t then g c else 0) :=
    Finset.sum_congr rfl (fun t ht => by rw [(Finset.mem_filter.mp ht).2])
  rw [h, ← Finset.sum_filter, Finset.filter_filter, Finset.sum_const, nsmul_eq_mul]

theorem F_eq (n : ℕ) : ∀ s : R, (F n s : ℤ) = W n (cls s) := by
  induction n with
  | zero =>
    intro s
    rw [F_zero]
    simp [W, ok]
  | succ n ih =>
    intro s
    rw [F_succ]
    push_cast
    simp only [ih]
    rw [sum_cls (W n) (fun t => ok s ∧ compat s t)]
    simp only [cnt]
    rfl

theorem swap_sum (f : Fin 22 → ℤ) (n : ℕ) :
    ∑ c, f c * W (n + 1) c = ∑ d, (∑ c, f c * Mat c d) * W n d := by
  have h : ∀ c, f c * W (n + 1) c = ∑ d, f c * Mat c d * W n d := by
    intro c
    show f c * ∑ d, Mat c d * W n d = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  simp only [h, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem W_inv : ∀ (n : ℕ) (l : Fin 1), ∑ c, Rm l c * W n c = 0 := by
  intro n
  induction n with
  | zero =>
    intro l
    simpa [W] using hR0 l
  | succ n ih =>
    intro l
    rw [swap_sum]
    simp only [hRA, Finset.sum_mul]
    rw [Finset.sum_comm]
    have h : ∀ l', ∑ d, Am l l' * Rm l' d * W n d = Am l l' * ∑ d, Rm l' d * W n d := by
      intro l'
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      ring
    simp only [h, ih, mul_zero, Finset.sum_const_zero]

theorem W_shift : ∀ (i : Fin 9) (n : ℕ), ∑ c, U 0 c * W (n + i) c = ∑ c, U i c * W n c := by
  intro i
  induction i using Fin.induction with
  | zero => intro n; simp
  | succ i ih =>
    intro n
    have h1 : n + ((i.succ : Fin 9) : ℕ) = (n + 1) + ((i.castSucc : Fin 9) : ℕ) := by
      simp only [Fin.val_succ, Fin.val_castSucc]; omega
    rw [h1, ih (n + 1), swap_sum]
    simp only [hU]

theorem a_eq (n : ℕ) : (a n : ℤ) = ∑ c, U 0 c * W n c := by
  unfold a
  rw [Nat.card_congr (Equiv.subtypeEquiv (enc n)
      (p := fun x : Fin (n + 1) → Fin 6 → Fin 2 => ∀ i : Fin n, ∀ j : Fin 5,
        Blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ))
      (q := fun y : Fin (n + 1) → R => Walk y)
      (fun x => ⟨fun h => ⟨fun _ => trivial, fun i => (compat_enc _ _).mpr (h i)⟩,
        fun h i => (compat_enc _ _).mp (h.2 i)⟩)), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_filter]
  have h1 : (∑ x : Fin (n + 1) → R, if Walk x then 1 else 0) = ∑ s : R, if init s then F n s else 0 := by
    unfold F
    simp only [init, if_true]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    have hh : ∀ s : R, (if Walk y ∧ y 0 = s then 1 else 0) = if y 0 = s then (if Walk y then 1 else 0) else 0 := by
      intro s
      by_cases h : y 0 = s
      · rw [if_pos h]; exact if_congr ⟨fun hh => hh.1, fun hh => ⟨hh, h⟩⟩ rfl rfl
      · rw [if_neg h, if_neg (show ¬(Walk y ∧ y 0 = s) from fun hh => h hh.2)]
    rw [Finset.sum_congr rfl (fun s _ => hh s), Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  rw [h1]
  push_cast
  simp only [F_eq]
  rw [sum_cls (W n) init]
  simp only [tot]

theorem a_shift (i : Fin 9) (n : ℕ) : (a (n + i) : ℤ) = ∑ c, U i c * W n c := by
  rw [a_eq, W_shift]

theorem a_rec (n : ℕ) : ∑ i : Fin 9, L i * (a (n + i) : ℤ) = 0 := by
  simp only [a_shift, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ c, ∑ i, L i * (U i c * W n c) = Rm 0 c * W n c := by
    intro c
    rw [← hL c, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [h]
  exact W_inv n 0

theorem a_val (i : Fin 9) : (a i : ℤ) = vals i := by
  have h := a_shift i 0
  rw [Nat.zero_add] at h
  rw [h, ← hV i]
  apply Finset.sum_congr rfl
  intro c _
  simp [W]

theorem rec0 (n : ℕ) : (a (n + 8) : ℤ) = 8 * (a (n + 7) : ℤ) - 27 * (a (n + 6) : ℤ) + 50 * (a (n + 5) : ℤ) - 55 * (a (n + 4) : ℤ) + 36 * (a (n + 3) : ℤ) - 13 * (a (n + 2) : ℤ) + 2 * (a (n + 1) : ℤ) := by
  have h := a_rec n
  simp [Fin.sum_univ_succ, L] at h
  linarith

theorem v0 : a 0 = 64 := by
  have h := a_val 0
  simp [vals] at h
  exact_mod_cast h

theorem v1 : a 1 = 209 := by
  have h := a_val 1
  simp [vals] at h
  exact_mod_cast h

theorem v2 : a 2 = 518 := by
  have h := a_val 2
  simp [vals] at h
  exact_mod_cast h

theorem v3 : a 3 = 1194 := by
  have h := a_val 3
  simp [vals] at h
  exact_mod_cast h

theorem v4 : a 4 = 2640 := by
  have h := a_val 4
  simp [vals] at h
  exact_mod_cast h

theorem v5 : a 5 = 5688 := by
  have h := a_val 5
  simp [vals] at h
  exact_mod_cast h

theorem v6 : a 6 = 12036 := by
  have h := a_val 6
  simp [vals] at h
  exact_mod_cast h

theorem v7 : a 7 = 25126 := by
  have h := a_val 7
  simp [vals] at h
  exact_mod_cast h

theorem v8 : a 8 = 51904 := by
  have h := a_val 8
  simp [vals] at h
  exact_mod_cast h

theorem conj1 : ∀ n : ℕ, 8 ≤ n → (a n : ℤ) = 8 * a (n - 1) - 27 * a (n - 2) + 50 * a (n - 3) - 55 * a (n - 4) + 36 * a (n - 5) - 13 * a (n - 6) + 2 * a (n - 7) := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
  rw [show k + 8 - 1 = k + 7 from by omega, show k + 8 - 2 = k + 6 from by omega, show k + 8 - 3 = k + 5 from by omega, show k + 8 - 4 = k + 4 from by omega, show k + 8 - 5 = k + 3 from by omega, show k + 8 - 6 = k + 2 from by omega, show k + 8 - 7 = k + 1 from by omega]
  have h0 : (a (k + 8) : ℤ) = 8 * (a (k + 7) : ℤ) - 27 * (a (k + 6) : ℤ) + 50 * (a (k + 5) : ℤ) - 55 * (a (k + 4) : ℤ) + 36 * (a (k + 3) : ℤ) - 13 * (a (k + 2) : ℤ) + 2 * (a (k + 1) : ℤ) := rec0 k
  linear_combination h0

theorem conj2 : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
  have e1 : F' * ((1 - PowerSeries.X) ^ 6 * (1 - 2 * PowerSeries.X)) =
      F' - PowerSeries.C (8 : ℚ) * (PowerSeries.X ^ 1 * F') + PowerSeries.C (27 : ℚ) * (PowerSeries.X ^ 2 * F') - PowerSeries.C (50 : ℚ) * (PowerSeries.X ^ 3 * F') + PowerSeries.C (55 : ℚ) * (PowerSeries.X ^ 4 * F') - PowerSeries.C (36 : ℚ) * (PowerSeries.X ^ 5 * F') + PowerSeries.C (13 : ℚ) * (PowerSeries.X ^ 6 * F') - PowerSeries.C (2 : ℚ) * (PowerSeries.X ^ 7 * F') := by
    simp only [map_ofNat]
    ring
  have e2 : (PowerSeries.X * (209 - 1154 * PowerSeries.X + 2693 * PowerSeries.X ^ 2 - 3376 * PowerSeries.X ^ 3 + 2401 * PowerSeries.X ^ 4 - 922 * PowerSeries.X ^ 5 + 153 * PowerSeries.X ^ 6) : PowerSeries ℚ) =
      PowerSeries.C (209 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (1154 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (2693 : ℚ) * PowerSeries.X ^ 3 - PowerSeries.C (3376 : ℚ) * PowerSeries.X ^ 4 + PowerSeries.C (2401 : ℚ) * PowerSeries.X ^ 5 - PowerSeries.C (922 : ℚ) * PowerSeries.X ^ 6 + PowerSeries.C (153 : ℚ) * PowerSeries.X ^ 7 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [F', map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
  by_cases hn : n ≤ 7
  · interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7]
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 8 := ⟨n - 8, by omega⟩
    have h0 : (a (j + 8) : ℚ) = 8 * (a (j + 7) : ℚ) - 27 * (a (j + 6) : ℚ) + 50 * (a (j + 5) : ℚ) - 55 * (a (j + 4) : ℚ) + 36 * (a (j + 3) : ℚ) - 13 * (a (j + 2) : ℚ) + 2 * (a (j + 1) : ℚ) := by exact_mod_cast rec0 j
    simp
    linear_combination h0

theorem conj3 : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 9 / 2 * (49 * 2 ^ n - 32) - 374 * (n : ℚ) / 5 - 9 * (n : ℚ) ^ 2 - 25 * (n : ℚ) ^ 3 / 6 - (n : ℚ) ^ 5 / 30 := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hs : n < 8
    · interval_cases n <;> norm_num [v1, v2, v3, v4, v5, v6, v7]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
      have g0 := ih (k + 1) (by omega) (by omega)
      have g1 := ih (k + 2) (by omega) (by omega)
      have g2 := ih (k + 3) (by omega) (by omega)
      have g3 := ih (k + 4) (by omega) (by omega)
      have g4 := ih (k + 5) (by omega) (by omega)
      have g5 := ih (k + 6) (by omega) (by omega)
      have g6 := ih (k + 7) (by omega) (by omega)
      have hr : (a (k + 8) : ℚ) = 8 * (a (k + 7) : ℚ) - 27 * (a (k + 6) : ℚ) + 50 * (a (k + 5) : ℚ) - 55 * (a (k + 4) : ℚ) + 36 * (a (k + 3) : ℚ) - 13 * (a (k + 2) : ℚ) + 2 * (a (k + 1) : ℚ) := by exact_mod_cast rec0 k
      rw [hr, g6, g5, g4, g3, g2, g1, g0]
      push_cast
      ring

end OMAA250780Helpers

open OMA.S_oeis_a250780 OMAA250780Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a250780.main :=
  ⟨conj1, conj2, conj3⟩
