import OMAStatements.S_oeis_a250758
import Mathlib

-- Proof of the statement of OEIS A250758 (statement by @schulzee).
-- Idea: the condition only involves 2 X 2 blocks, so the count is a walk count on the columns of the
-- array (transfer matrix). The 81 states (coded as numbers) are lumped into 14 classes with constant
-- numbers of successors in each class (checked by decide on a truth table of the block condition), which
-- gives a linear system for the class counts W n c. The recurrence follows from explicit row vectors
-- orthogonal to all W n, and the first values are read off.

namespace OMAA250758Helpers

open OMA.S_oeis_a250758

instance (p q r s : Fin 3) : Decidable (Blk p q r s) := by
  unfold Blk; infer_instance

/-- The states of the transfer matrix: the columns of the array, encoded as numbers in base 3
(digit j of the code is entry j). -/
abbrev R := Fin (3 ^ 4)

/-- Digit j of the code a in base 3. -/
def dig (a j : ℕ) : ℕ := a / 3 ^ j % 3

/-- Consecutive columns u, v: all the 2 X 2 blocks they form satisfy the condition. -/
abbrev BlockOK (u v : Fin 4 → Fin 3) : Prop :=
  ∀ i : Fin 3, Blk (u i.castSucc) (v i.castSucc) (u i.succ) (v i.succ)

/-- The truth table of `Blk` on entries below 3: bit ((p * 3 + q) * 3 + r) * 3 + s. -/
def blkTab : ℕ := 1469006537725837178850615

/-- `Blk` read off the truth table. -/
def blkB (p q r s : ℕ) : Bool := Nat.testBit blkTab (((p * 3 + q) * 3 + r) * 3 + s)

theorem blk_iff : ∀ p q r s : Fin 3, blkB p q r s = true ↔ Blk p q r s := by decide +kernel

/-- The same condition on codes. -/
def compatB (r s : ℕ) : Bool :=
  blkB (dig r 0) (dig s 0) (dig r 1) (dig s 1) &&
    (blkB (dig r 1) (dig s 1) (dig r 2) (dig s 2) &&
    (blkB (dig r 2) (dig s 2) (dig r 3) (dig s 3)))

abbrev compatN (r s : ℕ) : Prop := compatB r s = true

/-- States are unconstrained. -/
abbrev ok (_r : R) : Prop := True

/-- Every state may start a walk. -/
abbrev init (_r : R) : Prop := True

/-- Compatibility of consecutive states. -/
abbrev compat (r s : R) : Prop := compatN r.val s.val

theorem dig_enc (u : Fin 4 → Fin 3) (i : Fin 4) : dig ((finFunctionFinEquiv (m := 3) (n := 4)) u).val i.val = (u i).val :=
  congrArg Fin.val (congrFun (Equiv.symm_apply_apply (finFunctionFinEquiv (m := 3) (n := 4)) u) i)

theorem dig_e0 (u : Fin 4 → Fin 3) : dig ((finFunctionFinEquiv (m := 3) (n := 4)) u).val 0 = (u 0).val := dig_enc u 0

theorem dig_e1 (u : Fin 4 → Fin 3) : dig ((finFunctionFinEquiv (m := 3) (n := 4)) u).val 1 = (u 1).val := dig_enc u 1

theorem dig_e2 (u : Fin 4 → Fin 3) : dig ((finFunctionFinEquiv (m := 3) (n := 4)) u).val 2 = (u 2).val := dig_enc u 2

theorem dig_e3 (u : Fin 4 → Fin 3) : dig ((finFunctionFinEquiv (m := 3) (n := 4)) u).val 3 = (u 3).val := dig_enc u 3


theorem blockOK_iff (u v : Fin 4 → Fin 3) :
    BlockOK u v ↔
      (Blk (u 0) (v 0) (u 1) (v 1) ∧
      (Blk (u 1) (v 1) (u 2) (v 2) ∧
      (Blk (u 2) (v 2) (u 3) (v 3)))) := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ j
    fin_cases j <;>
      first
        | exact h0
        | exact h1
        | exact h2

theorem compat_enc (u v : Fin 4 → Fin 3) :
    compat ((finFunctionFinEquiv (m := 3) (n := 4)) u) ((finFunctionFinEquiv (m := 3) (n := 4)) v) ↔ BlockOK u v := by
  rw [blockOK_iff]
  simp only [compat, compatN, compatB, Bool.and_eq_true, dig_e0, dig_e1, dig_e2, dig_e3, blk_iff]

/-- Arrays as sequences of encoded columns. -/
def enc (n : ℕ) : (Fin 4 → Fin (n + 1) → Fin 3) ≃ (Fin (n + 1) → R) where
  toFun := fun x j => (finFunctionFinEquiv (m := 3) (n := 4)) (fun i => x i j)
  invFun := fun y i j => (finFunctionFinEquiv (m := 3) (n := 4)).symm (y j) i
  left_inv := fun x => by funext i j; exact congrFun (Equiv.symm_apply_apply _ _) i
  right_inv := fun y => by funext j; exact Equiv.apply_symm_apply _ _

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
def clsTab : ℕ := 9160665083225740988016783773013918268020913708671618370417829683128238909569774902768530883258764866941761729084558772573654842363660521544897731740387916155740175204928342198343604083374426624

/-- The class of a code (states of one class have the same numbers of successors in each class). -/
def clsF (a : ℕ) : Fin 14 := ⟨(clsTab >>> (8 * a)) % 256 % 14, Nat.mod_lt _ (by norm_num)⟩

/-- The class of a state. -/
def cls (t : R) : Fin 14 := clsF t.val

/-- The codes of the states of each class. -/
def mem : Fin 14 → List ℕ :=
  ![[0, 2], [27, 29, 30, 32, 36, 38, 39, 41], [54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80], [9, 11, 12, 14], [18, 19, 20, 21, 22, 23, 24, 25, 26], [45, 46, 47, 48, 49, 50, 51, 52, 53], [3, 5], [6, 7, 8], [33, 34, 35, 42, 43, 44], [15, 16, 17], [1], [28, 31, 37, 40], [10, 13], [4]]

/-- Mat c d: the number of successors of class d of a state of class c. -/
def Mat : Fin 14 → Fin 14 → ℤ :=
  ![![1, 3, 10, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 1, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 1, 4, 1, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 2, 7, 0, 0, 0, 1, 0, 2, 0, 0, 0, 0, 0],
    ![0, 0, 3, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0],
    ![0, 0, 2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 2, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0],
    ![0, 2, 12, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0],
    ![0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 5, 0, 0, 4, 0, 0, 0, 0, 0, 1, 1, 0],
    ![0, 0, 9, 0, 0, 0, 0, 0, 3, 0, 0, 2, 0, 1]]

/-- W n c: the number of walks with n steps starting at a given state of class c. -/
def W : ℕ → Fin 14 → ℤ
  | 0 => fun _ => 1
  | n + 1 => fun c => ∑ d, Mat c d * W n d

theorem hmem1 : ∀ a : R, a.val ∈ mem (cls a) := by decide +kernel

theorem hmem2 : ∀ c : Fin 14, ∀ a ∈ mem c, a < 3 ^ 4 ∧ clsF a = c := by decide +kernel

theorem hnodup : ∀ c : Fin 14, (mem c).Nodup := by decide +kernel

theorem cntN_0 : ∀ s : R, s.val / 49 = 0 → ∀ c : Fin 14,
    (((mem c).filter (fun a => compatB s.val a)).length : ℤ) = Mat (cls s) c := by
  decide +kernel

theorem cntN_1 : ∀ s : R, s.val / 49 = 1 → ∀ c : Fin 14,
    (((mem c).filter (fun a => compatB s.val a)).length : ℤ) = Mat (cls s) c := by
  decide +kernel

theorem cntN : ∀ s : R, ∀ c : Fin 14,
    (((mem c).filter (fun a => compatB s.val a)).length : ℤ) = Mat (cls s) c := by
  intro s c
  have hq : s.val / 49 < 2 := by
    have := s.isLt
    omega
  interval_cases h : s.val / 49
  · exact cntN_0 s h c
  · exact cntN_1 s h c

/-- U i: the row vector (class sizes) * Mat^i. -/
def U : Fin 6 → Fin 14 → ℤ :=
  ![![2, 8, 27, 4, 9, 9, 2, 3, 6, 3, 1, 4, 2, 1],
    ![2, 24, 205, 4, 9, 41, 2, 3, 22, 3, 1, 13, 2, 1],
    ![2, 40, 556, 4, 9, 73, 2, 3, 38, 3, 1, 22, 2, 1],
    ![2, 56, 1080, 4, 9, 105, 2, 3, 54, 3, 1, 31, 2, 1],
    ![2, 72, 1777, 4, 9, 137, 2, 3, 70, 3, 1, 40, 2, 1],
    ![2, 88, 2647, 4, 9, 169, 2, 3, 86, 3, 1, 49, 2, 1]]

theorem totN : ∀ c : Fin 14, ((mem c).length : ℤ) = U 0 c := by decide +kernel

theorem card_cls (c : Fin 14) (P : ℕ → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun t : R => cls t = c ∧ P t.val)).card = ((mem c).filter (fun a => P a)).length := by
  have key : (Finset.univ.filter (fun t : R => cls t = c ∧ P t.val)).map Fin.valEmbedding =
      ((mem c).filter (fun a => P a)).toFinset := by
    ext a
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
      exact ⟨h1 ▸ hmem1 t, h2⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨ha, hc⟩ := hmem2 c a h1
      exact ⟨⟨a, ha⟩, ⟨hc, h2⟩, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, key, List.toFinset_card_of_nodup ((hnodup c).filter _)]

theorem cnt : ∀ s : R, ∀ c : Fin 14,
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

theorem tot : ∀ c : Fin 14,
    ((Finset.univ.filter (fun t : R => cls t = c ∧ init t)).card : ℤ) = U 0 c := by
  intro c
  have h2 : Finset.univ.filter (fun t : R => cls t = c ∧ init t) =
      Finset.univ.filter (fun t : R => cls t = c ∧ (fun _ : ℕ => True) t.val) :=
    Finset.filter_congr (fun t _ => Iff.rfl)
  rw [h2, card_cls c (fun _ : ℕ => True)]
  simpa using totN c

theorem hU : ∀ (i : Fin 5) (d : Fin 14), ∑ c, U i.castSucc c * Mat c d = U i.succ d := by
  decide +kernel

/-- Coefficients of the recurrence. -/
def L : Fin 6 → ℤ := ![-1, 3, -3, 1, 0, 0]

/-- Row vectors orthogonal to all the vectors W n. -/
def Rm : Fin 1 → Fin 14 → ℤ :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

def Am : Fin 1 → Fin 1 → ℤ :=
  ![![0]]

theorem hRA : ∀ (l : Fin 1) (d : Fin 14), ∑ c, Rm l c * Mat c d = ∑ l', Am l l' * Rm l' d := by
  decide +kernel

theorem hR0 : ∀ l : Fin 1, ∑ c, Rm l c = 0 := by decide +kernel

theorem hL : ∀ c : Fin 14, ∑ i, L i * U i c = Rm 0 c := by decide +kernel

/-- The first values. -/
def vals : Fin 6 → ℤ := ![81, 332, 756, 1353, 2123, 3066]

theorem hV : ∀ i : Fin 6, ∑ c, U i c = vals i := by decide +kernel

theorem sum_cls (g : Fin 14 → ℤ) (P : R → Prop) [DecidablePred P] :
    (∑ t : R, if P t then g (cls t) else 0) =
      ∑ c : Fin 14, ((Finset.univ.filter (fun t => cls t = c ∧ P t)).card : ℤ) * g c := by
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

theorem swap_sum (f : Fin 14 → ℤ) (n : ℕ) :
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

theorem W_shift : ∀ (i : Fin 6) (n : ℕ), ∑ c, U 0 c * W (n + i) c = ∑ c, U i c * W n c := by
  intro i
  induction i using Fin.induction with
  | zero => intro n; simp
  | succ i ih =>
    intro n
    have h1 : n + ((i.succ : Fin 6) : ℕ) = (n + 1) + ((i.castSucc : Fin 6) : ℕ) := by
      simp only [Fin.val_succ, Fin.val_castSucc]; omega
    rw [h1, ih (n + 1), swap_sum]
    simp only [hU]

theorem a_eq (n : ℕ) : (a n : ℤ) = ∑ c, U 0 c * W n c := by
  unfold a
  rw [Nat.card_congr (Equiv.subtypeEquiv (enc n)
      (p := fun x : Fin 4 → Fin (n + 1) → Fin 3 => Good n x)
      (q := fun y : Fin (n + 1) → R => Walk y)
      (fun x => ⟨fun h => ⟨fun _ => trivial, fun j => (compat_enc _ _).mpr (fun i => h i j)⟩,
        fun h i j => (compat_enc _ _).mp (h.2 j) i⟩)), Nat.card_eq_fintype_card,
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

theorem a_shift (i : Fin 6) (n : ℕ) : (a (n + i) : ℤ) = ∑ c, U i c * W n c := by
  rw [a_eq, W_shift]

theorem a_rec (n : ℕ) : ∑ i : Fin 6, L i * (a (n + i) : ℤ) = 0 := by
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

theorem a_val (i : Fin 6) : (a i : ℤ) = vals i := by
  have h := a_shift i 0
  rw [Nat.zero_add] at h
  rw [h, ← hV i]
  apply Finset.sum_congr rfl
  intro c _
  simp [W]

theorem rec0 (n : ℕ) : (a (n + 3) : ℤ) = 3 * (a (n + 2) : ℤ) - 3 * (a (n + 1) : ℤ) + (a (n) : ℤ) := by
  have h := a_rec n
  simp [Fin.sum_univ_succ, L] at h
  linarith

theorem v0 : a 0 = 81 := by
  have h := a_val 0
  simp [vals] at h
  exact_mod_cast h

theorem v1 : a 1 = 332 := by
  have h := a_val 1
  simp [vals] at h
  exact_mod_cast h

theorem v2 : a 2 = 756 := by
  have h := a_val 2
  simp [vals] at h
  exact_mod_cast h

theorem v3 : a 3 = 1353 := by
  have h := a_val 3
  simp [vals] at h
  exact_mod_cast h

theorem v4 : a 4 = 2123 := by
  have h := a_val 4
  simp [vals] at h
  exact_mod_cast h

theorem v5 : a 5 = 3066 := by
  have h := a_val 5
  simp [vals] at h
  exact_mod_cast h

theorem cf : ∀ n : ℕ, 1 ≤ n → 2 * (a n : ℤ) = 173 * (n : ℤ) ^ 2 + 329 * n + 162 := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hs : n < 4
    · interval_cases n <;> norm_num [v1, v2, v3]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      have l0 : k + 1 < k + 4 := by omega
      have b0 : 1 ≤ k + 1 := by omega
      have l1 : k + 2 < k + 4 := by omega
      have b1 : 1 ≤ k + 2 := by omega
      have l2 : k + 3 < k + 4 := by omega
      have b2 : 1 ≤ k + 3 := by omega
      have g0 := ih (k + 1) l0 b0
      have g1 := ih (k + 2) l1 b1
      have g2 := ih (k + 3) l2 b2
      have hr : (a (k + 4) : ℤ) = 3 * (a (k + 3) : ℤ) - 3 * (a (k + 2) : ℤ) + (a (k + 1) : ℤ) := rec0 (k + 1)
      push_cast at g0 g1 g2 ⊢
      linear_combination 2 * hr + g0 - 3 * g1 + 3 * g2

end OMAA250758Helpers

open OMA.S_oeis_a250758 OMAA250758Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a250758.main :=
  ⟨v1, v2, v3, fun n _ => rec0 n, cf⟩
