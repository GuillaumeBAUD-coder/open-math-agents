import OMAStatements.S_oeis_a089937
import Mathlib

-- Proof of the formulas of OEIS A089937 (statement by @ivillar).
-- Idea: the conditions only involve consecutive lines, so the count is a walk count on lines (transfer matrix).
-- The lines are grouped into 13 classes such that the number of successors in each class depends only on the class
-- (checked by decide); the class counts V n c then satisfy an explicit linear system, from which the recurrence
-- follows by linear algebra, and the g.f. and the closed form follow from the recurrence and initial values.

namespace OMAA089937Helpers

open OMA.S_oeis_a089937

/-- The lines of the array (the states of the transfer matrix). -/
abbrev R := Fin 6 → Fin 2

instance (u v : R) : Decidable (BlockOK u v) := by unfold BlockOK; infer_instance

instance (u : R) : Decidable (LineOK u) := by unfold LineOK; infer_instance

abbrev ok (r : R) : Prop := LineOK r

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
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, fun i => h2 i.castSucc i.succ (by simp)⟩, trivial⟩
  · rintro ⟨⟨h1, h2⟩, -⟩
    refine ⟨h1, fun i j hij => ?_⟩
    · have hi : (i : ℕ) < n := by have := j.isLt; omega
      have e1 : (⟨i, hi⟩ : Fin n).castSucc = i := Fin.ext rfl
      have e2 : (⟨i, hi⟩ : Fin n).succ = j := Fin.ext (by simp [hij])
      have := h2 ⟨i, hi⟩
      rw [e1, e2] at this
      exact this

/-- Index of a line in the class table. -/
def code (r : R) : ℕ := (r 0 : ℕ) + 2 * ((r 1 : ℕ) + 2 * ((r 2 : ℕ) + 2 * ((r 3 : ℕ) + 2 * ((r 4 : ℕ) + 2 * ((r 5 : ℕ))))))

/-- The class of a line: lines of the same class have the same number of successors in each class. -/
def cls (r : R) : ℕ := ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 0, 0, 2, 4, 0, 5, 6, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 8, 0, 9, 5, 10, 0, 0, 0, 0, 0, 8, 4, 11, 0, 0, 3, 11, 0, 10, 7, 12] : List ℕ).getD (code r) 0

/-- Mt i j: the number of successors in class j of a line of class i. -/
def Mt (i j : ℕ) : ℕ :=
  (([[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1],
    [2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 1, 1],
    [6, 1, 0, 1, 0, 1, 0, 1, 1, 1, 2, 1, 1],
    [7, 0, 0, 0, 1, 1, 0, 1, 1, 1, 2, 1, 1],
    [6, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 2, 1],
    [8, 0, 0, 0, 0, 0, 0, 0, 2, 1, 2, 2, 1],
    [19, 1, 0, 1, 1, 1, 0, 1, 2, 1, 2, 2, 1],
    [4, 1, 1, 1, 1, 1, 1, 2, 1, 0, 1, 1, 1],
    [4, 0, 2, 2, 2, 0, 1, 2, 0, 0, 0, 2, 1],
    [16, 1, 2, 2, 2, 1, 1, 2, 1, 0, 1, 2, 1],
    [17, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1],
    [43, 2, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1]] : List (List ℕ)).getD i []).getD j 0

/-- V n c: the number of walks of n + 1 lines starting at a given line of class c. -/
def V : ℕ → ℕ → ℕ
  | 0, c => ([0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : List ℕ).getD c 0
  | n + 1, 1 => V n 1 + V n 3 + V n 5 + V n 7 + V n 8 + V n 10 + V n 11 + V n 12
  | n + 1, 2 => 2 * V n 0 + V n 8 + V n 9 + 2 * V n 10 + V n 11 + V n 12
  | n + 1, 3 => 6 * V n 0 + V n 1 + V n 3 + V n 5 + V n 7 + V n 8 + V n 9 + 2 * V n 10 + V n 11 + V n 12
  | n + 1, 4 => 7 * V n 0 + V n 4 + V n 5 + V n 7 + V n 8 + V n 9 + 2 * V n 10 + V n 11 + V n 12
  | n + 1, 5 => 6 * V n 0 + V n 1 + V n 3 + V n 4 + V n 5 + V n 7 + V n 8 + V n 10 + 2 * V n 11 + V n 12
  | n + 1, 6 => 8 * V n 0 + 2 * V n 8 + V n 9 + 2 * V n 10 + 2 * V n 11 + V n 12
  | n + 1, 7 => 19 * V n 0 + V n 1 + V n 3 + V n 4 + V n 5 + V n 7 + 2 * V n 8 + V n 9 + 2 * V n 10 + 2 * V n 11 + V n 12
  | n + 1, 8 => 4 * V n 0 + V n 1 + V n 2 + V n 3 + V n 4 + V n 5 + V n 6 + 2 * V n 7 + V n 8 + V n 10 + V n 11 + V n 12
  | n + 1, 9 => 4 * V n 0 + 2 * V n 2 + 2 * V n 3 + 2 * V n 4 + V n 6 + 2 * V n 7 + 2 * V n 11 + V n 12
  | n + 1, 10 => 16 * V n 0 + V n 1 + 2 * V n 2 + 2 * V n 3 + 2 * V n 4 + V n 5 + V n 6 + 2 * V n 7 + V n 8 + V n 10 + 2 * V n 11 + V n 12
  | n + 1, 11 => 17 * V n 0 + V n 1 + V n 2 + V n 3 + V n 4 + 2 * V n 5 + V n 6 + 2 * V n 7 + V n 8 + V n 9 + 2 * V n 10 + V n 11 + V n 12
  | n + 1, 12 => 43 * V n 0 + 2 * V n 1 + 2 * V n 2 + 2 * V n 3 + 2 * V n 4 + 2 * V n 5 + V n 6 + 2 * V n 7 + 2 * V n 8 + V n 9 + 2 * V n 10 + 2 * V n 11 + V n 12
  | _ + 1, _ => 0

theorem cls_lt : ∀ t : R, cls t < 13 := by decide +kernel

theorem sum_cls (g : ℕ → ℕ) (P : R → Prop) [DecidablePred P] :
    (∑ t : R, if P t then g (cls t) else 0) =
      ∑ c ∈ Finset.range 13, (Finset.univ.filter (fun t : R => cls t = c ∧ P t)).card * g c := by
  have h1 : ∀ t : R, (if P t then g (cls t) else 0) =
      ∑ c ∈ Finset.range 13, if cls t = c ∧ P t then g c else 0 := by
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

theorem cnt : ∀ s : R, ∀ c < 13,
    (Finset.univ.filter (fun t : R => cls t = c ∧ (ok s ∧ compat s t))).card = Mt (cls s) c := by
  decide +kernel

theorem cnt0 : ∀ s : R, (if ok s then 1 else 0) = V 0 (cls s) := by decide +kernel

theorem tcnt : ∀ c < 13, (Finset.univ.filter (fun t : R => cls t = c ∧ ini t)).card =
    ([43, 2, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1] : List ℕ).getD c 0 := by decide +kernel

theorem step (n : ℕ) : ∀ i < 13, (∑ c ∈ Finset.range 13, Mt i c * V n c) = V (n + 1) i := by
  intro i hi
  interval_cases i <;> simp [Finset.sum_range_succ, Mt, V]

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
def U (n : ℕ) : ℕ := 43 * V n 0 + 2 * V n 1 + 2 * V n 2 + 2 * V n 3 + 2 * V n 4 + 2 * V n 5 + V n 6 + 2 * V n 7 + 2 * V n 8 + V n 9 + 2 * V n 10 + 2 * V n 11 + V n 12

theorem usum (n : ℕ) : (∑ c ∈ Finset.range 13, ([43, 2, 2, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1] : List ℕ).getD c 0 * V n c) = U n := by
  simp [Finset.sum_range_succ, U]

theorem a_eq (n : ℕ) : a (n + 1) = U n := by
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

theorem up0 (n : ℕ) : U n = 43 * V n 0 + 2 * V n 1 + 2 * V n 2 + 2 * V n 3 + 2 * V n 4 + 2 * V n 5 + V n 6 + 2 * V n 7 + 2 * V n 8 + V n 9 + 2 * V n 10 + 2 * V n 11 + V n 12 := rfl

theorem up1 (n : ℕ) : U (n + 1) = 209 * V n 0 + 16 * V n 1 + 12 * V n 2 + 20 * V n 3 + 18 * V n 4 + 20 * V n 5 + 8 * V n 6 + 26 * V n 7 + 24 * V n 8 + 12 * V n 9 + 32 * V n 10 + 30 * V n 11 + 21 * V n 12 := by
  rw [up0 (n + 1)]
  simp only [V]
  ring

theorem up2 (n : ℕ) : U (n + 2) = 3017 * V n 0 + 210 * V n 1 + 184 * V n 2 + 266 * V n 3 + 248 * V n 4 + 258 * V n 5 + 119 * V n 6 + 338 * V n 7 + 282 * V n 8 + 135 * V n 9 + 362 * V n 10 + 358 * V n 11 + 239 * V n 12 := by
  rw [show n + 2 = (n + 1) + 1 from rfl, up1 (n + 1)]
  simp only [V]
  ring

theorem up3 (n : ℕ) : U (n + 3) = 36445 * V n 0 + 2552 * V n 1 + 2112 * V n 2 + 3184 * V n 3 + 2956 * V n 4 + 3158 * V n 5 + 1376 * V n 6 + 4072 * V n 7 + 3560 * V n 8 + 1752 * V n 9 + 4616 * V n 10 + 4450 * V n 11 + 2999 * V n 12 := by
  rw [show n + 3 = (n + 1) + 2 from rfl, up2 (n + 1)]
  simp only [V]
  ring

theorem up4 (n : ℕ) : U (n + 4) = 451055 * V n 0 + 31590 * V n 1 + 26744 * V n 2 + 39710 * V n 3 + 36930 * V n 4 + 38996 * V n 5 + 17377 * V n 6 + 50676 * V n 7 + 43482 * V n 8 + 21149 * V n 9 + 56184 * V n 10 + 54760 * V n 11 + 36787 * V n 12 := by
  rw [show n + 4 = (n + 1) + 3 from rfl, up3 (n + 1)]
  simp only [V]
  ring

theorem up5 (n : ℕ) : U (n + 5) = 5556323 * V n 0 + 388972 * V n 1 + 326482 * V n 2 + 487454 * V n 3 + 453084 * V n 4 + 480662 * V n 5 + 212362 * V n 6 + 622626 * V n 7 + 538076 * V n 8 + 262984 * V n 9 + 696220 * V n 10 + 675554 * V n 11 + 454385 * V n 12 := by
  rw [show n + 5 = (n + 1) + 4 from rfl, up4 (n + 1)]
  simp only [V]
  ring

theorem up6 (n : ℕ) : U (n + 6) = 68528771 * V n 0 + 4798334 * V n 1 + 4040808 * V n 2 + 6020522 * V n 3 + 5597180 * V n 4 + 5926972 * V n 5 + 2627219 * V n 6 + 7687236 * V n 7 + 6625250 * V n 8 + 3231947 * V n 9 + 8567824 * V n 10 + 8328100 * V n 11 + 5598861 * V n 12 := by
  rw [show n + 6 = (n + 1) + 5 from rfl, up5 (n + 1)]
  simp only [V]
  ring

theorem up7 (n : ℕ) : U (n + 7) = 844864771 * V n 0 + 59151960 * V n 1 + 49750614 * V n 2 + 74183678 * V n 3 + 68962002 * V n 4 + 73077240 * V n 5 + 32351982 * V n 6 + 94734208 * V n 7 + 81731622 * V n 8 + 39899926 * V n 9 + 105718232 * V n 10 + 102690312 * V n 11 + 69050253 * V n 12 := by
  rw [show n + 7 = (n + 1) + 6 from rfl, up6 (n + 1)]
  simp only [V]
  ring

theorem up8 (n : ℕ) : U (n + 8) = 10417480645 * V n 0 + 729387758 * V n 1 + 613758756 * V n 2 + 914905842 * V n 3 + 850532206 * V n 4 + 901040072 * V n 5 + 399090345 * V n 6 + 1168289778 * V n 7 + 1007538546 * V n 8 + 491723049 * V n 9 + 1303125152 * V n 10 + 1266133870 * V n 11 + 851302029 * V n 12 := by
  rw [show n + 8 = (n + 1) + 7 from rfl, up7 (n + 1)]
  simp only [V]
  ring

theorem up9 (n : ℕ) : U (n + 9) = 128444458829 * V n 0 + 8993025076 * V n 1 + 7565972876 * V n 2 + 11279596326 * V n 3 + 10485834932 * V n 4 + 11109691152 * V n 5 + 4919822646 * V n 6 + 14403800948 * V n 7 + 12423786506 * V n 8 + 6064012826 * V n 9 + 16069117180 * V n 10 + 15611397828 * V n 11 + 10496827403 * V n 12 := by
  rw [show n + 9 = (n + 1) + 8 from rfl, up8 (n + 1)]
  simp only [V]
  ring

theorem up10 (n : ℕ) : U (n + 10) = 1583713727937 * V n 0 + 110884069822 * V n 1 + 93295099152 * V n 2 + 139081212654 * V n 3 + 129294426184 * V n 4 + 136981302582 * V n 5 + 60665141743 * V n 6 + 177602231920 * V n 7 + 153179323870 * V n 8 + 74763252959 * V n 9 + 198122125832 * V n 10 + 192486157854 * V n 11 + 129422885699 * V n 12 := by
  rw [show n + 10 = (n + 1) + 9 from rfl, up9 (n + 1)]
  simp only [V]
  ring

theorem up11 (n : ℕ) : U (n + 11) = 19526962902635 * V n 0 + 1367182195932 * V n 1 + 1150282010704 * V n 2 + 1714830827682 * V n 3 + 1594159971390 * V n 4 + 1688962779970 * V n 5 + 747973746214 * V n 6 + 2189790735590 * V n 7 + 1888704236674 * V n 8 + 921847155206 * V n 9 + 2442861132518 * V n 10 + 2373334171006 * V n 11 + 1595777230271 * V n 12 := by
  rw [show n + 11 = (n + 1) + 10 from rfl, up10 (n + 1)]
  simp only [V]
  ring

theorem a_rec : ∀ m : ℕ, 12 ≤ m → (a m : ℤ) = 8 * (a (m - 1) : ℤ) + 62 * (a (m - 2) : ℤ) - 78 * (a (m - 3) : ℤ) - 375 * (a (m - 4) : ℤ) + 300 * (a (m - 5) : ℤ) + 486 * (a (m - 6) : ℤ) - 385 * (a (m - 7) : ℤ) - 30 * (a (m - 8) : ℤ) + 52 * (a (m - 9) : ℤ) - 2 * (a (m - 10) : ℤ) - (a (m - 11) : ℤ) := by
  intro m hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 12 := ⟨m - 12, by omega⟩
  rw [show k + 12 - 1 = k + 11 by omega, show k + 12 - 2 = k + 10 by omega, show k + 12 - 3 = k + 9 by omega, show k + 12 - 4 = k + 8 by omega, show k + 12 - 5 = k + 7 by omega, show k + 12 - 6 = k + 6 by omega, show k + 12 - 7 = k + 5 by omega, show k + 12 - 8 = k + 4 by omega, show k + 12 - 9 = k + 3 by omega, show k + 12 - 10 = k + 2 by omega, show k + 12 - 11 = k + 1 by omega]
  rw [show a (k + 12) = U (k + 11) from a_eq _, show a (k + 11) = U (k + 10) from a_eq _, show a (k + 10) = U (k + 9) from a_eq _, show a (k + 9) = U (k + 8) from a_eq _, show a (k + 8) = U (k + 7) from a_eq _, show a (k + 7) = U (k + 6) from a_eq _, show a (k + 6) = U (k + 5) from a_eq _, show a (k + 5) = U (k + 4) from a_eq _, show a (k + 4) = U (k + 3) from a_eq _, show a (k + 3) = U (k + 2) from a_eq _, show a (k + 2) = U (k + 1) from a_eq _, show a (k + 1) = U (k) from a_eq _]
  rw [up11 k, up10 k, up9 k, up8 k, up7 k, up6 k, up5 k, up4 k, up3 k, up2 k, up1 k, up0 k]
  push_cast
  ring

theorem a_v1 : a 1 = 21 := by
  rw [show a 1 = U 0 from a_eq _]; decide +kernel

theorem a_v2 : a 2 = 239 := by
  rw [show a 2 = U 1 from a_eq _]; decide +kernel

theorem a_v3 : a 3 = 2999 := by
  rw [show a 3 = U 2 from a_eq _]; decide +kernel

theorem a_v4 : a 4 = 36787 := by
  rw [show a 4 = U 3 from a_eq _]; decide +kernel

theorem a_v5 : a 5 = 454385 := by
  rw [show a 5 = U 4 from a_eq _]; decide +kernel

theorem a_v6 : a 6 = 5598861 := by
  rw [show a 6 = U 5 from a_eq _]; decide +kernel

theorem a_v7 : a 7 = 69050253 := by
  rw [show a 7 = U 6 from a_eq _]; decide +kernel

theorem a_v8 : a 8 = 851302029 := by
  rw [show a 8 = U 7 from a_eq _]; decide +kernel

theorem a_v9 : a 9 = 10496827403 := by
  rw [show a 9 = U 8 from a_eq _]; decide +kernel

theorem a_v10 : a 10 = 129422885699 := by
  rw [show a 10 = U 9 from a_eq _]; decide +kernel

theorem a_v11 : a 11 = 1595777230271 := by
  rw [show a 11 = U 10 from a_eq _]; decide +kernel

theorem gf_eq : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
  have e1 : F' * (1 - 8 * PowerSeries.X - 62 * PowerSeries.X ^ 2 + 78 * PowerSeries.X ^ 3 + 375 * PowerSeries.X ^ 4 - 300 * PowerSeries.X ^ 5 - 486 * PowerSeries.X ^ 6 + 385 * PowerSeries.X ^ 7 + 30 * PowerSeries.X ^ 8 - 52 * PowerSeries.X ^ 9 + 2 * PowerSeries.X ^ 10 + PowerSeries.X ^ 11) = F' - PowerSeries.C (8 : ℚ) * (PowerSeries.X ^ 1 * F') - PowerSeries.C (62 : ℚ) * (PowerSeries.X ^ 2 * F') + PowerSeries.C (78 : ℚ) * (PowerSeries.X ^ 3 * F') + PowerSeries.C (375 : ℚ) * (PowerSeries.X ^ 4 * F') - PowerSeries.C (300 : ℚ) * (PowerSeries.X ^ 5 * F') - PowerSeries.C (486 : ℚ) * (PowerSeries.X ^ 6 * F') + PowerSeries.C (385 : ℚ) * (PowerSeries.X ^ 7 * F') + PowerSeries.C (30 : ℚ) * (PowerSeries.X ^ 8 * F') - PowerSeries.C (52 : ℚ) * (PowerSeries.X ^ 9 * F') + PowerSeries.C (2 : ℚ) * (PowerSeries.X ^ 10 * F') + PowerSeries.X ^ 11 * F' := by
    simp only [map_ofNat]
    ring
  have e2 : (PowerSeries.X * (21 + 71 * PowerSeries.X - 215 * PowerSeries.X ^ 2 - 385 * PowerSeries.X ^ 3 + 668 * PowerSeries.X ^ 4 + 234 * PowerSeries.X ^ 5 - 400 * PowerSeries.X ^ 6 + 9 * PowerSeries.X ^ 7 + 49 * PowerSeries.X ^ 8 - 3 * PowerSeries.X ^ 9 - PowerSeries.X ^ 10) : PowerSeries ℚ) = PowerSeries.C (21 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (71 : ℚ) * PowerSeries.X ^ 2 - PowerSeries.C (215 : ℚ) * PowerSeries.X ^ 3 - PowerSeries.C (385 : ℚ) * PowerSeries.X ^ 4 + PowerSeries.C (668 : ℚ) * PowerSeries.X ^ 5 + PowerSeries.C (234 : ℚ) * PowerSeries.X ^ 6 - PowerSeries.C (400 : ℚ) * PowerSeries.X ^ 7 + PowerSeries.C (9 : ℚ) * PowerSeries.X ^ 8 + PowerSeries.C (49 : ℚ) * PowerSeries.X ^ 9 - PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 10 - PowerSeries.X ^ 11 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [F', map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
  by_cases hn : n ≤ 11
  · interval_cases n <;> norm_num [a_v1, a_v2, a_v3, a_v4, a_v5, a_v6, a_v7, a_v8, a_v9, a_v10, a_v11]
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 12 := ⟨n - 12, by omega⟩
    have h := a_rec (j + 12) (by omega)
    rw [show j + 12 - 1 = j + 11 by omega, show j + 12 - 2 = j + 10 by omega, show j + 12 - 3 = j + 9 by omega, show j + 12 - 4 = j + 8 by omega, show j + 12 - 5 = j + 7 by omega, show j + 12 - 6 = j + 6 by omega, show j + 12 - 7 = j + 5 by omega, show j + 12 - 8 = j + 4 by omega, show j + 12 - 9 = j + 3 by omega, show j + 12 - 10 = j + 2 by omega, show j + 12 - 11 = j + 1 by omega] at h
    have q : (a (j + 12) : ℚ) = 8 * (a (j + 11) : ℚ) + 62 * (a (j + 10) : ℚ) - 78 * (a (j + 9) : ℚ) - 375 * (a (j + 8) : ℚ) + 300 * (a (j + 7) : ℚ) + 486 * (a (j + 6) : ℚ) - 385 * (a (j + 5) : ℚ) - 30 * (a (j + 4) : ℚ) + 52 * (a (j + 3) : ℚ) - 2 * (a (j + 2) : ℚ) - (a (j + 1) : ℚ) := by exact_mod_cast h
    simp
    linear_combination q

end OMAA089937Helpers

open OMA.S_oeis_a089937 OMAA089937Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a089937.main :=
  gf_eq
