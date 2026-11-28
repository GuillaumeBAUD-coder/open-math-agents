import OMAStatements.S_oeis_a184541
import Mathlib

/-!
Proof of the conjectures for A184541 ((n+2) X 4 binary arrays whose 3 X 3 subblocks have rows and
columns in lexicographically nondecreasing order).

The condition `Good` of the statement only involves three consecutive rows, so splitting off the
first row (`good_cons184541`) gives a transfer recursion on pairs of rows: `T (m + 1) x y` is the sum
of `T m y z` over the rows `z` with `TriOK x y z`, and `a n` is the sum of `T n x y`. On the
binary codes of rows, `TriOK` becomes a Boolean test `Vt184541` (each window of three columns compares
as numbers, `TriOK_code184541`), and `T` becomes the recursion `G184541`.

The 256 pairs of codes fall into 6 types (`typ184541`); for `n ≥ 0`,
`G (n + 2) u v = Sum_k Kt (typ u v) k * C(n, k)`, proved by induction using Pascal's rule and the
kernel-checked identities `step_fact184541` (the successors of a pair of type `t` have coefficient
sums `Kt t k + Kt t (k + 1)`). Summing over all pairs gives `a (n + 2)` as a combination of
binomials, which expands to the closed form; `a 1` is checked directly. The recurrence and the
generating function follow by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a184541 Finset

/-- A row of the array. -/
abbrev Row184541 := Fin 4 → Fin 2

theorem good_cons184541 {m : ℕ} (x : Row184541) (B : Fin (m + 2) → Row184541) :
    Good (Fin.cons x B : Fin (m + 3) → Row184541) ↔ TriOK x (B 0) (B 1) ∧ Good B := by
  constructor
  · intro h
    refine ⟨?_, fun i j l hj hl => ?_⟩
    · have h1 := h 0 (0 : Fin (m + 2)).succ (1 : Fin (m + 2)).succ
        (by simp only [Fin.val_succ, Fin.val_zero])
        (by simp only [Fin.val_succ, Fin.val_zero, Fin.val_one])
      rwa [Fin.cons_zero, Fin.cons_succ, Fin.cons_succ] at h1
    · have h1 := h i.succ j.succ l.succ (by simp only [Fin.val_succ]; omega)
        (by simp only [Fin.val_succ]; omega)
      rwa [Fin.cons_succ, Fin.cons_succ, Fin.cons_succ] at h1
  · rintro ⟨h0, h⟩ i j l hj hl
    cases i using Fin.cases with
    | zero =>
      have ej : j = (0 : Fin (m + 2)).succ := Fin.ext (by
        simp only [Fin.val_succ, Fin.val_zero] at hj ⊢; omega)
      have el : l = (1 : Fin (m + 2)).succ := Fin.ext (by
        rw [ej] at hl; simp only [Fin.val_succ, Fin.val_zero, Fin.val_one] at hl ⊢; omega)
      subst ej el
      rwa [Fin.cons_zero, Fin.cons_succ, Fin.cons_succ]
    | succ i =>
      have hj0 : (j : ℕ) ≠ 0 := by simp only [Fin.val_succ] at hj; omega
      have hl0 : (l : ℕ) ≠ 0 := by omega
      obtain ⟨j', rfl⟩ : ∃ j' : Fin (m + 2), j = j'.succ :=
        ⟨j.pred (fun e => hj0 (by rw [e]; rfl)), (Fin.succ_pred _ _).symm⟩
      obtain ⟨l', rfl⟩ : ∃ l' : Fin (m + 2), l = l'.succ :=
        ⟨l.pred (fun e => hl0 (by rw [e]; rfl)), (Fin.succ_pred _ _).symm⟩
      rw [Fin.cons_succ, Fin.cons_succ, Fin.cons_succ]
      exact h i j' l' (by simp only [Fin.val_succ] at hj; omega)
        (by simp only [Fin.val_succ] at hl; omega)

instance decTriOK184541 (x y z : Row184541) : Decidable (TriOK x y z) := by
  unfold TriOK Lex3
  infer_instance

/-- The number of ways to continue the rows `x, y` by `m` more rows. -/
noncomputable def T184541 (m : ℕ) (x y : Row184541) : ℕ := by
  classical
  exact ∑ B : Fin m → Row184541,
    if Good (Fin.cons x (Fin.cons y B) : Fin (m + 2) → Row184541) then 1 else 0

theorem T_zero184541 (x y : Row184541) : T184541 0 x y = 1 := by
  classical
  unfold T184541
  rw [Fintype.sum_unique, if_pos]
  intro i j l hj hl
  have := l.isLt
  omega

theorem T_succ184541 (m : ℕ) (x y : Row184541) :
    T184541 (m + 1) x y = ∑ z : Row184541, if TriOK x y z then T184541 m y z else 0 := by
  classical
  unfold T184541
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row184541).symm _
    (fun p => if Good (Fin.cons x (Fin.cons y (Fin.cons p.1 p.2)) : Fin (m + 3) → Row184541)
      then 1 else 0) (fun B => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hv : TriOK x y z
  · rw [if_pos hv]
    refine Finset.sum_congr rfl fun B _ => if_congr ?_ rfl rfl
    rw [good_cons184541]
    simp only [Fin.cons_zero, Fin.cons_one]
    exact and_iff_right hv
  · rw [if_neg hv]
    refine Finset.sum_eq_zero fun B _ => if_neg ?_
    rw [good_cons184541]
    simp only [Fin.cons_zero, Fin.cons_one]
    exact fun h => hv h.1

theorem a_eq184541 (n : ℕ) : a n = ∑ x : Row184541, ∑ y : Row184541, T184541 n x y := by
  classical
  have h1 : a n = ∑ A : Fin (n + 2) → Row184541, if Good A then 1 else 0 := by
    unfold a
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  rw [h1, Fintype.sum_equiv (Fin.consEquiv fun _ => Row184541).symm _
    (fun p => if Good (Fin.cons p.1 p.2 : Fin (n + 2) → Row184541) then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row184541).symm _
    (fun p => if Good (Fin.cons x (Fin.cons p.1 p.2) : Fin (n + 2) → Row184541) then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  unfold T184541
  exact Finset.sum_congr rfl fun B _ => if_congr Iff.rfl rfl rfl

/-- The row with code `c`: the bits of `c`, most significant first. -/
def row184541 (c : Fin 16) : Row184541 := fun j => ⟨c.val / 2 ^ (3 - j.val) % 2, Nat.mod_lt _ (by norm_num)⟩

theorem row_injective184541 : Function.Injective row184541 := by
  decide +kernel

theorem row_bijective184541 : Function.Bijective row184541 := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective184541, by simp⟩

theorem lex3_iff184541 : ∀ a b c a' b' c' : Fin 2,
    Lex3 a b c a' b' c' ↔ 4 * a.val + 2 * b.val + c.val ≤ 4 * a'.val + 2 * b'.val + c'.val := by
  unfold Lex3
  decide

/-- The conditions of `TriOK` on the window of columns `t, t + 1, t + 2`. -/
def Win184541 (u v w : Row184541) (t : ℕ) (ht : t + 2 < 4) : Prop :=
  Lex3 (u ⟨t, by omega⟩) (u ⟨t + 1, by omega⟩) (u ⟨t + 2, ht⟩)
      (v ⟨t, by omega⟩) (v ⟨t + 1, by omega⟩) (v ⟨t + 2, ht⟩) ∧
    Lex3 (v ⟨t, by omega⟩) (v ⟨t + 1, by omega⟩) (v ⟨t + 2, ht⟩)
      (w ⟨t, by omega⟩) (w ⟨t + 1, by omega⟩) (w ⟨t + 2, ht⟩) ∧
    Lex3 (u ⟨t, by omega⟩) (v ⟨t, by omega⟩) (w ⟨t, by omega⟩)
      (u ⟨t + 1, by omega⟩) (v ⟨t + 1, by omega⟩) (w ⟨t + 1, by omega⟩) ∧
    Lex3 (u ⟨t + 1, by omega⟩) (v ⟨t + 1, by omega⟩) (w ⟨t + 1, by omega⟩)
      (u ⟨t + 2, ht⟩) (v ⟨t + 2, ht⟩) (w ⟨t + 2, ht⟩)

theorem TriOK_iff184541 (u v w : Row184541) : TriOK u v w ↔ ∀ t (ht : t + 2 < 4), Win184541 u v w t ht := by
  constructor
  · intro h t ht
    exact h ⟨t, by omega⟩ ⟨t + 1, by omega⟩ ⟨t + 2, ht⟩ rfl rfl
  · intro h j j' j'' h1 h2
    have ht : (j : ℕ) + 2 < 4 := by have := j''.isLt; omega
    have e1 : j' = ⟨j + 1, by clear h1 h2; omega⟩ := Fin.ext h1
    have e2 : j'' = ⟨j + 2, ht⟩ := Fin.ext (by rw [h2, h1])
    subst e1 e2
    exact h j ht

/-- Bit `t` of the code `x`, the most significant first. -/
def bt184541 (x t : ℕ) : ℕ := x / 2 ^ (3 - t) % 2

/-- The window test on codes. -/
def WT184541 (u v w t : ℕ) : Bool :=
  decide (4 * bt184541 u t + 2 * bt184541 u (t + 1) + bt184541 u (t + 2) ≤
      4 * bt184541 v t + 2 * bt184541 v (t + 1) + bt184541 v (t + 2)) &&
    decide (4 * bt184541 v t + 2 * bt184541 v (t + 1) + bt184541 v (t + 2) ≤
      4 * bt184541 w t + 2 * bt184541 w (t + 1) + bt184541 w (t + 2)) &&
    decide (4 * bt184541 u t + 2 * bt184541 v t + bt184541 w t ≤
      4 * bt184541 u (t + 1) + 2 * bt184541 v (t + 1) + bt184541 w (t + 1)) &&
    decide (4 * bt184541 u (t + 1) + 2 * bt184541 v (t + 1) + bt184541 w (t + 1) ≤
      4 * bt184541 u (t + 2) + 2 * bt184541 v (t + 2) + bt184541 w (t + 2))

theorem Win_iff184541 (u v w : Fin 16) (t : ℕ) (ht : t + 2 < 4) :
    Win184541 (row184541 u) (row184541 v) (row184541 w) t ht ↔ WT184541 u.val v.val w.val t = true := by
  simp only [Win184541, lex3_iff184541, WT184541, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  rfl

/-- `TriOK` on codes. -/
def Vt184541 (u v w : ℕ) : Bool := WT184541 u v w 0 && WT184541 u v w 1

theorem TriOK_code184541 (u v w : Fin 16) :
    TriOK (row184541 u) (row184541 v) (row184541 w) ↔ Vt184541 u.val v.val w.val = true := by
  rw [TriOK_iff184541]
  simp only [Vt184541, Bool.and_eq_true]
  constructor
  · intro h
    exact ⟨(Win_iff184541 u v w 0 (by norm_num)).1 (h 0 (by norm_num)), (Win_iff184541 u v w 1 (by norm_num)).1 (h 1 (by norm_num))⟩
  · rintro ⟨h0, h1⟩ t ht
    have : t = 0 ∨ t = 1 := by omega
    rcases this with rfl | rfl
    · exact (Win_iff184541 u v w 0 ht).2 h0
    · exact (Win_iff184541 u v w 1 ht).2 h1

/-- The transfer recursion on codes. -/
def G184541 : ℕ → Fin 16 → Fin 16 → ℕ
  | 0, _, _ => 1
  | m + 1, u, v => ∑ w : Fin 16, if Vt184541 u.val v.val w.val then G184541 m v w else 0

theorem T_eq_G184541 (m : ℕ) : ∀ u v : Fin 16, T184541 m (row184541 u) (row184541 v) = G184541 m u v := by
  induction m with
  | zero => intro u v; rw [T_zero184541]; rfl
  | succ m ih =>
    intro u v
    rw [T_succ184541, ← row_bijective184541.sum_comp]
    simp only [G184541]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ih v w]
    exact if_congr (TriOK_code184541 u v w) rfl rfl

theorem a_eq_G184541 (n : ℕ) : a n = ∑ u : Fin 16, ∑ v : Fin 16, G184541 n u v := by
  rw [a_eq184541, ← row_bijective184541.sum_comp]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← row_bijective184541.sum_comp]
  exact Finset.sum_congr rfl fun v _ => T_eq_G184541 n u v

/-- The type of a pair of codes. -/
def TYtab184541 : List (List ℕ) :=
  [[3, 5, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1],
   [0, 5, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- The number of continuations of a pair by one row. -/
def L1tab184541 : List (List ℕ) :=
  [[5, 7, 0, 7, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1],
   [0, 7, 10, 9, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 2, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 7, 6, 6, 0, 2, 0, 0, 0, 0, 3, 3, 0, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- The binomial coefficients of each type. -/
def Kttab184541 : List (List ℕ) := [[0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0], [3, 1, 0, 0, 0, 0], [22, 67, 37, 6, 1, 0], [28, 4, 1, 0, 0, 0], [35, 32, 5, 1, 0, 0]]

def typ184541 (u v : Fin 16) : ℕ := (TYtab184541.getD u.val []).getD v.val 0

def L1184541 (u v : Fin 16) : ℕ := (L1tab184541.getD u.val []).getD v.val 0

def Kt184541 (t k : ℕ) : ℕ := (Kttab184541.getD t []).getD k 0

theorem L1_fact184541 : ∀ u v : Fin 16,
    (∑ w : Fin 16, if Vt184541 u.val v.val w.val then 1 else 0) = L1184541 u v := by
  decide +kernel

theorem base_fact184541 : ∀ u v : Fin 16,
    (∑ w : Fin 16, if Vt184541 u.val v.val w.val then L1184541 v w else 0) = Kt184541 (typ184541 u v) 0 := by
  decide +kernel

theorem top_fact184541 : ∀ u v : Fin 16, Kt184541 (typ184541 u v) 5 = 0 := by
  decide +kernel

theorem step_fact0_184541 : ∀ u v : Fin 16,
    (∑ w : Fin 16, if Vt184541 u.val v.val w.val then Kt184541 (typ184541 v w) 0 else 0) =
      Kt184541 (typ184541 u v) 0 + Kt184541 (typ184541 u v) 1 := by
  decide +kernel

theorem step_fact1_184541 : ∀ u v : Fin 16,
    (∑ w : Fin 16, if Vt184541 u.val v.val w.val then Kt184541 (typ184541 v w) 1 else 0) =
      Kt184541 (typ184541 u v) 1 + Kt184541 (typ184541 u v) 2 := by
  decide +kernel

theorem step_fact2_184541 : ∀ u v : Fin 16,
    (∑ w : Fin 16, if Vt184541 u.val v.val w.val then Kt184541 (typ184541 v w) 2 else 0) =
      Kt184541 (typ184541 u v) 2 + Kt184541 (typ184541 u v) 3 := by
  decide +kernel

theorem step_fact3_184541 : ∀ u v : Fin 16,
    (∑ w : Fin 16, if Vt184541 u.val v.val w.val then Kt184541 (typ184541 v w) 3 else 0) =
      Kt184541 (typ184541 u v) 3 + Kt184541 (typ184541 u v) 4 := by
  decide +kernel

theorem step_fact4_184541 : ∀ u v : Fin 16,
    (∑ w : Fin 16, if Vt184541 u.val v.val w.val then Kt184541 (typ184541 v w) 4 else 0) =
      Kt184541 (typ184541 u v) 4 + Kt184541 (typ184541 u v) 5 := by
  decide +kernel

theorem step_fact184541 (u v : Fin 16) (k : ℕ) (hk : k < 5) :
    (∑ w : Fin 16, if Vt184541 u.val v.val w.val then Kt184541 (typ184541 v w) k else 0) =
      Kt184541 (typ184541 u v) k + Kt184541 (typ184541 u v) (k + 1) := by
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl
  · exact step_fact0_184541 u v
  · exact step_fact1_184541 u v
  · exact step_fact2_184541 u v
  · exact step_fact3_184541 u v
  · exact step_fact4_184541 u v

theorem G_one184541 (u v : Fin 16) : G184541 1 u v = L1184541 u v := by
  rw [← L1_fact184541 u v]
  rfl

theorem G_two184541 (u v : Fin 16) : G184541 2 u v = Kt184541 (typ184541 u v) 0 := by
  rw [← base_fact184541 u v]
  show (∑ w : Fin 16, if Vt184541 u.val v.val w.val then G184541 1 v w else 0) = _
  simp only [G_one184541]

theorem G_closed184541 (m : ℕ) :
    ∀ u v : Fin 16, G184541 (m + 2) u v = ∑ k ∈ range 5, Kt184541 (typ184541 u v) k * m.choose k := by
  induction m with
  | zero =>
    intro u v
    rw [G_two184541]
    simp [Finset.sum_range_succ]
  | succ m ih =>
    intro u v
    have h1 : G184541 (m + 1 + 2) u v = ∑ k ∈ range 5,
        (∑ w : Fin 16, if Vt184541 u.val v.val w.val then Kt184541 (typ184541 v w) k else 0) * m.choose k := by
      show (∑ w : Fin 16, if Vt184541 u.val v.val w.val then G184541 (m + 2) v w else 0) = _
      rw [Finset.sum_congr rfl fun w _ => (show (if Vt184541 u.val v.val w.val then
          G184541 (m + 2) v w else 0) = ∑ k ∈ range 5, (if Vt184541 u.val v.val w.val then
          Kt184541 (typ184541 v w) k else 0) * m.choose k by
        split_ifs
        · exact ih v w
        · simp), Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => (Finset.sum_mul _ _ _).symm
    have h2 : G184541 (m + 1 + 2) u v =
        ∑ k ∈ range 5, (Kt184541 (typ184541 u v) k + Kt184541 (typ184541 u v) (k + 1)) * m.choose k := by
      rw [h1]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [step_fact184541 u v k (Finset.mem_range.mp hk)]
    rw [h2]
    have p1 : (m + 1).choose 1 = m.choose 0 + m.choose 1 := Nat.choose_succ_succ' m 0
    have p2 : (m + 1).choose 2 = m.choose 1 + m.choose 2 := Nat.choose_succ_succ' m 1
    have p3 : (m + 1).choose 3 = m.choose 2 + m.choose 3 := Nat.choose_succ_succ' m 2
    have p4 : (m + 1).choose 4 = m.choose 3 + m.choose 4 := Nat.choose_succ_succ' m 3
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, p1, p2, p3, p4,
      Nat.choose_zero_right, top_fact184541 u v]
    ring

theorem D_facts184541 :
    (∑ u : Fin 16, ∑ v : Fin 16, Kt184541 (typ184541 u v) 0) = 193 ∧
    (∑ u : Fin 16, ∑ v : Fin 16, Kt184541 (typ184541 u v) 1) = 147 ∧
    (∑ u : Fin 16, ∑ v : Fin 16, Kt184541 (typ184541 u v) 2) = 50 ∧
    (∑ u : Fin 16, ∑ v : Fin 16, Kt184541 (typ184541 u v) 3) = 8 ∧
    (∑ u : Fin 16, ∑ v : Fin 16, Kt184541 (typ184541 u v) 4) = 1 := by
  decide +kernel

theorem a_one184541 : a 1 = 89 := by
  rw [a_eq_G184541]
  simp only [G_one184541]
  decide +kernel

theorem a_closed184541 (n : ℕ) :
    a (n + 2) = 193 * n.choose 0 + 147 * n.choose 1 + 50 * n.choose 2 + 8 * n.choose 3 + 1 * n.choose 4 := by
  rw [a_eq_G184541]
  simp only [G_closed184541 n]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_add_distrib, ← Finset.sum_mul,
    zero_add]
  obtain ⟨d0, d1, d2, d3, d4⟩ := D_facts184541
  rw [d0, d1, d2, d3, d4]

theorem ch1_184541 (n : ℕ) : (n.choose 1 : ℚ) = n := by simp

theorem ch2_184541 (n : ℕ) : (n.choose 2 : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1).choose 2 = n.choose 1 + n.choose 2 from Nat.choose_succ_succ' n 1,
      Nat.cast_add, ih, ch1_184541]
    push_cast
    ring

theorem ch3_184541 (n : ℕ) : (n.choose 3 : ℚ) = (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1).choose 3 = n.choose 2 + n.choose 3 from Nat.choose_succ_succ' n 2,
      Nat.cast_add, ih, ch2_184541]
    push_cast
    ring

theorem ch4_184541 (n : ℕ) : (n.choose 4 : ℚ) = (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3) / 24 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1).choose 4 = n.choose 3 + n.choose 4 from Nat.choose_succ_succ' n 3,
      Nat.cast_add, ih, ch3_184541]
    push_cast
    ring

theorem closedQ184541 (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = (1 / 24) * (n : ℚ) ^ 4 + (3 / 4) * (n : ℚ) ^ 3 + (383 / 24) * (n : ℚ) ^ 2 + (201 / 4) * (n : ℚ) + 22 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [a_one184541]
    norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [a_closed184541]
    push_cast
    rw [ch1_184541, ch2_184541, ch3_184541, ch4_184541]
    simp only [Nat.choose_zero_right, Nat.cast_one]
    ring

theorem recurrence184541 (n : ℕ) (hn : 6 ≤ n) :
    (a n : ℤ) = 5 * (a (n - 1) : ℤ) - 10 * (a (n - 2) : ℤ) + 10 * (a (n - 3) : ℤ) - 5 * (a (n - 4) : ℤ) + (a (n - 5) : ℤ) := by
  have h : ((a n : ℤ) : ℚ) = ((5 * (a (n - 1) : ℤ) - 10 * (a (n - 2) : ℤ) + 10 * (a (n - 3) : ℤ) - 5 * (a (n - 4) : ℤ) + (a (n - 5) : ℤ) : ℤ) : ℚ) := by
    push_cast
    rw [closedQ184541 n (by omega), closedQ184541 (n - 1) (by omega), closedQ184541 (n - 2) (by omega), closedQ184541 (n - 3) (by omega), closedQ184541 (n - 4) (by omega), closedQ184541 (n - 5) (by omega)]
    push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega]
    ring
  exact_mod_cast h

open PowerSeries in
theorem gen_fun184541 :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  unfold G
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hF
  have key : PowerSeries.mk F * (1 - PowerSeries.X) ^ 5 =
      C 1 * (PowerSeries.mk F * PowerSeries.X ^ 0) - C 5 * (PowerSeries.mk F * PowerSeries.X ^ 1) + C 10 * (PowerSeries.mk F * PowerSeries.X ^ 2) - C 10 * (PowerSeries.mk F * PowerSeries.X ^ 3) + C 5 * (PowerSeries.mk F * PowerSeries.X ^ 4) - C 1 * (PowerSeries.mk F * PowerSeries.X ^ 5) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (PowerSeries.X * (89 - 252 * PowerSeries.X + 265 * PowerSeries.X ^ 2 - 123 * PowerSeries.X ^ 3 + 22 * PowerSeries.X ^ 4) : ℚ⟦X⟧) =
      C 89 * PowerSeries.X ^ 1 - C 252 * PowerSeries.X ^ 2 + C 265 * PowerSeries.X ^ 3 - C 123 * PowerSeries.X ^ 4 + C 22 * PowerSeries.X ^ 5 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 6
  · interval_cases k <;> norm_num [hF, closedQ184541]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
    simp only [show 0 ≤ j + 6 by omega,
      show j + 6 - 0 = j + 6 by omega,
      show 1 ≤ j + 6 by omega,
      show j + 6 - 1 = j + 5 by omega,
      show 2 ≤ j + 6 by omega,
      show j + 6 - 2 = j + 4 by omega,
      show 3 ≤ j + 6 by omega,
      show j + 6 - 3 = j + 3 by omega,
      show 4 ≤ j + 6 by omega,
      show j + 6 - 4 = j + 2 by omega,
      show 5 ≤ j + 6 by omega,
      show j + 6 - 5 = j + 1 by omega,
      show ¬ (j + 6 = 1) by omega,
      show ¬ (j + 6 = 2) by omega,
      show ¬ (j + 6 = 3) by omega,
      show ¬ (j + 6 = 4) by omega,
      show ¬ (j + 6 = 5) by omega,
      show ¬ (j + 1 = 0) by omega,
      show ¬ (j + 2 = 0) by omega,
      show ¬ (j + 3 = 0) by omega,
      show ¬ (j + 4 = 0) by omega,
      show ¬ (j + 5 = 0) by omega,
      show ¬ (j + 6 = 0) by omega,
      if_true, if_false, hF]
    rw [closedQ184541 (j + 6) (by omega), closedQ184541 (j + 5) (by omega), closedQ184541 (j + 4) (by omega), closedQ184541 (j + 3) (by omega), closedQ184541 (j + 2) (by omega), closedQ184541 (j + 1) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a184541.main :=
  ⟨OMA.Helpers.recurrence184541, OMA.Helpers.gen_fun184541, OMA.Helpers.closedQ184541⟩
