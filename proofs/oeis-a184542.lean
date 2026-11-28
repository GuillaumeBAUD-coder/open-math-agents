import OMAStatements.S_oeis_a184542
import Mathlib

/-!
Proof of the conjectures for A184542 ((n+2) X 5 binary arrays whose 3 X 3 subblocks have rows and
columns in lexicographically nondecreasing order).

The condition `Good` of the statement only involves three consecutive rows, so splitting off the
first row (`good_cons184542`) gives a transfer recursion on pairs of rows: `T (m + 1) x y` is the sum
of `T m y z` over the rows `z` with `TriOK x y z`, and `a n` is the sum of `T n x y`. On the
binary codes of rows, `TriOK` becomes a Boolean test `Vt184542` (each window of three columns compares
as numbers, `TriOK_code184542`), and `T` becomes the recursion `G184542`.

The 1024 pairs of codes fall into 7 types (`typ184542`); for `n ≥ 0`,
`G (n + 2) u v = Sum_k Kt (typ u v) k * C(n, k)`, proved by induction using Pascal's rule and the
kernel-checked identities `step_fact184542` (the successors of a pair of type `t` have coefficient
sums `Kt t k + Kt t (k + 1)`). Summing over all pairs gives `a (n + 2)` as a combination of
binomials, which expands to the closed form; `a 1` is checked directly. The recurrence and the
generating function follow by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a184542 Finset

/-- A row of the array. -/
abbrev Row184542 := Fin 5 → Fin 2

theorem good_cons184542 {m : ℕ} (x : Row184542) (B : Fin (m + 2) → Row184542) :
    Good (Fin.cons x B : Fin (m + 3) → Row184542) ↔ TriOK x (B 0) (B 1) ∧ Good B := by
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

instance decTriOK184542 (x y z : Row184542) : Decidable (TriOK x y z) := by
  unfold TriOK Lex3
  infer_instance

/-- The number of ways to continue the rows `x, y` by `m` more rows. -/
noncomputable def T184542 (m : ℕ) (x y : Row184542) : ℕ := by
  classical
  exact ∑ B : Fin m → Row184542,
    if Good (Fin.cons x (Fin.cons y B) : Fin (m + 2) → Row184542) then 1 else 0

theorem T_zero184542 (x y : Row184542) : T184542 0 x y = 1 := by
  classical
  unfold T184542
  rw [Fintype.sum_unique, if_pos]
  intro i j l hj hl
  have := l.isLt
  omega

theorem T_succ184542 (m : ℕ) (x y : Row184542) :
    T184542 (m + 1) x y = ∑ z : Row184542, if TriOK x y z then T184542 m y z else 0 := by
  classical
  unfold T184542
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row184542).symm _
    (fun p => if Good (Fin.cons x (Fin.cons y (Fin.cons p.1 p.2)) : Fin (m + 3) → Row184542)
      then 1 else 0) (fun B => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hv : TriOK x y z
  · rw [if_pos hv]
    refine Finset.sum_congr rfl fun B _ => if_congr ?_ rfl rfl
    rw [good_cons184542]
    simp only [Fin.cons_zero, Fin.cons_one]
    exact and_iff_right hv
  · rw [if_neg hv]
    refine Finset.sum_eq_zero fun B _ => if_neg ?_
    rw [good_cons184542]
    simp only [Fin.cons_zero, Fin.cons_one]
    exact fun h => hv h.1

theorem a_eq184542 (n : ℕ) : a n = ∑ x : Row184542, ∑ y : Row184542, T184542 n x y := by
  classical
  have h1 : a n = ∑ A : Fin (n + 2) → Row184542, if Good A then 1 else 0 := by
    unfold a
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  rw [h1, Fintype.sum_equiv (Fin.consEquiv fun _ => Row184542).symm _
    (fun p => if Good (Fin.cons p.1 p.2 : Fin (n + 2) → Row184542) then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Row184542).symm _
    (fun p => if Good (Fin.cons x (Fin.cons p.1 p.2) : Fin (n + 2) → Row184542) then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  unfold T184542
  exact Finset.sum_congr rfl fun B _ => if_congr Iff.rfl rfl rfl

/-- The row with code `c`: the bits of `c`, most significant first. -/
def row184542 (c : Fin 32) : Row184542 := fun j => ⟨c.val / 2 ^ (4 - j.val) % 2, Nat.mod_lt _ (by norm_num)⟩

theorem row_injective184542 : Function.Injective row184542 := by
  decide +kernel

theorem row_bijective184542 : Function.Bijective row184542 := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨row_injective184542, by simp⟩

theorem lex3_iff184542 : ∀ a b c a' b' c' : Fin 2,
    Lex3 a b c a' b' c' ↔ 4 * a.val + 2 * b.val + c.val ≤ 4 * a'.val + 2 * b'.val + c'.val := by
  unfold Lex3
  decide

/-- The conditions of `TriOK` on the window of columns `t, t + 1, t + 2`. -/
def Win184542 (u v w : Row184542) (t : ℕ) (ht : t + 2 < 5) : Prop :=
  Lex3 (u ⟨t, by omega⟩) (u ⟨t + 1, by omega⟩) (u ⟨t + 2, ht⟩)
      (v ⟨t, by omega⟩) (v ⟨t + 1, by omega⟩) (v ⟨t + 2, ht⟩) ∧
    Lex3 (v ⟨t, by omega⟩) (v ⟨t + 1, by omega⟩) (v ⟨t + 2, ht⟩)
      (w ⟨t, by omega⟩) (w ⟨t + 1, by omega⟩) (w ⟨t + 2, ht⟩) ∧
    Lex3 (u ⟨t, by omega⟩) (v ⟨t, by omega⟩) (w ⟨t, by omega⟩)
      (u ⟨t + 1, by omega⟩) (v ⟨t + 1, by omega⟩) (w ⟨t + 1, by omega⟩) ∧
    Lex3 (u ⟨t + 1, by omega⟩) (v ⟨t + 1, by omega⟩) (w ⟨t + 1, by omega⟩)
      (u ⟨t + 2, ht⟩) (v ⟨t + 2, ht⟩) (w ⟨t + 2, ht⟩)

theorem TriOK_iff184542 (u v w : Row184542) : TriOK u v w ↔ ∀ t (ht : t + 2 < 5), Win184542 u v w t ht := by
  constructor
  · intro h t ht
    exact h ⟨t, by omega⟩ ⟨t + 1, by omega⟩ ⟨t + 2, ht⟩ rfl rfl
  · intro h j j' j'' h1 h2
    have ht : (j : ℕ) + 2 < 5 := by have := j''.isLt; omega
    have e1 : j' = ⟨j + 1, by clear h1 h2; omega⟩ := Fin.ext h1
    have e2 : j'' = ⟨j + 2, ht⟩ := Fin.ext (by rw [h2, h1])
    subst e1 e2
    exact h j ht

/-- Bit `t` of the code `x`, the most significant first. -/
def bt184542 (x t : ℕ) : ℕ := x / 2 ^ (4 - t) % 2

/-- The window test on codes. -/
def WT184542 (u v w t : ℕ) : Bool :=
  decide (4 * bt184542 u t + 2 * bt184542 u (t + 1) + bt184542 u (t + 2) ≤
      4 * bt184542 v t + 2 * bt184542 v (t + 1) + bt184542 v (t + 2)) &&
    decide (4 * bt184542 v t + 2 * bt184542 v (t + 1) + bt184542 v (t + 2) ≤
      4 * bt184542 w t + 2 * bt184542 w (t + 1) + bt184542 w (t + 2)) &&
    decide (4 * bt184542 u t + 2 * bt184542 v t + bt184542 w t ≤
      4 * bt184542 u (t + 1) + 2 * bt184542 v (t + 1) + bt184542 w (t + 1)) &&
    decide (4 * bt184542 u (t + 1) + 2 * bt184542 v (t + 1) + bt184542 w (t + 1) ≤
      4 * bt184542 u (t + 2) + 2 * bt184542 v (t + 2) + bt184542 w (t + 2))

theorem Win_iff184542 (u v w : Fin 32) (t : ℕ) (ht : t + 2 < 5) :
    Win184542 (row184542 u) (row184542 v) (row184542 w) t ht ↔ WT184542 u.val v.val w.val t = true := by
  simp only [Win184542, lex3_iff184542, WT184542, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  rfl

/-- `TriOK` on codes. -/
def Vt184542 (u v w : ℕ) : Bool := WT184542 u v w 0 && WT184542 u v w 1 && WT184542 u v w 2

theorem TriOK_code184542 (u v w : Fin 32) :
    TriOK (row184542 u) (row184542 v) (row184542 w) ↔ Vt184542 u.val v.val w.val = true := by
  rw [TriOK_iff184542]
  simp only [Vt184542, Bool.and_eq_true]
  constructor
  · intro h
    exact ⟨⟨(Win_iff184542 u v w 0 (by norm_num)).1 (h 0 (by norm_num)), (Win_iff184542 u v w 1 (by norm_num)).1 (h 1 (by norm_num))⟩, (Win_iff184542 u v w 2 (by norm_num)).1 (h 2 (by norm_num))⟩
  · rintro ⟨⟨h0, h1⟩, h2⟩ t ht
    have : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact (Win_iff184542 u v w 0 ht).2 h0
    · exact (Win_iff184542 u v w 1 ht).2 h1
    · exact (Win_iff184542 u v w 2 ht).2 h2

/-- The transfer recursion on codes. -/
def G184542 : ℕ → Fin 32 → Fin 32 → ℕ
  | 0, _, _ => 1
  | m + 1, u, v => ∑ w : Fin 32, if Vt184542 u.val v.val w.val then G184542 m v w else 0

theorem T_eq_G184542 (m : ℕ) : ∀ u v : Fin 32, T184542 m (row184542 u) (row184542 v) = G184542 m u v := by
  induction m with
  | zero => intro u v; rw [T_zero184542]; rfl
  | succ m ih =>
    intro u v
    rw [T_succ184542, ← row_bijective184542.sum_comp]
    simp only [G184542]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ih v w]
    exact if_congr (TriOK_code184542 u v w) rfl rfl

theorem a_eq_G184542 (n : ℕ) : a n = ∑ u : Fin 32, ∑ v : Fin 32, G184542 n u v := by
  rw [a_eq184542, ← row_bijective184542.sum_comp]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← row_bijective184542.sum_comp]
  exact Finset.sum_congr rfl fun v _ => T_eq_G184542 n u v

/-- The type of a pair of codes. -/
def TYtab184542 : List (List ℕ) :=
  [[4, 6, 0, 5, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
   [0, 6, 0, 5, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 5, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- The number of continuations of a pair by one row. -/
def L1tab184542 : List (List ℕ) :=
  [[6, 9, 0, 10, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
   [0, 9, 14, 13, 0, 0, 6, 3, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 10, 9, 9, 0, 3, 0, 0, 0, 0, 6, 6, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]

/-- The binomial coefficients of each type. -/
def Kttab184542 : List (List ℕ) := [[0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0], [3, 1, 0, 0, 0, 0], [6, 4, 1, 0, 0, 0], [31, 116, 77, 21, 7, 1], [52, 10, 5, 1, 0, 0], [54, 62, 15, 6, 1, 0]]

def typ184542 (u v : Fin 32) : ℕ := (TYtab184542.getD u.val []).getD v.val 0

def L1184542 (u v : Fin 32) : ℕ := (L1tab184542.getD u.val []).getD v.val 0

def Kt184542 (t k : ℕ) : ℕ := (Kttab184542.getD t []).getD k 0

theorem L1_fact184542 : ∀ u v : Fin 32,
    (∑ w : Fin 32, if Vt184542 u.val v.val w.val then 1 else 0) = L1184542 u v := by
  decide +kernel

theorem base_fact184542 : ∀ u v : Fin 32,
    (∑ w : Fin 32, if Vt184542 u.val v.val w.val then L1184542 v w else 0) = Kt184542 (typ184542 u v) 0 := by
  decide +kernel

theorem top_fact184542 : ∀ u v : Fin 32, Kt184542 (typ184542 u v) 6 = 0 := by
  decide +kernel

theorem step_fact0_184542 : ∀ u v : Fin 32,
    (∑ w : Fin 32, if Vt184542 u.val v.val w.val then Kt184542 (typ184542 v w) 0 else 0) =
      Kt184542 (typ184542 u v) 0 + Kt184542 (typ184542 u v) 1 := by
  decide +kernel

theorem step_fact1_184542 : ∀ u v : Fin 32,
    (∑ w : Fin 32, if Vt184542 u.val v.val w.val then Kt184542 (typ184542 v w) 1 else 0) =
      Kt184542 (typ184542 u v) 1 + Kt184542 (typ184542 u v) 2 := by
  decide +kernel

theorem step_fact2_184542 : ∀ u v : Fin 32,
    (∑ w : Fin 32, if Vt184542 u.val v.val w.val then Kt184542 (typ184542 v w) 2 else 0) =
      Kt184542 (typ184542 u v) 2 + Kt184542 (typ184542 u v) 3 := by
  decide +kernel

theorem step_fact3_184542 : ∀ u v : Fin 32,
    (∑ w : Fin 32, if Vt184542 u.val v.val w.val then Kt184542 (typ184542 v w) 3 else 0) =
      Kt184542 (typ184542 u v) 3 + Kt184542 (typ184542 u v) 4 := by
  decide +kernel

theorem step_fact4_184542 : ∀ u v : Fin 32,
    (∑ w : Fin 32, if Vt184542 u.val v.val w.val then Kt184542 (typ184542 v w) 4 else 0) =
      Kt184542 (typ184542 u v) 4 + Kt184542 (typ184542 u v) 5 := by
  decide +kernel

theorem step_fact5_184542 : ∀ u v : Fin 32,
    (∑ w : Fin 32, if Vt184542 u.val v.val w.val then Kt184542 (typ184542 v w) 5 else 0) =
      Kt184542 (typ184542 u v) 5 + Kt184542 (typ184542 u v) 6 := by
  decide +kernel

theorem step_fact184542 (u v : Fin 32) (k : ℕ) (hk : k < 6) :
    (∑ w : Fin 32, if Vt184542 u.val v.val w.val then Kt184542 (typ184542 v w) k else 0) =
      Kt184542 (typ184542 u v) k + Kt184542 (typ184542 u v) (k + 1) := by
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl
  · exact step_fact0_184542 u v
  · exact step_fact1_184542 u v
  · exact step_fact2_184542 u v
  · exact step_fact3_184542 u v
  · exact step_fact4_184542 u v
  · exact step_fact5_184542 u v

theorem G_one184542 (u v : Fin 32) : G184542 1 u v = L1184542 u v := by
  rw [← L1_fact184542 u v]
  rfl

theorem G_two184542 (u v : Fin 32) : G184542 2 u v = Kt184542 (typ184542 u v) 0 := by
  rw [← base_fact184542 u v]
  show (∑ w : Fin 32, if Vt184542 u.val v.val w.val then G184542 1 v w else 0) = _
  simp only [G_one184542]

theorem G_closed184542 (m : ℕ) :
    ∀ u v : Fin 32, G184542 (m + 2) u v = ∑ k ∈ range 6, Kt184542 (typ184542 u v) k * m.choose k := by
  induction m with
  | zero =>
    intro u v
    rw [G_two184542]
    simp [Finset.sum_range_succ]
  | succ m ih =>
    intro u v
    have h1 : G184542 (m + 1 + 2) u v = ∑ k ∈ range 6,
        (∑ w : Fin 32, if Vt184542 u.val v.val w.val then Kt184542 (typ184542 v w) k else 0) * m.choose k := by
      show (∑ w : Fin 32, if Vt184542 u.val v.val w.val then G184542 (m + 2) v w else 0) = _
      rw [Finset.sum_congr rfl fun w _ => (show (if Vt184542 u.val v.val w.val then
          G184542 (m + 2) v w else 0) = ∑ k ∈ range 6, (if Vt184542 u.val v.val w.val then
          Kt184542 (typ184542 v w) k else 0) * m.choose k by
        split_ifs
        · exact ih v w
        · simp), Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => (Finset.sum_mul _ _ _).symm
    have h2 : G184542 (m + 1 + 2) u v =
        ∑ k ∈ range 6, (Kt184542 (typ184542 u v) k + Kt184542 (typ184542 u v) (k + 1)) * m.choose k := by
      rw [h1]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [step_fact184542 u v k (Finset.mem_range.mp hk)]
    rw [h2]
    have p1 : (m + 1).choose 1 = m.choose 0 + m.choose 1 := Nat.choose_succ_succ' m 0
    have p2 : (m + 1).choose 2 = m.choose 1 + m.choose 2 := Nat.choose_succ_succ' m 1
    have p3 : (m + 1).choose 3 = m.choose 2 + m.choose 3 := Nat.choose_succ_succ' m 2
    have p4 : (m + 1).choose 4 = m.choose 3 + m.choose 4 := Nat.choose_succ_succ' m 3
    have p5 : (m + 1).choose 5 = m.choose 4 + m.choose 5 := Nat.choose_succ_succ' m 4
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, p1, p2, p3, p4, p5,
      Nat.choose_zero_right, top_fact184542 u v]
    ring

theorem D_facts184542 :
    (∑ u : Fin 32, ∑ v : Fin 32, Kt184542 (typ184542 u v) 0) = 340 ∧
    (∑ u : Fin 32, ∑ v : Fin 32, Kt184542 (typ184542 u v) 1) = 291 ∧
    (∑ u : Fin 32, ∑ v : Fin 32, Kt184542 (typ184542 u v) 2) = 126 ∧
    (∑ u : Fin 32, ∑ v : Fin 32, Kt184542 (typ184542 u v) 3) = 36 ∧
    (∑ u : Fin 32, ∑ v : Fin 32, Kt184542 (typ184542 u v) 4) = 9 ∧
    (∑ u : Fin 32, ∑ v : Fin 32, Kt184542 (typ184542 u v) 5) = 1 := by
  decide +kernel

theorem a_one184542 : a 1 = 147 := by
  rw [a_eq_G184542]
  simp only [G_one184542]
  decide +kernel

theorem a_closed184542 (n : ℕ) :
    a (n + 2) = 340 * n.choose 0 + 291 * n.choose 1 + 126 * n.choose 2 + 36 * n.choose 3 + 9 * n.choose 4 + 1 * n.choose 5 := by
  rw [a_eq_G184542]
  simp only [G_closed184542 n]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Finset.sum_add_distrib, ← Finset.sum_mul,
    zero_add]
  obtain ⟨d0, d1, d2, d3, d4, d5⟩ := D_facts184542
  rw [d0, d1, d2, d3, d4, d5]

theorem ch1_184542 (n : ℕ) : (n.choose 1 : ℚ) = n := by simp

theorem ch2_184542 (n : ℕ) : (n.choose 2 : ℚ) = (n : ℚ) * ((n : ℚ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1).choose 2 = n.choose 1 + n.choose 2 from Nat.choose_succ_succ' n 1,
      Nat.cast_add, ih, ch1_184542]
    push_cast
    ring

theorem ch3_184542 (n : ℕ) : (n.choose 3 : ℚ) = (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1).choose 3 = n.choose 2 + n.choose 3 from Nat.choose_succ_succ' n 2,
      Nat.cast_add, ih, ch2_184542]
    push_cast
    ring

theorem ch4_184542 (n : ℕ) : (n.choose 4 : ℚ) = (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3) / 24 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1).choose 4 = n.choose 3 + n.choose 4 from Nat.choose_succ_succ' n 3,
      Nat.cast_add, ih, ch3_184542]
    push_cast
    ring

theorem ch5_184542 (n : ℕ) : (n.choose 5 : ℚ) = (n : ℚ) * ((n : ℚ) - 1) * ((n : ℚ) - 2) * ((n : ℚ) - 3) * ((n : ℚ) - 4) / 120 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show (n + 1).choose 5 = n.choose 4 + n.choose 5 from Nat.choose_succ_succ' n 4,
      Nat.cast_add, ih, ch4_184542]
    push_cast
    ring

theorem closedQ184542 (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = (1 / 120) * (n : ℚ) ^ 5 + (5 / 24) * (n : ℚ) ^ 4 + (49 / 24) * (n : ℚ) ^ 3 + (739 / 24) * (n : ℚ) ^ 2 + (1659 / 20) * (n : ℚ) + 31 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [a_one184542]
    norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [a_closed184542]
    push_cast
    rw [ch1_184542, ch2_184542, ch3_184542, ch4_184542, ch5_184542]
    simp only [Nat.choose_zero_right, Nat.cast_one]
    ring

theorem recurrence184542 (n : ℕ) (hn : 7 ≤ n) :
    (a n : ℤ) = 6 * (a (n - 1) : ℤ) - 15 * (a (n - 2) : ℤ) + 20 * (a (n - 3) : ℤ) - 15 * (a (n - 4) : ℤ) + 6 * (a (n - 5) : ℤ) - (a (n - 6) : ℤ) := by
  have h : ((a n : ℤ) : ℚ) = ((6 * (a (n - 1) : ℤ) - 15 * (a (n - 2) : ℤ) + 20 * (a (n - 3) : ℤ) - 15 * (a (n - 4) : ℤ) + 6 * (a (n - 5) : ℤ) - (a (n - 6) : ℤ) : ℤ) : ℚ) := by
    push_cast
    rw [closedQ184542 n (by omega), closedQ184542 (n - 1) (by omega), closedQ184542 (n - 2) (by omega), closedQ184542 (n - 3) (by omega), closedQ184542 (n - 4) (by omega), closedQ184542 (n - 5) (by omega), closedQ184542 (n - 6) (by omega)]
    push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega]
    ring
  exact_mod_cast h

open PowerSeries in
theorem gen_fun184542 :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  unfold G
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  set F : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hF
  have key : PowerSeries.mk F * (1 - PowerSeries.X) ^ 6 =
      C 1 * (PowerSeries.mk F * PowerSeries.X ^ 0) - C 6 * (PowerSeries.mk F * PowerSeries.X ^ 1) + C 15 * (PowerSeries.mk F * PowerSeries.X ^ 2) - C 20 * (PowerSeries.mk F * PowerSeries.X ^ 3) + C 15 * (PowerSeries.mk F * PowerSeries.X ^ 4) - C 6 * (PowerSeries.mk F * PowerSeries.X ^ 5) + C 1 * (PowerSeries.mk F * PowerSeries.X ^ 6) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (PowerSeries.X * (147 - 542 * PowerSeries.X + 796 * PowerSeries.X ^ 2 - 578 * PowerSeries.X ^ 3 + 209 * PowerSeries.X ^ 4 - 31 * PowerSeries.X ^ 5) : ℚ⟦X⟧) =
      C 147 * PowerSeries.X ^ 1 - C 542 * PowerSeries.X ^ 2 + C 796 * PowerSeries.X ^ 3 - C 578 * PowerSeries.X ^ 4 + C 209 * PowerSeries.X ^ 5 - C 31 * PowerSeries.X ^ 6 := by
    simp only [map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 7
  · interval_cases k <;> norm_num [hF, closedQ184542]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 7 := ⟨k - 7, by omega⟩
    simp only [show 0 ≤ j + 7 by omega,
      show j + 7 - 0 = j + 7 by omega,
      show 1 ≤ j + 7 by omega,
      show j + 7 - 1 = j + 6 by omega,
      show 2 ≤ j + 7 by omega,
      show j + 7 - 2 = j + 5 by omega,
      show 3 ≤ j + 7 by omega,
      show j + 7 - 3 = j + 4 by omega,
      show 4 ≤ j + 7 by omega,
      show j + 7 - 4 = j + 3 by omega,
      show 5 ≤ j + 7 by omega,
      show j + 7 - 5 = j + 2 by omega,
      show 6 ≤ j + 7 by omega,
      show j + 7 - 6 = j + 1 by omega,
      show ¬ (j + 7 = 1) by omega,
      show ¬ (j + 7 = 2) by omega,
      show ¬ (j + 7 = 3) by omega,
      show ¬ (j + 7 = 4) by omega,
      show ¬ (j + 7 = 5) by omega,
      show ¬ (j + 7 = 6) by omega,
      show ¬ (j + 1 = 0) by omega,
      show ¬ (j + 2 = 0) by omega,
      show ¬ (j + 3 = 0) by omega,
      show ¬ (j + 4 = 0) by omega,
      show ¬ (j + 5 = 0) by omega,
      show ¬ (j + 6 = 0) by omega,
      show ¬ (j + 7 = 0) by omega,
      if_true, if_false, hF]
    rw [closedQ184542 (j + 7) (by omega), closedQ184542 (j + 6) (by omega), closedQ184542 (j + 5) (by omega), closedQ184542 (j + 4) (by omega), closedQ184542 (j + 3) (by omega), closedQ184542 (j + 2) (by omega), closedQ184542 (j + 1) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a184542.main :=
  ⟨OMA.Helpers.recurrence184542, OMA.Helpers.gen_fun184542, OMA.Helpers.closedQ184542⟩
