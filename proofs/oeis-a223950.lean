import OMAStatements.S_oeis_a223950

/-!
Proof of the conjectures of A223950 (3 X n binary arrays with diagonals and antidiagonals unimodal and rows nondecreasing).

An array is a sequence of columns. It is good iff every two consecutive columns satisfy
`BlockOK` and every three consecutive columns satisfy `TriOK` (`good_iff`). Removing the first
column gives a transfer recursion on pairs of consecutive columns: if `T m x y` counts the ways
to continue the columns `x, y` by `m` more columns, then `T 0 x y` is 1 or 0 as `BlockOK x y`
holds or not, `T (m + 1) x y` sums `T m y z` over the `z` with `BlockOK x y` and `TriOK x y z`,
and `a (m + 2)` is the sum of all `T m x y`.

Columns are coded by 0, ..., 7 (bit `2 - i` of the code is the entry in row `i`). On codes, both
conditions become table lookups (`Bt`, `Tt`), checked once against the definitions, and `G` is
the recursion on codes. For `m ≥ 2`, six times `G m u v` is a cubic in `m` whose coefficients are
listed in the tables `K3, K2, K1, K0`; this is proved by induction from `m = 2`, where the step
is a finite check of four coefficient identities for each pair of codes. Summing gives
`6 a(m + 2) = 4 m^3 + 33 m^2 + 125 m + 162` for `m ≥ 2`, the cases `m = 0, 1` are computed
directly, and the recurrence and the generating function follow by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a223950 Finset

/-- A column of the array. -/
abbrev Cola223950 := Fin 3 → Fin 2

instance decBlockOKa223950 (u v : Cola223950) : Decidable (BlockOK u v) := by
  unfold BlockOK
  infer_instance

instance decTriOKa223950 (u v w : Cola223950) : Decidable (TriOK u v w) := by
  unfold TriOK
  infer_instance

/-- The conditions of the statement with natural-number indices. -/
def Chna223950 {m : ℕ} (A : Fin m → Cola223950) : Prop :=
  (∀ (i : ℕ) (h : i + 1 < m), BlockOK (A ⟨i, by omega⟩) (A ⟨i + 1, h⟩)) ∧
    ∀ (i : ℕ) (h : i + 2 < m), TriOK (A ⟨i, by omega⟩) (A ⟨i + 1, by omega⟩) (A ⟨i + 2, h⟩)

theorem good_iffa223950 {m : ℕ} (A : Fin m → Cola223950) : Good A ↔ Chna223950 A := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i hi => h1 _ _ rfl, fun i hi => h2 _ _ _ rfl rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hj => ?_, fun i j l hj hl => ?_⟩
    · obtain ⟨i, hi⟩ := i
      obtain ⟨j, hj'⟩ := j
      dsimp only at hj
      subst hj
      exact h1 i hj'
    · obtain ⟨i, hi⟩ := i
      obtain ⟨j, hj'⟩ := j
      obtain ⟨l, hl'⟩ := l
      dsimp only at hj hl
      subst hj hl
      exact h2 i hl'

theorem chn_consa223950 {m : ℕ} (x : Cola223950) (B : Fin (m + 2) → Cola223950) :
    Chna223950 (Fin.cons x B : Fin (m + 3) → Cola223950) ↔
      (BlockOK x (B ⟨0, by omega⟩) ∧ TriOK x (B ⟨0, by omega⟩) (B ⟨1, by omega⟩)) ∧
        Chna223950 B := by
  constructor
  · rintro ⟨h1, h2⟩
    have a1 := h1 0 (by omega)
    have a2 := h2 0 (by omega)
    exact ⟨⟨a1, a2⟩, fun i hi => h1 (i + 1) (by omega), fun i hi => h2 (i + 1) (by omega)⟩
  · rintro ⟨⟨h0, h0'⟩, h1, h2⟩
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · cases i with
      | zero => exact h0
      | succ i => exact h1 i (by omega)
    · cases i with
      | zero => exact h0'
      | succ i => exact h2 i (by omega)

/-- The number of ways to continue the columns `x, y` by `m` more columns. -/
noncomputable def Ta223950 (m : ℕ) (x y : Cola223950) : ℕ := by
  classical
  exact ∑ B : Fin m → Cola223950,
    if Chna223950 (Fin.cons x (Fin.cons y B) : Fin (m + 2) → Cola223950) then 1 else 0

theorem T_zeroa223950 (x y : Cola223950) : Ta223950 0 x y = if BlockOK x y then 1 else 0 := by
  classical
  unfold Ta223950
  rw [Fintype.sum_unique]
  refine if_congr ⟨fun h => ?_, fun h => ⟨fun i hi => ?_, fun i hi => ?_⟩⟩ rfl rfl
  · have a1 := h.1 0 (by omega)
    exact a1
  · obtain rfl : i = 0 := by omega
    exact h
  · omega

theorem T_succa223950 (m : ℕ) (x y : Cola223950) :
    Ta223950 (m + 1) x y =
      ∑ z : Cola223950, if BlockOK x y ∧ TriOK x y z then Ta223950 m y z else 0 := by
  classical
  unfold Ta223950
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Cola223950).symm _
    (fun p => if Chna223950 (Fin.cons x (Fin.cons y (Fin.cons p.1 p.2)) : Fin (m + 3) → Cola223950)
      then 1 else 0) (fun B => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hv : BlockOK x y ∧ TriOK x y z
  · rw [if_pos hv]
    refine Finset.sum_congr rfl fun B _ => if_congr ?_ rfl rfl
    rw [chn_consa223950]
    exact and_iff_right hv
  · rw [if_neg hv]
    refine Finset.sum_eq_zero fun B _ => if_neg ?_
    rw [chn_consa223950]
    exact fun h => hv h.1

theorem a_eqa223950 (m : ℕ) : a (m + 2) = ∑ x : Cola223950, ∑ y : Cola223950, Ta223950 m x y := by
  classical
  have h1 : a (m + 2) = ∑ A : Fin (m + 2) → Cola223950, if Chna223950 A then 1 else 0 := by
    unfold a
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
    exact Finset.sum_congr rfl fun A _ => if_congr (good_iffa223950 A) rfl rfl
  rw [h1, Fintype.sum_equiv (Fin.consEquiv fun _ => Cola223950).symm _
    (fun p => if Chna223950 (Fin.cons p.1 p.2 : Fin (m + 2) → Cola223950) then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Cola223950).symm _
    (fun p => if Chna223950 (Fin.cons x (Fin.cons p.1 p.2) : Fin (m + 2) → Cola223950) then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  rfl

theorem a_onea223950 : a 1 = 8 := by
  have h : ∀ x : Fin 1 → Cola223950, Good x := fun x =>
    ⟨fun i j hj => by have := j.isLt; omega, fun i j l hj hl => by have := l.isLt; omega⟩
  unfold a
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv h), Nat.card_eq_fintype_card]
  simp

/-- The column with code `c`: entry `i` is bit `2 - i` of `c`. -/
def cola223950 (c : Fin 8) : Cola223950 :=
  fun i => ⟨c.val / 2 ^ (2 - i.val) % 2, Nat.mod_lt _ (by norm_num)⟩

theorem col_bijectivea223950 : Function.Bijective cola223950 := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨by decide, by simp⟩

/-- `BlockOK` on codes, as a table. -/
def Bta223950 (u v : Fin 8) : Bool := Nat.beq (9277592187330931455 / 2 ^ (8 * u.val + v.val) % 2) 1

/-- `TriOK` on codes, as a table. -/
def Tta223950 (u v w : Fin 8) : Bool :=
  Nat.beq (13407607357598192597685115344168081630849823577416422865060604137431599510322902081976043692212823867195473238976839782427568279653561763649945094603145215 / 2 ^ (64 * u.val + 8 * v.val + w.val) % 2) 1

theorem Bt_iffa223950 : ∀ u v : Fin 8, BlockOK (cola223950 u) (cola223950 v) ↔ Bta223950 u v = true := by
  decide +kernel

theorem Tt_iffa223950 : ∀ u v w : Fin 8,
    TriOK (cola223950 u) (cola223950 v) (cola223950 w) ↔ Tta223950 u v w = true := by
  decide +kernel

/-- The transfer recursion on codes. -/
def Ga223950 : ℕ → Fin 8 → Fin 8 → ℕ
  | 0, u, v => if Bta223950 u v then 1 else 0
  | m + 1, u, v => ∑ w : Fin 8, if Bta223950 u v && Tta223950 u v w then Ga223950 m v w else 0

theorem T_eq_Ga223950 (m : ℕ) : ∀ u v : Fin 8, Ta223950 m (cola223950 u) (cola223950 v) = Ga223950 m u v := by
  induction m with
  | zero =>
    intro u v
    rw [T_zeroa223950]
    exact if_congr (Bt_iffa223950 u v) rfl rfl
  | succ m ih =>
    intro u v
    rw [T_succa223950, ← col_bijectivea223950.sum_comp]
    simp only [Ga223950]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ih v w]
    refine if_congr ?_ rfl rfl
    rw [Bt_iffa223950, Tt_iffa223950, Bool.and_eq_true]

theorem a_eq_Ga223950 (m : ℕ) : a (m + 2) = ∑ u : Fin 8, ∑ v : Fin 8, Ga223950 m u v := by
  rw [a_eqa223950, ← col_bijectivea223950.sum_comp]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← col_bijectivea223950.sum_comp]
  exact Finset.sum_congr rfl fun v _ => T_eq_Ga223950 m u v

/-- Coefficients of `m ^ 3` of six times `G m u v` (`m ≥ 2`), indexed by `8 u + v`. -/
def K3a223950 : List ℤ := [4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Coefficients of `m ^ 2`. -/
def K2a223950 : List ℤ := [9, 3, 6, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Coefficients of `m`. -/
def K1a223950 : List ℤ := [41, 3, 12, 6, 3, 0, 6, 0, 0, 3, 0, 6, 0, 0, 0, 0, 0, 0, 12, 6, 0, 0, 6, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Constant coefficients. -/
def K0a223950 : List ℤ := [12, 12, 6, 6, 12, 6, 6, 6, 0, 6, 0, 6, 0, 0, 0, 6, 0, 0, 6, 6, 0, 0, 6, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 0, 6, 0, 6, 6, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 6, 6, 0, 0, 0, 0, 0, 0, 0, 6]

def c3a223950 (u v : Fin 8) : ℤ := K3a223950.getD (8 * u.val + v.val) 0
def c2a223950 (u v : Fin 8) : ℤ := K2a223950.getD (8 * u.val + v.val) 0
def c1a223950 (u v : Fin 8) : ℤ := K1a223950.getD (8 * u.val + v.val) 0
def c0a223950 (u v : Fin 8) : ℤ := K0a223950.getD (8 * u.val + v.val) 0

/-- Six times `G m u v` for `m ≥ 2`. -/
def Pa223950 (u v : Fin 8) (m : ℤ) : ℤ :=
  c3a223950 u v * m ^ 3 + c2a223950 u v * m ^ 2 + c1a223950 u v * m + c0a223950 u v

/-- The induction step of `G_closed`, coefficient by coefficient. -/
theorem step_factsa223950 : ∀ u v : Fin 8,
    (∑ w : Fin 8, if Bta223950 u v && Tta223950 u v w then c3a223950 v w else 0) = c3a223950 u v ∧
    (∑ w : Fin 8, if Bta223950 u v && Tta223950 u v w then c2a223950 v w else 0) =
      3 * c3a223950 u v + c2a223950 u v ∧
    (∑ w : Fin 8, if Bta223950 u v && Tta223950 u v w then c1a223950 v w else 0) =
      3 * c3a223950 u v + 2 * c2a223950 u v + c1a223950 u v ∧
    (∑ w : Fin 8, if Bta223950 u v && Tta223950 u v w then c0a223950 v w else 0) =
      c3a223950 u v + c2a223950 u v + c1a223950 u v + c0a223950 u v := by
  decide +kernel

theorem base_factsa223950 : ∀ u v : Fin 8, 6 * (Ga223950 2 u v : ℤ) = Pa223950 u v 2 := by
  decide +kernel

theorem G_closeda223950 (m : ℕ) (hm : 2 ≤ m) :
    ∀ u v : Fin 8, 6 * (Ga223950 m u v : ℤ) = Pa223950 u v m := by
  induction m, hm using Nat.le_induction with
  | base => exact base_factsa223950
  | succ m hm ih =>
    intro u v
    have hsum : 6 * (Ga223950 (m + 1) u v : ℤ) =
        ∑ w : Fin 8, if Bta223950 u v && Tta223950 u v w then Pa223950 v w m else 0 := by
      rw [Ga223950]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      split_ifs
      · exact ih v w
      · simp
    rw [hsum]
    have hP : ∀ w : Fin 8, (if Bta223950 u v && Tta223950 u v w then Pa223950 v w m else 0) =
        (if Bta223950 u v && Tta223950 u v w then c3a223950 v w else 0) * (m : ℤ) ^ 3 +
        (if Bta223950 u v && Tta223950 u v w then c2a223950 v w else 0) * (m : ℤ) ^ 2 +
        (if Bta223950 u v && Tta223950 u v w then c1a223950 v w else 0) * (m : ℤ) +
        (if Bta223950 u v && Tta223950 u v w then c0a223950 v w else 0) := by
      intro w
      split_ifs <;> simp [Pa223950]
    simp only [hP, Finset.sum_add_distrib, ← Finset.sum_mul]
    obtain ⟨h3, h2, h1, h0⟩ := step_factsa223950 u v
    rw [h3, h2, h1, h0]
    unfold Pa223950
    push_cast
    ring

theorem sum_factsa223950 :
    (∑ u : Fin 8, ∑ v : Fin 8, c3a223950 u v) = 4 ∧
    (∑ u : Fin 8, ∑ v : Fin 8, c2a223950 u v) = 33 ∧
    (∑ u : Fin 8, ∑ v : Fin 8, c1a223950 u v) = 125 ∧
    (∑ u : Fin 8, ∑ v : Fin 8, c0a223950 u v) = 162 := by
  decide +kernel

theorem small_factsa223950 :
    (∑ u : Fin 8, ∑ v : Fin 8, Ga223950 0 u v) = 27 ∧
    (∑ u : Fin 8, ∑ v : Fin 8, Ga223950 1 u v) = 54 := by
  decide +kernel

theorem closed_ma223950 (m : ℕ) :
    6 * (a (m + 2) : ℤ) = 4 * (m : ℤ) ^ 3 + 33 * (m : ℤ) ^ 2 + 125 * (m : ℤ) + 162 := by
  rcases Nat.lt_or_ge m 2 with h | h
  · rw [a_eq_Ga223950]
    obtain ⟨h0, h1⟩ := small_factsa223950
    interval_cases m
    · rw [h0] <;> norm_num
    · rw [h1] <;> norm_num
  · rw [a_eq_Ga223950]
    push_cast
    simp only [Finset.mul_sum, G_closeda223950 m h]
    simp only [Pa223950, Finset.sum_add_distrib, ← Finset.sum_mul]
    obtain ⟨h3, h2, h1, h0⟩ := sum_factsa223950
    rw [h3, h2, h1, h0] <;> ring

theorem closedQa223950 (n : ℕ) (hn : 2 ≤ n) :
    (a n : ℚ) = (2 / 3) * (n : ℚ) ^ 3 + (3 / 2) * (n : ℚ) ^ 2 + (41 / 6) * (n : ℚ) + 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h : ((6 * (a (m + 2) : ℤ) : ℤ) : ℚ) =
      ((4 * (m : ℤ) ^ 3 + 33 * (m : ℤ) ^ 2 + 125 * (m : ℤ) + 162 : ℤ) : ℚ) := by
    rw [closed_ma223950 m]
  push_cast at h ⊢
  linarith

theorem recurrencea223950 (n : ℕ) (hn : 6 ≤ n) :
    (a n : ℤ) = 4 * (a (n - 1) : ℤ) - 6 * (a (n - 2) : ℤ) + 4 * (a (n - 3) : ℤ) - (a (n - 4) : ℤ) := by
  have hQ : (a n : ℚ) = 4 * (a (n - 1) : ℚ) - 6 * (a (n - 2) : ℚ) + 4 * (a (n - 3) : ℚ) -
      (a (n - 4) : ℚ) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
    rw [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega,
      show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega]
    rw [closedQa223950 (k + 6) (by omega), closedQa223950 (k + 5) (by omega),
      closedQa223950 (k + 4) (by omega), closedQa223950 (k + 3) (by omega),
      closedQa223950 (k + 2) (by omega)]
    push_cast
    ring
  exact_mod_cast hQ

open PowerSeries in
theorem gen_funa223950 :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  unfold G
  have hD : constantCoeff ((1 - X : ℚ⟦X⟧) ^ 4) ≠ 0 := by
    simp
  rw [PowerSeries.eq_mul_inv_iff_mul_eq hD]
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have key : A * (1 - X) ^ 4 =
      A * X ^ 0 - C (4 : ℚ) * (A * X ^ 1) + C (6 : ℚ) * (A * X ^ 2) - C (4 : ℚ) * (A * X ^ 3) +
        A * X ^ 4 := by
    simp only [map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (8 - 5 * X - 6 * X ^ 2 + 10 * X ^ 3 - 3 * X ^ 4) =
      C (8 : ℚ) * X ^ 1 - C (5 : ℚ) * X ^ 2 - C (6 : ℚ) * X ^ 3 + C (10 : ℚ) * X ^ 4 - C (3 : ℚ) * X ^ 5 := by
    simp only [map_ofNat, map_one]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, hA, coeff_mk]
  have h1 := a_onea223950
  by_cases hk : k < 6
  · interval_cases k <;> norm_num [closedQa223950, h1]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
    simp only [show 0 ≤ j + 6 by omega, show 1 ≤ j + 6 by omega, show 2 ≤ j + 6 by omega,
      show 3 ≤ j + 6 by omega, show 4 ≤ j + 6 by omega, show 5 ≤ j + 6 by omega,
      show j + 6 - 0 = j + 6 by omega, show j + 6 - 1 = j + 5 by omega,
      show j + 6 - 2 = j + 4 by omega, show j + 6 - 3 = j + 3 by omega,
      show j + 6 - 4 = j + 2 by omega,
      show ¬ (j + 6 = 0) by omega, show ¬ (j + 5 = 0) by omega, show ¬ (j + 4 = 0) by omega,
      show ¬ (j + 3 = 0) by omega, show ¬ (j + 2 = 0) by omega,
      if_true, if_false]
    rw [closedQa223950 (j + 6) (by omega), closedQa223950 (j + 5) (by omega),
      closedQa223950 (j + 4) (by omega), closedQa223950 (j + 3) (by omega),
      closedQa223950 (j + 2) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a223950.main :=
  ⟨OMA.Helpers.recurrencea223950, OMA.Helpers.gen_funa223950, OMA.Helpers.closedQa223950⟩
