import OMAStatements.S_oeis_a224134

/-!
Proof of the conjectures of A224134 (3 X n binary arrays with rows nondecreasing and antidiagonals unimodal).

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
`6 a(m + 2) = 4 m^3 + 39 m^2 + 143 m + 162` for `m ≥ 2`, the cases `m = 0, 1` are computed
directly, and the recurrence and the generating function follow by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a224134 Finset

/-- A column of the array. -/
abbrev Cola224134 := Fin 3 → Fin 2

instance decBlockOKa224134 (u v : Cola224134) : Decidable (BlockOK u v) := by
  unfold BlockOK
  infer_instance

instance decTriOKa224134 (u v w : Cola224134) : Decidable (TriOK u v w) := by
  unfold TriOK
  infer_instance

/-- The conditions of the statement with natural-number indices. -/
def Chna224134 {m : ℕ} (A : Fin m → Cola224134) : Prop :=
  (∀ (i : ℕ) (h : i + 1 < m), BlockOK (A ⟨i, by omega⟩) (A ⟨i + 1, h⟩)) ∧
    ∀ (i : ℕ) (h : i + 2 < m), TriOK (A ⟨i, by omega⟩) (A ⟨i + 1, by omega⟩) (A ⟨i + 2, h⟩)

theorem good_iffa224134 {m : ℕ} (A : Fin m → Cola224134) : Good A ↔ Chna224134 A := by
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

theorem chn_consa224134 {m : ℕ} (x : Cola224134) (B : Fin (m + 2) → Cola224134) :
    Chna224134 (Fin.cons x B : Fin (m + 3) → Cola224134) ↔
      (BlockOK x (B ⟨0, by omega⟩) ∧ TriOK x (B ⟨0, by omega⟩) (B ⟨1, by omega⟩)) ∧
        Chna224134 B := by
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
noncomputable def Ta224134 (m : ℕ) (x y : Cola224134) : ℕ := by
  classical
  exact ∑ B : Fin m → Cola224134,
    if Chna224134 (Fin.cons x (Fin.cons y B) : Fin (m + 2) → Cola224134) then 1 else 0

theorem T_zeroa224134 (x y : Cola224134) : Ta224134 0 x y = if BlockOK x y then 1 else 0 := by
  classical
  unfold Ta224134
  rw [Fintype.sum_unique]
  refine if_congr ⟨fun h => ?_, fun h => ⟨fun i hi => ?_, fun i hi => ?_⟩⟩ rfl rfl
  · have a1 := h.1 0 (by omega)
    exact a1
  · obtain rfl : i = 0 := by omega
    exact h
  · omega

theorem T_succa224134 (m : ℕ) (x y : Cola224134) :
    Ta224134 (m + 1) x y =
      ∑ z : Cola224134, if BlockOK x y ∧ TriOK x y z then Ta224134 m y z else 0 := by
  classical
  unfold Ta224134
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Cola224134).symm _
    (fun p => if Chna224134 (Fin.cons x (Fin.cons y (Fin.cons p.1 p.2)) : Fin (m + 3) → Cola224134)
      then 1 else 0) (fun B => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hv : BlockOK x y ∧ TriOK x y z
  · rw [if_pos hv]
    refine Finset.sum_congr rfl fun B _ => if_congr ?_ rfl rfl
    rw [chn_consa224134]
    exact and_iff_right hv
  · rw [if_neg hv]
    refine Finset.sum_eq_zero fun B _ => if_neg ?_
    rw [chn_consa224134]
    exact fun h => hv h.1

theorem a_eqa224134 (m : ℕ) : a (m + 2) = ∑ x : Cola224134, ∑ y : Cola224134, Ta224134 m x y := by
  classical
  have h1 : a (m + 2) = ∑ A : Fin (m + 2) → Cola224134, if Chna224134 A then 1 else 0 := by
    unfold a
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
    exact Finset.sum_congr rfl fun A _ => if_congr (good_iffa224134 A) rfl rfl
  rw [h1, Fintype.sum_equiv (Fin.consEquiv fun _ => Cola224134).symm _
    (fun p => if Chna224134 (Fin.cons p.1 p.2 : Fin (m + 2) → Cola224134) then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Cola224134).symm _
    (fun p => if Chna224134 (Fin.cons x (Fin.cons p.1 p.2) : Fin (m + 2) → Cola224134) then 1 else 0)
    (fun A => by simp), Fintype.sum_prod_type]
  rfl

theorem a_onea224134 : a 1 = 8 := by
  have h : ∀ x : Fin 1 → Cola224134, Good x := fun x =>
    ⟨fun i j hj => by have := j.isLt; omega, fun i j l hj hl => by have := l.isLt; omega⟩
  unfold a
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv h), Nat.card_eq_fintype_card]
  simp

/-- The column with code `c`: entry `i` is bit `2 - i` of `c`. -/
def cola224134 (c : Fin 8) : Cola224134 :=
  fun i => ⟨c.val / 2 ^ (2 - i.val) % 2, Nat.mod_lt _ (by norm_num)⟩

theorem col_bijectivea224134 : Function.Bijective cola224134 := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨by decide, by simp⟩

/-- `BlockOK` on codes, as a table. -/
def Bta224134 (u v : Fin 8) : Bool := Nat.beq (9277592187330931455 / 2 ^ (8 * u.val + v.val) % 2) 1

/-- `TriOK` on codes, as a table. -/
def Tta224134 (u v w : Fin 8) : Bool :=
  Nat.beq (13407615380491968777760678828255703402689156149087296200885725536919071003773382240297756376192398826971269431168750024057161758305551768318008070143737855 / 2 ^ (64 * u.val + 8 * v.val + w.val) % 2) 1

theorem Bt_iffa224134 : ∀ u v : Fin 8, BlockOK (cola224134 u) (cola224134 v) ↔ Bta224134 u v = true := by
  decide +kernel

theorem Tt_iffa224134 : ∀ u v w : Fin 8,
    TriOK (cola224134 u) (cola224134 v) (cola224134 w) ↔ Tta224134 u v w = true := by
  decide +kernel

/-- The transfer recursion on codes. -/
def Ga224134 : ℕ → Fin 8 → Fin 8 → ℕ
  | 0, u, v => if Bta224134 u v then 1 else 0
  | m + 1, u, v => ∑ w : Fin 8, if Bta224134 u v && Tta224134 u v w then Ga224134 m v w else 0

theorem T_eq_Ga224134 (m : ℕ) : ∀ u v : Fin 8, Ta224134 m (cola224134 u) (cola224134 v) = Ga224134 m u v := by
  induction m with
  | zero =>
    intro u v
    rw [T_zeroa224134]
    exact if_congr (Bt_iffa224134 u v) rfl rfl
  | succ m ih =>
    intro u v
    rw [T_succa224134, ← col_bijectivea224134.sum_comp]
    simp only [Ga224134]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ih v w]
    refine if_congr ?_ rfl rfl
    rw [Bt_iffa224134, Tt_iffa224134, Bool.and_eq_true]

theorem a_eq_Ga224134 (m : ℕ) : a (m + 2) = ∑ u : Fin 8, ∑ v : Fin 8, Ga224134 m u v := by
  rw [a_eqa224134, ← col_bijectivea224134.sum_comp]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← col_bijectivea224134.sum_comp]
  exact Finset.sum_congr rfl fun v _ => T_eq_Ga224134 m u v

/-- Coefficients of `m ^ 3` of six times `G m u v` (`m ≥ 2`), indexed by `8 u + v`. -/
def K3a224134 : List ℤ := [4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Coefficients of `m ^ 2`. -/
def K2a224134 : List ℤ := [15, 3, 6, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Coefficients of `m`. -/
def K1a224134 : List ℤ := [35, 3, 12, 6, 15, 0, 6, 0, 0, 3, 0, 6, 0, 0, 0, 0, 0, 0, 12, 6, 0, 0, 6, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 15, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- Constant coefficients. -/
def K0a224134 : List ℤ := [0, 12, 6, 6, 12, 6, 6, 6, 0, 6, 0, 6, 0, 0, 0, 6, 0, 0, 6, 6, 0, 0, 6, 6, 0, 0, 0, 6, 0, 0, 0, 6, 0, 0, 0, 0, 12, 6, 6, 6, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 6, 6, 0, 0, 0, 0, 0, 0, 0, 6]

def c3a224134 (u v : Fin 8) : ℤ := K3a224134.getD (8 * u.val + v.val) 0
def c2a224134 (u v : Fin 8) : ℤ := K2a224134.getD (8 * u.val + v.val) 0
def c1a224134 (u v : Fin 8) : ℤ := K1a224134.getD (8 * u.val + v.val) 0
def c0a224134 (u v : Fin 8) : ℤ := K0a224134.getD (8 * u.val + v.val) 0

/-- Six times `G m u v` for `m ≥ 2`. -/
def Pa224134 (u v : Fin 8) (m : ℤ) : ℤ :=
  c3a224134 u v * m ^ 3 + c2a224134 u v * m ^ 2 + c1a224134 u v * m + c0a224134 u v

/-- The induction step of `G_closed`, coefficient by coefficient. -/
theorem step_factsa224134 : ∀ u v : Fin 8,
    (∑ w : Fin 8, if Bta224134 u v && Tta224134 u v w then c3a224134 v w else 0) = c3a224134 u v ∧
    (∑ w : Fin 8, if Bta224134 u v && Tta224134 u v w then c2a224134 v w else 0) =
      3 * c3a224134 u v + c2a224134 u v ∧
    (∑ w : Fin 8, if Bta224134 u v && Tta224134 u v w then c1a224134 v w else 0) =
      3 * c3a224134 u v + 2 * c2a224134 u v + c1a224134 u v ∧
    (∑ w : Fin 8, if Bta224134 u v && Tta224134 u v w then c0a224134 v w else 0) =
      c3a224134 u v + c2a224134 u v + c1a224134 u v + c0a224134 u v := by
  decide +kernel

theorem base_factsa224134 : ∀ u v : Fin 8, 6 * (Ga224134 2 u v : ℤ) = Pa224134 u v 2 := by
  decide +kernel

theorem G_closeda224134 (m : ℕ) (hm : 2 ≤ m) :
    ∀ u v : Fin 8, 6 * (Ga224134 m u v : ℤ) = Pa224134 u v m := by
  induction m, hm using Nat.le_induction with
  | base => exact base_factsa224134
  | succ m hm ih =>
    intro u v
    have hsum : 6 * (Ga224134 (m + 1) u v : ℤ) =
        ∑ w : Fin 8, if Bta224134 u v && Tta224134 u v w then Pa224134 v w m else 0 := by
      rw [Ga224134]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      split_ifs
      · exact ih v w
      · simp
    rw [hsum]
    have hP : ∀ w : Fin 8, (if Bta224134 u v && Tta224134 u v w then Pa224134 v w m else 0) =
        (if Bta224134 u v && Tta224134 u v w then c3a224134 v w else 0) * (m : ℤ) ^ 3 +
        (if Bta224134 u v && Tta224134 u v w then c2a224134 v w else 0) * (m : ℤ) ^ 2 +
        (if Bta224134 u v && Tta224134 u v w then c1a224134 v w else 0) * (m : ℤ) +
        (if Bta224134 u v && Tta224134 u v w then c0a224134 v w else 0) := by
      intro w
      split_ifs <;> simp [Pa224134]
    simp only [hP, Finset.sum_add_distrib, ← Finset.sum_mul]
    obtain ⟨h3, h2, h1, h0⟩ := step_factsa224134 u v
    rw [h3, h2, h1, h0]
    unfold Pa224134
    push_cast
    ring

theorem sum_factsa224134 :
    (∑ u : Fin 8, ∑ v : Fin 8, c3a224134 u v) = 4 ∧
    (∑ u : Fin 8, ∑ v : Fin 8, c2a224134 u v) = 39 ∧
    (∑ u : Fin 8, ∑ v : Fin 8, c1a224134 u v) = 143 ∧
    (∑ u : Fin 8, ∑ v : Fin 8, c0a224134 u v) = 162 := by
  decide +kernel

theorem small_factsa224134 :
    (∑ u : Fin 8, ∑ v : Fin 8, Ga224134 0 u v) = 27 ∧
    (∑ u : Fin 8, ∑ v : Fin 8, Ga224134 1 u v) = 58 := by
  decide +kernel

theorem closed_ma224134 (m : ℕ) :
    6 * (a (m + 2) : ℤ) = 4 * (m : ℤ) ^ 3 + 39 * (m : ℤ) ^ 2 + 143 * (m : ℤ) + 162 := by
  rcases Nat.lt_or_ge m 2 with h | h
  · rw [a_eq_Ga224134]
    obtain ⟨h0, h1⟩ := small_factsa224134
    interval_cases m
    · rw [h0] <;> norm_num
    · rw [h1] <;> norm_num
  · rw [a_eq_Ga224134]
    push_cast
    simp only [Finset.mul_sum, G_closeda224134 m h]
    simp only [Pa224134, Finset.sum_add_distrib, ← Finset.sum_mul]
    obtain ⟨h3, h2, h1, h0⟩ := sum_factsa224134
    rw [h3, h2, h1, h0] <;> ring

theorem closedQa224134 (n : ℕ) (hn : 2 ≤ n) :
    (a n : ℚ) = (2 / 3) * (n : ℚ) ^ 3 + (5 / 2) * (n : ℚ) ^ 2 + (35 / 6) * (n : ℚ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h : ((6 * (a (m + 2) : ℤ) : ℤ) : ℚ) =
      ((4 * (m : ℤ) ^ 3 + 39 * (m : ℤ) ^ 2 + 143 * (m : ℤ) + 162 : ℤ) : ℚ) := by
    rw [closed_ma224134 m]
  push_cast at h ⊢
  linarith

theorem recurrencea224134 (n : ℕ) (hn : 6 ≤ n) :
    (a n : ℤ) = 4 * (a (n - 1) : ℤ) - 6 * (a (n - 2) : ℤ) + 4 * (a (n - 3) : ℤ) - (a (n - 4) : ℤ) := by
  have hQ : (a n : ℚ) = 4 * (a (n - 1) : ℚ) - 6 * (a (n - 2) : ℚ) + 4 * (a (n - 3) : ℚ) -
      (a (n - 4) : ℚ) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
    rw [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega,
      show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega]
    rw [closedQa224134 (k + 6) (by omega), closedQa224134 (k + 5) (by omega),
      closedQa224134 (k + 4) (by omega), closedQa224134 (k + 3) (by omega),
      closedQa224134 (k + 2) (by omega)]
    push_cast
    ring
  exact_mod_cast hQ

open PowerSeries in
theorem gen_funa224134 :
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
  have hrhs : (X : ℚ⟦X⟧) * (8 - 5 * X - 2 * X ^ 2 + 4 * X ^ 3 - X ^ 4) =
      C (8 : ℚ) * X ^ 1 - C (5 : ℚ) * X ^ 2 - C (2 : ℚ) * X ^ 3 + C (4 : ℚ) * X ^ 4 - C (1 : ℚ) * X ^ 5 := by
    simp only [map_ofNat, map_one]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, hA, coeff_mk]
  have h1 := a_onea224134
  by_cases hk : k < 6
  · interval_cases k <;> norm_num [closedQa224134, h1]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
    simp only [show 0 ≤ j + 6 by omega, show 1 ≤ j + 6 by omega, show 2 ≤ j + 6 by omega,
      show 3 ≤ j + 6 by omega, show 4 ≤ j + 6 by omega, show 5 ≤ j + 6 by omega,
      show j + 6 - 0 = j + 6 by omega, show j + 6 - 1 = j + 5 by omega,
      show j + 6 - 2 = j + 4 by omega, show j + 6 - 3 = j + 3 by omega,
      show j + 6 - 4 = j + 2 by omega,
      show ¬ (j + 6 = 0) by omega, show ¬ (j + 5 = 0) by omega, show ¬ (j + 4 = 0) by omega,
      show ¬ (j + 3 = 0) by omega, show ¬ (j + 2 = 0) by omega,
      if_true, if_false]
    rw [closedQa224134 (j + 6) (by omega), closedQa224134 (j + 5) (by omega),
      closedQa224134 (j + 4) (by omega), closedQa224134 (j + 3) (by omega),
      closedQa224134 (j + 2) (by omega)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a224134.main :=
  ⟨OMA.Helpers.recurrencea224134, OMA.Helpers.gen_funa224134, OMA.Helpers.closedQa224134⟩
