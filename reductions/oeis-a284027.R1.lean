import OMAStatements.S_oeis_a284027
import Mathlib

-- Credit: @qu1r0ra

/-!
Reduction of `OMA.S_oeis_a284027.main` (Rule 782) to two hypotheses about the three cells nearest
the origin on the axis.

* `H1`: for `t ≥ 22`, the origin is ON and the cell `(2, 0)` is OFF.
* `H2`: for `t ≥ 22`, the cell `(1, 0)` is ON exactly when `t % 4 ∈ {1, 2}`.

Both hold for `22 ≤ t ≤ 1200` (simulation). They are the open part: the three core cells read the
interior of the quadrant, which keeps a self-similar (Pascal-mod-2) structure, and no finite region
around the origin determines itself (a greatest-fixpoint closure of any band around the origin
erodes to nothing, and one-cell perturbations at distance 31-69 reach the origin).

Everything else is proved here:
* the grid up to `t = 22` by a split `decide` certificate;
* for `t ≥ 22`, the edge band `{e + 2y ≤ 16}` (in the frame moving with the front, `e` the
  distance to the edge) has period 8 in `t`; it is closed under the rule, so one finite
  certificate carries it;
* the rest of the axis, `3 ≤ x ≤ t - 16`, stays OFF (a row-0 cell whose row-0 neighbours are OFF
  sees `0` or `2` live neighbours, so it stays OFF whatever row 1 does);
* hence `a n = 2^n + [n % 4 ∈ {1,2}] 2^(n-1) + c (n % 8)` for `n ≥ 22`, which gives the
  recurrence for `n ≥ 33` and, with the first 33 terms, the generating function.
-/

open OMA.S_oeis_a284027

namespace OMA.R_oeis_a284027_R1

def H1 : Prop :=
  ∀ t : ℕ, 22 ≤ t → cell 782 t 0 0 = true ∧ cell 782 t 2 0 = false

def H2 : Prop :=
  ∀ t : ℕ, 22 ≤ t → cell 782 t 1 0 = decide (t % 4 = 1 ∨ t % 4 = 2)

section

private def rule782 (c e w n s : Bool) : Bool :=
  match e.toNat + w.toNat + n.toNat + s.toNat with
  | 0 => c
  | 1 => true
  | 4 => true
  | _ => false

lemma rule782_eq (c e w n s : Bool) :
    (782 : ℕ).testBit (c.toNat + 2 * (e.toNat + w.toNat + n.toNat + s.toNat)) =
      rule782 c e w n s := by
  cases c <;> cases e <;> cases w <;> cases n <;> cases s <;> decide

lemma cell_succ (t : ℕ) (i j : ℤ) :
    cell 782 (t + 1) i j = rule782 (cell 782 t i j) (cell 782 t (i + 1) j)
      (cell 782 t (i - 1) j) (cell 782 t i (j + 1)) (cell 782 t i (j - 1)) := by
  exact rule782_eq _ _ _ _ _

lemma negLeft (i : ℤ) : -i + 1 = -(i - 1) := by omega
lemma negRight (i : ℤ) : -i - 1 = -(i + 1) := by omega

lemma cell_neg_i (t : ℕ) (i j : ℤ) : cell 782 t (-i) j = cell 782 t i j := by
  induction t generalizing i j with
  | zero => simp [cell]
  | succ t ih =>
    simp only [cell]
    rw [negLeft i, negRight i, ih i j, ih (i - 1) j, ih (i + 1) j, ih i (j + 1), ih i (j - 1)]
    congr 1
    omega

lemma cell_neg_j (t : ℕ) (i j : ℤ) : cell 782 t i (-j) = cell 782 t i j := by
  induction t generalizing i j with
  | zero => simp [cell]
  | succ t ih =>
    simp only [cell]
    rw [negLeft j, negRight j, ih i j, ih (i + 1) j, ih (i - 1) j, ih i (j - 1), ih i (j + 1)]
    congr 1
    omega

lemma cell_swap (t : ℕ) (i j : ℤ) : cell 782 t j i = cell 782 t i j := by
  induction t generalizing i j with
  | zero => simp [cell, and_comm]
  | succ t ih =>
    simp only [cell]
    rw [ih i j, ih i (j + 1), ih i (j - 1), ih (i + 1) j, ih (i - 1) j]
    congr 1
    omega

lemma cell_natAbs (t : ℕ) (i j : ℤ) :
    cell 782 t i j = cell 782 t (i.natAbs : ℤ) (j.natAbs : ℤ) := by
  rcases Int.natAbs_eq i with hi | hi <;> rcases Int.natAbs_eq j with hj | hj
  · conv_lhs => rw [hi, hj]
  · conv_lhs => rw [hi, hj]
    exact cell_neg_j t _ _
  · conv_lhs => rw [hi, hj]
    exact cell_neg_i t _ _
  · conv_lhs => rw [hi, hj]
    rw [cell_neg_i, cell_neg_j]

lemma cell_outside (t : ℕ) (i j : ℤ) (h : t < i.natAbs + j.natAbs) :
    cell 782 t i j = false := by
  induction t generalizing i j with
  | zero =>
    simp only [cell]
    have hne : ¬(i = 0 ∧ j = 0) := by omega
    simp [hne]
  | succ t ih =>
    rw [cell_succ, ih i j (by omega), ih (i + 1) j (by omega),
        ih (i - 1) j (by omega), ih i (j + 1) (by omega), ih i (j - 1) (by omega)]
    rfl

private def bit782 (m k : ℕ) : Bool := (m / 2 ^ k) % 2 == 1

/-! ### The grid up to `t = 22`

`gridRow t y` has bit `x` set when the canonical cell `(x, y)`, `y ≤ x`, is ON after `t` steps. -/

private def gridRow : ℕ → ℕ → ℕ
  | 0, 0 => 1 | 1, 0 => 3 | 2, 0 => 7 | 3, 0 => 13 | 3, 1 => 4
  | 4, 0 => 25 | 4, 1 => 4 | 5, 0 => 59 | 5, 1 => 20 | 6, 0 => 127
  | 6, 1 => 22 | 6, 2 => 16 | 7, 0 => 215 | 7, 1 => 66 | 7, 2 => 56
  | 7, 3 => 16 | 8, 0 => 407 | 8, 1 => 72 | 8, 2 => 40 | 8, 3 => 24
  | 9, 0 => 957 | 9, 1 => 328 | 9, 2 => 32 | 9, 3 => 24 | 10, 0 => 2029
  | 10, 1 => 328 | 10, 2 => 288 | 10, 3 => 16 | 11, 0 => 3429 | 11, 1 => 1112
  | 11, 2 => 936 | 11, 3 => 272 | 12, 0 => 6437 | 12, 1 => 1136 | 12, 2 => 696
  | 12, 3 => 280 | 12, 4 => 256 | 13, 0 => 15245 | 13, 1 => 5476 | 13, 2 => 656
  | 13, 3 => 264 | 13, 4 => 896 | 13, 5 => 256 | 14, 0 => 32665 | 14, 1 => 6116
  | 14, 2 => 5008 | 14, 3 => 264 | 14, 4 => 1984 | 14, 5 => 256 | 14, 6 => 256
  | 15, 0 => 55067 | 15, 1 => 17316 | 15, 2 => 14608 | 15, 3 => 5192 | 15, 4 => 3424
  | 15, 5 => 1088 | 15, 6 => 896 | 15, 7 => 256 | 16, 0 => 103967 | 16, 1 => 18854
  | 16, 2 => 10576 | 16, 3 => 7880 | 16, 4 => 2336 | 16, 5 => 1120 | 16, 6 => 704
  | 16, 7 => 384 | 17, 0 => 245271 | 17, 1 => 84130 | 17, 2 => 8656 | 17, 3 => 7048
  | 17, 4 => 2336 | 17, 5 => 1312 | 17, 6 => 576 | 17, 7 => 384 | 18, 0 => 518935
  | 18, 1 => 84640 | 18, 2 => 73936 | 18, 3 => 4904 | 18, 4 => 2144 | 18, 5 => 1408
  | 18, 6 => 576 | 18, 7 => 256 | 19, 0 => 876821 | 19, 1 => 285348 | 19, 2 => 239728
  | 19, 3 => 71464 | 19, 4 => 2624 | 19, 5 => 1408 | 19, 6 => 576 | 19, 7 => 256
  | 20, 0 => 1646865 | 20, 1 => 291500 | 20, 2 => 178544 | 20, 3 => 73128 | 20, 4 => 69184
  | 20, 5 => 1920 | 20, 6 => 576 | 20, 7 => 256 | 21, 0 => 3899667 | 21, 1 => 1402812
  | 21, 2 => 168432 | 21, 3 => 67816 | 21, 4 => 230464 | 21, 5 => 66176 | 21, 6 => 576
  | 21, 7 => 256 | 22, 0 => 8355843 | 22, 1 => 1568022 | 22, 2 => 1283232 | 22, 3 => 67656
  | 22, 4 => 508992 | 22, 5 => 66176 | 22, 6 => 67136 | 22, 7 => 256
  | _, _ => 0

private def gridVal (t i j : ℕ) : Bool :=
  if t < i + j then false else bit782 (gridRow t (min i j)) (max i j)

lemma gridVal_symm (t i j : ℕ) : gridVal t j i = gridVal t i j := by
  simp only [gridVal, Nat.add_comm j i, min_comm j i, max_comm j i]

private def stepGridVal (t i j : ℕ) : Bool :=
  rule782
    (gridVal t i j)
    (gridVal t (i + 1) j)
    (gridVal t (if i = 0 then 1 else i - 1) j)
    (gridVal t i (j + 1))
    (gridVal t i (if j = 0 then 1 else j - 1))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma gridStep0 :
    ∀ t : Fin 8, ∀ i : Fin 23, ∀ j : Fin 12,
      i.val + j.val ≤ t.val + 1 → j.val ≤ i.val →
      stepGridVal (t.val) i.val j.val = gridVal (t.val + 1) i.val j.val := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma gridStep1 :
    ∀ t : Fin 7, ∀ i : Fin 23, ∀ j : Fin 12,
      i.val + j.val ≤ t.val + 8 + 1 → j.val ≤ i.val →
      stepGridVal (t.val + 8) i.val j.val = gridVal (t.val + 8 + 1) i.val j.val := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma gridStep2 :
    ∀ t : Fin 4, ∀ i : Fin 23, ∀ j : Fin 12,
      i.val + j.val ≤ t.val + 15 + 1 → j.val ≤ i.val →
      stepGridVal (t.val + 15) i.val j.val = gridVal (t.val + 15 + 1) i.val j.val := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma gridStep3 :
    ∀ t : Fin 3, ∀ i : Fin 23, ∀ j : Fin 12,
      i.val + j.val ≤ t.val + 19 + 1 → j.val ≤ i.val →
      stepGridVal (t.val + 19) i.val j.val = gridVal (t.val + 19 + 1) i.val j.val := by
  decide

lemma gridVal_step_ok (t i j : ℕ) (ht : t < 22) (hij : i + j ≤ t + 1) (hji : j ≤ i) :
    stepGridVal t i j = gridVal (t + 1) i j := by
  have hi : i < 23 := by omega
  have hj : j < 12 := by omega
  by_cases h0 : t < 8
  · exact gridStep0 ⟨t, h0⟩ ⟨i, hi⟩ ⟨j, hj⟩ hij hji
  by_cases h1 : t < 15
  · obtain ⟨u, rfl⟩ : ∃ u, t = u + 8 := ⟨t - 8, by omega⟩
    exact gridStep1 ⟨u, by omega⟩ ⟨i, hi⟩ ⟨j, hj⟩ hij hji
  by_cases h2 : t < 19
  · obtain ⟨u, rfl⟩ : ∃ u, t = u + 15 := ⟨t - 15, by omega⟩
    exact gridStep2 ⟨u, by omega⟩ ⟨i, hi⟩ ⟨j, hj⟩ hij hji
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 19 := ⟨t - 19, by omega⟩
  exact gridStep3 ⟨u, by omega⟩ ⟨i, hi⟩ ⟨j, hj⟩ hij hji

lemma natAbs_sub_one (k : ℕ) :
    ((k : ℤ) - 1).natAbs = if k = 0 then 1 else k - 1 := by
  cases k with
  | zero => rfl
  | succ k => simp

lemma cell_eq_gridVal (t : ℕ) (ht : t ≤ 22) (i j : ℤ) :
    cell 782 t i j = gridVal t i.natAbs j.natAbs := by
  induction t generalizing i j with
  | zero =>
    rw [cell_natAbs]
    set x := i.natAbs
    set y := j.natAbs
    by_cases h : 0 < x + y
    · rw [cell_outside 0 (x : ℤ) (y : ℤ) (by simpa using h)]
      simp [gridVal, h]
    · have hx : x = 0 := by omega
      have hy : y = 0 := by omega
      rw [hx, hy]
      decide
  | succ t ih =>
    rw [cell_natAbs]
    set x := i.natAbs
    set y := j.natAbs
    by_cases hout : t + 1 < x + y
    · rw [cell_outside (t + 1) (x : ℤ) (y : ℤ) (by simpa using hout)]
      simp [gridVal, hout]
    · have hle : x + y ≤ t + 1 := by omega
      suffices step : ∀ u v : ℕ, u + v ≤ t + 1 → v ≤ u →
          cell 782 (t + 1) (u : ℤ) (v : ℤ) = gridVal (t + 1) u v by
        rcases le_total y x with hyx | hxy
        · exact step x y hle hyx
        · rw [← cell_swap, ← gridVal_symm]
          exact step y x (by omega) hxy
      intro u v huv hvu
      rw [cell_succ, ih (by omega), ih (by omega), ih (by omega), ih (by omega), ih (by omega)]
      have hu1 : ((u : ℤ) + 1).natAbs = u + 1 := by omega
      have hv1 : ((v : ℤ) + 1).natAbs = v + 1 := by omega
      simp only [Int.natAbs_natCast, hu1, hv1, natAbs_sub_one]
      exact gridVal_step_ok t u v (by omega) huv hvu

/-! ### The edge band, for `t ≥ 22`

Bit `e` of `bandRow r y` is the cell `(t + 1 - e - y, y)` for any `t ≥ 22` with `t % 8 = r`
(`e + 2y ≤ 16`). `tv r y k` reads it at `k = e + 2`, and is OFF for `k < 2` (outside the
diamond). -/

private def bandRow : ℕ → ℕ → ℕ
  | 0, 0 => 422 | 0, 1 => 11044 | 0, 2 => 6804 | 0, 3 => 444 | 0, 4 => 292
  | 0, 5 => 68 | 0, 6 => 20 | 0, 7 => 4 | 1, 0 => 1006 | 1, 1 => 21578
  | 1, 2 => 5896 | 1, 3 => 472 | 1, 4 => 72 | 1, 5 => 40 | 1, 6 => 8
  | 2, 0 => 3454 | 2, 1 => 10900 | 2, 2 => 3090 | 2, 3 => 400 | 2, 4 => 16
  | 2, 5 => 80 | 2, 6 => 16 | 3, 0 => 4310 | 3, 1 => 21922 | 3, 2 => 4270
  | 3, 3 => 930 | 3, 4 => 160 | 3, 5 => 32 | 4, 0 => 8486 | 4, 1 => 10692
  | 4, 2 => 2516 | 4, 3 => 1476 | 4, 4 => 450 | 4, 5 => 64 | 5, 0 => 16622
  | 5, 1 => 31146 | 5, 2 => 4392 | 5, 3 => 264 | 5, 4 => 270 | 5, 5 => 2
  | 6, 0 => 510 | 6, 1 => 23540 | 6, 2 => 2674 | 6, 3 => 528 | 6, 4 => 62
  | 6, 5 => 4 | 6, 6 => 2 | 7, 0 => 470 | 7, 1 => 5570 | 7, 2 => 7246
  | 7, 3 => 1162 | 7, 4 => 214 | 7, 5 => 34 | 7, 6 => 14 | 7, 7 => 2
  | _, _ => 0

private def tv (r y k : ℕ) : Bool := if k < 2 then false else bit782 (bandRow r y) (k - 2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma bandCert : ∀ r : Fin 8, ∀ y : Fin 9, ∀ e : Fin 17, e.val + 2 + 2 * y.val ≤ 18 →
    rule782 (tv r.val y.val (e.val + 1)) (tv r.val y.val e.val) (tv r.val y.val (e.val + 2))
      (tv r.val (y.val + 1) e.val)
      (if y.val = 0 then tv r.val 1 e.val else tv r.val (y.val - 1) (e.val + 2)) =
    tv ((r.val + 1) % 8) y.val (e.val + 2) := by
  decide

lemma tvEdge : ∀ r : Fin 8, tv r.val 0 17 = false ∧ tv r.val 0 18 = false := by
  decide

/-- The band at time `t`, read in the frame moving with the front. -/
private def Inv (t : ℕ) : Prop :=
  ∀ (x j : ℤ) (y k : ℕ), j = y → x + y + k = t + 3 → k + 2 * y ≤ 18 →
    cell 782 t x j = tv (t % 8) y k

/-- The axis between the core and the band is OFF. -/
private def Mid (t : ℕ) : Prop := ∀ x : ℕ, 3 ≤ x → x + 17 ≤ t + 1 → cell 782 t x 0 = false

lemma inv_small (t : ℕ) (ht : 8 ≤ t) (x j : ℤ) (y k : ℕ) (hj : j = y)
    (hx : x + y + k = t + 3) (hb : k + 2 * y ≤ 18) (hk : k < 2) : cell 782 t x j = false :=
  cell_outside t x j (by subst hj; omega)

lemma inv_step (t : ℕ) (ht : 22 ≤ t) (ih : Inv t) : Inv (t + 1) := by
  intro x j y k hj hx hb
  by_cases hk : k < 2
  · rw [inv_small (t + 1) (by omega) x j y k hj (by omega) hb hk]
    simp [tv, hk]
  obtain ⟨e, rfl⟩ : ∃ e, k = e + 2 := ⟨k - 2, by omega⟩
  subst hj
  rw [cell_succ]
  have h1 := ih x y y (e + 1) rfl (by omega) (by omega)
  have h2 := ih (x + 1) y y e rfl (by omega) (by omega)
  have h3 := ih (x - 1) y y (e + 2) rfl (by omega) (by omega)
  have h4 := ih x ((y : ℤ) + 1) (y + 1) e (by omega) (by omega) (by omega)
  have h5 : cell 782 t x ((y : ℤ) - 1) =
      (if y = 0 then tv (t % 8) 1 e else tv (t % 8) (y - 1) (e + 2)) := by
    split_ifs with hy0
    · subst hy0
      rw [show ((0 : ℕ) : ℤ) - 1 = -1 by norm_num, cell_neg_j]
      exact ih x 1 1 e (by norm_num) (by omega) (by omega)
    · exact ih x ((y : ℤ) - 1) (y - 1) (e + 2) (by omega) (by omega) (by omega)
  rw [h1, h2, h3, h4, h5, show (t + 1) % 8 = (t % 8 + 1) % 8 by omega]
  exact bandCert ⟨t % 8, Nat.mod_lt _ (by norm_num)⟩ ⟨y, by omega⟩ ⟨e, by omega⟩ hb

lemma mid_step (t : ℕ) (hI : Inv t) (hM : Mid t) (h2 : cell 782 t 2 0 = false) :
    Mid (t + 1) := by
  intro x hx3 hxt
  rw [cell_succ]
  have hr := tvEdge ⟨t % 8, Nat.mod_lt _ (by norm_num)⟩
  have c1 : cell 782 t (x : ℤ) 0 = false := by
    by_cases h : x + 17 ≤ t + 1
    · exact hM x hx3 h
    · rw [hI (x : ℤ) 0 0 18 (by simp) (by omega) (by omega)]
      exact hr.2
  have c2 : cell 782 t ((x : ℤ) + 1) 0 = false := by
    by_cases h : x + 1 + 17 ≤ t + 1
    · have := hM (x + 1) (by omega) h
      push_cast at this
      exact this
    · rcases (show t + 2 - x = 17 ∨ t + 2 - x = 18 by omega) with h' | h'
      · rw [hI ((x : ℤ) + 1) 0 0 17 (by simp) (by omega) (by omega)]
        exact hr.1
      · rw [hI ((x : ℤ) + 1) 0 0 18 (by simp) (by omega) (by omega)]
        exact hr.2
  have c3 : cell 782 t ((x : ℤ) - 1) 0 = false := by
    by_cases h : x = 3
    · subst h
      rw [show ((3 : ℕ) : ℤ) - 1 = 2 by norm_num]
      exact h2
    · have := hM (x - 1) (by omega) (by omega)
      rwa [show ((x - 1 : ℕ) : ℤ) = (x : ℤ) - 1 by omega] at this
  rw [c1, c2, c3, show (0 : ℤ) - 1 = -(0 + 1) by norm_num, cell_neg_j]
  cases cell 782 t (x : ℤ) (0 + 1) <;> rfl

lemma inv_base_fin : ∀ y : Fin 9, ∀ k : Fin 19, 2 ≤ k.val → k.val + 2 * y.val ≤ 18 →
    gridVal 22 (25 - k.val - y.val) y.val = tv (22 % 8) y.val k.val := by
  decide

lemma inv_base : Inv 22 := by
  intro x j y k hj hx hb
  by_cases hk : k < 2
  · rw [inv_small 22 (by norm_num) x j y k hj hx hb hk]
    simp [tv, hk]
  · subst hj
    rw [cell_eq_gridVal 22 le_rfl, show x.natAbs = 25 - k - y by omega, Int.natAbs_natCast]
    exact inv_base_fin ⟨y, by omega⟩ ⟨k, by omega⟩ (show 2 ≤ k by omega) hb

lemma mid_base_fin : ∀ x : Fin 7, 3 ≤ x.val → gridVal 22 x.val 0 = false := by
  decide

lemma mid_base : Mid 22 := by
  intro x h3 h
  rw [cell_eq_gridVal 22 le_rfl, Int.natAbs_natCast, Int.natAbs_zero]
  exact mid_base_fin ⟨x, by omega⟩ h3

lemma good (h1 : H1) (t : ℕ) (ht : 22 ≤ t) : Inv t ∧ Mid t := by
  induction t, ht using Nat.le_induction with
  | base => exact ⟨inv_base, mid_base⟩
  | succ t ht ih => exact ⟨inv_step t ht ih.1, mid_step t ih.1 ih.2 (h1 t ht).2⟩

/-! ### The closed form -/

private def bandConst (r : ℕ) : ℤ :=
  ∑ d ∈ Finset.range 16, if tv r 0 (18 - d) then (2 : ℤ) ^ (15 - d) else 0

lemma a_closed (h1 : H1) (h2 : H2) (n : ℕ) (hn : 22 ≤ n) :
    a n = 2 ^ n + (if n % 4 = 1 ∨ n % 4 = 2 then (2 : ℤ) ^ (n - 1) else 0) +
      bandConst (n % 8) := by
  obtain ⟨hI, hM⟩ := good h1 n hn
  obtain ⟨c0, c2⟩ := h1 n hn
  have c1 := h2 n hn
  set f : ℕ → ℤ := fun k => if cell 782 n (k : ℤ) 0 then (2 : ℤ) ^ (n - k) else 0 with hf
  have hsum : a n = ∑ k ∈ Finset.range (n + 1), f k := rfl
  rw [hsum, show n + 1 = 3 + (n - 18) + 16 by omega, Finset.sum_range_add, Finset.sum_range_add]
  have p1 : ∑ k ∈ Finset.range 3, f k =
      2 ^ n + (if n % 4 = 1 ∨ n % 4 = 2 then (2 : ℤ) ^ (n - 1) else 0) := by
    by_cases hp : n % 4 = 1 ∨ n % 4 = 2
    · simp [Finset.sum_range_succ, hf, c0, c1, c2, hp]
    · simp [Finset.sum_range_succ, hf, c0, c1, c2, hp]
  have p2 : ∑ x ∈ Finset.range (n - 18), f (3 + x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hx' := Finset.mem_range.mp hx
    simp only [hf]
    rw [hM (3 + x) (by omega) (by omega)]
    simp
  have p3 : ∑ d ∈ Finset.range 16, f (3 + (n - 18) + d) = bandConst (n % 8) := by
    unfold bandConst
    apply Finset.sum_congr rfl
    intro d hd
    have hd' := Finset.mem_range.mp hd
    simp only [hf]
    rw [hI ((3 + (n - 18) + d : ℕ) : ℤ) 0 0 (18 - d) (by simp) (by omega) (by omega),
      show n - (3 + (n - 18) + d) = 15 - d by omega]
  rw [p1, p2, p3]
  ring

private def cv : ℕ → ℤ
  | 0 => 211
  | 1 => 503
  | 2 => 1727
  | 3 => 2155
  | 4 => 4243
  | 5 => 8311
  | 6 => 255
  | 7 => 235
  | _ => 0

lemma bandConst_val : ∀ r : Fin 8, bandConst r.val = cv r.val := by
  decide

lemma bandConst_eq (r : ℕ) (hr : r < 8) : bandConst r = cv r := bandConst_val ⟨r, hr⟩

lemma recur (h1 : H1) (h2 : H2) (n : ℕ) (hn : 33 ≤ n) :
    (a n : ℚ) = 2 * a (n - 1) - 4 * a (n - 2) + 8 * a (n - 3) + a (n - 8) - 2 * a (n - 9) +
      4 * a (n - 10) - 8 * a (n - 11) := by
  have h : a n = 2 * a (n - 1) - 4 * a (n - 2) + 8 * a (n - 3) + a (n - 8) - 2 * a (n - 9) +
      4 * a (n - 10) - 8 * a (n - 11) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 33 := ⟨n - 33, by omega⟩
    simp only [show m + 33 - 1 = m + 32 by omega, show m + 33 - 2 = m + 31 by omega, show m + 33 - 3 = m + 30 by omega, show m + 33 - 8 = m + 25 by omega, show m + 33 - 9 = m + 24 by omega, show m + 33 - 10 = m + 23 by omega, show m + 33 - 11 = m + 22 by omega]
    rw [a_closed h1 h2 (m + 33) (by omega), a_closed h1 h2 (m + 32) (by omega), a_closed h1 h2 (m + 31) (by omega), a_closed h1 h2 (m + 30) (by omega), a_closed h1 h2 (m + 25) (by omega), a_closed h1 h2 (m + 24) (by omega), a_closed h1 h2 (m + 23) (by omega), a_closed h1 h2 (m + 22) (by omega)]
    rw [show (m + 25) % 8 = (m + 33) % 8 by omega, show (m + 24) % 8 = (m + 32) % 8 by omega, show (m + 23) % 8 = (m + 31) % 8 by omega, show (m + 22) % 8 = (m + 30) % 8 by omega]
    simp only [show m + 33 - 1 = m + 32 by omega, show m + 32 - 1 = m + 31 by omega, show m + 31 - 1 = m + 30 by omega, show m + 30 - 1 = m + 29 by omega, show m + 25 - 1 = m + 24 by omega, show m + 24 - 1 = m + 23 by omega, show m + 23 - 1 = m + 22 by omega, show m + 22 - 1 = m + 21 by omega]
    rcases (show m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 by omega) with hm | hm | hm | hm
    · simp only [show (m + 33) % 4 = 1 by omega, show (m + 32) % 4 = 0 by omega, show (m + 31) % 4 = 3 by omega, show (m + 30) % 4 = 2 by omega, show (m + 25) % 4 = 1 by omega, show (m + 24) % 4 = 0 by omega, show (m + 23) % 4 = 3 by omega, show (m + 22) % 4 = 2 by omega]
      norm_num
      ring
    · simp only [show (m + 33) % 4 = 2 by omega, show (m + 32) % 4 = 1 by omega, show (m + 31) % 4 = 0 by omega, show (m + 30) % 4 = 3 by omega, show (m + 25) % 4 = 2 by omega, show (m + 24) % 4 = 1 by omega, show (m + 23) % 4 = 0 by omega, show (m + 22) % 4 = 3 by omega]
      norm_num
      ring
    · simp only [show (m + 33) % 4 = 3 by omega, show (m + 32) % 4 = 2 by omega, show (m + 31) % 4 = 1 by omega, show (m + 30) % 4 = 0 by omega, show (m + 25) % 4 = 3 by omega, show (m + 24) % 4 = 2 by omega, show (m + 23) % 4 = 1 by omega, show (m + 22) % 4 = 0 by omega]
      norm_num
      ring
    · simp only [show (m + 33) % 4 = 0 by omega, show (m + 32) % 4 = 3 by omega, show (m + 31) % 4 = 2 by omega, show (m + 30) % 4 = 1 by omega, show (m + 25) % 4 = 0 by omega, show (m + 24) % 4 = 3 by omega, show (m + 23) % 4 = 2 by omega, show (m + 22) % 4 = 1 by omega]
      norm_num
      ring
  exact_mod_cast h

private def init : ℕ → ℤ
  | 0 => 1
  | 1 => 3
  | 2 => 7
  | 3 => 11
  | 4 => 19
  | 5 => 55
  | 6 => 127
  | 7 => 235
  | 8 => 467
  | 9 => 759
  | 10 => 1471
  | 11 => 2667
  | 12 => 5267
  | 13 => 11383
  | 14 => 19711
  | 15 => 55531
  | 16 => 127187
  | 17 => 238071
  | 18 => 476863
  | 19 => 690283
  | 20 => 1118355
  | 21 => 3285111
  | 22 => 6291711
  | 23 => 8388843
  | 24 => 16777427
  | 25 => 50332151
  | 26 => 100665023
  | 27 => 134219883
  | 28 => 268439699
  | 29 => 805314679
  | 30 => 1610612991
  | 31 => 2147483883
  | 32 => 4294967507
  | _ => 0

private def gridAxisSum (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if gridVal n k 0 then (2 : ℤ) ^ (n - k) else 0

lemma gridAxisSum_eq (n : ℕ) (hn : n ≤ 22) : a n = gridAxisSum n := by
  unfold a gridAxisSum
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [cell_eq_gridVal n hn, Int.natAbs_natCast, Int.natAbs_zero]

set_option maxRecDepth 100000 in
lemma init_lo : ∀ x : Fin 12, gridAxisSum x.val = init x.val := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
lemma init_hi : ∀ x : Fin 10, gridAxisSum (x.val + 12) = init (x.val + 12) := by
  decide

lemma a_init (h1 : H1) (h2 : H2) (n : ℕ) (hn : n < 33) : a n = init n := by
  by_cases hs : n < 22
  · rw [gridAxisSum_eq n (by omega)]
    by_cases hl : n < 12
    · exact init_lo ⟨n, hl⟩
    · obtain ⟨u, rfl⟩ : ∃ u, n = u + 12 := ⟨n - 12, by omega⟩
      exact init_hi ⟨u, by omega⟩
  · rw [a_closed h1 h2 n (by omega), bandConst_eq (n % 8) (Nat.mod_lt _ (by norm_num))]
    interval_cases n <;> norm_num [cv, init]

set_option maxHeartbeats 8000000 in
open PowerSeries in
lemma gf (b : ℕ → ℤ)
    (hinit : ∀ n, n < 33 → b n = init n)
    (hrec : ∀ n : ℕ, 33 ≤ n → (b n : ℚ) = 2 * b (n - 1) - 4 * b (n - 2) + 8 * b (n - 3) +
      b (n - 8) - 2 * b (n - 9) + 4 * b (n - 10) - 8 * b (n - 11)) :
    mk (fun n => (b n : ℚ)) * ((X - 1) * (X + 1) * (2 * X - 1) * (X ^ 2 + 1) * (4 * X ^ 2 + 1) *
      (X ^ 4 + 1) : PowerSeries ℚ) =
      1048576 * X ^ 32 + 1310720 * X ^ 30 + 262144 * X ^ 28 + 327680 * X ^ 27 - 65536 * X ^ 26 - 49152 * X ^ 25 - 1118208 * X ^ 24 - 20480 * X ^ 23 - 1324032 * X ^ 22 - 5120 * X ^ 21 - 259072 * X ^ 20 - 327680 * X ^ 19 + 65280 * X ^ 18 + 48384 * X ^ 17 + 3840 * X ^ 16 + 19456 * X ^ 15 - 3328 * X ^ 14 - 256 * X ^ 13 - 256 * X ^ 12 - 976 * X ^ 11 - 64 * X ^ 10 - 252 * X ^ 9 + 64 * X ^ 8 + 49 * X ^ 7 + 5 * X ^ 6 + 5 * X ^ 5 + X ^ 4 + X ^ 3 + 5 * X ^ 2 + X + 1 := by
  set F : PowerSeries ℚ := mk (fun n => (b n : ℚ)) with hF
  have lhs :
      F * ((X - 1) * (X + 1) * (2 * X - 1) * (X ^ 2 + 1) * (4 * X ^ 2 + 1) * (X ^ 4 + 1) :
        PowerSeries ℚ) =
      F + (-2 : ℤ) • (F * X ^ 1) + (4 : ℤ) • (F * X ^ 2) + (-8 : ℤ) • (F * X ^ 3) + (-1 : ℤ) • (F * X ^ 8) + (2 : ℤ) • (F * X ^ 9) + (-4 : ℤ) • (F * X ^ 10) + (8 : ℤ) • (F * X ^ 11) := by
    simp only [zsmul_eq_mul]
    push_cast
    ring
  have rhs :
      (1048576 * X ^ 32 + 1310720 * X ^ 30 + 262144 * X ^ 28 + 327680 * X ^ 27 - 65536 * X ^ 26 - 49152 * X ^ 25 - 1118208 * X ^ 24 - 20480 * X ^ 23 - 1324032 * X ^ 22 - 5120 * X ^ 21 - 259072 * X ^ 20 - 327680 * X ^ 19 + 65280 * X ^ 18 + 48384 * X ^ 17 + 3840 * X ^ 16 + 19456 * X ^ 15 - 3328 * X ^ 14 - 256 * X ^ 13 - 256 * X ^ 12 - 976 * X ^ 11 - 64 * X ^ 10 - 252 * X ^ 9 + 64 * X ^ 8 + 49 * X ^ 7 + 5 * X ^ 6 + 5 * X ^ 5 + X ^ 4 + X ^ 3 + 5 * X ^ 2 + X + 1 : PowerSeries ℚ) =
        (1048576 : ℤ) • X ^ 32 +
        (1310720 : ℤ) • X ^ 30 +
        (262144 : ℤ) • X ^ 28 +
        (327680 : ℤ) • X ^ 27 +
        (-65536 : ℤ) • X ^ 26 +
        (-49152 : ℤ) • X ^ 25 +
        (-1118208 : ℤ) • X ^ 24 +
        (-20480 : ℤ) • X ^ 23 +
        (-1324032 : ℤ) • X ^ 22 +
        (-5120 : ℤ) • X ^ 21 +
        (-259072 : ℤ) • X ^ 20 +
        (-327680 : ℤ) • X ^ 19 +
        (65280 : ℤ) • X ^ 18 +
        (48384 : ℤ) • X ^ 17 +
        (3840 : ℤ) • X ^ 16 +
        (19456 : ℤ) • X ^ 15 +
        (-3328 : ℤ) • X ^ 14 +
        (-256 : ℤ) • X ^ 13 +
        (-256 : ℤ) • X ^ 12 +
        (-976 : ℤ) • X ^ 11 +
        (-64 : ℤ) • X ^ 10 +
        (-252 : ℤ) • X ^ 9 +
        (64 : ℤ) • X ^ 8 +
        (49 : ℤ) • X ^ 7 +
        (5 : ℤ) • X ^ 6 +
        (5 : ℤ) • X ^ 5 +
        (1 : ℤ) • X ^ 4 +
        (1 : ℤ) • X ^ 3 +
        (5 : ℤ) • X ^ 2 +
        (1 : ℤ) • X ^ 1 +
        (1 : ℤ) • X ^ 0 := by
    simp only [zsmul_eq_mul]
    push_cast
    ring
  rw [lhs, rhs]
  ext n
  simp only [map_add, map_zsmul, coeff_mul_X_pow', hF, coeff_mk, coeff_X_pow]
  simp only [zsmul_eq_mul]
  by_cases hn : 33 ≤ n
  · have hr := hrec n hn
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 8 ≤ n by omega, show 9 ≤ n by omega, show 10 ≤ n by omega, show 11 ≤ n by omega,
      show n ≠ 32 by omega, show n ≠ 30 by omega, show n ≠ 28 by omega, show n ≠ 27 by omega, show n ≠ 26 by omega, show n ≠ 25 by omega, show n ≠ 24 by omega, show n ≠ 23 by omega, show n ≠ 22 by omega, show n ≠ 21 by omega, show n ≠ 20 by omega, show n ≠ 19 by omega, show n ≠ 18 by omega, show n ≠ 17 by omega, show n ≠ 16 by omega, show n ≠ 15 by omega, show n ≠ 14 by omega, show n ≠ 13 by omega, show n ≠ 12 by omega, show n ≠ 11 by omega, show n ≠ 10 by omega, show n ≠ 9 by omega, show n ≠ 8 by omega, show n ≠ 7 by omega, show n ≠ 6 by omega, show n ≠ 5 by omega, show n ≠ 4 by omega, show n ≠ 3 by omega, show n ≠ 2 by omega, show n ≠ 1 by omega, show n ≠ 0 by omega, ite_true, ite_false]
    push_cast
    linarith
  · have h0 := hinit n (by omega)
    have h1 := hinit (n - 1) (by omega)
    have h2 := hinit (n - 2) (by omega)
    have h3 := hinit (n - 3) (by omega)
    have h8 := hinit (n - 8) (by omega)
    have h9 := hinit (n - 9) (by omega)
    have h10 := hinit (n - 10) (by omega)
    have h11 := hinit (n - 11) (by omega)
    rw [h0, h1, h2, h3, h8, h9, h10, h11]
    interval_cases n <;> norm_num [init]

end

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a284027.main := fun h1 h2 =>
  ⟨recur h1 h2, gf a (a_init h1 h2) (recur h1 h2)⟩

end OMA.R_oeis_a284027_R1
