import OMAStatements.S_oeis_a282606
import Mathlib

-- Credit: @qu1r0ra

open OMA.S_oeis_a282606

private def rule489 (c e w n s : Bool) : Bool :=
  match e.toNat + w.toNat + n.toNat + s.toNat with
  | 0 | 4 => !c
  | 3 => true
  | _ => c

private lemma rule489_eq (c e w n s : Bool) :
    (489 : ℕ).testBit (c.toNat + 2 * (e.toNat + w.toNat + n.toNat + s.toNat)) =
      rule489 c e w n s := by
  cases c <;> cases e <;> cases w <;> cases n <;> cases s <;> decide

private lemma cell_succ (t : ℕ) (i j : ℤ) :
    cell 489 (t + 1) i j =
      rule489 (cell 489 t i j) (cell 489 t (i + 1) j) (cell 489 t (i - 1) j)
        (cell 489 t i (j + 1)) (cell 489 t i (j - 1)) := by
  exact rule489_eq _ _ _ _ _

private lemma negLeft (i : ℤ) : -i + 1 = -(i - 1) := by omega
private lemma negRight (i : ℤ) : -i - 1 = -(i + 1) := by omega

private lemma cell_neg_i (t : ℕ) (i j : ℤ) : cell 489 t (-i) j = cell 489 t i j := by
  induction t generalizing i j with
  | zero => simp [cell]
  | succ t ih =>
    simp only [cell]
    rw [negLeft i, negRight i, ih i j, ih (i - 1) j, ih (i + 1) j,
        ih i (j + 1), ih i (j - 1)]
    congr 1
    omega

private lemma cell_neg_j (t : ℕ) (i j : ℤ) : cell 489 t i (-j) = cell 489 t i j := by
  induction t generalizing i j with
  | zero => simp [cell]
  | succ t ih =>
    simp only [cell]
    rw [negLeft j, negRight j, ih i j, ih (i + 1) j, ih (i - 1) j,
        ih i (j - 1), ih i (j + 1)]
    congr 1
    omega

private lemma cell_swap (t : ℕ) (i j : ℤ) : cell 489 t j i = cell 489 t i j := by
  induction t generalizing i j with
  | zero => simp [cell, and_comm]
  | succ t ih =>
    simp only [cell]
    rw [ih i j, ih i (j + 1), ih i (j - 1), ih (i + 1) j, ih (i - 1) j]
    congr 1
    omega

private lemma cell_natAbs (t : ℕ) (i j : ℤ) :
    cell 489 t i j = cell 489 t (i.natAbs : ℤ) (j.natAbs : ℤ) := by
  rcases Int.natAbs_eq i with hi | hi <;> rcases Int.natAbs_eq j with hj | hj
  · conv_lhs => rw [hi, hj]
  · conv_lhs => rw [hi, hj]
    exact cell_neg_j t _ _
  · conv_lhs => rw [hi, hj]
    exact cell_neg_i t _ _
  · conv_lhs => rw [hi, hj]
    rw [cell_neg_i, cell_neg_j]

private lemma cell_canonical (t : ℕ) (i j : ℤ) :
    cell 489 t i j =
      cell 489 t ((max i.natAbs j.natAbs : ℕ) : ℤ) ((min i.natAbs j.natAbs : ℕ) : ℤ) := by
  rw [cell_natAbs]
  rcases le_total i.natAbs j.natAbs with h | h
  · rw [max_eq_right h, min_eq_left h, cell_swap]
  · rw [max_eq_left h, min_eq_right h]

private lemma cell_outside (t : ℕ) (i j : ℤ) (h : t < i.natAbs + j.natAbs) :
    cell 489 t i j = decide (t % 2 = 1) := by
  induction t generalizing i j with
  | zero =>
    simp only [cell]
    have hne : ¬(i = 0 ∧ j = 0) := by omega
    simp [hne]
  | succ t ih =>
    rw [cell_succ, ih i j (by omega), ih (i + 1) j (by omega),
        ih (i - 1) j (by omega), ih i (j + 1) (by omega), ih i (j - 1) (by omega)]
    have hmod : t % 2 = 0 ∨ t % 2 = 1 := by omega
    rcases hmod with hm | hm
    · have hm1 : (t + 1) % 2 = 1 := by omega
      simp [hm, hm1, rule489]
    · have hm1 : (t + 1) % 2 ≠ 1 := by omega
      simp [hm, hm1, rule489]

private def bit489 (m k : ℕ) : Bool := (m / 2 ^ k) % 2 == 1

private def gridRow : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 2, 0 => 7 | 2, 1 => 2
  | 3, 0 => 4 | 3, 1 => 2
  | 4, 0 => 27 | 4, 1 => 12 | 4, 2 => 4
  | 5, 0 => 30 | 5, 1 => 14 | 5, 2 => 4
  | 6, 0 => 115 | 6, 1 => 56 | 6, 2 => 28 | 6, 3 => 8
  | 7, 0 => 90 | 7, 1 => 40 | 7, 2 => 20 | 7, 3 => 8
  | 8, 0 => 441 | 8, 1 => 216 | 8, 2 => 104 | 8, 3 => 48 | 8, 4 => 16
  | 9, 0 => 488 | 9, 1 => 250 | 9, 2 => 120 | 9, 3 => 56 | 9, 4 => 16
  | 10, 0 => 1849 | 10, 1 => 920 | 10, 2 => 456 | 10, 3 => 224 | 10, 4 => 112 | 10, 5 => 32
  | 11, 0 => 1448 | 11, 1 => 666 | 11, 2 => 328 | 11, 3 => 160 | 11, 4 => 80 | 11, 5 => 32
  | 12, 0 => 7065 | 12, 1 => 3480 | 12, 2 => 1672 | 12, 3 => 832 | 12, 4 => 416 | 12, 5 => 192 | 12, 6 => 64
  | 13, 0 => 7832 | 13, 1 => 3994 | 13, 2 => 1960 | 13, 3 => 912 | 13, 4 => 448 | 13, 5 => 224 | 13, 6 => 64
  | _, _ => 0

private def gridVal (t i j : ℕ) : Bool :=
  if t < i + j then decide (t % 2 = 1) else bit489 (gridRow t (min i j)) (max i j)

private lemma gridVal_symm (t i j : ℕ) : gridVal t j i = gridVal t i j := by
  simp only [gridVal, Nat.add_comm j i, min_comm j i, max_comm j i]

private def stepGridVal (t i j : ℕ) : Bool :=
  rule489
    (gridVal t i j)
    (gridVal t (i + 1) j)
    (gridVal t (if i = 0 then 1 else i - 1) j)
    (gridVal t i (j + 1))
    (gridVal t i (if j = 0 then 1 else j - 1))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private lemma gridVal_step_ok :
    ∀ t : Fin 13, ∀ i : Fin 14, ∀ j : Fin 14,
      i.val + j.val ≤ t.val + 1 → j.val ≤ i.val →
      stepGridVal t.val i.val j.val = gridVal (t.val + 1) i.val j.val := by
  decide

private lemma natAbs_sub_one (k : ℕ) :
    ((k : ℤ) - 1).natAbs = if k = 0 then 1 else k - 1 := by
  cases k with
  | zero => rfl
  | succ k => simp

private lemma cell_eq_gridVal (t : ℕ) (ht : t ≤ 13) (i j : ℤ) :
    cell 489 t i j = gridVal t i.natAbs j.natAbs := by
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
          cell 489 (t + 1) (u : ℤ) (v : ℤ) = gridVal (t + 1) u v by
        rcases le_total y x with hyx | hxy
        · exact step x y hle hyx
        · rw [← cell_swap, ← gridVal_symm]
          exact step y x (by omega) hxy
      intro u v huv hvu
      rw [cell_succ, ih (by omega), ih (by omega), ih (by omega), ih (by omega), ih (by omega)]
      have hu1 : ((u : ℤ) + 1).natAbs = u + 1 := by omega
      have hv1 : ((v : ℤ) + 1).natAbs = v + 1 := by omega
      simp only [Int.natAbs_natCast, hu1, hv1, natAbs_sub_one]
      exact gridVal_step_ok ⟨t, by omega⟩ ⟨u, by omega⟩ ⟨v, by omega⟩ huv hvu

private def axisMask : ℕ → ℕ
  | 0 => 59 | 1 => 94 | 2 => 231 | _ => 90

private def rowMask : ℕ → ℕ
  | 0 => 54 | 1 => 125 | 2 => 78 | _ => 21

private def radMask : ℕ → ℕ
  | 0 => 11 | 1 => 14 | 2 => 7 | _ => 10

private def stripe (x : ℕ) : Bool := decide (x % 4 = 0 ∨ x % 4 = 3)

private def axisPattern (t x : ℕ) : Bool :=
  if t < x then decide (t % 2 = 1)
  else if t - x < 8 then bit489 (axisMask (t % 4)) (t - x)
  else if x = 0 then decide (t % 2 = 0)
  else stripe x

private def radial (r : ℕ) (d : ℤ) : Bool :=
  if d < 0 then decide (r % 2 = 1) else bit489 (radMask r) d.toNat

-- The view records only cells whose values are needed to recover the axis.
private def view489 (r : ℕ) (d : ℤ) (x y : ℕ) : Option Bool :=
  if d < (y : ℤ) + 4 then some (radial r (d - (y : ℤ)))
  else if y = 0 then
    some (if d < 8 then bit489 (axisMask r) d.toNat
      else if x = 0 then decide (r % 2 = 0) else stripe x)
  else if y = 1 then
    some (if d < 7 then bit489 (rowMask r) d.toNat
      else if x = 1 then decide (r % 2 = 1) else stripe x)
  else if y = 2 ∧ x = 2 then some false
  else if y = 2 ∧ x = 3 then some true
  else if y = 2 ∧ d = 6 then some (decide (r = 1))
  else none

private def obs (t : ℕ) (i j : ℤ) : Option Bool :=
  let x := max i.natAbs j.natAbs
  let y := min i.natAbs j.natAbs
  view489 (t % 4) ((t : ℤ) - (x : ℤ)) x y

private def admits (o : Option Bool) (b : Bool) : Prop := o = none ∨ o = some b

private instance (o : Option Bool) (b : Bool) : Decidable (admits o b) := by
  unfold admits
  infer_instance

private lemma viewDepth (r x y : ℕ) (d d' : ℤ) (hy : y ≤ 3)
    (hd : 8 ≤ d) (hd' : 8 ≤ d') :
    view489 r d x y = view489 r d' x y := by
  have h0 : ¬d < (y : ℤ) + 4 := by omega
  have h0' : ¬d' < (y : ℤ) + 4 := by omega
  simp [view489, h0, h0', show ¬d < 8 by omega, show ¬d' < 8 by omega,
    show ¬d < 7 by omega, show ¬d' < 7 by omega, show d ≠ 6 by omega, show d' ≠ 6 by omega]

private lemma viewSpace (r y x x' : ℕ) (d : ℤ) (hx : 4 ≤ x) (hx' : 4 ≤ x')
    (hmod : x % 4 = x' % 4) :
    view489 r d x y = view489 r d x' y := by
  simp [view489, stripe, hmod, show x ≠ 0 by omega, show x' ≠ 0 by omega,
    show x ≠ 1 by omega, show x' ≠ 1 by omega, show x ≠ 2 by omega, show x' ≠ 2 by omega,
    show x ≠ 3 by omega, show x' ≠ 3 by omega]

private def viewAt (r : ℕ) (d : ℤ) (x y : ℕ) (a b : ℤ) : Option Bool :=
  let u := ((x : ℤ) + a).natAbs
  let v := ((y : ℤ) + b).natAbs
  let X := max u v
  let Y := min u v
  view489 r (d + (x : ℤ) - (X : ℤ)) X Y

private lemma viewAt_eq_obs (t x y : ℕ) (a b : ℤ) :
    viewAt (t % 4) ((t : ℤ) - (x : ℤ)) x y a b = obs t ((x : ℤ) + a) ((y : ℤ) + b) := by
  simp only [viewAt, obs, sub_add_cancel]

private lemma viewAt_depth (r x y : ℕ) (d d' a b : ℤ)
    (hy : y ≤ 2) (ha : -1 ≤ a) (ha' : a ≤ 1) (hb : -1 ≤ b) (hb' : b ≤ 1)
    (hd : 11 ≤ d) (hd' : 11 ≤ d') :
    viewAt r d x y a b = viewAt r d' x y a b := by
  unfold viewAt
  dsimp only
  apply viewDepth
  · exact le_trans (min_le_right _ _) (by omega)
  · have hmax : max ((x : ℤ) + a).natAbs ((y : ℤ) + b).natAbs ≤ x + 3 :=
      Nat.max_le.mpr ⟨by omega, by omega⟩
    omega
  · have hmax : max ((x : ℤ) + a).natAbs ((y : ℤ) + b).natAbs ≤ x + 3 :=
      Nat.max_le.mpr ⟨by omega, by omega⟩
    omega

private lemma viewAt_space (r x x' y : ℕ) (d a b : ℤ)
    (hx : 8 ≤ x) (hx' : 8 ≤ x') (hmod : x % 4 = x' % 4)
    (hy : y ≤ 2) (ha : -1 ≤ a) (ha' : a ≤ 1) (hb : -1 ≤ b) (hb' : b ≤ 1) :
    viewAt r d x y a b = viewAt r d x' y a b := by
  have hmax : ((y : ℤ) + b).natAbs ≤ ((x : ℤ) + a).natAbs := by omega
  have hmax' : ((y : ℤ) + b).natAbs ≤ ((x' : ℤ) + a).natAbs := by omega
  have hd : d + (x : ℤ) - (((x : ℤ) + a).natAbs : ℤ) = d - a := by omega
  have hd' : d + (x' : ℤ) - (((x' : ℤ) + a).natAbs : ℤ) = d - a := by omega
  simp only [viewAt, max_eq_left hmax, min_eq_right hmax,
    max_eq_left hmax', min_eq_right hmax', hd, hd']
  apply viewSpace
  · omega
  · omega
  · omega

private lemma viewAt_reduce (r x y : ℕ) (d a b : ℤ) (hy : y ≤ 2)
    (ha : -1 ≤ a) (ha' : a ≤ 1) (hb : -1 ≤ b) (hb' : b ≤ 1) :
    viewAt r d x y a b =
      viewAt r (if d < 11 then d else 11 + (d - 11) % 4)
        (if x < 8 then x else 8 + (x - 8) % 4) y a b := by
  split_ifs
  · rfl
  · exact viewAt_space r _ _ _ _ _ _ (by omega) (by omega) (by omega) hy ha ha' hb hb'
  · exact viewAt_depth r _ _ _ _ _ _ hy ha ha' hb hb' (by omega) (by omega)
  · rw [viewAt_depth r x y d (11 + (d - 11) % 4) a b hy ha ha' hb hb' (by omega) (by omega)]
    exact viewAt_space r _ _ _ _ _ _ (by omega) (by omega) (by omega) hy ha ha' hb hb'

private def compatible (r r' : ℕ) (d : ℤ) (x y : ℕ) (c e w n s : Bool) : Prop :=
  admits (viewAt r d x y 0 0) c →
  admits (viewAt r d x y 1 0) e →
  admits (viewAt r d x y (-1) 0) w →
  admits (viewAt r d x y 0 1) n →
  admits (viewAt r d x y 0 (-1)) s →
  admits (viewAt r' (d + 1) x y 0 0) (rule489 c e w n s)

private instance (r r' : ℕ) (d : ℤ) (x y : ℕ) (c e w n s : Bool) :
    Decidable (compatible r r' d x y c e w n s) := by
  unfold compatible
  infer_instance

set_option maxRecDepth 30000 in
set_option maxHeartbeats 30000000 in
private lemma viewFinite :
    ∀ r : Fin 4, ∀ d : Fin 15, ∀ x : Fin 12, ∀ y : Fin 3,
      y.val ≤ x.val → (x.val + d.val) % 4 = r.val → 8 ≤ x.val + d.val →
      y.val + 3 ≤ d.val →
      ∀ c e w n s : Bool, compatible r.val ((r.val + 1) % 4) (d.val : ℤ) x.val y.val c e w n s := by
  decide

set_option maxHeartbeats 1000000 in
private lemma viewStep (t x y : ℕ) (ht : 8 ≤ t) (hxy : y ≤ x) (hy : y ≤ 2)
    (hdeep : x + y + 3 ≤ t) (c e w n s : Bool) :
    compatible (t % 4) ((t + 1) % 4) ((t : ℤ) - (x : ℤ)) x y c e w n s := by
  let d : ℤ := (t : ℤ) - (x : ℤ)
  let d' : ℤ := if d < 11 then d else 11 + (d - 11) % 4
  let x' : ℕ := if x < 8 then x else 8 + (x - 8) % 4
  have hx' : x' < 12 := by dsimp [x']; split_ifs <;> omega
  have hd' : 0 ≤ d' ∧ d' < 15 := by dsimp [d', d]; split_ifs <;> omega
  have hxy' : y ≤ x' := by dsimp [x']; split_ifs <;> omega
  have hdeep' : (y : ℤ) + 3 ≤ d' := by dsimp [d', d]; split_ifs <;> omega
  have ht' : (8 : ℤ) ≤ (x' : ℤ) + d' := by dsimp [x', d', d]; split_ifs <;> omega
  have hm : (x' + d'.toNat) % 4 = t % 4 := by dsimp [x', d', d]; split_ifs <;> omega
  have hcast : (d'.toNat : ℤ) = d' := Int.toNat_of_nonneg hd'.1
  have htimeNat : 8 ≤ x' + d'.toNat := by omega
  have hdeepNat : y + 3 ≤ d'.toNat := by omega
  have h := viewFinite ⟨t % 4, by omega⟩ ⟨d'.toNat, by omega⟩ ⟨x', hx'⟩ ⟨y, by omega⟩
    hxy' hm htimeNat hdeepNat c e w n s
  dsimp only at h
  rw [hcast, show (t % 4 + 1) % 4 = (t + 1) % 4 by omega] at h
  have hold (a b : ℤ) (ha : -1 ≤ a) (ha' : a ≤ 1) (hb : -1 ≤ b) (hb' : b ≤ 1) :
      viewAt (t % 4) d x y a b = viewAt (t % 4) d' x' y a b :=
    viewAt_reduce _ _ _ _ _ _ hy ha ha' hb hb'
  have hnew : viewAt ((t + 1) % 4) (d + 1) x y 0 0 =
      viewAt ((t + 1) % 4) (d' + 1) x' y 0 0 := by
    by_cases hx : x < 8
    · have hx' : x' = x := if_pos hx
      rw [hx']
      by_cases hd : d < 11
      · rw [show d' = d from if_pos hd]
      · exact viewAt_depth _ _ _ _ _ _ _ hy (by omega) (by omega) (by omega) (by omega)
          (by omega) (by dsimp [d']; split_ifs <;> omega)
    · have hx' : x' = 8 + (x - 8) % 4 := if_neg hx
      have hs := viewAt_space ((t + 1) % 4) x x' y (d + 1) 0 0
        (by omega) (by omega) (by omega) hy (by omega) (by omega) (by omega) (by omega)
      rw [hs]
      by_cases hd : d < 11
      · rw [show d' = d from if_pos hd]
      · exact viewAt_depth _ _ _ _ _ _ _ hy (by omega) (by omega) (by omega) (by omega)
          (by omega) (by dsimp [d']; split_ifs <;> omega)
  change compatible (t % 4) ((t + 1) % 4) d x y c e w n s
  unfold compatible at h ⊢
  rw [hold 0 0 (by omega) (by omega) (by omega) (by omega),
      hold 1 0 (by omega) (by omega) (by omega) (by omega),
      hold (-1) 0 (by omega) (by omega) (by omega) (by omega),
      hold 0 1 (by omega) (by omega) (by omega) (by omega),
      hold 0 (-1) (by omega) (by omega) (by omega) (by omega), hnew]
  exact h


private lemma obsRadial (t : ℕ) (i j : ℤ)
    (h : (t : ℤ) - (i.natAbs : ℤ) - (j.natAbs : ℤ) < 4) :
    obs t i j = some (radial (t % 4) ((t : ℤ) - (i.natAbs : ℤ) - (j.natAbs : ℤ))) := by
  unfold obs
  dsimp only
  rcases le_total i.natAbs j.natAbs with hle | hle
  · rw [max_eq_right hle, min_eq_left hle]
    rw [view489, if_pos (by omega), show (t : ℤ) - (j.natAbs : ℤ) - (i.natAbs : ℤ) =
      (t : ℤ) - (i.natAbs : ℤ) - (j.natAbs : ℤ) by ring]
  · rw [max_eq_left hle, min_eq_right hle]
    rw [view489, if_pos (by omega)]

private lemma obs_canonical (t : ℕ) (i j : ℤ) :
    obs t i j = obs t ((max i.natAbs j.natAbs : ℕ) : ℤ) ((min i.natAbs j.natAbs : ℕ) : ℤ) := by
  have h : min i.natAbs j.natAbs ≤ max i.natAbs j.natAbs :=
    le_trans (min_le_left _ _) (le_max_left _ _)
  simp only [obs, Int.natAbs_natCast, max_eq_left h, min_eq_right h]

private lemma obsBaseFinite :
    ∀ x y : Fin 9, y.val ≤ x.val → x.val + y.val ≤ 8 →
      admits (obs 8 (x.val : ℤ) (y.val : ℤ)) (gridVal 8 x.val y.val) := by
  decide

private lemma obsOutside (t : ℕ) (i j : ℤ) (hout : t < i.natAbs + j.natAbs) :
    admits (obs t i j) (cell 489 t i j) := by
  rw [obsRadial t i j (by omega), cell_outside t i j hout]
  apply Or.inr
  rw [radial, if_pos (by omega), show t % 4 % 2 = t % 2 by omega]

private lemma obsBase (i j : ℤ) : admits (obs 8 i j) (cell 489 8 i j) := by
  rw [obs_canonical 8 i j, cell_canonical 8 i j]
  set x := max i.natAbs j.natAbs
  set y := min i.natAbs j.natAbs
  have hxy : y ≤ x := le_trans (min_le_left _ _) (le_max_left _ _)
  by_cases hout : 8 < x + y
  · exact obsOutside 8 (x : ℤ) (y : ℤ) (by simpa using hout)
  · rw [cell_eq_gridVal 8 (by omega), Int.natAbs_natCast, Int.natAbs_natCast]
    have hle : x + y ≤ 8 := by omega
    exact obsBaseFinite ⟨x, by omega⟩ ⟨y, by omega⟩ hxy hle

private lemma radFinite :
    ∀ r d : Fin 4, ∀ axis : Bool,
      rule489 (radial r.val ((d.val : ℤ) - 1)) (radial r.val ((d.val : ℤ) - 2))
        (radial r.val (d.val : ℤ)) (radial r.val ((d.val : ℤ) - 2))
        (radial r.val (if axis then (d.val : ℤ) - 2 else (d.val : ℤ))) =
      radial ((r.val + 1) % 4) (d.val : ℤ) := by
  decide

private lemma obsShell (t x y : ℕ) (ht : 8 ≤ t) (hxy : y ≤ x)
    (hlo : x + y ≤ t + 1) (hhi : t < x + y + 3)
    (ih : ∀ i j : ℤ, admits (obs t i j) (cell 489 t i j)) :
    admits (obs (t + 1) (x : ℤ) (y : ℤ)) (cell 489 (t + 1) (x : ℤ) (y : ℤ)) := by
  let d : ℤ := (t : ℤ) + 1 - (x : ℤ) - (y : ℤ)
  have hd : 0 ≤ d ∧ d < 4 := by dsimp [d]; omega
  have hx : 0 < x := by omega
  have old (i j k : ℤ) (hk : (t : ℤ) - (i.natAbs : ℤ) - (j.natAbs : ℤ) = k)
      (hk' : k < 4) : cell 489 t i j = radial (t % 4) k := by
    have h := ih i j
    rw [obsRadial t i j (by omega), hk] at h
    have he : radial (t % 4) k = cell 489 t i j := by simpa [admits] using h
    exact he.symm
  have hc := old (x : ℤ) (y : ℤ) (d - 1) (by dsimp [d]; omega) (by omega)
  have he := old ((x : ℤ) + 1) (y : ℤ) (d - 2) (by dsimp [d]; omega) (by omega)
  have hw := old ((x : ℤ) - 1) (y : ℤ) d (by dsimp [d]; omega) hd.2
  have hn := old (x : ℤ) ((y : ℤ) + 1) (d - 2) (by dsimp [d]; omega) (by omega)
  have hs := old (x : ℤ) ((y : ℤ) - 1) (if y = 0 then d - 2 else d)
    (by split_ifs <;> dsimp [d] <;> omega) (by split_ifs <;> omega)
  have hcast : (d.toNat : ℤ) = d := Int.toNat_of_nonneg hd.1
  have hfin := radFinite ⟨t % 4, by omega⟩ ⟨d.toNat, by omega⟩ (decide (y = 0))
  dsimp only at hfin
  rw [hcast, show (t % 4 + 1) % 4 = (t + 1) % 4 by omega] at hfin
  rw [obsRadial (t + 1) (x : ℤ) (y : ℤ) (by dsimp [d] at hd; omega), cell_succ,
    hc, he, hw, hn, hs]
  apply Or.inr
  congr 1
  simp only [Int.natAbs_natCast, Nat.cast_add, Nat.cast_one]
  change radial ((t + 1) % 4) d = _
  by_cases hy : y = 0 <;> simpa [hy] using hfin.symm

private lemma obsCell (t : ℕ) (ht : 8 ≤ t) :
    ∀ i j : ℤ, admits (obs t i j) (cell 489 t i j) := by
  induction t, ht using Nat.le_induction with
  | base => exact obsBase
  | succ t ht ih =>
    intro i j
    rw [obs_canonical (t + 1) i j, cell_canonical (t + 1) i j]
    set x := max i.natAbs j.natAbs
    set y := min i.natAbs j.natAbs
    have hxy : y ≤ x := le_trans (min_le_left _ _) (le_max_left _ _)
    by_cases hout : t + 1 < x + y
    · exact obsOutside (t + 1) (x : ℤ) (y : ℤ) (by simpa using hout)
    by_cases hshell : t < x + y + 3
    · exact obsShell t x y ht hxy (by omega) hshell ih
    by_cases hy : y ≤ 2
    · rw [cell_succ]
      have h := viewStep t x y ht hxy hy (by omega)
        (cell 489 t (x : ℤ) (y : ℤ))
        (cell 489 t ((x : ℤ) + 1) (y : ℤ))
        (cell 489 t ((x : ℤ) - 1) (y : ℤ))
        (cell 489 t (x : ℤ) ((y : ℤ) + 1))
        (cell 489 t (x : ℤ) ((y : ℤ) - 1))
      unfold compatible at h
      rw [viewAt_eq_obs, viewAt_eq_obs, viewAt_eq_obs, viewAt_eq_obs, viewAt_eq_obs,
        show (t : ℤ) - (x : ℤ) + 1 = ((t + 1 : ℕ) : ℤ) - (x : ℤ) by omega,
        viewAt_eq_obs] at h
      simp only [add_zero, ← sub_eq_add_neg] at h
      exact h (ih _ _) (ih _ _) (ih _ _) (ih _ _) (ih _ _)
    · apply Or.inl
      have hdeep : ¬ ((t + 1 : ℕ) : ℤ) - (x : ℤ) < (y : ℤ) + 4 := by omega
      simp only [obs, Int.natAbs_natCast, max_eq_left hxy, min_eq_right hxy]
      rw [view489, if_neg hdeep]
      simp only [show y ≠ 0 by omega, show y ≠ 1 by omega, show y ≠ 2 by omega, false_and, if_false]

private lemma axisMasksAgree :
    ∀ r d : Fin 4, radial r.val (d.val : ℤ) = bit489 (axisMask r.val) d.val := by
  decide

private lemma axis_observed (t x : ℕ) :
    obs t (x : ℤ) 0 = some (axisPattern t x) := by
  have hmax : max x 0 = x := max_eq_left (Nat.zero_le x)
  have hmin : min x 0 = 0 := min_eq_right (Nat.zero_le x)
  simp only [obs, Int.natAbs_natCast, Int.natAbs_zero, hmax, hmin, view489, Nat.cast_zero,
    zero_add, sub_zero, ↓reduceIte, axisPattern]
  by_cases hout : t < x
  · simp [hout, show (t : ℤ) - (x : ℤ) < 4 by omega,
      radial, show (t : ℤ) - (x : ℤ) < 0 by omega,
      show t % 4 % 2 = t % 2 by omega]
  · have hcast : ((t - x : ℕ) : ℤ) = (t : ℤ) - (x : ℤ) := Nat.cast_sub (by omega)
    have hnat : ((t : ℤ) - (x : ℤ)).toNat = t - x := by omega
    by_cases hsmall : t - x < 4
    · have h := axisMasksAgree ⟨t % 4, by omega⟩ ⟨t - x, hsmall⟩
      dsimp only at h
      rw [hcast] at h
      simp [hout, show (t : ℤ) - (x : ℤ) < 4 by omega, show t - x < 8 by omega, h]
    · by_cases hmid : t - x < 8
      · simp [hout, hmid, show ¬ ((t : ℤ) - (x : ℤ) < 4) by omega,
          show (t : ℤ) - (x : ℤ) < 8 by omega, hnat]
      · simp [hout, hmid, show ¬ ((t : ℤ) - (x : ℤ) < 4) by omega,
          show ¬ ((t : ℤ) - (x : ℤ) < 8) by omega,
          show t % 4 % 2 = t % 2 by omega]

private lemma axis_cell (t x : ℕ) (ht : 8 ≤ t) :
    cell 489 t (x : ℤ) 0 = axisPattern t x := by
  have h := obsCell t ht (x : ℤ) 0
  rw [axis_observed] at h
  have he : axisPattern t x = cell 489 t (x : ℤ) 0 := by simpa [admits] using h
  exact he.symm


private def gridAxisSum (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if gridVal n (n - k) 0 then (10 : ℤ) ^ (n - k) else 0

private lemma gridAxisSum_eq (n : ℕ) (hn : n < 14) : a n = gridAxisSum n := by
  unfold a gridAxisSum
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  rw [cell_eq_gridVal n (by omega), show ((k : ℤ) - (n : ℤ)).natAbs = n - k by omega, Int.natAbs_zero]

private def initial489 : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | 2 => 111
  | 3 => 100
  | 4 => 11011
  | 5 => 11110
  | 6 => 1110011
  | 7 => 1011010
  | 8 => 110111001
  | 9 => 111101000
  | 10 => 11100111001
  | 11 => 10110101000
  | 12 => 1101110011001
  | 13 => 1111010011000
  | _ => 0

private lemma a_eq_initial489 (n : ℕ) (hn : n < 14) : a n = initial489 n := by
  rw [gridAxisSum_eq n hn]
  have h : ∀ x : Fin 14, gridAxisSum x.val = initial489 x.val := by decide
  exact h ⟨n, hn⟩

private lemma recur489 (b : ℕ → ℤ)
    (hshift : ∀ n, 8 ≤ n →
      b (n + 4) = 10000 * b n + if n % 2 = 0 then 1001 else 11000)
    (n : ℕ) (hn : 14 ≤ n) :
    (b n : ℚ) = b (n - 2) + 10000 * b (n - 4) - 10000 * b (n - 6) := by
  have h₀ := hshift (n - 4) (by omega)
  have h₂ := hshift (n - 6) (by omega)
  rw [show n - 4 + 4 = n by omega] at h₀
  rw [show n - 6 + 4 = n - 2 by omega,
    show (n - 6) % 2 = (n - 4) % 2 by omega] at h₂
  have h : b n = b (n - 2) + 10000 * b (n - 4) - 10000 * b (n - 6) := by
    linarith
  exact_mod_cast h

open PowerSeries in
private lemma gf489 (b : ℕ → ℤ)
    (hinit : ∀ n, n < 14 → b n = initial489 n)
    (hrec : ∀ n : ℕ, 14 ≤ n → (b n : ℚ) =
      b (n - 2) + 10000 * b (n - 4) - 10000 * b (n - 6)) :
    mk (fun n => (b n : ℚ)) *
      (10000 * X ^ 6 - 10000 * X ^ 4 - X ^ 2 + 1 : PowerSeries ℚ) =
    10000 * X ^ 13 - 10010 * X ^ 9 + 990 * X ^ 8 - 100 * X ^ 7 -
      1000 * X ^ 6 + 11010 * X ^ 5 + 900 * X ^ 4 + 100 * X ^ 3 + 110 * X ^ 2 + 1 := by
  set F : PowerSeries ℚ := mk (fun n => (b n : ℚ)) with hF
  have lhs :
      F * (10000 * X ^ 6 - 10000 * X ^ 4 - X ^ 2 + 1 : PowerSeries ℚ) =
      F + (-1 : ℤ) • (F * X ^ 2) + (-10000 : ℤ) • (F * X ^ 4) +
        (10000 : ℤ) • (F * X ^ 6) := by
    simp only [zsmul_eq_mul]
    push_cast
    ring
  have rhs :
      (10000 * X ^ 13 - 10010 * X ^ 9 + 990 * X ^ 8 - 100 * X ^ 7 -
        1000 * X ^ 6 + 11010 * X ^ 5 + 900 * X ^ 4 + 100 * X ^ 3 +
        110 * X ^ 2 + 1 : PowerSeries ℚ) =
      (10000 : ℤ) • X ^ 13 + (-10010 : ℤ) • X ^ 9 + (990 : ℤ) • X ^ 8 +
        (-100 : ℤ) • X ^ 7 + (-1000 : ℤ) • X ^ 6 + (11010 : ℤ) • X ^ 5 +
        (900 : ℤ) • X ^ 4 + (100 : ℤ) • X ^ 3 + (110 : ℤ) • X ^ 2 +
        (1 : ℤ) • X ^ 0 := by
    simp only [zsmul_eq_mul]
    push_cast
    ring
  rw [lhs, rhs]
  ext n
  simp only [map_add, map_zsmul, coeff_mul_X_pow', hF, coeff_mk, coeff_X_pow]
  simp only [zsmul_eq_mul]
  by_cases hn : 14 ≤ n
  · have hr := hrec n hn
    simp only [show 2 ≤ n by omega, show 4 ≤ n by omega, show 6 ≤ n by omega,
      show n ≠ 13 by omega, show n ≠ 9 by omega, show n ≠ 8 by omega,
      show n ≠ 7 by omega, show n ≠ 6 by omega, show n ≠ 5 by omega,
      show n ≠ 4 by omega, show n ≠ 3 by omega, show n ≠ 2 by omega,
      show n ≠ 0 by omega, ite_true, ite_false]
    push_cast
    linarith
  · have h₀ := hinit n (by omega)
    have h₂ := hinit (n - 2) (by omega)
    have h₄ := hinit (n - 4) (by omega)
    have h₆ := hinit (n - 6) (by omega)
    rw [h₀, h₂, h₄, h₆]
    interval_cases n <;> norm_num [initial489]


private def axisDigit489 (p : ℕ → ℕ → Bool) (n x : ℕ) : ℤ :=
  if p n x then 10 ^ x else 0

private lemma digitSumShift489 (p : ℕ → ℕ → Bool) (n : ℕ)
    (hs : ∀ x, 0 < x → x ≤ n → p (n + 4) (4 + x) = p n x)
    (h0 : p n 0 = decide (n % 2 = 0))
    (h40 : p (n + 4) 0 = decide (n % 2 = 0))
    (h41 : p (n + 4) 1 = false)
    (h42 : p (n + 4) 2 = false)
    (h43 : p (n + 4) 3 = true)
    (h44 : p (n + 4) 4 = true) :
    ∑ x ∈ Finset.range (n + 4 + 1), axisDigit489 p (n + 4) x =
      10000 * (∑ x ∈ Finset.range (n + 1), axisDigit489 p n x) +
        if n % 2 = 0 then 1001 else 11000 := by
  rw [show n + 4 + 1 = 4 + (n + 1) by omega, Finset.sum_range_add,
    Finset.sum_range_succ' (fun x => axisDigit489 p (n + 4) (4 + x)),
    Finset.sum_range_succ' (axisDigit489 p n), mul_add, Finset.mul_sum]
  have hsum : (∑ x ∈ Finset.range n, axisDigit489 p (n + 4) (4 + (x + 1))) =
      ∑ x ∈ Finset.range n, 10000 * axisDigit489 p n (x + 1) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := Finset.mem_range.mp hx
    simp only [axisDigit489, hs (x + 1) (by omega) (by omega)]
    split
    · rw [pow_add]
      norm_num
    · simp
  rw [hsum]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, axisDigit489,
    h0, h40, h41, h42, h43, h44, Nat.add_zero]
  by_cases he : n % 2 = 0 <;> norm_num [he] <;> ring

private def pattern489 (m : ℕ → ℕ) (n x : ℕ) : Bool :=
  if n < x then decide (n % 2 = 1)
  else if n - x < 8 then (m (n % 4) / 2 ^ (n - x)) % 2 == 1
  else if x = 0 then decide (n % 2 = 0)
  else decide (x % 4 = 0 ∨ x % 4 = 3)

private lemma patternDigitSumShift489 (m : ℕ → ℕ) (n : ℕ) (hn : 8 ≤ n) :
    ∑ x ∈ Finset.range (n + 4 + 1), axisDigit489 (pattern489 m) (n + 4) x =
      10000 * (∑ x ∈ Finset.range (n + 1), axisDigit489 (pattern489 m) n x) +
        if n % 2 = 0 then 1001 else 11000 := by
  apply digitSumShift489
  · intro x hx hxn
    have hout : ¬ n + 4 < 4 + x := by omega
    have hxout : ¬ n < x := by omega
    have hdepth : n + 4 - (4 + x) = n - x := by omega
    have hmodt : (n + 4) % 4 = n % 4 := by omega
    have hmodx : (4 + x) % 4 = x % 4 := by omega
    simp [pattern489, hout, hxout, hdepth, hmodt, hmodx, Nat.ne_of_gt hx]
  · simp [pattern489, show ¬ n < 8 by omega]
  · have hdepth : ¬ n + 4 - 0 < 8 := by omega
    have hpar : (n + 4) % 2 = n % 2 := by omega
    unfold pattern489
    rw [if_neg (by omega), if_neg hdepth, if_pos rfl, hpar]
  · have hout : ¬ n + 4 < 1 := by omega
    have hdepth : ¬ n + 4 - 1 < 8 := by omega
    unfold pattern489
    rw [if_neg hout, if_neg hdepth]
    norm_num
  · have hout : ¬ n + 4 < 2 := by omega
    have hdepth : ¬ n + 4 - 2 < 8 := by omega
    unfold pattern489
    rw [if_neg hout, if_neg hdepth]
    norm_num
  · have hout : ¬ n + 4 < 3 := by omega
    have hdepth : ¬ n + 4 - 3 < 8 := by omega
    unfold pattern489
    rw [if_neg hout, if_neg hdepth]
    norm_num
  · have hout : ¬ n + 4 < 4 := by omega
    have hdepth : ¬ n + 4 - 4 < 8 := by omega
    unfold pattern489
    rw [if_neg hout, if_neg hdepth]
    norm_num

private lemma a_eq_axisDigits489 (n : ℕ) (hn : 8 ≤ n) :
    a n = ∑ x ∈ Finset.range (n + 1), axisDigit489 (pattern489 axisMask) n x := by
  calc
    a n = ∑ k ∈ Finset.range (n + 1), axisDigit489 (pattern489 axisMask) n (n - k) := by
      unfold a
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.mp hk
      rw [show (k : ℤ) - (n : ℤ) = -((n - k : ℕ) : ℤ) by omega,
        cell_neg_i, axis_cell n (n - k) hn]
      rfl
    _ = _ := by
      simpa only [Nat.add_sub_cancel] using
        Finset.sum_range_reflect (axisDigit489 (pattern489 axisMask) n) (n + 1)

private lemma a_shift489 (n : ℕ) (hn : 8 ≤ n) :
    a (n + 4) = 10000 * a n + if n % 2 = 0 then 1001 else 11000 := by
  rw [a_eq_axisDigits489 (n + 4) (by omega), a_eq_axisDigits489 n hn]
  exact patternDigitSumShift489 axisMask n hn

theorem OMA.solution : type_of% @OMA.S_oeis_a282606.main :=
  ⟨recur489 a a_shift489, gf489 a a_eq_initial489 (recur489 a a_shift489)⟩
