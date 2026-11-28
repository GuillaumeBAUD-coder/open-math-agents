import OMAStatements.S_oeis_a284245
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A284245: Rule841 axis recurrence and generating function

Source: https://oeis.org/A284245
Credit: @CubeJerry
Canonical statement: @clementtrecourt

From stage11 the axis alternates, except for an explicit four-phase tip.
A three-valued invariant fixes the checkerboard-ON class, alternating axis
interior, and a depth10,width5,eight-phase moving tip; all remaining cells
are unspecified. Finite local implications and an exact initial grid are
checked in the Lean kernel, then induction proves the infinite evolution.
The closed form yields the recurrence and full generating-function identity.

Prior partial result: @longling12's PR27662 proves Rules841 and857 coincide,
using the checkerboard-ON invariant. That proof gives no axis classification.
We acknowledge its prior invariant; no code from it is incorporated here.
Our moving-tip certificate and axis classification are new for this target.
Generic symmetry, finite-grid and three-valued infrastructure is adapted
from our earlier original CA proofs in this session.
-/

namespace A284245

open OMA.S_oeis_a284245

lemma cell_swap (code n : ℕ) (x y : ℤ) : cell code n x y = cell code n y x := by
  induction n generalizing x y with
  | zero => simp [cell, and_comm]
  | succ n ih =>
    simp only [cell, ih x y, ih (x + 1) y, ih (x - 1) y,
      ih x (y + 1), ih x (y - 1)]
    congr 1
    omega

lemma cell_neg_left (code n : ℕ) (x y : ℤ) : cell code n (-x) y = cell code n x y := by
  induction n generalizing x y with
  | zero => simp [cell]
  | succ n ih =>
    simp only [cell]
    rw [show -x + 1 = -(x - 1) by omega,
      show -x - 1 = -(x + 1) by omega, ih, ih, ih, ih, ih]
    congr 1
    omega

def prevN (x : ℕ) : ℕ := if x = 0 then 1 else x - 1

def quad (n x y : ℕ) : Bool := cell 841 n x y

def rule (c e w u d : Bool) : Bool :=
  (841 : ℕ).testBit (c.toNat + 2 * (e.toNat + w.toNat + u.toNat + d.toNat))

lemma quad_swap (n x y : ℕ) : quad n x y = quad n y x := cell_swap 841 n x y

lemma left_prev (n x y : ℕ) : cell 841 n ((x : ℤ) - 1) y = quad n (prevN x) y := by
  by_cases h : x = 0
  · subst x
    simpa [prevN, quad] using cell_neg_left 841 n 1 y
  · congr 2
    simp only [prevN, h, if_false]
    omega

lemma down_prev (n x y : ℕ) : cell 841 n x ((y : ℤ) - 1) = quad n x (prevN y) := by
  rw [cell_swap, left_prev, quad_swap]

lemma quad_succ (n x y : ℕ) : quad (n + 1) x y =
    rule (quad n x y) (quad n (x + 1) y) (quad n (prevN x) y)
      (quad n x (y + 1)) (quad n x (prevN y)) := by
  simp only [quad, cell, rule, Nat.cast_add, Nat.cast_one, left_prev, down_prev]

lemma quad_outside (n x y : ℕ) (h : n < x + y) : quad n x y = decide (0 < n) := by
  induction n generalizing x y with
  | zero => simp [quad, cell]; omega
  | succ n ih =>
    have hx : n < prevN x + y := by unfold prevN; split <;> omega
    have hy : n < x + prevN y := by unfold prevN; split <;> omega
    rw [quad_succ, ih x y (by omega), ih (x + 1) y (by omega),
      ih (prevN x) y hx, ih x (y + 1) (by omega), ih x (prevN y) hy]
    cases n <;> norm_num [rule] <;> decide

/-- Values zero and one assert a cell value; two leaves it unspecified. -/
def Agrees (v : ℕ) (b : Bool) : Prop := v = 2 ∨ v = b.toNat

instance (v : ℕ) (b : Bool) : Decidable (Agrees v b) := by
  unfold Agrees
  infer_instance

def ones (v : ℕ) : ℕ := if v = 1 then 1 else 0
def possible (v : ℕ) : ℕ := if v = 0 then 0 else 1

def triNext (c e w u d : ℕ) : ℕ :=
  let lo := ones e + ones w + ones u + ones d
  let hi := possible e + possible w + possible u + possible d
  if (if c = 0 then hi = 0 ∨ 3 ≤ lo
      else if c = 1 then (lo = 1 ∧ hi = 1) ∨ 4 ≤ lo else 4 ≤ lo) then 1
  else if (if c = 0 then 1 ≤ lo ∧ hi ≤ 2
      else if c = 1 then hi = 0 ∨ (2 ≤ lo ∧ hi ≤ 3) else (lo = 2 ∧ hi = 2)) then 0
  else 2

def triAxis (c e w u : ℕ) : ℕ :=
  if c = 1 ∧ e = 0 ∧ w = 0 then 0 else triNext c e w u u

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def triNext_sound : ∀ c e w u d : Fin 3, ∀ bc be bw bu bd : Bool,
    Agrees c bc → Agrees e be → Agrees w bw → Agrees u bu → Agrees d bd →
      Agrees (triNext c e w u d) (rule bc be bw bu bd) := by
  decide

def compatible (v c e w u d : ℕ) : Bool :=
  v == 2 || v == triNext c e w u d

lemma compatible_sound {v c e w u d : ℕ}
    (hc : c < 3) (he : e < 3) (hw : w < 3) (hu : u < 3) (hd : d < 3)
    (h : compatible v c e w u d = true)
    {bc be bw bu bd : Bool}
    (hbc : Agrees c bc) (hbe : Agrees e be) (hbw : Agrees w bw)
    (hbu : Agrees u bu) (hbd : Agrees d bd) : Agrees v (rule bc be bw bu bd) := by
  simp only [compatible, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact Or.inl h
  · rw [h]
    exact triNext_sound ⟨c, hc⟩ ⟨e, he⟩ ⟨w, hw⟩ ⟨u, hu⟩ ⟨d, hd⟩
      bc be bw bu bd hbc hbe hbw hbu hbd

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def triAxis_sound : ∀ c e w u : Fin 3, ∀ bc be bw bu : Bool,
    Agrees c bc → Agrees e be → Agrees w bw → Agrees u bu →
      Agrees (triAxis c e w u) (rule bc be bw bu bu) := by
  decide

def compatibleAxis (v c e w u : ℕ) : Bool :=
  v == 2 || v == triAxis c e w u

lemma compatibleAxis_sound {v c e w u : ℕ}
    (hc : c < 3) (he : e < 3) (hw : w < 3) (hu : u < 3)
    (h : compatibleAxis v c e w u = true)
    {bc be bw bu : Bool}
    (hbc : Agrees c bc) (hbe : Agrees e be) (hbw : Agrees w bw)
    (hbu : Agrees u bu) : Agrees v (rule bc be bw bu bu) := by
  simp only [compatibleAxis, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact Or.inl h
  · rw [h]
    exact triAxis_sound ⟨c, hc⟩ ⟨e, he⟩ ⟨w, hw⟩ ⟨u, hu⟩
      bc be bw bu hbc hbe hbw hbu

end A284245

namespace A284245

def tipRow (p y : ℕ) : ℕ :=
  ([283988, 1118481, 2442565, 1642773, 2511957, 1675605, 345172, 1397073, 2446661, 1660181, 2511957, 1675605, 279636, 1380625, 2442309, 1659157, 2507861, 1675605, 279892, 1118545, 2376773, 1659157, 2507861, 1675605, 283988, 1118481, 2442565, 1659157, 2507861, 1675605, 345172, 1397073, 2381125, 1660181, 2507861, 1675605, 279636, 1118481, 2376773, 1642773, 2511957, 1675605, 279892, 1118545, 2376773, 1659157, 2511957, 1675605] : List ℕ)[p * 6 + y]?.getD 0

def tip (p d y : ℕ) : ℕ := tipRow p y / 4 ^ d % 4

set_option maxRecDepth 10000 in
def tip_lt_three : ∀ p : Fin 8, ∀ d : Fin 11, ∀ y : Fin 6, tip p d y < 3 := by
  decide

end A284245

namespace A284245

def pattern (n x y : ℕ) : ℕ :=
  let a := max x y
  let b := min x y
  if n < a + b then 1
  else if (n + a + b) % 2 = 1 then 1
  else if 5 < b then 2
  else if a + 10 < n then if b = 0 then 0 else 2
  else tip (n % 8) (n - a) b

lemma pattern_swap (n x y : ℕ) : pattern n x y = pattern n y x := by
  simp only [pattern, max_comm x y, min_comm x y]

lemma pattern_checker (n x y : ℕ) (h : (n + x + y) % 2 = 1) : pattern n x y = 1 := by
  have he : n + max x y + min x y = n + x + y := by
    have := max_add_min x y
    omega
  simp only [pattern, he, h, if_true]
  split <;> rfl

lemma pattern_lt (n x y : ℕ) : pattern n x y < 3 := by
  unfold pattern
  dsimp
  split_ifs with h1 h2 h3 h4 h5
  all_goals try omega
  exact tip_lt_three ⟨n % 8, Nat.mod_lt _ (by decide)⟩
    ⟨n - max x y, by omega⟩ ⟨min x y, by omega⟩

lemma pattern_small {n m x y : ℕ} (hn : 40 ≤ n) (hm : 40 ≤ m)
    (hx : x ≤ 10) (hy : y ≤ 8) (hr : n % 2 = m % 2) : pattern n x y = pattern m x y := by
  have ha : max x y ≤ 10 := by omega
  have hb : min x y ≤ 8 := by omega
  have hp : (n + max x y + min x y) % 2 = (m + max x y + min x y) % 2 := by omega
  simp only [pattern, if_neg (show ¬ n < max x y + min x y by omega),
    if_neg (show ¬ m < max x y + min x y by omega), hp,
    if_pos (show max x y + 10 < n by omega),
    if_pos (show max x y + 10 < m by omega)]

lemma pattern_translate {n m x z y : ℕ} (hy : y ≤ 8)
    (hx : 9 ≤ x) (hz : 9 ≤ z) (he : x + m = z + n) (hr : n % 8 = m % 8) :
    pattern n x y = pattern m z y := by
  have hxy : y ≤ x := by omega
  have hzy : y ≤ z := by omega
  have hcone : n < x + y ↔ m < z + y := by omega
  have hinterior : x + 10 < n ↔ z + 10 < m := by omega
  have hdepth : n - x = m - z := by omega
  have hp : (n + x + y) % 2 = (m + z + y) % 2 := by omega
  simp only [pattern, max_eq_left hxy, min_eq_right hxy,
    max_eq_left hzy, min_eq_right hzy, hp,
    hcone, hinterior, hdepth, hr]

lemma pattern_middle {n m x z y : ℕ} (hy : y ≤ 8)
    (hx : 9 ≤ x) (hz : 9 ≤ z) (hn : x + 10 < n) (hm : z + 10 < m)
    (hr : (n + x) % 2 = (m + z) % 2) : pattern n x y = pattern m z y := by
  have hxy : y ≤ x := by omega
  have hzy : y ≤ z := by omega
  have hp : (n + x + y) % 2 = (m + z + y) % 2 := by omega
  simp only [pattern, max_eq_left hxy, min_eq_right hxy,
    max_eq_left hzy, min_eq_right hzy, hp,
    if_neg (show ¬ n < x + y by omega), if_neg (show ¬ m < z + y by omega),
    if_pos hn, if_pos hm]

def localCheck (n x y : ℕ) : Bool :=
  if y = 0 then
    compatibleAxis (pattern (n + 1) x y) (pattern n x y)
      (pattern n (x + 1) y) (pattern n (prevN x) y) (pattern n x (y + 1))
  else
    compatible (pattern (n + 1) x y) (pattern n x y)
      (pattern n (x + 1) y) (pattern n (prevN x) y)
      (pattern n x (y + 1)) (pattern n x (prevN y))

end A284245

namespace A284245

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
def local_certificate :
    ((List.range 37).all fun t =>
      (List.range 50).all fun x =>
        (List.range 6).all fun y => if y ≤ x then localCheck (t + 11) x y else true) = true := by
  decide

lemma localCheck_finite (n x y : ℕ) (hn : 11 ≤ n) (hn' : n < 48)
    (hx : x < 50) (hy : y < 6) (hyx : y ≤ x) : localCheck n x y = true := by
  have h := (List.all_eq_true.mp local_certificate) (n - 11) (by simp; omega)
  have h := (List.all_eq_true.mp h) x (by simpa)
  have h := (List.all_eq_true.mp h) y (by simpa)
  simpa only [Nat.sub_add_cancel hn, if_pos hyx] using h

lemma prevN_le (x : ℕ) : prevN x ≤ x + 1 := by
  unfold prevN
  split <;> omega

lemma localCheck_small {n m x y : ℕ} (hn : 40 ≤ n) (hm : 40 ≤ m)
    (hx : x ≤ 9) (hy : y ≤ 5) (hr : n % 8 = m % 8) : localCheck n x y = localCheck m x y := by
  have hpx : prevN x ≤ 10 := by have := prevN_le x; omega
  have hpy : prevN y ≤ 8 := by have := prevN_le y; omega
  by_cases hy0 : y = 0
  all_goals simp only [localCheck, hy0, if_true, if_false]
  all_goals congr 1 <;> apply pattern_small <;> omega

lemma localCheck_middle {n m x z y : ℕ} (hy : y ≤ 5)
    (hx : 10 ≤ x) (hz : 10 ≤ z) (hn : x + 12 ≤ n) (hm : z + 12 ≤ m) (hr : (n + x) % 2 = (m + z) % 2) :
    localCheck n x y = localCheck m z y := by
  have hpx : prevN x = x - 1 := if_neg (by omega)
  have hpz : prevN z = z - 1 := if_neg (by omega)
  have hpy : prevN y ≤ 8 := by have := prevN_le y; omega
  by_cases hy0 : y = 0
  all_goals simp only [localCheck, hy0, if_true, if_false, hpx, hpz]
  all_goals congr 1 <;> apply pattern_middle <;> omega

lemma localCheck_translate {n m x z y : ℕ} (hy : y ≤ 5)
    (hx : 10 ≤ x) (hz : 10 ≤ z) (he : x + m = z + n) (hr : n % 8 = m % 8) :
    localCheck n x y = localCheck m z y := by
  have hpx : prevN x = x - 1 := if_neg (by omega)
  have hpz : prevN z = z - 1 := if_neg (by omega)
  have hpy : prevN y ≤ 8 := by have := prevN_le y; omega
  by_cases hy0 : y = 0
  all_goals simp only [localCheck, hy0, if_true, if_false, hpx, hpz]
  all_goals congr 1 <;> apply pattern_translate <;> omega

lemma localCheck_all (n x y : ℕ) (hn : 11 ≤ n) (hx : x ≤ n + 1) (hy : y ≤ 5) (hyx : y ≤ x) :
    localCheck n x y = true := by
  by_cases hsmall : n < 40
  · exact localCheck_finite n x y hn (by omega) (by omega) (by omega) hyx
  let m := 40 + n % 8
  have hm : 40 ≤ m := by dsimp [m]; omega
  have hm' : m < 48 := by dsimp [m]; omega
  have hr : n % 8 = m % 8 := by dsimp [m]; omega
  by_cases hleft : x ≤ 9
  · rw [localCheck_small (m := m) (by omega) (by omega) hleft hy hr]
    exact localCheck_finite m x y (by omega) hm' (by omega) (by omega) hyx
  by_cases hmiddle : x + 12 ≤ n
  · rw [localCheck_middle (m := m) (z := 20 + x % 2) hy (by omega) (by omega) hmiddle (by omega) (by omega)]
    exact localCheck_finite m (20 + x % 2) y (by omega) hm' (by omega) (by omega) (by omega)
  let z := x + m - n
  have hz : 10 ≤ z := by dsimp [z]; omega
  have he : x + m = z + n := by dsimp [z]; omega
  have hz' : z < 50 := by dsimp [z]; omega
  rw [localCheck_translate (m := m) (z := z) hy (by omega) hz he hr]
  exact localCheck_finite m z y (by omega) hm' hz' (by omega) (by omega)

lemma step_sound (n : ℕ) (hn : 11 ≤ n)
    (ih : ∀ x y, Agrees (pattern n x y) (quad n x y)) :
    ∀ x y, Agrees (pattern (n + 1) x y) (quad (n + 1) x y) := by
  have one (a b : ℕ) (hp : (n + a + b) % 2 = 1) : quad n a b = true := by
    have h := ih a b
    rw [pattern_checker n a b hp] at h
    cases hb : quad n a b <;> simp_all [Agrees]
  have wedge : ∀ x y, y ≤ x →
      Agrees (pattern (n + 1) x y) (quad (n + 1) x y) := by
    intro x y hyx
    by_cases hout : n + 1 < x + y
    · rw [quad_outside (n + 1) x y hout]
      right
      simp only [pattern, max_eq_left hyx, min_eq_right hyx, if_pos hout,
        decide_eq_true (by omega : 0 < n + 1), Bool.toNat_true]
    by_cases hcolor : (n + 1 + x + y) % 2 = 1
    · right
      rw [pattern_checker (n + 1) x y hcolor, quad_succ,
        one (x + 1) y (by omega),
        one (prevN x) y (by unfold prevN; split <;> omega),
        one x (y + 1) (by omega),
        one x (prevN y) (by unfold prevN; split <;> omega)]
      cases quad n x y <;> decide
    by_cases hhigh : 5 < y
    · left
      simp only [pattern, max_eq_left hyx, min_eq_right hyx, if_neg hout,
        if_neg hcolor, if_pos hhigh]
    have hc := localCheck_all n x y hn (by omega) (by omega) hyx
    rw [quad_succ]
    by_cases hy0 : y = 0
    · subst y
      apply compatibleAxis_sound (pattern_lt _ _ _) (pattern_lt _ _ _)
        (pattern_lt _ _ _) (pattern_lt _ _ _)
      · simpa [localCheck] using hc
      all_goals exact ih _ _
    · apply compatible_sound (pattern_lt _ _ _) (pattern_lt _ _ _)
        (pattern_lt _ _ _) (pattern_lt _ _ _) (pattern_lt _ _ _)
      · simpa only [localCheck, if_neg hy0] using hc
      all_goals exact ih _ _
  intro x y
  by_cases h : y ≤ x
  · exact wedge x y h
  · rw [pattern_swap (n + 1) x y, quad_swap (n + 1) x y]
    exact wedge y x (by omega)

end A284245

namespace A284245Initial

open A284245 OMA.S_oeis_a284245

/-- Quadrant rows inside the finite propagation diamond. -/
def rows : List (List ℕ) :=
  [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [7, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
   [15, 5, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0],
   [29, 14, 7, 3, 1, 0, 0, 0, 0, 0, 0, 0],
   [58, 21, 10, 5, 3, 1, 0, 0, 0, 0, 0, 0],
   [125, 58, 21, 11, 7, 3, 1, 0, 0, 0, 0, 0],
   [254, 85, 59, 21, 15, 5, 3, 1, 0, 0, 0, 0],
   [471, 239, 127, 62, 29, 14, 7, 3, 1, 0, 0, 0],
   [939, 343, 174, 93, 42, 21, 10, 5, 3, 1, 0, 0],
   [2005, 938, 341, 186, 93, 42, 21, 11, 7, 3, 1, 0]]

def grid (n x y : ℕ) : Bool :=
  if x + y ≤ n then ((rows[n]?.getD [])[y]?.getD 0).testBit x else decide (0 < n)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 6000000 in
def grid_step : ∀ n : Fin 11, ∀ x y : Fin 12,
    grid (n + 1) x y =
      rule (grid n x y) (grid n (x + 1) y) (grid n (prevN x) y)
        (grid n x (y + 1)) (grid n x (prevN y)) := by
  decide +kernel

lemma quad_eq_grid (n : ℕ) (hn : n ≤ 11) (x y : ℕ) :
    quad n x y = grid n x y := by
  induction n generalizing x y with
  | zero =>
    by_cases h : x + y ≤ 0
    · have hx : x = 0 := by omega
      have hy : y = 0 := by omega
      subst x; subst y
      rfl
    · rw [quad_outside 0 x y (by omega)]
      simp [grid, h]
  | succ n ih =>
    by_cases h : x + y ≤ n + 1
    · have hx : x < 12 := by omega
      have hy : y < 12 := by omega
      rw [quad_succ]
      simp only [ih (by omega)]
      exact (grid_step ⟨n, by omega⟩ ⟨x, hx⟩ ⟨y, hy⟩).symm
    · rw [quad_outside (n + 1) x y (by omega)]
      simp [grid, h]

theorem cell_eq_grid (n x y : ℕ) (hn : n ≤ 11) (_hx : x ≤ 11) (_hy : y ≤ 11) :
    cell 841 n x y = grid n x y := quad_eq_grid n hn x y

lemma a_grid (n : ℕ) (hn : n ≤ 11) :
    a n = ∑ k ∈ Finset.range (n + 1),
      if grid n (n - k) 0 then (2 : ℤ) ^ (n - k) else 0 := by
  unfold a
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simpa using hk
  have he : (k : ℤ) - n = -((n - k : ℕ) : ℤ) := by omega
  rw [he, cell_neg_left]
  rw [show cell 841 n ((n - k : ℕ) : ℤ) 0 = grid n (n - k) 0 from
    quad_eq_grid n hn (n - k) 0]

end A284245Initial

namespace A284245

set_option maxRecDepth 10000 in
def initial_pattern : ∀ x y : Fin 12,
    Agrees (pattern 11 x y) (A284245Initial.grid 11 x y) := by
  decide +kernel

lemma base_sound (x y : ℕ) : Agrees (pattern 11 x y) (quad 11 x y) := by
  rw [A284245Initial.quad_eq_grid 11 (by omega)]
  by_cases h : x + y ≤ 11
  · exact initial_pattern ⟨x, by omega⟩ ⟨y, by omega⟩
  · right
    have he : max x y + min x y = x + y := max_add_min x y
    simp only [pattern, if_pos (show 11 < max x y + min x y by omega),
      A284245Initial.grid, if_neg h, decide_eq_true (by decide : 0 < 11), Bool.toNat_true]

theorem pattern_sound (n : ℕ) (hn : 11 ≤ n) :
    ∀ x y, Agrees (pattern n x y) (quad n x y) := by
  induction n, hn using Nat.le_induction with
  | base => exact base_sound
  | succ n hn ih => exact step_sound n hn ih

end A284245

namespace A284245Algebra
open OMA.S_oeis_a284245 PowerSeries

def extra (n d : ℕ) : Bool :=
  match n % 4 with
  | 0 => decide (d = 2 ∨ d = 4 ∨ d = 6)
  | 1 => decide (d = 2 ∨ d = 8)
  | 2 => decide (d = 2)
  | _ => decide (d = 2 ∨ d = 4)
def pattern (n d : ℕ) : Bool := decide (d % 2 = 1) || extra n d
def Axis : Prop := ∀ n k : ℕ, 11 ≤ n → k ≤ n →
  cell 841 n ((k : ℤ) - n) 0 = pattern n k
def parity (n : ℕ) : ℚ := if n % 2 = 0 then 2 else 1
def correction (n : ℕ) : ℚ :=
  ∑ d ∈ Finset.range 9, if extra n d then (2 : ℚ) ^ (8 - d) else 0
def leading (n : ℕ) : ℚ := 512 + 3 * correction n
def baseline (n : ℕ) : ℚ :=
  ∑ d ∈ Finset.range (n + 1), if d % 2 = 1 then (2 : ℚ) ^ (n - d) else 0
def initialValues : List ℤ := [1, 0, 3, 7, 15, 29, 58, 125, 254, 471, 939]
def Initial : Prop := ∀ n : ℕ, n < 11 → a n = initialValues[n]?.getD 0

lemma extra_large (n d : ℕ) (hd : 9 ≤ d) : extra n d = false := by
  have hn : n % 4 < 4 := Nat.mod_lt n (by decide)
  unfold extra
  interval_cases h : n % 4 <;> simp <;> omega

lemma extra_even (n d : ℕ) (h : extra n d = true) : d % 2 = 0 := by
  have hn : n % 4 < 4 := Nat.mod_lt n (by decide)
  unfold extra at h
  interval_cases e : n % 4 <;> simp_all <;> omega

lemma leading_period {n m : ℕ} (h : n % 4 = m % 4) : leading n = leading m := by
  simp only [leading, correction, extra, h]
  rfl

lemma baseline_succ (n : ℕ) :
    baseline (n + 1) = 2 * baseline n + if (n + 1) % 2 = 1 then 1 else 0 := by
  unfold baseline
  rw [Finset.sum_range_succ]
  have hs : (∑ d ∈ Finset.range (n + 1), if d % 2 = 1 then (2 : ℚ) ^ (n + 1 - d) else 0) =
      2 * ∑ d ∈ Finset.range (n + 1), if d % 2 = 1 then (2 : ℚ) ^ (n - d) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have he : n + 1 - d = (n - d) + 1 := by have := Finset.mem_range.mp hd; omega
    split_ifs <;> simp [he, pow_succ, mul_comm]
  rw [hs]
  simp

lemma baseline_formula (n : ℕ) : 3 * baseline n = 2 ^ (n + 1) - parity n := by
  induction n with
  | zero => norm_num [baseline, parity]
  | succ n ih =>
    have hm : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hm with hm | hm
    · have hn : (n + 1) % 2 = 1 := by omega
      rw [baseline_succ]
      simp only [parity, hm, hn] at ih ⊢
      simp only [ite_true, ite_false, Nat.one_ne_zero, pow_succ] at ih ⊢
      linarith
    · have hn : (n + 1) % 2 = 0 := by omega
      rw [baseline_succ]
      simp only [parity, hm, hn] at ih ⊢
      simp only [ite_true, ite_false, Nat.one_ne_zero, Nat.zero_ne_one, pow_succ] at ih ⊢
      linarith

lemma correction_sum (n : ℕ) (hn : 11 ≤ n) :
    (∑ d ∈ Finset.range (n + 1), if extra n d then (2 : ℚ) ^ (n - d) else 0) =
      2 ^ (n - 8) * correction n := by
  have hs : (∑ d ∈ Finset.range (n + 1), if extra n d then (2 : ℚ) ^ (n - d) else 0) =
      ∑ d ∈ Finset.range 9, if extra n d then (2 : ℚ) ^ (n - d) else 0 := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro d hd hnot
    have hlarge : 9 ≤ d := by simpa using hnot
    rw [extra_large n d hlarge]
    rfl
  rw [hs, correction, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have he : n - d = (n - 8) + (8 - d) := by have := Finset.mem_range.mp hd; omega
  cases extra n d <;> simp [he, pow_add]

lemma formula (haxis : Axis) (n : ℕ) (hn : 11 ≤ n) :
    3 * (a n : ℚ) = leading n * 2 ^ (n - 8) - parity n := by
  have hs : (a n : ℚ) = baseline n +
      ∑ d ∈ Finset.range (n + 1), if extra n d then (2 : ℚ) ^ (n - d) else 0 := by
    simp only [a, Int.cast_sum, Int.cast_ite, Int.cast_pow, Int.cast_ofNat, Int.cast_zero,
      baseline, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    have hdn : d ≤ n := by have := Finset.mem_range.mp hd; omega
    rw [haxis n d hn hdn]
    by_cases ho : d % 2 = 1
    · have he : extra n d = false := by
        cases hx : extra n d
        · rfl
        · have := extra_even n d hx; omega
      simp [pattern, ho, he]
    · simp [pattern, ho]
  rw [correction_sum n hn] at hs
  have hb := baseline_formula n
  have hp : (2 : ℚ) ^ (n + 1) = 512 * 2 ^ (n - 8) := by
    have he : n + 1 = (n - 8) + 9 := by omega
    rw [he, pow_add]
    norm_num
    ring
  rw [hp] at hb
  unfold leading
  nlinarith

lemma recurrence (haxis : Axis) (n : ℕ) (hn : 17 ≤ n) :
    (a n : ℚ) = a (n - 2) + 16 * a (n - 4) - 16 * a (n - 6) := by
  have h0 := formula haxis n (by omega)
  have h2 := formula haxis (n - 2) (by omega)
  have h4 := formula haxis (n - 4) (by omega)
  have h6 := formula haxis (n - 6) (by omega)
  rw [leading_period (show (n - 4) % 4 = n % 4 by omega)] at h4
  rw [leading_period (show (n - 6) % 4 = (n - 2) % 4 by omega)] at h6
  have p2 : parity (n - 2) = parity n := by
    unfold parity
    rw [show (n - 2) % 2 = n % 2 by omega]
  have p4 : parity (n - 4) = parity n := by
    unfold parity
    rw [show (n - 4) % 2 = n % 2 by omega]
  have p6 : parity (n - 6) = parity n := by
    unfold parity
    rw [show (n - 6) % 2 = n % 2 by omega]
  rw [p2] at h2
  rw [p4] at h4
  rw [p6] at h6
  have e0 : n - 8 = (n - 14) + 6 := by omega
  have e2 : n - 2 - 8 = (n - 14) + 4 := by omega
  have e4 : n - 4 - 8 = (n - 14) + 2 := by omega
  have e6 : n - 6 - 8 = n - 14 := by omega
  rw [e0, pow_add] at h0
  rw [e2, pow_add] at h2
  rw [e4, pow_add] at h4
  rw [e6] at h6
  norm_num at h0 h2 h4
  nlinarith

end A284245Algebra

namespace A284245

set_option maxRecDepth 10000 in
def axis_table : ∀ p : Fin 8, ∀ d : Fin 11,
    tip p d 0 = (A284245Algebra.pattern p d).toNat := by
  decide +kernel

lemma pattern_axis (n x : ℕ) (hn : 11 ≤ n) (hx : x ≤ n) :
    pattern n x 0 = (A284245Algebra.pattern n (n - x)).toNat := by
  have hcone : ¬ n < x := by omega
  have hpar : (n + x) % 2 = (n - x) % 2 := by omega
  simp only [pattern, max_eq_left (Nat.zero_le x), min_eq_right (Nat.zero_le x),
    Nat.add_zero, if_neg hcone, show ¬ 5 < 0 by omega, if_false, if_pos rfl]
  rw [hpar]
  by_cases ho : (n - x) % 2 = 1
  · simp [ho, A284245Algebra.pattern]
  · rw [if_neg ho]
    by_cases hinterior : x + 10 < n
    · rw [if_pos hinterior, A284245Algebra.pattern,
        A284245Algebra.extra_large n (n - x) (by omega)]
      simp [ho]
    · rw [if_neg hinterior]
      have h := axis_table ⟨n % 8, Nat.mod_lt _ (by decide)⟩ ⟨n - x, by omega⟩
      have h4 : (n % 8) % 4 = n % 4 := by omega
      simpa only [A284245Algebra.pattern, A284245Algebra.extra, h4] using h

lemma axis_of_sound
    (hs : ∀ n : ℕ, 11 ≤ n → ∀ x y, Agrees (pattern n x y) (quad n x y)) :
    A284245Algebra.Axis := by
  intro n k hn hk
  have h := hs n hn (n - k) 0
  rw [pattern_axis n (n - k) hn (Nat.sub_le _ _), Nat.sub_sub_self hk] at h
  have he : OMA.S_oeis_a284245.cell 841 n ((k : ℤ) - n) 0 = quad n (n - k) 0 := by
    rw [show (k : ℤ) - n = -((n - k : ℕ) : ℤ) by omega, cell_neg_left]
    rfl
  rw [he]
  cases hc : quad n (n - k) 0 <;>
    cases hv : A284245Algebra.pattern n k <;> simp_all [Agrees]

end A284245

namespace A284245Initial

open A284245 OMA.S_oeis_a284245

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
lemma initial : A284245Algebra.Initial := by
  intro n hn
  rw [a_grid n (by omega)]
  interval_cases n <;> decide +kernel

end A284245Initial

namespace A284245Algebra
open OMA.S_oeis_a284245 PowerSeries

def value (n : ℕ) : ℚ :=
  if n < 11 then (initialValues[n]?.getD 0 : ℤ)
  else (leading n * 2 ^ (n - 8) - parity n) / 3
lemma a_value (haxis : Axis) (hi : Initial) (n : ℕ) : (a n : ℚ) = value n := by
  unfold value
  split_ifs with h
  · rw [hi n h]
  · have := formula haxis n (by omega)
    linarith
lemma coeff_mk_mul_monomial (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then f (n - k) * c else 0 := by
  rw [← mul_assoc, coeff_mul_X_pow']
  split_ifs with h
  · rw [coeff_mul_C, coeff_mk]
  · rfl

set_option maxHeartbeats 3000000 in
lemma generating_function (haxis : Axis) (hi : Initial) :
    mk (fun n => (a n : ℚ)) * (C (1) * X ^ 0 + C (-1) * X ^ 2 + C (-16) * X ^ 4 + C (16) * X ^ 6 : PowerSeries ℚ) =
      C (1) * X ^ 0 + C (2) * X ^ 2 + C (7) * X ^ 3 + C (-4) * X ^ 4 + C (22) * X ^ 5 + C (11) * X ^ 6 + C (-16) * X ^ 7 + C (4) * X ^ 8 + C (-6) * X ^ 9 + C (-3) * X ^ 10 + C (-2) * X ^ 11 + C (-1) * X ^ 12 + C (-16) * X ^ 14 + C (16) * X ^ 16 := by
  ext n
  simp only [mul_add, map_add, coeff_mk_mul_monomial, coeff_C_mul_X_pow]
  by_cases h : 17 ≤ n
  · have hr := recurrence haxis n h
    simp (disch := omega) only [if_pos, if_neg, Nat.sub_zero]
    linarith
  · simp_rw [a_value haxis hi]
    interval_cases n <;> norm_num [value, initialValues, leading, correction, extra, parity,
      Finset.sum_range_succ]

theorem solution_of_axis (haxis : Axis) (hi : Initial) :
    type_of% @OMA.S_oeis_a284245.main := by
  refine ⟨recurrence haxis, ?_⟩
  convert generating_function haxis hi using 1 <;>
    simp only [map_one, map_neg, map_ofNat] <;> ring

end A284245Algebra

theorem OMA.solution : type_of% @OMA.S_oeis_a284245.main :=
  A284245Algebra.solution_of_axis
    (A284245.axis_of_sound A284245.pattern_sound) A284245Initial.initial
