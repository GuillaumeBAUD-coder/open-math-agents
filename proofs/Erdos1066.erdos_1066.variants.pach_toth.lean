import FormalConjectures.ErdosProblems.«1066»

/-! The open-chain version of the construction of Pach and Tóth, On the
independence number of coin graphs, Geombinatorics 6 (1996), 30–33. -/

open Filter Finset
open scoped BigOperators EuclideanGeometry

namespace OMA.CoinChain

/-- Coefficients in the basis `1, s, t, s*t`. The coordinates below give two
successive blocks and the translation that repeats them. -/
structure Coord where
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ


def rotSqConst : ℚ := (449437 / 466874)
def rotSqSqrt : ℚ := (-1670439 / 3268118)

def firstBlock : Fin 16 → Coord × Coord :=
  ![
    ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩,
    ⟨⟨0, 0, 0, 0⟩, ⟨(-1), 0, 0, 0⟩⟩,
    ⟨⟨0, (1 / 2), 0, 0⟩, ⟨(-1 / 2), 0, 0, 0⟩⟩,
    ⟨⟨0, (1 / 2), 0, 0⟩, ⟨(-3 / 2), 0, 0, 0⟩⟩,
    ⟨⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩⟩,
    ⟨⟨0, (1 / 2), 0, 0⟩, ⟨(1 / 2), 0, 0, 0⟩⟩,
    ⟨⟨0, (1 / 2), 0, 0⟩, ⟨(3 / 2), 0, 0, 0⟩⟩,
    ⟨⟨(10 / 101), (100 / 101), 0, 0⟩, ⟨(-102 / 101), (-10 / 101), 0, 0⟩⟩,
    ⟨⟨(-10 / 101), (100 / 101), 0, 0⟩, ⟨(-201 / 101), (-10 / 101), 0, 0⟩⟩,
    ⟨⟨0, (299 / 202), 0, 0⟩, ⟨(-3 / 2), (-20 / 101), 0, 0⟩⟩,
    ⟨⟨(1397 / 3737), (15241 / 22422), (-3296 / 3737), (-438 / 3737)⟩, ⟨(14507 / 7474), (219 / 3737), (2794 / 3737), (4030 / 11211)⟩⟩,
    ⟨⟨(1027 / 3737), (9085 / 11211), (367 / 3737), (1178 / 3737)⟩, ⟨(5422 / 3737), (-589 / 3737), (2054 / 3737), (6959 / 11211)⟩⟩,
    ⟨⟨(24 / 37), (100 / 101), (-29 / 37), (20 / 101)⟩, ⟨(70 / 37), (-10 / 101), (48 / 37), (99 / 101)⟩⟩,
    ⟨⟨(3821 / 3737), (13115 / 11211), (367 / 3737), (1178 / 3737)⟩, ⟨(8718 / 3737), (-151 / 3737), (2054 / 3737), (6959 / 11211)⟩⟩,
    ⟨⟨(3451 / 3737), (29159 / 22422), (-3296 / 3737), (-438 / 3737)⟩, ⟨(13773 / 7474), (-959 / 3737), (2794 / 3737), (4030 / 11211)⟩⟩,
    ⟨⟨(48 / 37), (299 / 202), 0, 0⟩, ⟨(169 / 74), (-20 / 101), 0, 0⟩⟩]

def secondBlock : Fin 16 → Coord × Coord :=
  ![
    ⟨⟨(24 / 37), (299 / 202), 0, 0⟩, ⟨(29 / 74), (-20 / 101), 0, 0⟩⟩,
    ⟨⟨(36 / 37), (299 / 202), 0, 0⟩, ⟨(99 / 74), (-20 / 101), 0, 0⟩⟩,
    ⟨⟨(30 / 37), (7299 / 3737), 0, 0⟩, ⟨(32 / 37), (-1346 / 3737), 0, 0⟩⟩,
    ⟨⟨(42 / 37), (7299 / 3737), 0, 0⟩, ⟨(67 / 37), (-1346 / 3737), 0, 0⟩⟩,
    ⟨⟨(12 / 37), (299 / 202), 0, 0⟩, ⟨(-41 / 74), (-20 / 101), 0, 0⟩⟩,
    ⟨⟨(18 / 37), (7299 / 3737), 0, 0⟩, ⟨(-3 / 37), (-1346 / 3737), 0, 0⟩⟩,
    ⟨⟨(6 / 37), (7299 / 3737), 0, 0⟩, ⟨(-38 / 37), (-1346 / 3737), 0, 0⟩⟩,
    ⟨⟨(3998 / 3737), (18303 / 7474), 0, 0⟩, ⟨(9829 / 7474), (-1590 / 3737), 0, 0⟩⟩,
    ⟨⟨(4486 / 3737), (18303 / 7474), 0, 0⟩, ⟨(17239 / 7474), (-1590 / 3737), 0, 0⟩⟩,
    ⟨⟨(42 / 37), (11004 / 3737), 0, 0⟩, ⟨(67 / 37), (-1834 / 3737), 0, 0⟩⟩,
    ⟨⟨(1393 / 3737), (23590 / 11211), (-4024 / 3737), (-850 / 3737)⟩, ⟨(-5850 / 3737), (-1771 / 3737), (-1574 / 3737), (-3386 / 11211)⟩⟩,
    ⟨⟨(1637 / 3737), (51523 / 22422), (-319 / 3737), (362 / 3737)⟩, ⟨(-7995 / 7474), (-1165 / 3737), (-2062 / 3737), (-7729 / 11211)⟩⟩,
    ⟨⟨(24 / 37), (18303 / 7474), (-43 / 37), (-488 / 3737)⟩, ⟨(-119 / 74), (-1590 / 3737), (-36 / 37), (-3705 / 3737)⟩⟩,
    ⟨⟨(3211 / 3737), (58295 / 22422), (-319 / 3737), (362 / 3737)⟩, ⟨(-16043 / 7474), (-2015 / 3737), (-2062 / 3737), (-7729 / 11211)⟩⟩,
    ⟨⟨(3455 / 3737), (31319 / 11211), (-4024 / 3737), (-850 / 3737)⟩, ⟨(-6169 / 3737), (-1409 / 3737), (-1574 / 3737), (-3386 / 11211)⟩⟩,
    ⟨⟨(42 / 37), (11004 / 3737), 0, 0⟩, ⟨(-81 / 37), (-1834 / 3737), 0, 0⟩⟩]

def periodOffset : Coord × Coord := ⟨⟨(42 / 37), (11004 / 3737), 0, 0⟩, ⟨(-7 / 37), (-1834 / 3737), 0, 0⟩⟩


noncomputable def s : ℝ := Real.sqrt 3
noncomputable def t : ℝ := Real.sqrt ((rotSqConst : ℝ) + (rotSqSqrt : ℝ) * s)

lemma s_bounds : (173205 / 100000 : ℝ) ≤ s ∧ s ≤ 173206 / 100000 := by
  unfold s
  constructor
  · exact (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  · exact (Real.sqrt_le_left (by norm_num)).2 (by norm_num)

lemma t_bounds : (27810 / 100000 : ℝ) ≤ t ∧ t ≤ 27813 / 100000 := by
  have hmin : (27810 / 100000 : ℝ)^2 ≤ (rotSqConst : ℝ) + (rotSqSqrt : ℝ) * s := by
    have h := s_bounds.2
    norm_num [rotSqConst, rotSqSqrt] at *
    linarith
  have hmax : (rotSqConst : ℝ) + (rotSqSqrt : ℝ) * s ≤ (27813 / 100000 : ℝ)^2 := by
    have h := s_bounds.1
    norm_num [rotSqConst, rotSqSqrt] at *
    linarith
  have h0 : 0 ≤ (rotSqConst : ℝ) + (rotSqSqrt : ℝ) * s := (sq_nonneg _).trans hmin
  exact ⟨(Real.le_sqrt (by norm_num) h0).2 hmin, (Real.sqrt_le_left (by norm_num)).2 hmax⟩

lemma st_bounds : (48167 / 100000 : ℝ) ≤ s * t ∧ s * t ≤ 48174 / 100000 := by
  constructor
  · calc
      (48167 / 100000 : ℝ) ≤ (173205 / 100000 : ℝ) * (27810 / 100000 : ℝ) := by norm_num
      _ ≤ s * t := mul_le_mul s_bounds.1 t_bounds.1 (by norm_num) (Real.sqrt_nonneg _)
  · calc
      s * t ≤ (173206 / 100000 : ℝ) * (27813 / 100000 : ℝ) :=
        mul_le_mul s_bounds.2 t_bounds.2 (Real.sqrt_nonneg _) (by norm_num)
      _ ≤ _ := by norm_num

noncomputable def Coord.eval (x : Coord) : ℝ := (x.a : ℝ) + x.b * s + ((x.c : ℝ) + x.d * s) * t

def Coord.add (x y : Coord) : Coord := ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩
def Coord.sub (x y : Coord) : Coord := ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.d - y.d⟩

def Coord.mul (x y : Coord) : Coord :=
  let ac := x.c * y.c + 3 * x.d * y.d
  let bd := x.c * y.d + x.d * y.c
  ⟨x.a * y.a + 3 * x.b * y.b + ac * rotSqConst + 3 * bd * rotSqSqrt,
    x.a * y.b + x.b * y.a + ac * rotSqSqrt + bd * rotSqConst,
    x.a * y.c + 3 * x.b * y.d + x.c * y.a + 3 * x.d * y.b,
    x.a * y.d + x.b * y.c + x.c * y.b + x.d * y.a⟩

lemma eval_add (x y : Coord) : (x.add y).eval = x.eval + y.eval := by
  unfold Coord.add Coord.eval
  push_cast
  ring

lemma eval_sub (x y : Coord) : (x.sub y).eval = x.eval - y.eval := by
  unfold Coord.sub Coord.eval
  push_cast
  ring

lemma s_sq : s ^ 2 = 3 := Real.sq_sqrt (by norm_num)

lemma t_sq : t ^ 2 = (rotSqConst : ℝ) + (rotSqSqrt : ℝ) * s := by
  apply Real.sq_sqrt
  have h := s_bounds.2
  norm_num [rotSqConst, rotSqSqrt] at *
  linarith

lemma semiMul (a b c d : ℝ) :
    (a + b * s) * (c + d * s) = (a * c + 3 * b * d) + (a * d + b * c) * s := by
  linear_combination b * d * s_sq

lemma eval_mul (x y : Coord) : (x.mul y).eval = x.eval * y.eval := by
  dsimp only [Coord.mul, Coord.eval]
  push_cast
  symm
  calc
    _ = (((x.a : ℝ) + x.b * s) * ((y.a : ℝ) + y.b * s)) +
          (((x.c : ℝ) + x.d * s) * ((y.c : ℝ) + y.d * s)) * t ^ 2 +
          ((((x.a : ℝ) + x.b * s) * ((y.c : ℝ) + y.d * s)) +
           (((x.c : ℝ) + x.d * s) * ((y.a : ℝ) + y.b * s))) * t := by ring
    _ = _ := by rw [t_sq, semiMul, semiMul, semiMul, semiMul, semiMul]; ring

def lowerTerm (c l u : ℚ) : ℚ := c * if 0 ≤ c then l else u
def Coord.lower (x : Coord) : ℚ := x.a +
  lowerTerm x.b (173205/100000) (173206/100000) +
  lowerTerm x.c (27810/100000) (27813/100000) +
  lowerTerm x.d (48167/100000) (48174/100000)

lemma lowerTerm_le {c l u : ℚ} {x : ℝ} (hl : (l : ℝ) ≤ x) (hu : x ≤ (u : ℝ)) :
    (lowerTerm c l u : ℝ) ≤ (c : ℝ) * x := by
  unfold lowerTerm
  split
  · rename_i hc
    push_cast
    exact mul_le_mul_of_nonneg_left hl (by exact_mod_cast hc)
  · rename_i hc
    push_cast
    exact mul_le_mul_of_nonpos_left hu (by exact_mod_cast (le_of_lt (lt_of_not_ge hc)))

lemma lower_eval (x : Coord) : (x.lower : ℝ) ≤ x.eval := by
  unfold Coord.lower Coord.eval
  push_cast
  rw [add_mul, mul_assoc]
  have hs := lowerTerm_le (c := x.b) (l := 173205/100000) (u := 173206/100000)
    (by convert s_bounds.1 using 1; norm_num) (by convert s_bounds.2 using 1; norm_num)
  have ht := lowerTerm_le (c := x.c) (l := 27810/100000) (u := 27813/100000)
    (by convert t_bounds.1 using 1; norm_num) (by convert t_bounds.2 using 1; norm_num)
  have hst := lowerTerm_le (c := x.d) (l := 48167/100000) (u := 48174/100000)
    (by convert st_bounds.1 using 1; norm_num) (by convert st_bounds.2 using 1; norm_num)
  linarith only [hs, ht, hst]

abbrev Pt := Coord × Coord

def Pt.add (x y : Pt) : Pt := (x.1.add y.1, x.2.add y.2)
def Pt.distSq (x y : Pt) : Coord :=
  let u := x.1.sub y.1
  let v := x.2.sub y.2
  (u.mul u).add (v.mul v)

abbrev Coord.isOne (x : Coord) : Prop := x.a = 1 ∧ x.b = 0 ∧ x.c = 0 ∧ x.d = 0

lemma eval_one {x : Coord} (h : x.isOne) : x.eval = 1 := by
  rcases h with ⟨ha, hb, hc, hd⟩
  simp [Coord.eval, ha, hb, hc, hd]

noncomputable def planePt (k : ℕ) (x : Pt) : ℝ² :=
  !₂[x.1.eval + k * periodOffset.1.eval, x.2.eval + k * periodOffset.2.eval]

lemma planeDist (k l : ℕ) (a b : Pt) :
    dist (planePt k a) (planePt l b) = Real.sqrt
      ((a.1.eval + k * periodOffset.1.eval - (b.1.eval + l * periodOffset.1.eval)) ^ 2 +
       (a.2.eval + k * periodOffset.2.eval - (b.2.eval + l * periodOffset.2.eval)) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp [planePt, Real.dist_eq, sq_abs]

lemma eval_distSq (a b : Pt) : (a.distSq b).eval =
    (a.1.eval - b.1.eval)^2 + (a.2.eval - b.2.eval)^2 := by
  simp [Pt.distSq, eval_add, eval_mul, eval_sub, pow_two]

lemma samePeriod_dist (k : ℕ) (a b : Pt) :
    dist (planePt k a) (planePt k b) = Real.sqrt (a.distSq b).eval := by
  rw [planeDist, eval_distSq]
  congr 1
  ring

lemma nextPeriod_dist (k : ℕ) (a b : Pt) :
    dist (planePt k a) (planePt (k+1) b) = Real.sqrt (a.distSq (b.add periodOffset)).eval := by
  rw [planeDist, eval_distSq]
  simp only [Pt.add, eval_add, Nat.cast_add, Nat.cast_one]
  congr 1
  ring

lemma dist_of_cert (x : Coord) (h : x.isOne ∨ 1 ≤ x.lower) : 1 ≤ Real.sqrt x.eval := by
  rcases h with h | h
  · simp [eval_one h]
  · have h' : (1 : ℝ) ≤ x.lower := by exact_mod_cast h
    exact le_trans (by norm_num) (Real.sqrt_le_sqrt (h'.trans (lower_eval x)))

def block (p : Bool) (i : Fin 16) : Pt := if p then secondBlock i else firstBlock i

def edges : List (Fin 16 × Fin 16) :=
  [(0,1), (0,2), (0,4), (0,5), (1,2), (1,3), (2,3), (2,5), (3,7),
   (3,8), (4,5), (4,6), (5,6), (6,10), (6,11), (7,8), (7,9), (8,9),
   (10,11), (10,12), (11,12), (12,13), (12,14), (13,14), (13,15), (14,15)]

abbrev Edge (i j : Fin 16) : Prop := (i,j) ∈ edges ∨ (j,i) ∈ edges
abbrev Link (i j : Fin 16) : Prop := (i,j) ∈ ([(9,4),(9,6),(15,1),(15,3)] : List (Fin 16 × Fin 16))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma certificateSame (p q : Bool) (i j : Fin 16) (h : (p,i) ≠ (q,j)) :
    ((block p i).distSq (block q j)).isOne ∨ 1 ≤ ((block p i).distSq (block q j)).lower := by
  revert h j
  cases p <;> cases q <;> fin_cases i <;> decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma certificateNext (p q : Bool) (i j : Fin 16) :
    ((block p i).distSq ((block q j).add periodOffset)).isOne ∨
      1 ≤ ((block p i).distSq ((block q j).add periodOffset)).lower := by
  revert j
  cases p <;> cases q <;> fin_cases i <;> decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma certificateEdge (p : Bool) (i j : Fin 16) (h : Edge i j) :
    ((block p i).distSq (block p j)).isOne := by
  revert h j
  cases p <;> fin_cases i <;> decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma certificateLinkFirst (i j : Fin 16) (h : Link i j) :
    ((block false i).distSq (block true j)).isOne := by
  revert h j
  fin_cases i <;> decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 10000000 in
lemma certificateLinkSecond (i j : Fin 16) (h : Link i j) :
    ((block true i).distSq ((block false j).add periodOffset)).isOne := by
  revert h j
  fin_cases i <;> decide +kernel

lemma leftmost (p : Bool) (i : Fin 16) : 0 ≤ (block p i).1.eval := by
  suffices h : 0 ≤ (block p i).1.lower by
    exact (show (0 : ℝ) ≤ (block p i).1.lower by exact_mod_cast h).trans (lower_eval _)
  cases p <;> fin_cases i <;> decide +kernel

lemma rightmost (p : Bool) (i : Fin 16) : (block p i).1.eval ≤ 7 := by
  let b : Coord := (⟨7,0,0,0⟩ : Coord).sub (block p i).1
  have hb : 0 ≤ b.lower := by
    dsimp only [b]
    cases p <;> fin_cases i <;> decide +kernel
  have hb' := (show (0 : ℝ) ≤ b.lower by exact_mod_cast hb).trans (lower_eval b)
  have h7 : (⟨7,0,0,0⟩ : Coord).eval = 7 := by simp [Coord.eval]
  dsimp only [b] at hb'
  rw [eval_sub, h7] at hb'
  exact sub_nonneg.mp hb'

lemma period_pos : (6 : ℝ) ≤ periodOffset.1.eval := by
  have h : (6 : ℚ) ≤ periodOffset.1.lower := by decide +kernel
  exact (show (6 : ℝ) ≤ periodOffset.1.lower by exact_mod_cast h).trans (lower_eval _)

lemma farPeriod_dist (k l : ℕ) (a b : Pt) (ha : a.1.eval ≤ 7) (hb : 0 ≤ b.1.eval)
    (hkl : k + 2 ≤ l) : 1 ≤ dist (planePt k a) (planePt l b) := by
  rw [planeDist]
  have hd : (2 : ℝ) ≤ (l : ℝ) - k := by
    have h : (k : ℝ) + 2 ≤ (l : ℝ) := by exact_mod_cast hkl
    linarith
  have hgap : (12 : ℝ) ≤ ((l : ℝ) - k) * periodOffset.1.eval := by
    calc
      (12 : ℝ) = 2 * 6 := by norm_num
      _ ≤ _ := mul_le_mul hd period_pos (by norm_num) (by linarith)
  have hx : a.1.eval + k * periodOffset.1.eval - (b.1.eval + l * periodOffset.1.eval) ≤ -1 := by
    nlinarith only [hgap, ha, hb]
  apply (Real.le_sqrt (by norm_num) (by positivity)).2
  nlinarith only [mul_nonneg (show 0 ≤ -1 - (a.1.eval + (k : ℝ) * periodOffset.1.eval -
    (b.1.eval + (l : ℝ) * periodOffset.1.eval)) by linarith)
    (show 0 ≤ 1 - (a.1.eval + (k : ℝ) * periodOffset.1.eval -
    (b.1.eval + (l : ℝ) * periodOffset.1.eval)) by linarith),
    sq_nonneg (a.2.eval + (k : ℝ) * periodOffset.2.eval - (b.2.eval + (l : ℝ) * periodOffset.2.eval))]

def phase (n : ℕ) : Bool := n % 2 == 1
noncomputable def node (x : ℕ × Fin 16) : ℝ² := planePt (x.1 / 2) (block (phase x.1) x.2)

lemma node_sep {x y : ℕ × Fin 16} (hne : x ≠ y) : 1 ≤ dist (node x) (node y) := by
  suffices h : ∀ x y : ℕ × Fin 16, x.1 / 2 ≤ y.1 / 2 → x ≠ y → 1 ≤ dist (node x) (node y) by
    rcases le_total (x.1 / 2) (y.1 / 2) with hxy | hyx
    · exact h x y hxy hne
    · rw [dist_comm]
      exact h y x hyx hne.symm
  intro x y hxy hne'
  unfold node
  by_cases h0 : x.1 / 2 = y.1 / 2
  · rw [h0, samePeriod_dist]
    apply dist_of_cert
    apply certificateSame
    intro h
    apply hne'
    have hp := congrArg Prod.fst h
    have hs := congrArg Prod.snd h
    have hm : x.1 % 2 = y.1 % 2 := by
      unfold phase at hp
      have hx := Nat.mod_lt x.1 (by norm_num : 0 < 2)
      have hy := Nat.mod_lt y.1 (by norm_num : 0 < 2)
      by_contra hh
      have hh' : x.1 % 2 = 0 ∧ y.1 % 2 = 1 ∨ x.1 % 2 = 1 ∧ y.1 % 2 = 0 := by omega
      rcases hh' with ⟨hx0, hy1⟩ | ⟨hx1, hy0⟩ <;> simp_all
    exact Prod.ext (by omega) hs
  by_cases h1 : x.1 / 2 + 1 = y.1 / 2
  · rw [← h1, nextPeriod_dist]
    exact dist_of_cert _ (certificateNext _ _ _ _)
  exact farPeriod_dist _ _ _ _ (rightmost _ _) (leftmost _ _) (by omega)

lemma node_edge (n : ℕ) {i j : Fin 16} (h : Edge i j) :
    dist (node (n,i)) (node (n,j)) = 1 := by
  unfold node
  change dist (planePt (n/2) _) (planePt (n/2) _) = 1
  rw [samePeriod_dist, eval_one (certificateEdge _ _ _ h)]
  norm_num

lemma node_link (n : ℕ) {i j : Fin 16} (h : Link i j) :
    dist (node (n,i)) (node (n+1,j)) = 1 := by
  unfold node
  change dist (planePt (n/2) (block (phase n) i)) (planePt ((n+1)/2) (block (phase (n+1)) j)) = 1
  rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with h0 | h1
  · have h' : (n+1)/2 = n/2 := by omega
    have h'' : (n+1)%2 = 1 := by omega
    simp only [phase, h0, h'', h', show ((0 : ℕ) == 1) = false from rfl, beq_self_eq_true]
    rw [samePeriod_dist, eval_one (certificateLinkFirst _ _ h)]
    norm_num
  · have h' : (n+1)/2 = n/2+1 := by omega
    have h'' : (n+1)%2 = 0 := by omega
    simp only [phase, h1, h'', h', show ((0 : ℕ) == 1) = false from rfl, beq_self_eq_true]
    rw [nextPeriod_dist, eval_one (certificateLinkSecond _ _ h)]
    norm_num


def group (i : Fin 16) : Fin 6 :=
  ⟨if i = 0 then 0 else 1 + (i.val - 1) / 3, by split <;> omega⟩

def cappedGroup (i : Fin 16) : Fin 4 :=
  ⟨if i.val < 7 then 0 else 1 + (i.val - 7) / 3, by split <;> omega⟩

abbrev Clean (S : Finset (Fin 16)) : Prop := ∀ i ∈ S, ∀ j ∈ S, ¬ Edge i j

lemma sameGroup_edge (i j : Fin 16) (h : i ≠ j) (heq : group i = group j) : Edge i j := by
  revert heq h j
  fin_cases i <;> decide +kernel

lemma capEdge (i j : Fin 16) (hi : i ≠ 1 ∧ i ≠ 3 ∧ i ≠ 4 ∧ i ≠ 6)
    (hj : j ≠ 1 ∧ j ≠ 3 ∧ j ≠ 4 ∧ j ≠ 6) (h : i ≠ j)
    (heq : cappedGroup i = cappedGroup j) : Edge i j := by
  revert heq h hj hi
  fin_cases i <;> fin_cases j <;> decide +kernel

lemma group_inj {S : Finset (Fin 16)} (hS : Clean S) : Set.InjOn group S := by
  intro i hi j hj hij
  by_contra hne
  exact hS i hi j hj (sameGroup_edge i j hne hij)

lemma card_block {S : Finset (Fin 16)} (hS : Clean S) : S.card ≤ 6 := by
  have h := Finset.card_le_univ (S.image group)
  rw [Finset.card_image_of_injOn (group_inj hS)] at h
  simpa using h

lemma full_group {S : Finset (Fin 16)} (hS : Clean S) (hc : S.card = 6) (i : Fin 6) :
    ∃ j ∈ S, group j = i := by
  have hall : S.image group = univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_image_of_injOn (group_inj hS), hc]
    simp
  exact Finset.mem_image.mp (by rw [hall]; simp)

lemma forced {S : Finset (Fin 16)} (hS : Clean S) (hc : S.card = 6) {w : Fin 16}
    (hw : w ∈ S) (i : Fin 16) (j : Fin 6)
    (hf : ∀ v : Fin 16, group v = j → v ≠ i → Edge w v) : i ∈ S := by
  rcases full_group hS hc j with ⟨v, hv, he⟩
  by_contra hn
  have hne : v ≠ i := fun h => hn (h ▸ hv)
  exact hS w hw v hv (hf v he hne)

lemma endpoints {S : Finset (Fin 16)} (hS : Clean S) (hc : S.card = 6) : 9 ∈ S ∧ 15 ∈ S := by
  rcases full_group hS hc 0 with ⟨v, hv, hv0⟩
  have only_zero : ∀ v : Fin 16, group v = 0 → v = 0 := by decide +kernel
  have h0 : (0 : Fin 16) ∈ S := only_zero v hv0 ▸ hv
  have h3 := forced hS hc h0 3 1 (by decide +kernel)
  have h6 := forced hS hc h0 6 2 (by decide +kernel)
  have h12 := forced hS hc h6 12 4 (by decide +kernel)
  exact ⟨forced hS hc h3 9 3 (by decide +kernel), forced hS hc h12 15 5 (by decide +kernel)⟩

lemma next_block {S T : Finset (Fin 16)} (hS : Clean S) (hT : Clean T) (hc : S.card = 6)
    (hl : ∀ i ∈ S, ∀ j ∈ T, ¬ Link i j) : T.card ≤ 4 := by
  rcases endpoints hS hc with ⟨hp,hq⟩
  have ha {i : Fin 16} (hi : i ∈ T) : i ≠ 1 ∧ i ≠ 3 ∧ i ≠ 4 ∧ i ≠ 6 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl
    · exact hl 15 hq 1 hi (by decide +kernel)
    · exact hl 15 hq 3 hi (by decide +kernel)
    · exact hl 9 hp 4 hi (by decide +kernel)
    · exact hl 9 hp 6 hi (by decide +kernel)
  have hinj : Set.InjOn cappedGroup T := by
    intro i hi j hj heq
    by_contra hne
    exact hT i hi j hj (capEdge i j (ha hi) (ha hj) hne heq)
  have h := Finset.card_le_univ (T.image cappedGroup)
  rw [Finset.card_image_of_injOn hinj] at h
  simpa using h

/-- A block of size six is paid for by the following block of size at most four.
Only the last block can leave an outstanding surplus. -/
lemma open_chain_sum (f : ℕ → ℕ) (h6 : ∀ i, f i ≤ 6)
    (h4 : ∀ i, f i = 6 → f (i+1) ≤ 4) (k : ℕ) :
    ∑ i ∈ range k, f i ≤ 5*k + (if f (k-1) = 6 then 1 else 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    cases k with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, zero_add, Nat.succ_sub_one]
      have h := h6 0
      split <;> omega
    | succ q =>
      simp only [Nat.succ_sub_one] at ih ⊢
      by_cases hp : f q = 6
      · have h := h4 q hp
        rw [if_pos hp] at ih
        split <;> omega
      · have h := h6 (q+1)
        rw [if_neg hp] at ih
        split <;> omega

def slot (S : Finset (ℕ × Fin 16)) (i : ℕ) : Finset (Fin 16) :=
  univ.filter fun j => (i,j) ∈ S

lemma slot_mem {S : Finset (ℕ × Fin 16)} {i : ℕ} {j : Fin 16} :
    j ∈ slot S i ↔ (i,j) ∈ S := by simp [slot]

lemma slot_count {S : Finset (ℕ × Fin 16)} (k : ℕ) (hk : ∀ x ∈ S, x.1 < k) :
    S.card = ∑ i ∈ range k, (slot S i).card := by
  have hm : (S : Set (ℕ × Fin 16)).MapsTo Prod.fst (range k : Set ℕ) :=
    fun x hx => Finset.mem_range.mpr (hk x hx)
  rw [Finset.card_eq_sum_card_fiberwise hm]
  apply Finset.sum_congr rfl
  intro i _
  let e : Fin 16 ↪ ℕ × Fin 16 := ⟨(i,·), fun _ _ h => congrArg Prod.snd h⟩
  have hf : S.filter (fun x => x.1 = i) = (slot S i).map e := by
    ext x
    rcases x with ⟨a,b⟩
    simp only [Finset.mem_filter, Finset.mem_map, slot_mem]
    change (a,b) ∈ S ∧ a = i ↔ ∃ j, (i,j) ∈ S ∧ (i,j) = (a,b)
    constructor
    · rintro ⟨hm, rfl⟩
      exact ⟨b, hm, rfl⟩
    · rintro ⟨j, hm, h⟩
      cases h
      exact ⟨hm, rfl⟩
  rw [hf, Finset.card_map]

lemma node_inj : Function.Injective node := by
  intro x y hxy
  by_contra h
  have hd := node_sep h
  rw [hxy, dist_self] at hd
  norm_num at hd

lemma count_nodes (k : ℕ) : Erdos1066.g (16*k) ≤ 5*k+1 := by
  classical
  let F : Finset (ℕ × Fin 16) := (range k).product (univ : Finset (Fin 16))
  let f : (ℕ × Fin 16) ↪ ℝ² := ⟨node, node_inj⟩
  let X : Finset ℝ² := F.map f
  have hX : X.card = 16*k := by simp [X,F, Nat.mul_comm]
  have hsep : (X : Set ℝ²).Pairwise (fun x y => 1 ≤ dist x y) := by
    intro x hx y hy hne
    obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b,_,rfl⟩ := Finset.mem_map.mp hy
    exact node_sep (fun h => hne (congrArg f h))
  have hg := Erdos1066.g_le X hsep
  rw [hX] at hg
  refine hg.trans ?_
  let G := SimpleGraph.UnitDistancePlaneGraph (X : Set ℝ²)
  obtain ⟨M, hM⟩ := G.maximumIndepSet_exists
  have hMc := G.maximumIndepSet_card_eq_indepNum M hM
  let e : {x // x ∈ F} ≃ {y // y ∈ (X : Set ℝ²)} := Equiv.ofBijective
    (fun x => ⟨f x.val, Finset.mem_map.mpr ⟨x.val,x.property,rfl⟩⟩)
    ⟨fun _ _ h => Subtype.ext (node_inj (congrArg Subtype.val h)), by
      intro y
      obtain ⟨x, hx, hy⟩ := Finset.mem_map.mp y.property
      exact ⟨⟨x,hx⟩, Subtype.ext hy⟩⟩
  let S : Finset (ℕ × Fin 16) := (M.map e.symm.toEmbedding).map (Function.Embedding.subtype (· ∈ F))
  have hSc : S.card = M.card := by simp [S]
  have himage {x : ℕ × Fin 16} (hx : x ∈ S) :
      ∃ y ∈ M, y.val = node x := by
    obtain ⟨z, hz, hzx⟩ := Finset.mem_map.mp hx
    obtain ⟨y, hy, hyz⟩ := Finset.mem_map.mp hz
    refine ⟨y, hy, ?_⟩
    have eq : e z = y := by simpa using (congrArg e hyz).symm
    have he : (e z).val = node z.val := rfl
    rw [← eq, he]
    exact congrArg node hzx
  have hne {x y : ℕ × Fin 16} (hx : x ∈ S) (hy : y ∈ S) : dist (node x) (node y) ≠ 1 := by
    intro hd
    rcases himage hx with ⟨v, hv, hvx⟩
    rcases himage hy with ⟨w, hw, hwy⟩
    have hvw : v ≠ w := by
      intro h
      have hvw' := congrArg Subtype.val h
      rw [hvx, hwy] at hvw'
      rw [hvw', dist_self] at hd
      norm_num at hd
    exact hM.isIndepSet hv hw hvw (show dist v.val w.val = 1 by simpa [hvx,hwy] using hd)
  have hSk (x : ℕ × Fin 16) (hx : x ∈ S) : x.1 < k := by
    obtain ⟨z, _, rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_range.mp (Finset.mem_product.mp z.property).1
  have hc (i : ℕ) : Clean (slot S i) := by
    intro a ha b hb hab
    exact hne (slot_mem.mp ha) (slot_mem.mp hb) (node_edge i hab)
  have hl (i : ℕ) : ∀ a ∈ slot S i, ∀ b ∈ slot S (i+1), ¬ Link a b := by
    intro a ha b hb hab
    exact hne (slot_mem.mp ha) (slot_mem.mp hb) (node_link i hab)
  have hs := open_chain_sum (fun i => (slot S i).card) (fun i => card_block (hc i))
    (fun i hi => next_block (hc i) (hc (i+1)) hi (hl i)) k
  change G.indepNum ≤ _
  rw [← hMc, ← hSc, slot_count k hSk]
  split at hs <;> omega

end OMA.CoinChain

theorem OMA.solution : type_of% @Erdos1066.erdos_1066.variants.pach_toth := by
  intro ε hε
  apply Filter.frequently_atTop.mpr
  intro a
  obtain ⟨B, hB⟩ := exists_nat_gt (1/ε)
  let k := max a B
  refine ⟨16*k, by dsimp [k]; have := le_max_left a B; omega, ?_⟩
  have hBk : (B : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_max_right a B
  have hmain : (Erdos1066.g (16*k) : ℝ) ≤ (5*k : ℝ)+1 := by
    exact_mod_cast OMA.CoinChain.count_nodes k
  have he := (div_lt_iff₀ hε).mp hB
  have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
  push_cast
  nlinarith only [hmain, he, mul_nonneg hε.le (sub_nonneg.mpr hBk), mul_nonneg hε.le hk]
