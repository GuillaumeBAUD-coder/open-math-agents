import OMAStatements.S_oeis_a183690

open OMA.S_oeis_a183690

namespace OMA.A183690Proof

/-- Coefficient of degree n-k in the series starting at index one. -/
def lag (n k : Nat) : Int :=
  if k < n then (a (n - k) : Int) else 0

/-- The pair (u,v) represents u + v√57. -/
def qMul (p q : Int × Int) : Int × Int :=
  (p.1 * q.1 + 57 * p.2 * q.2, p.1 * q.2 + p.2 * q.1)

def qPow (p : Int × Int) : Nat → Int × Int
  | 0 => (1, 0)
  | n + 1 => qMul p (qPow p n)

def qAdd (p q : Int × Int) : Int × Int := (p.1 + q.1, p.2 + q.2)

inductive Kind where
  | zero | paired | single
  deriving DecidableEq

def kind (r : Row) : Kind :=
  if r.1.val = 0 ∧ r.2.val = 0 then .zero
  else if r.1.val = 0 ∨ r.2.val = 0 ∨ r.1 = r.2 then .paired
  else .single

def weight (z p s : Nat) : Kind → Nat
  | .zero => z
  | .paired => p
  | .single => s

def tally (xs : List Kind) : Nat × Nat × Nat :=
  (xs.count .zero, xs.count .paired, xs.count .single)

def weighted (c : Nat × Nat × Nat) (z p s : Nat) : Nat :=
  c.1 * z + c.2.1 * p + c.2.2 * s

theorem sum_weights (xs : List Kind) (z p s : Nat) :
    (xs.map (weight z p s)).sum = weighted (tally xs) z p s := by
  induction xs with
  | nil => simp [tally, weighted]
  | cons k xs ih =>
    cases k <;> simp [weight, tally, weighted, Nat.add_mul] at * <;> omega

theorem row_weights (xs : List Row) (z p s : Nat) :
    (xs.map (fun r => weight z p s (kind r))).sum =
      weighted (tally (xs.map kind)) z p s := by
  simpa only [List.map_map, Function.comp_def] using sum_weights (xs.map kind) z p s

theorem row_tally : tally (rows.map kind) = (1, 6, 2) := by decide

theorem neighbor_tally : ∀ i j : Fin 3, tally ((neighbors (i,j)).map kind) =
    match kind (i,j) with
    | .zero => (0, 0, 0)
    | .paired => (0, 4, 2)
    | .single => (0, 6, 1) := by decide

/-- Extension counts from one fixed nonzero row of each type. -/
def ways : Nat → Nat × Nat
  | 0 => (1, 1)
  | n + 1 =>
    let w := ways n
    (4 * w.1 + 2 * w.2, 6 * w.1 + w.2)

theorem count_extensions (n : Nat) (r : Row) :
    (extensions n r).length =
    weight (if n = 0 then 1 else 0) (ways n).1 (ways n).2 (kind r) := by
  induction n generalizing r with
  | zero => cases kind r <;> rfl
  | succ n ih =>
    rw [extensions, List.length_flatMap]
    simp only [List.length_map, ih]
    rw [row_weights, neighbor_tally r.1 r.2]
    cases kind r <;> simp [ways, weight, weighted]

def total (n : Nat) : Nat := 6 * (ways n).1 + 2 * (ways n).2

theorem count_arrays {n : Nat} (hn : 1 ≤ n) : a n = total n := by
  simp only [a, List.length_flatMap, List.length_map, count_extensions]
  rw [row_weights, row_tally]
  simp [total, weighted, show n ≠ 0 by omega]

theorem recurrence (n : Nat) :
    total (n+2) = 5 * total (n+1) + 8 * total n := by
  simp only [total, ways]
  omega

theorem gf (n : Nat) : lag n 0 - 5 * lag n 1 - 8 * lag n 2 =
    (if n = 1 then 50 else if n = 2 then 64 else 0) := by
  match n with
  | 0 => decide
  | 1 =>
    have first : a 1 = 50 := (count_arrays (by decide)).trans (by decide)
    simp [lag, first]
  | 2 =>
    have first : a 1 = 50 := (count_arrays (by decide)).trans (by decide)
    have second : a 2 = 314 := (count_arrays (by decide)).trans (by decide)
    simp [lag, first, second]
  | k + 3 =>
    simp only [lag, if_pos (show 0 < k+3 by omega), if_pos (show 1 < k+3 by omega),
      if_pos (show 2 < k+3 by omega), if_neg (show k+3 ≠ 1 by omega),
      if_neg (show k+3 ≠ 2 by omega)]
    rw [count_arrays (by omega), count_arrays (by omega), count_arrays (by omega)]
    change (total (k+1+2) : Int) - 5 * (total (k+1+1) : Int) -
      8 * (total (k+1) : Int) = 0
    have h := recurrence (k+1)
    omega

/-- Coefficients of (5+√57)^n in the basis (1, √57). -/
def basisCoeffs : Nat → Nat × Nat
  | 0 => (1, 0)
  | n + 1 =>
    let c := basisCoeffs n
    (5 * c.1 + 57 * c.2, c.1 + 5 * c.2)

theorem conjugates (n : Nat) :
    qPow (5, 1) n = (((basisCoeffs n).1 : Int), ((basisCoeffs n).2 : Int)) ∧
    qPow (5, -1) n = (((basisCoeffs n).1 : Int), -((basisCoeffs n).2 : Int)) := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨pos, neg⟩ := ih
    simp only [qPow, pos, neg, qMul, basisCoeffs, Prod.mk.injEq]
    omega

theorem scaled_ways (n : Nat) :
    2^n * (ways n).1 = (basisCoeffs n).1 + 7 * (basisCoeffs n).2 ∧
    2^n * (ways n).2 = (basisCoeffs n).1 + 9 * (basisCoeffs n).2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨hp, hs⟩ := ih
    simp only [ways, basisCoeffs, Nat.pow_succ]
    grind

theorem radical (n : Nat) (hn : 1 ≤ n) :
    qAdd (qMul (qPow (5,-1) n) (-15,2)) (qMul (qPow (5,1) n) (15,2)) =
      (0, ((2^(n-1) * a n : Nat) : Int)) := by
  obtain ⟨pos, neg⟩ := conjugates n
  have scale : 2^n * a n = 8 * (basisCoeffs n).1 + 60 * (basisCoeffs n).2 := by
    rw [count_arrays hn]
    obtain ⟨hp, hs⟩ := scaled_ways n
    unfold total
    grind
  have two : 2 ^ n * a n = 2 * (2^(n-1) * a n) := by
    have hn' : (n-1).succ = n := by omega
    have h := Nat.pow_succ 2 (n-1)
    rw [hn'] at h
    rw [h]
    grind
  rw [neg, pos]
  simp only [qAdd, qMul, Prod.mk.injEq]
  omega

open PowerSeries

theorem coeff_lag (n k : ℕ) :
    coeff n (series * X ^ k) = (lag n k : ℚ) := by
  rw [coeff_mul_X_pow']
  simp only [series, coeff_mk, lag]
  split_ifs <;> simp_all <;> omega

theorem series_identity :
    series * (1 - 5 * X - 8 * X ^ 2) = 2 * X * (25 + 32 * X) := by
  have eqL : series * (1 - 5 * X - 8 * X ^ 2) =
      series * X ^ 0 - C (5 : ℚ) * (series * X ^ 1) -
        C (8 : ℚ) * (series * X ^ 2) := by
    simp only [map_ofNat, pow_zero, pow_one]
    ring
  have eqR : (2 * X * (25 + 32 * X) : PowerSeries ℚ) =
      C (50 : ℚ) * X ^ 1 + C (64 : ℚ) * X ^ 2 := by
    simp only [map_ofNat, pow_one]
    ring
  rw [eqL, eqR]
  apply PowerSeries.ext
  intro n
  simp only [map_sub, map_add, coeff_C_mul, coeff_lag, coeff_X_pow]
  have h := gf n
  split_ifs at * <;> norm_num at * <;> first | exact_mod_cast h | omega

/-- Evaluate an integer coefficient pair in the real numbers. -/
noncomputable def evalPair (p : ℤ × ℤ) : ℝ := (p.1 : ℝ) + (p.2 : ℝ) * Real.sqrt 57

theorem eval_add (p q : ℤ × ℤ) : evalPair (qAdd p q) = evalPair p + evalPair q := by
  simp [evalPair, qAdd]
  ring

theorem eval_mul (p q : ℤ × ℤ) : evalPair (qMul p q) = evalPair p * evalPair q := by
  simp only [evalPair, qMul, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
  have h : Real.sqrt 57 ^ 2 = 57 := Real.sq_sqrt (by norm_num)
  linear_combination -(p.2 : ℝ) * (q.2 : ℝ) * h

theorem eval_pow (p : ℤ × ℤ) (n : ℕ) : evalPair (qPow p n) = (evalPair p) ^ n := by
  induction n with
  | zero => simp [qPow, evalPair]
  | succ n ih => rw [qPow, eval_mul, ih, pow_succ']

theorem real_formula (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℝ) =
      ((5 - Real.sqrt 57) ^ n * (-15 + 2 * Real.sqrt 57) +
       (5 + Real.sqrt 57) ^ n * (15 + 2 * Real.sqrt 57)) /
       (2 ^ (n - 1) * Real.sqrt 57) := by
  have h := congrArg evalPair (radical n hn)
  simp only [eval_add, eval_mul, eval_pow] at h
  norm_num [evalPair, sub_eq_add_neg] at h
  apply (eq_div_iff (by positivity)).2
  linear_combination -h

end OMA.A183690Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a183690.main :=
  ⟨OMA.A183690Proof.series_identity, OMA.A183690Proof.real_formula⟩
