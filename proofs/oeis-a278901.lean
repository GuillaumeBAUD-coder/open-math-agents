import OMAStatements.S_oeis_a278901

section Rule107Proof
open OMA.S_oeis_a278901
open PowerSeries

-- 1. Fast finite-box evaluator for stages 0..15 and base case stage 8 = evenPat 4
def lookupL {α : Type} : List α → ℕ → α → α
  | [], _, d => d
  | b :: _, 0, _ => b
  | _ :: bs, i + 1, d => lookupL bs i d

def buildL {α : Type} : ℕ → (ℕ → α) → List α
  | 0, _ => []
  | n + 1, f => f 0 :: buildL n (fun i => f (i + 1))

lemma lookupL_buildL {α : Type} (n : ℕ) (f : ℕ → α) (i : ℕ) (d : α) :
    lookupL (buildL n f) i d = if i < n then f i else d := by
  induction n generalizing f i with
  | zero => simp [buildL, lookupL]
  | succ n ih =>
    cases i with
    | zero => simp [buildL, lookupL]
    | succ i => simp only [buildL, lookupL, ih, Nat.succ_lt_succ_iff]

def evalBox (rows : List (List Bool)) (t : ℕ) (bg : Bool) (x y : ℤ) : Bool :=
  if -↑t ≤ x ∧ x ≤ ↑t ∧ -↑t ≤ y ∧ y ≤ ↑t then
    lookupL (lookupL rows (y + ↑t).toNat []) (x + ↑t).toNat bg
  else bg

lemma evalBox_out (rows : List (List Bool)) (t : ℕ) (bg : Bool) (x y : ℤ)
    (h : ¬(-↑t ≤ x ∧ x ≤ ↑t ∧ -↑t ≤ y ∧ y ≤ ↑t)) :
    evalBox rows t bg x y = bg :=
  if_neg h

def nextCfg (t : ℕ) (c : Bool × List (List Bool)) : Bool × List (List Bool) :=
  let bg := c.1
  let g := evalBox c.2 t bg
  let bg' := Nat.testBit 107 (bg.toNat + 2 * (bg.toNat + bg.toNat + bg.toNat + bg.toNat))
  let rows' := buildL (2 * (t + 1) + 1) fun iy =>
    buildL (2 * (t + 1) + 1) fun ix =>
      step g ((ix : ℤ) - ↑(t + 1)) ((iy : ℤ) - ↑(t + 1))
  (bg', rows')

def cfg : ℕ → Bool × List (List Bool)
  | 0 => (false, [[true]])
  | t + 1 => nextCfg t (cfg t)

lemma state_eq_cfg (t : ℕ) : state t = evalBox (cfg t).2 t (cfg t).1 := by
  induction t with
  | zero =>
    funext x y
    simp only [state, cfg, evalBox, Nat.cast_zero, neg_zero, add_zero]
    by_cases h : 0 ≤ x ∧ x ≤ 0 ∧ 0 ≤ y ∧ y ≤ 0
    · obtain ⟨rfl, rfl⟩ : x = 0 ∧ y = 0 := ⟨by omega, by omega⟩
      simp [lookupL]
    · have hxy : ¬(x = 0 ∧ y = 0) := by omega
      simp [h, hxy]
  | succ t ih =>
    funext x y
    change step (state t) x y = evalBox (nextCfg t (cfg t)).2 (t + 1) (nextCfg t (cfg t)).1 x y
    rw [ih]
    by_cases h : -↑(t + 1) ≤ x ∧ x ≤ ↑(t + 1) ∧ -↑(t + 1) ≤ y ∧ y ≤ ↑(t + 1)
    · unfold evalBox nextCfg
      rw [if_pos h]
      rw [lookupL_buildL, if_pos (by omega : (y + ↑(t + 1)).toNat < 2 * (t + 1) + 1)]
      rw [lookupL_buildL, if_pos (by omega : (x + ↑(t + 1)).toNat < 2 * (t + 1) + 1)]
      have hx : ((x + ↑(t + 1)).toNat : ℤ) - ↑(t + 1) = x := by omega
      have hy : ((y + ↑(t + 1)).toNat : ℤ) - ↑(t + 1) = y := by omega
      rw [hx, hy]
      rfl
    · rw [evalBox_out _ _ _ _ _ h]
      unfold step nextCfg
      rw [evalBox_out _ _ _ x y (by omega),
          evalBox_out _ _ _ (x - 1) y (by omega),
          evalBox_out _ _ _ (x + 1) y (by omega),
          evalBox_out _ _ _ x (y - 1) (by omega),
          evalBox_out _ _ _ x (y + 1) (by omega)]

def sumUp (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => sumUp f k + f k

lemma sum_range_eq_sumUp (f : ℕ → ℕ) (k : ℕ) :
    (∑ i ∈ Finset.range k, f i) = sumUp f k := by
  induction k with
  | zero => simp [sumUp]
  | succ k ih => rw [Finset.sum_range_succ, ih, sumUp]

-- 2. Exact 2-step invariant evenPat m for m >= 4 via 17-bucket finite abstraction
def evenPat (m : ℕ) (x y : ℤ) : Bool :=
  decide (-(m : ℤ) ≤ x ∧ x ≤ m ∧ -(m : ℤ) ≤ y ∧ y ≤ m ∧ (x + y) % 2 = 0 ∧ ¬(x = 0 ∧ y = 0))

def bucket (m : ℕ) (z : ℤ) : ℕ :=
  if z < -(m : ℤ) - 2 then 0
  else if z = -(m : ℤ) - 2 then 1
  else if z = -(m : ℤ) - 1 then 2
  else if z = -(m : ℤ) then 3
  else if z = -(m : ℤ) + 1 then 4
  else if z < -2 then 5
  else if z = -2 then 6
  else if z = -1 then 7
  else if z = 0 then 8
  else if z = 1 then 9
  else if z = 2 then 10
  else if z < (m : ℤ) - 1 then 11
  else if z = (m : ℤ) - 1 then 12
  else if z = (m : ℤ) then 13
  else if z = (m : ℤ) + 1 then 14
  else if z = (m : ℤ) + 2 then 15
  else 16

lemma bucket_spec (m : ℕ) (hm : 4 ≤ m) (z : ℤ) :
    ((z < -(m : ℤ) - 2) ∧ bucket m z = 0) ∨
    ((z = -(m : ℤ) - 2) ∧ bucket m z = 1) ∨
    ((z = -(m : ℤ) - 1) ∧ bucket m z = 2) ∨
    ((z = -(m : ℤ)) ∧ bucket m z = 3) ∨
    ((z = -(m : ℤ) + 1) ∧ bucket m z = 4) ∨
    ((-(m : ℤ) + 1 < z ∧ z < -2) ∧ bucket m z = 5) ∨
    ((z = -2) ∧ bucket m z = 6) ∨
    ((z = -1) ∧ bucket m z = 7) ∨
    ((z = 0) ∧ bucket m z = 8) ∨
    ((z = 1) ∧ bucket m z = 9) ∨
    ((z = 2) ∧ bucket m z = 10) ∨
    ((2 < z ∧ z < (m : ℤ) - 1) ∧ bucket m z = 11) ∨
    ((z = (m : ℤ) - 1) ∧ bucket m z = 12) ∨
    ((z = (m : ℤ)) ∧ bucket m z = 13) ∨
    ((z = (m : ℤ) + 1) ∧ bucket m z = 14) ∨
    ((z = (m : ℤ) + 2) ∧ bucket m z = 15) ∨
    ((m : ℤ) + 2 < z ∧ bucket m z = 16) := by
  have _ := hm
  unfold bucket
  by_cases h0 : z < -(m : ℤ) - 2
  · rw [if_pos h0]; left; exact ⟨by omega, rfl⟩
  rw [if_neg h0]
  by_cases h1 : z = -(m : ℤ) - 2
  · rw [if_pos h1]; right; left; exact ⟨by omega, rfl⟩
  rw [if_neg h1]
  by_cases h2 : z = -(m : ℤ) - 1
  · rw [if_pos h2]; right; right; left; exact ⟨by omega, rfl⟩
  rw [if_neg h2]
  by_cases h3 : z = -(m : ℤ)
  · rw [if_pos h3]; right; right; right; left; exact ⟨by omega, rfl⟩
  rw [if_neg h3]
  by_cases h4 : z = -(m : ℤ) + 1
  · rw [if_pos h4]; right; right; right; right; left; exact ⟨by omega, rfl⟩
  rw [if_neg h4]
  by_cases h5 : z < -2
  · rw [if_pos h5]; right; right; right; right; right; left; exact ⟨by omega, rfl⟩
  rw [if_neg h5]
  by_cases h6 : z = -2
  · rw [if_pos h6]; right; right; right; right; right; right; left; exact ⟨by omega, rfl⟩
  rw [if_neg h6]
  by_cases h7 : z = -1
  · rw [if_pos h7]; right; right; right; right; right; right; right; left; exact ⟨by omega, rfl⟩
  rw [if_neg h7]
  by_cases h8 : z = 0
  · rw [if_pos h8]; right; right; right; right; right; right; right; right; left; exact ⟨by omega, rfl⟩
  rw [if_neg h8]
  by_cases h9 : z = 1
  · rw [if_pos h9]; right; right; right; right; right; right; right; right; right; left; exact ⟨by omega, rfl⟩
  rw [if_neg h9]
  by_cases h10 : z = 2
  · rw [if_pos h10]; right; right; right; right; right; right; right; right; right; right; left; exact ⟨by omega, rfl⟩
  rw [if_neg h10]
  by_cases h11 : z < (m : ℤ) - 1
  · rw [if_pos h11]; right; right; right; right; right; right; right; right; right; right; right; left; exact ⟨by omega, rfl⟩
  rw [if_neg h11]
  by_cases h12 : z = (m : ℤ) - 1
  · rw [if_pos h12]; right; right; right; right; right; right; right; right; right; right; right; right; left; exact ⟨by omega, rfl⟩
  rw [if_neg h12]
  by_cases h13 : z = (m : ℤ)
  · rw [if_pos h13]; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact ⟨by omega, rfl⟩
  rw [if_neg h13]
  by_cases h14 : z = (m : ℤ) + 1
  · rw [if_pos h14]; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact ⟨by omega, rfl⟩
  rw [if_neg h14]
  by_cases h15 : z = (m : ℤ) + 2
  · rw [if_pos h15]; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; left; exact ⟨by omega, rfl⟩
  rw [if_neg h15]
  right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; right; exact ⟨by omega, rfl⟩

lemma bucket_lt (m : ℕ) (hm : 4 ≤ m) (z : ℤ) : bucket m z < 17 := by
  rcases bucket_spec m hm z with ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ <;> omega

def symInBox (b : ℕ) (d : ℤ) : Bool :=
  match b with
  | 0 => false
  | 1 => decide (d = 2)
  | 2 => decide (1 ≤ d)
  | 3 => decide (0 ≤ d)
  | 4 => decide (-1 ≤ d)
  | 5 | 6 | 7 | 8 | 9 | 10 | 11 => true
  | 12 => decide (d ≤ 1)
  | 13 => decide (d ≤ 0)
  | 14 => decide (d ≤ -1)
  | 15 => decide (d = -2)
  | _ => false

def symIsZero (b : ℕ) (d : ℤ) : Bool :=
  match b with
  | 6 => decide (d = 2)
  | 7 => decide (d = 1)
  | 8 => decide (d = 0)
  | 9 => decide (d = -1)
  | 10 => decide (d = -2)
  | _ => false

def symInBoxNext (b : ℕ) : Bool :=
  match b with
  | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 => true
  | _ => false

lemma inBox_eq_sym (m : ℕ) (hm : 4 ≤ m) (z d : ℤ) (hd : -2 ≤ d ∧ d ≤ 2) :
    decide (-(m : ℤ) ≤ z + d ∧ z + d ≤ m) = symInBox (bucket m z) d := by
  rcases bucket_spec m hm z with ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ <;>
    (rw [hb]; dsimp only [symInBox]; simp only [decide_eq_false_iff_not, decide_eq_true_iff, decide_eq_decide]; first | omega | (constructor <;> intro <;> omega))

lemma isZero_eq_sym (m : ℕ) (hm : 4 ≤ m) (z d : ℤ) (hd : -2 ≤ d ∧ d ≤ 2) :
    decide (z + d = 0) = symIsZero (bucket m z) d := by
  rcases bucket_spec m hm z with ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ <;>
    (rw [hb]; dsimp only [symIsZero]; simp only [decide_eq_false_iff_not, decide_eq_decide]; first | omega | (constructor <;> intro <;> omega))

lemma inBoxNext_eq_sym (m : ℕ) (hm : 4 ≤ m) (z : ℤ) :
    decide (-(((m + 1 : ℕ) : ℤ)) ≤ z ∧ z ≤ ((m + 1 : ℕ) : ℤ)) = symInBoxNext (bucket m z) := by
  rcases bucket_spec m hm z with ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ <;>
    (rw [hb]; dsimp only [symInBoxNext]; simp only [decide_eq_false_iff_not, decide_eq_true_iff]; omega)

def symEven (bx by_ : ℕ) (p : Fin 2) (dx dy : ℤ) : Bool :=
  symInBox bx dx && symInBox by_ dy &&
    decide (((p.val : ℤ) + dx + dy) % 2 = 0) &&
    !(symIsZero bx dx && symIsZero by_ dy)

lemma evenPat_shift_eq_sym (m : ℕ) (hm : 4 ≤ m) (x y dx dy : ℤ)
    (hdx : -2 ≤ dx ∧ dx ≤ 2) (hdy : -2 ≤ dy ∧ dy ≤ 2) :
    evenPat m (x + dx) (y + dy) =
      symEven (bucket m x) (bucket m y) ⟨((x + y) % 2).toNat, by omega⟩ dx dy := by
  unfold evenPat symEven
  rw [← inBox_eq_sym m hm x dx hdx, ← inBox_eq_sym m hm y dy hdy,
      ← isZero_eq_sym m hm x dx hdx, ← isZero_eq_sym m hm y dy hdy]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
             decide_eq_true_iff, decide_eq_false_iff_not]
  constructor <;> intro h <;> omega

def symOdd (bx by_ : ℕ) (p : Fin 2) (dx dy : ℤ) : Bool :=
  let c := symEven bx by_ p dx dy
  let s := (symEven bx by_ p (dx - 1) dy).toNat + (symEven bx by_ p (dx + 1) dy).toNat +
           (symEven bx by_ p dx (dy - 1)).toNat + (symEven bx by_ p dx (dy + 1)).toNat
  Nat.testBit 107 (c.toNat + 2 * s)

def symStep2 (bx by_ : ℕ) (p : Fin 2) : Bool :=
  let c := symOdd bx by_ p 0 0
  let s := (symOdd bx by_ p (-1) 0).toNat + (symOdd bx by_ p 1 0).toNat +
           (symOdd bx by_ p 0 (-1)).toNat + (symOdd bx by_ p 0 1).toNat
  Nat.testBit 107 (c.toNat + 2 * s)

def symTarget (bx by_ : ℕ) (p : Fin 2) : Bool :=
  symInBoxNext bx && symInBoxNext by_ &&
    decide (p.val = 0) && !(symIsZero bx 0 && symIsZero by_ 0)

lemma symStep2_eq_symTarget_fin : ∀ (bx by_ : Fin 17) (p : Fin 2),
    symStep2 bx.val by_.val p = symTarget bx.val by_.val p := by
  decide

lemma step_evenPat_shift (m : ℕ) (hm : 4 ≤ m) (x y dx dy : ℤ)
    (hdx : -1 ≤ dx ∧ dx ≤ 1) (hdy : -1 ≤ dy ∧ dy ≤ 1) :
    step (evenPat m) (x + dx) (y + dy) =
      symOdd (bucket m x) (bucket m y) ⟨((x + y) % 2).toNat, by omega⟩ dx dy := by
  unfold step symOdd
  have e1 : x + dx - 1 = x + (dx - 1) := by omega
  have e2 : x + dx + 1 = x + (dx + 1) := by omega
  have e3 : y + dy - 1 = y + (dy - 1) := by omega
  have e4 : y + dy + 1 = y + (dy + 1) := by omega
  rw [e1, e2, e3, e4,
      evenPat_shift_eq_sym m hm x y dx dy (by omega) (by omega),
      evenPat_shift_eq_sym m hm x y (dx - 1) dy (by omega) (by omega),
      evenPat_shift_eq_sym m hm x y (dx + 1) dy (by omega) (by omega),
      evenPat_shift_eq_sym m hm x y dx (dy - 1) (by omega) (by omega),
      evenPat_shift_eq_sym m hm x y dx (dy + 1) (by omega) (by omega)]

lemma step_step_evenPat (m : ℕ) (hm : 4 ≤ m) (x y : ℤ) :
    step (step (evenPat m)) x y = evenPat (m + 1) x y := by
  have lhs_eq : step (step (evenPat m)) x y =
      symStep2 (bucket m x) (bucket m y) ⟨((x + y) % 2).toNat, by omega⟩ := by
    have s00 := step_evenPat_shift m hm x y 0 0 (by omega) (by omega)
    have sm0 := step_evenPat_shift m hm x y (-1) 0 (by omega) (by omega)
    have sp0 := step_evenPat_shift m hm x y 1 0 (by omega) (by omega)
    have s0m := step_evenPat_shift m hm x y 0 (-1) (by omega) (by omega)
    have s0p := step_evenPat_shift m hm x y 0 1 (by omega) (by omega)
    simp only [add_zero] at s00 sm0 sp0 s0m s0p
    have xm : x - 1 = x + -1 := by omega
    have ym : y - 1 = y + -1 := by omega
    change Nat.testBit 107 ((step (evenPat m) x y).toNat + 2 *
      ((step (evenPat m) (x - 1) y).toNat + (step (evenPat m) (x + 1) y).toNat +
       (step (evenPat m) x (y - 1)).toNat + (step (evenPat m) x (y + 1)).toNat)) = _
    unfold symStep2
    rw [xm, ym, s00, sm0, sp0, s0m, s0p]
  have hfin := symStep2_eq_symTarget_fin ⟨bucket m x, bucket_lt m hm x⟩ ⟨bucket m y, bucket_lt m hm y⟩
    ⟨((x + y) % 2).toNat, by omega⟩
  rw [lhs_eq, hfin]
  unfold evenPat symTarget
  dsimp only
  rw [← inBoxNext_eq_sym m hm x, ← inBoxNext_eq_sym m hm y,
      ← isZero_eq_sym m hm x 0 (by omega), ← isZero_eq_sym m hm y 0 (by omega)]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
             decide_eq_true_iff, decide_eq_false_iff_not, add_zero]
  constructor <;> intro h <;> omega

def check8 : Bool :=
  let c := cfg 8
  c.1 == false &&
    (List.range 17).all fun iy =>
      (List.range 17).all fun ix =>
        evalBox c.2 8 c.1 ((ix : ℤ) - 8) ((iy : ℤ) - 8) ==
          evenPat 4 ((ix : ℤ) - 8) ((iy : ℤ) - 8)

lemma check8_true : check8 = true := by decide

lemma state_8_eq : state 8 = evenPat 4 := by
  rw [state_eq_cfg 8]
  funext x y
  have hc := check8_true
  unfold check8 at hc
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hc
  by_cases hbox : -(8 : ℤ) ≤ x ∧ x ≤ 8 ∧ -(8 : ℤ) ≤ y ∧ y ≤ 8
  · have ix_lt : (x + 8).toNat < 17 := by omega
    have iy_lt : (y + 8).toNat < 17 := by omega
    have hcell := hc.2 (y + 8).toNat iy_lt (x + 8).toNat ix_lt
    have hx : (((x + 8).toNat : ℕ) : ℤ) - 8 = x := by omega
    have hy : (((y + 8).toNat : ℕ) : ℤ) - 8 = y := by omega
    rw [hx, hy] at hcell
    exact hcell
  · have hev : evalBox (cfg 8).2 8 (cfg 8).1 x y = false := by
      rw [evalBox_out _ _ _ _ _ (by simpa using hbox), hc.1]
    have hep : evenPat 4 x y = false := by
      unfold evenPat
      simp only [decide_eq_false_iff_not]
      omega
    rw [hev, hep]

lemma state_even_eq (m : ℕ) (hm : 4 ≤ m) : state (2 * m) = evenPat m := by
  obtain ⟨d, rfl⟩ : ∃ d, m = 4 + d := ⟨m - 4, by omega⟩
  induction d with
  | zero => exact state_8_eq
  | succ d ih =>
    have heq : 2 * (4 + (d + 1)) = (2 * (4 + d) + 1) + 1 := by omega
    rw [heq]
    change step (step (state (2 * (4 + d)))) = evenPat (4 + d + 1)
    rw [ih (by omega)]
    funext x y
    exact step_step_evenPat (4 + d) (by omega) x y

-- 3. Explicit x-axis bit formulas at stage 2*m and 2*m+1 (m >= 4)
lemma state_neg_x (t : ℕ) : ∀ x y : ℤ, state t (-x) y = state t x y := by
  induction t with
  | zero => intro x y; simp only [state, neg_eq_zero]
  | succ t ih =>
    intro x y
    change step (state t) (-x) y = step (state t) x y
    unfold step
    have h1 : -x - 1 = -(x + 1) := by omega
    have h2 : -x + 1 = -(x - 1) := by omega
    rw [h1, h2, ih x y, ih (x + 1) y, ih (x - 1) y, ih x (y - 1), ih x (y + 1)]
    congr 1
    omega

def bitEven (m j : ℕ) : Bool :=
  decide (1 ≤ j ∧ j ≤ m ∧ j % 2 = 0)

def bitOdd (m j : ℕ) : Bool :=
  decide (j % 2 = 0 ∨ j = 1 ∨ (j = m ∧ m % 2 = 1) ∨ m + 2 ≤ j)

lemma bitEven_true {m j : ℕ} (h : 1 ≤ j ∧ j ≤ m ∧ j % 2 = 0) : bitEven m j = true :=
  decide_eq_true h

lemma bitEven_false {m j : ℕ} (h : ¬(1 ≤ j ∧ j ≤ m ∧ j % 2 = 0)) : bitEven m j = false :=
  decide_eq_false h

lemma bitEven_congr (m1 m2 j : ℕ)
    (h : (1 ≤ j ∧ j ≤ m1 ∧ j % 2 = 0) ↔ (1 ≤ j ∧ j ≤ m2 ∧ j % 2 = 0)) :
    bitEven m1 j = bitEven m2 j := by
  unfold bitEven
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_iff]
  exact h

lemma bitOdd_true {m j : ℕ}
    (h : j % 2 = 0 ∨ j = 1 ∨ (j = m ∧ m % 2 = 1) ∨ m + 2 ≤ j) : bitOdd m j = true :=
  decide_eq_true h

lemma bitOdd_false {m j : ℕ}
    (h : ¬(j % 2 = 0 ∨ j = 1 ∨ (j = m ∧ m % 2 = 1) ∨ m + 2 ≤ j)) : bitOdd m j = false :=
  decide_eq_false h

lemma bitOdd_congr (m1 m2 j : ℕ)
    (h : (j % 2 = 0 ∨ j = 1 ∨ (j = m1 ∧ m1 % 2 = 1) ∨ m1 + 2 ≤ j) ↔
         (j % 2 = 0 ∨ j = 1 ∨ (j = m2 ∧ m2 % 2 = 1) ∨ m2 + 2 ≤ j)) :
    bitOdd m1 j = bitOdd m2 j := by
  unfold bitOdd
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_iff]
  exact h

lemma state_xaxis_even (m j : ℕ) (hm : 4 ≤ m) :
    state (2 * m) (j : ℤ) 0 = bitEven m j := by
  rw [state_even_eq m hm]
  unfold evenPat bitEven
  rw [decide_eq_decide]
  constructor
  · rintro ⟨_, h2, _, _, h5, h6⟩
    refine ⟨?_, by omega, by omega⟩
    by_contra hj0
    have : j = 0 := by omega
    subst this
    exact h6 ⟨rfl, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
    rintro ⟨hj0, _⟩
    omega

lemma bucket_zero (m : ℕ) (hm : 4 ≤ m) : bucket m 0 = 8 := by
  rcases bucket_spec m hm 0 with ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ <;> omega

def symBitOdd (bx pj pm : ℕ) : Bool :=
  decide (pj = 0 ∨ bx = 9 ∨ (bx = 13 ∧ pm = 1) ∨ 15 ≤ bx)

lemma symOdd_xaxis_eq_fin : ∀ (bx : Fin 17) (pj pm : Fin 2),
    8 ≤ bx.val →
    (bx.val = 8 → pj.val = 0) →
    (bx.val = 9 → pj.val = 1) →
    (bx.val = 10 → pj.val = 0) →
    (bx.val = 12 → pj.val ≠ pm.val) →
    (bx.val = 13 → pj.val = pm.val) →
    (bx.val = 14 → pj.val ≠ pm.val) →
    (bx.val = 15 → pj.val = pm.val) →
    symOdd bx.val 8 pj 0 0 = symBitOdd bx.val pj.val pm.val := by
  decide

lemma state_xaxis_odd (m j : ℕ) (hm : 4 ≤ m) :
    state (2 * m + 1) (j : ℤ) 0 = bitOdd m j := by
  change step (state (2 * m)) (j : ℤ) 0 = bitOdd m j
  rw [state_even_eq m hm]
  have hsh := step_evenPat_shift m hm (j : ℤ) 0 0 0 (by omega) (by omega)
  simp only [add_zero] at hsh
  rw [hsh, bucket_zero m hm]
  have hpj : (((j : ℤ) % 2).toNat : ℕ) = j % 2 := by omega
  have hfin : (⟨((j : ℤ) % 2).toNat, by omega⟩ : Fin 2) = ⟨j % 2, by omega⟩ := by
    ext; exact hpj
  rw [hfin]
  have hsym := symOdd_xaxis_eq_fin ⟨bucket m (j : ℤ), bucket_lt m hm (j : ℤ)⟩
    ⟨j % 2, by omega⟩ ⟨m % 2, by omega⟩
    (by rcases bucket_spec m hm (j : ℤ) with ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ <;> (change 8 ≤ bucket m (j : ℤ); rw [hb]; try omega))
    (by rcases bucket_spec m hm (j : ℤ) with ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ <;> (change bucket m (j : ℤ) = 8 → j % 2 = 0; rw [hb]; omega))
    (by rcases bucket_spec m hm (j : ℤ) with ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ <;> (change bucket m (j : ℤ) = 9 → j % 2 = 1; rw [hb]; omega))
    (by rcases bucket_spec m hm (j : ℤ) with ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ <;> (change bucket m (j : ℤ) = 10 → j % 2 = 0; rw [hb]; omega))
    (by rcases bucket_spec m hm (j : ℤ) with ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ <;> (change bucket m (j : ℤ) = 12 → j % 2 ≠ m % 2; rw [hb]; omega))
    (by rcases bucket_spec m hm (j : ℤ) with ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ <;> (change bucket m (j : ℤ) = 13 → j % 2 = m % 2; rw [hb]; omega))
    (by rcases bucket_spec m hm (j : ℤ) with ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ <;> (change bucket m (j : ℤ) = 14 → j % 2 ≠ m % 2; rw [hb]; omega))
    (by rcases bucket_spec m hm (j : ℤ) with ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ <;> (change bucket m (j : ℤ) = 15 → j % 2 = m % 2; rw [hb]; omega))
  have hsym' : symOdd (bucket m (j : ℤ)) 8 ⟨j % 2, by omega⟩ 0 0 =
      symBitOdd (bucket m (j : ℤ)) (j % 2) (m % 2) := hsym
  clear hfin hsym
  rw [hsym']
  unfold symBitOdd bitOdd
  rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;>
    rcases Nat.mod_two_eq_zero_or_one m with hmp | hmp <;>
    (rcases bucket_spec m hm (j : ℤ) with ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ | ⟨hz, hb⟩ <;>
      (rw [hb, hj, hmp]; simp; try omega))

def aFast (n : ℕ) : ℕ :=
  let c := cfg n
  sumUp (fun i => (evalBox c.2 n c.1 (i : ℤ) 0).toNat * 2 ^ (n - i)) (n + 1)

lemma a_eq_aFast (n : ℕ) : a n = aFast n := by
  unfold a aFast
  rw [state_eq_cfg, sum_range_eq_sumUp]

def u (n : ℕ) : ℤ := (a n : ℤ) - 4 * a (n - 2)

lemma u_expand (n : ℕ) (hn : 2 ≤ n) :
    u n = (∑ j ∈ Finset.range (n - 1),
      (((state n (j : ℤ) 0).toNat : ℤ) - ((state (n - 2) (j : ℤ) 0).toNat : ℤ)) * 2 ^ (n - j)) +
      ((state n ((n - 1 : ℕ) : ℤ) 0).toNat : ℤ) * 2 +
      ((state n (n : ℤ) 0).toNat : ℤ) := by
  unfold u a
  have h1 : n + 1 = (n - 1) + 2 := by omega
  have h2 : n - 2 + 1 = n - 1 := by omega
  conv_lhs =>
    arg 1
    rw [Nat.cast_sum]
    rw [h1, Finset.sum_range_add]
  conv_lhs =>
    arg 2
    rw [Nat.cast_sum, h2, Finset.mul_sum]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  have sub1 : n - (n - 1 + 0) = 1 := by omega
  have sub2 : n - (n - 1 + 1) = 0 := by omega
  have c0 : n - 1 + 0 = n - 1 := by omega
  have c1 : n - 1 + 1 = n := by omega
  have hmul4 : ∀ j ∈ Finset.range (n - 1),
      (4 : ℤ) * ↑((state (n - 2) (j : ℤ) 0).toNat * 2 ^ (n - 2 - j)) =
      ((state (n - 2) (j : ℤ) 0).toNat : ℤ) * 2 ^ (n - j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    push_cast
    have hp : (2 : ℤ) ^ (n - j) = 4 * 2 ^ (n - 2 - j) := by
      have : (4 : ℤ) = 2 ^ 2 := by norm_num
      rw [this, ← pow_add]; congr 1; omega
    rw [hp]; ring
  rw [Finset.sum_congr rfl hmul4]
  rw [sub1, sub2, c0, c1]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_one, pow_zero, mul_one, zero_add]
  have hdiff : (∑ j ∈ Finset.range (n - 1), ((state n (j : ℤ) 0).toNat : ℤ) * 2 ^ (n - j)) -
      (∑ j ∈ Finset.range (n - 1), ((state (n - 2) (j : ℤ) 0).toNat : ℤ) * 2 ^ (n - j)) =
      ∑ j ∈ Finset.range (n - 1),
        (((state n (j : ℤ) 0).toNat : ℤ) - ((state (n - 2) (j : ℤ) 0).toNat : ℤ)) * 2 ^ (n - j) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _; ring
  linarith

lemma u_phase2 (k : ℕ) (hk : 2 ≤ k) : u (4 * k + 2) = 0 := by
  rw [u_expand (4 * k + 2) (by omega)]
  have s0 : 4 * k + 2 - 2 = 4 * k := by omega
  have s1 : 4 * k + 2 - 1 = 4 * k + 1 := by omega
  rw [s0, s1]
  have he1 : 4 * k + 2 = 2 * (2 * k + 1) := by omega
  have he2 : 4 * k = 2 * (2 * k) := by omega
  have hsum : ∑ j ∈ Finset.range (4 * k + 1),
      (((state (4 * k + 2) (j : ℤ) 0).toNat : ℤ) - ((state (4 * k) (j : ℤ) 0).toNat : ℤ)) *
        2 ^ (4 * k + 2 - j) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [he1, he2, state_xaxis_even (2 * k + 1) j (by omega), state_xaxis_even (2 * k) j (by omega),
        bitEven_congr (2 * k + 1) (2 * k) j (by omega)]
    ring
  rw [hsum, he1, state_xaxis_even (2 * k + 1) (4 * k + 1) (by omega),
      state_xaxis_even (2 * k + 1) (2 * (2 * k + 1)) (by omega),
      bitEven_false (by omega), bitEven_false (by omega)]
  simp

lemma u_phase0 (k : ℕ) (hk : 2 ≤ k) : u (4 * k + 4) = 2 ^ (2 * k + 2) := by
  rw [u_expand (4 * k + 4) (by omega)]
  have s0 : 4 * k + 4 - 2 = 4 * k + 2 := by omega
  have s1 : 4 * k + 4 - 1 = 4 * k + 3 := by omega
  rw [s0, s1]
  have he1 : 4 * k + 4 = 2 * (2 * k + 2) := by omega
  have he2 : 4 * k + 2 = 2 * (2 * k + 1) := by omega
  have hsum : ∑ j ∈ Finset.range (4 * k + 3),
      (((state (4 * k + 4) (j : ℤ) 0).toNat : ℤ) - ((state (4 * k + 2) (j : ℤ) 0).toNat : ℤ)) *
        2 ^ (4 * k + 4 - j) = 2 ^ (2 * k + 2) := by
    rw [Finset.sum_eq_single (2 * k + 2)]
    · rw [he1, he2, state_xaxis_even (2 * k + 2) _ (by omega), state_xaxis_even (2 * k + 1) _ (by omega),
          bitEven_true (by omega), bitEven_false (by omega)]
      have hp : 2 * (2 * k + 2) - (2 * k + 2) = 2 * k + 2 := by omega
      simp [hp]
    · intro j _ hne
      rw [he1, he2, state_xaxis_even (2 * k + 2) j (by omega), state_xaxis_even (2 * k + 1) j (by omega),
          bitEven_congr (2 * k + 2) (2 * k + 1) j (by omega)]
      ring
    · intro hmem; exfalso; apply hmem; rw [Finset.mem_range]; omega
  rw [hsum, he1, state_xaxis_even (2 * k + 2) (4 * k + 3) (by omega),
      state_xaxis_even (2 * k + 2) (2 * (2 * k + 2)) (by omega),
      bitEven_false (by omega), bitEven_false (by omega)]
  simp

lemma u_phase3 (k : ℕ) (hk : 2 ≤ k) : u (4 * k + 3) = 2 ^ (2 * k + 2) + 3 := by
  rw [u_expand (4 * k + 3) (by omega)]
  have s0 : 4 * k + 3 - 2 = 4 * k + 1 := by omega
  have s1 : 4 * k + 3 - 1 = 4 * k + 2 := by omega
  rw [s0, s1]
  have he1 : 4 * k + 3 = 2 * (2 * k + 1) + 1 := by omega
  have he2 : 4 * k + 1 = 2 * (2 * k) + 1 := by omega
  have hsum : ∑ j ∈ Finset.range (4 * k + 2),
      (((state (4 * k + 3) (j : ℤ) 0).toNat : ℤ) - ((state (4 * k + 1) (j : ℤ) 0).toNat : ℤ)) *
        2 ^ (4 * k + 3 - j) = 2 ^ (2 * k + 2) := by
    rw [Finset.sum_eq_single (2 * k + 1)]
    · rw [he1, he2, state_xaxis_odd (2 * k + 1) _ (by omega), state_xaxis_odd (2 * k) _ (by omega),
          bitOdd_true (by omega), bitOdd_false (by omega)]
      have hp : 2 * (2 * k + 1) + 1 - (2 * k + 1) = 2 * k + 2 := by omega
      simp [hp]
    · intro j _ hne
      rw [he1, he2, state_xaxis_odd (2 * k + 1) j (by omega), state_xaxis_odd (2 * k) j (by omega),
          bitOdd_congr (2 * k + 1) (2 * k) j (by omega)]
      ring
    · intro hmem; exfalso; apply hmem; rw [Finset.mem_range]; omega
  rw [hsum, he1, state_xaxis_odd (2 * k + 1) (4 * k + 2) (by omega),
      state_xaxis_odd (2 * k + 1) (2 * (2 * k + 1) + 1) (by omega),
      bitOdd_true (by omega), bitOdd_true (by omega)]
  simp only [Bool.toNat_true, Nat.cast_one, one_mul]
  ring

lemma u_phase1 (k : ℕ) (hk : 2 ≤ k) :
    u (4 * k + 5) = -2 ^ (2 * k + 4) - 2 ^ (2 * k + 2) + 3 := by
  rw [u_expand (4 * k + 5) (by omega)]
  have s0 : 4 * k + 5 - 2 = 4 * k + 3 := by omega
  have s1 : 4 * k + 5 - 1 = 4 * k + 4 := by omega
  rw [s0, s1]
  have he1 : 4 * k + 5 = 2 * (2 * k + 2) + 1 := by omega
  have he2 : 4 * k + 3 = 2 * (2 * k + 1) + 1 := by omega
  have hsplit : 4 * k + 4 = (2 * k + 2) + (2 * k + 2) := by omega
  have hsum : ∑ j ∈ Finset.range (4 * k + 4),
      (((state (4 * k + 5) (j : ℤ) 0).toNat : ℤ) - ((state (4 * k + 3) (j : ℤ) 0).toNat : ℤ)) *
        2 ^ (4 * k + 5 - j) = -2 ^ (2 * k + 4) - 2 ^ (2 * k + 2) := by
    rw [hsplit, Finset.sum_range_add]
    have hs1 : ∑ j ∈ Finset.range (2 * k + 2),
        (((state (4 * k + 5) (j : ℤ) 0).toNat : ℤ) - ((state (4 * k + 3) (j : ℤ) 0).toNat : ℤ)) *
          2 ^ (4 * k + 5 - j) = -2 ^ (2 * k + 4) := by
      rw [Finset.sum_eq_single (2 * k + 1)]
      · rw [he1, he2, state_xaxis_odd (2 * k + 2) _ (by omega), state_xaxis_odd (2 * k + 1) _ (by omega),
            bitOdd_false (by omega), bitOdd_true (by omega)]
        have hp : 2 * (2 * k + 2) + 1 - (2 * k + 1) = 2 * k + 4 := by omega
        simp [hp]
      · intro j hj hne
        rw [Finset.mem_range] at hj
        rw [he1, he2, state_xaxis_odd (2 * k + 2) j (by omega), state_xaxis_odd (2 * k + 1) j (by omega),
            bitOdd_congr (2 * k + 2) (2 * k + 1) j (by omega)]
        ring
      · intro hmem; exfalso; apply hmem; rw [Finset.mem_range]; omega
    have hs2 : ∑ x ∈ Finset.range (2 * k + 2),
        (((state (4 * k + 5) ((2 * k + 2 + x : ℕ) : ℤ) 0).toNat : ℤ) -
         ((state (4 * k + 3) ((2 * k + 2 + x : ℕ) : ℤ) 0).toNat : ℤ)) *
          2 ^ (4 * k + 5 - (2 * k + 2 + x)) = -2 ^ (2 * k + 2) := by
      rw [Finset.sum_eq_single 1]
      · rw [he1, he2, state_xaxis_odd (2 * k + 2) _ (by omega), state_xaxis_odd (2 * k + 1) _ (by omega),
            bitOdd_false (by omega), bitOdd_true (by omega)]
        have hp : 2 * (2 * k + 2) + 1 - (2 * k + 2 + 1) = 2 * k + 2 := by omega
        simp [hp]
      · intro x hx hne
        rw [Finset.mem_range] at hx
        rw [he1, he2, state_xaxis_odd (2 * k + 2) _ (by omega), state_xaxis_odd (2 * k + 1) _ (by omega),
            bitOdd_congr (2 * k + 2) (2 * k + 1) (2 * k + 2 + x) (by omega)]
        ring
      · intro hmem; exfalso; apply hmem; rw [Finset.mem_range]; omega
    rw [hs1, hs2]
    ring
  rw [hsum, he1, state_xaxis_odd (2 * k + 2) (4 * k + 4) (by omega),
      state_xaxis_odd (2 * k + 2) (2 * (2 * k + 2) + 1) (by omega),
      bitOdd_true (by omega), bitOdd_true (by omega)]
  simp only [Bool.toNat_true, Nat.cast_one, one_mul]
  ring

lemma rec_claim (n : ℕ) (hn : 15 < n) :
    (a n : ℤ) = 5 * a (n - 2) - 20 * a (n - 6) + 16 * a (n - 8) := by
  have hu_eq : (a n : ℤ) - (5 * a (n - 2) - 20 * a (n - 6) + 16 * a (n - 8)) =
      u n - u (n - 2) - 4 * u (n - 4) + 4 * u (n - 6) := by
    unfold u
    have s1 : n - 2 - 2 = n - 4 := by omega
    have s2 : n - 4 - 2 = n - 6 := by omega
    have s3 : n - 6 - 2 = n - 8 := by omega
    rw [s1, s2, s3]
    ring
  suffices h0 : u n - u (n - 2) - 4 * u (n - 4) + 4 * u (n - 6) = 0 by linarith
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 4 ∧ n = 4 * k + 16 + r :=
    ⟨(n - 16) / 4, (n - 16) % 4, Nat.mod_lt _ (by decide), by omega⟩
  interval_cases r
  · have e0 : 4 * k + 16 + 0 = 4 * (k + 3) + 4 := by omega
    have e2 : 4 * k + 16 + 0 - 2 = 4 * (k + 3) + 2 := by omega
    have e4 : 4 * k + 16 + 0 - 4 = 4 * (k + 2) + 4 := by omega
    have e6 : 4 * k + 16 + 0 - 6 = 4 * (k + 2) + 2 := by omega
    rw [e6, e4, e2, e0, u_phase0 (k + 3) (by omega), u_phase2 (k + 3) (by omega),
        u_phase0 (k + 2) (by omega), u_phase2 (k + 2) (by omega)]
    ring
  · have e0 : 4 * k + 16 + 1 = 4 * (k + 3) + 5 := by omega
    have e2 : 4 * k + 16 + 1 - 2 = 4 * (k + 3) + 3 := by omega
    have e4 : 4 * k + 16 + 1 - 4 = 4 * (k + 2) + 5 := by omega
    have e6 : 4 * k + 16 + 1 - 6 = 4 * (k + 2) + 3 := by omega
    rw [e6, e4, e2, e0, u_phase1 (k + 3) (by omega), u_phase3 (k + 3) (by omega),
        u_phase1 (k + 2) (by omega), u_phase3 (k + 2) (by omega)]
    ring
  · have e0 : 4 * k + 16 + 2 = 4 * (k + 4) + 2 := by omega
    have e2 : 4 * k + 16 + 2 - 2 = 4 * (k + 3) + 4 := by omega
    have e4 : 4 * k + 16 + 2 - 4 = 4 * (k + 3) + 2 := by omega
    have e6 : 4 * k + 16 + 2 - 6 = 4 * (k + 2) + 4 := by omega
    rw [e6, e4, e2, e0, u_phase2 (k + 4) (by omega), u_phase0 (k + 3) (by omega),
        u_phase2 (k + 3) (by omega), u_phase0 (k + 2) (by omega)]
    ring
  · have e0 : 4 * k + 16 + 3 = 4 * (k + 4) + 3 := by omega
    have e2 : 4 * k + 16 + 3 - 2 = 4 * (k + 3) + 5 := by omega
    have e4 : 4 * k + 16 + 3 - 4 = 4 * (k + 3) + 3 := by omega
    have e6 : 4 * k + 16 + 3 - 6 = 4 * (k + 2) + 5 := by omega
    rw [e6, e4, e2, e0, u_phase3 (k + 4) (by omega), u_phase1 (k + 3) (by omega),
        u_phase3 (k + 3) (by omega), u_phase1 (k + 2) (by omega)]
    ring

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 200000 in
lemma init_vals :
    a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 4 ∧ a 3 = 15 ∧ a 4 = 4 ∧ a 5 = 59 ∧
    a 6 = 0 ∧ a 7 = 239 ∧ a 8 = 80 ∧ a 9 = 943 ∧ a 10 = 320 ∧
    a 11 = 3839 ∧ a 12 = 1344 ∧ a 13 = 15039 ∧ a 14 = 5376 ∧ a 15 = 60415 :=
  ⟨(a_eq_aFast 0).trans (by decide), (a_eq_aFast 1).trans (by decide),
   (a_eq_aFast 2).trans (by decide), (a_eq_aFast 3).trans (by decide),
   (a_eq_aFast 4).trans (by decide), (a_eq_aFast 5).trans (by decide),
   (a_eq_aFast 6).trans (by decide), (a_eq_aFast 7).trans (by decide),
   (a_eq_aFast 8).trans (by decide), (a_eq_aFast 9).trans (by decide),
   (a_eq_aFast 10).trans (by decide), (a_eq_aFast 11).trans (by decide),
   (a_eq_aFast 12).trans (by decide), (a_eq_aFast 13).trans (by decide),
   (a_eq_aFast 14).trans (by decide), (a_eq_aFast 15).trans (by decide)⟩

lemma gf_claim :
    PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 - 2 * X ^ 2) * (1 + 2 * X ^ 2)) =
      1 + 2 * X - X ^ 2 + 5 * X ^ 3 - 16 * X ^ 4 - 16 * X ^ 5 - 16 * X ^ 7 + 144 * X ^ 8 +
      16 * X ^ 9 - 64 * X ^ 10 + 64 * X ^ 11 - 320 * X ^ 12 - 320 * X ^ 13 + 256 * X ^ 14 +
      256 * X ^ 15 := by
  let s := PowerSeries.mk (fun n => (a n : ℤ))
  have hring : s * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 - 2 * X ^ 2) * (1 + 2 * X ^ 2)) =
      C (1 : ℤ) * (s * X ^ 0) + C (-5 : ℤ) * (s * X ^ 2) +
      C (20 : ℤ) * (s * X ^ 6) + C (-16 : ℤ) * (s * X ^ 8) := by
    simp only [map_neg, map_one, map_ofNat]; ring
  rw [hring]
  have hrhs : (1 + 2 * X - X ^ 2 + 5 * X ^ 3 - 16 * X ^ 4 - 16 * X ^ 5 - 16 * X ^ 7 +
      144 * X ^ 8 + 16 * X ^ 9 - 64 * X ^ 10 + 64 * X ^ 11 - 320 * X ^ 12 - 320 * X ^ 13 +
      256 * X ^ 14 + 256 * X ^ 15 : PowerSeries ℤ) =
      C (1 : ℤ) * X ^ 0 + C (2 : ℤ) * X ^ 1 + C (-1 : ℤ) * X ^ 2 + C (5 : ℤ) * X ^ 3 +
      C (-16 : ℤ) * X ^ 4 + C (-16 : ℤ) * X ^ 5 + C (-16 : ℤ) * X ^ 7 + C (144 : ℤ) * X ^ 8 +
      C (16 : ℤ) * X ^ 9 + C (-64 : ℤ) * X ^ 10 + C (64 : ℤ) * X ^ 11 + C (-320 : ℤ) * X ^ 12 +
      C (-320 : ℤ) * X ^ 13 + C (256 : ℤ) * X ^ 14 + C (256 : ℤ) * X ^ 15 := by
    simp only [map_neg, map_one, map_ofNat]; ring
  rw [hrhs]
  ext n
  simp only [map_add, coeff_C_mul]
  simp only [coeff_mul_X_pow', coeff_X_pow, s, coeff_mk]
  by_cases hn : n < 16
  · obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15⟩ := init_vals
    interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15]
  · have h16 : 15 < n := by omega
    have hrec := rec_claim n h16
    simp [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega,
          show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 7 by omega, show n ≠ 8 by omega,
          show n ≠ 9 by omega, show n ≠ 10 by omega, show n ≠ 11 by omega, show n ≠ 12 by omega,
          show n ≠ 13 by omega, show n ≠ 14 by omega, show n ≠ 15 by omega,
          show 2 ≤ n by omega, show 6 ≤ n by omega, show 8 ≤ n by omega]
    linarith

end Rule107Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a278901.main :=
  ⟨rec_claim, gf_claim⟩
