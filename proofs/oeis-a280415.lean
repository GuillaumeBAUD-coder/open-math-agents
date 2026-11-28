import OMAStatements.S_oeis_a280415
import Mathlib

namespace OMA.Helpers_oeis_a280415
open OMA.S_oeis_a280415

def cl : ℕ → ℤ → ℤ → Bool
  | 0 => fun i j => decide (i = 0 ∧ j = 0)
  | t + 1 => fun i j => Nat.testBit 262 ((cl t i j).toNat + 2 * ((cl t (i + 1) j).toNat +
      (cl t (i - 1) j).toNat + (cl t i (j + 1)).toNat + (cl t i (j - 1)).toNat))

def R (c r l u d : Bool) : Bool := Nat.testBit 262 (c.toNat + 2 * (r.toNat + l.toNat + u.toNat + d.toNat))

theorem cell_succ (t : ℕ) (i j : ℤ) : cl (t + 1) i j = R (cl t i j) (cl t (i + 1) j)
    (cl t (i - 1) j) (cl t i (j + 1)) (cl t i (j - 1)) := rfl

def bg (_t : ℕ) : Bool := false

theorem cone : ∀ t : ℕ, ∀ x y : ℤ, (t : ℤ) < |x| + |y| → cl t x y = bg t := by
  intro t
  induction t with
  | zero =>
    intro x y h
    show decide (x = 0 ∧ y = 0) = false
    simp only [decide_eq_false_iff_not, not_and]
    intro hx hy; subst hx hy; simp at h
  | succ t ih =>
    intro x y h
    push_cast at h
    rw [cell_succ, ih x y (by omega),
      ih (x + 1) y (by cases abs_cases x <;> cases abs_cases (x + 1) <;> cases abs_cases y <;> omega),
      ih (x - 1) y (by cases abs_cases x <;> cases abs_cases (x - 1) <;> cases abs_cases y <;> omega),
      ih x (y + 1) (by cases abs_cases x <;> cases abs_cases (y + 1) <;> cases abs_cases y <;> omega),
      ih x (y - 1) (by cases abs_cases x <;> cases abs_cases (y - 1) <;> cases abs_cases y <;> omega)]
    show R false false false false false = false
    decide

theorem symm : ∀ t : ℕ, ∀ x y : ℤ, cl t (-x) y = cl t x y := by
  intro t
  induction t with
  | zero => intro x y; show decide (-x = 0 ∧ y = 0) = decide (x = 0 ∧ y = 0); simp
  | succ t ih =>
    intro x y
    rw [cell_succ, cell_succ, ih, show -x + 1 = -(x - 1) by ring, ih, show -x - 1 = -(x + 1) by ring, ih, ih, ih]
    unfold R; congr 2; omega

theorem swap : ∀ t : ℕ, ∀ x y : ℤ, cl t x y = cl t y x := by
  intro t
  induction t with
  | zero => intro x y; show decide (x = 0 ∧ y = 0) = decide (y = 0 ∧ x = 0); simp [and_comm]
  | succ t ih =>
    intro x y
    rw [cell_succ, cell_succ, ih x y, ih (x + 1) y, ih (x - 1) y, ih x (y + 1), ih x (y - 1)]
    unfold R; congr 2; omega

theorem negy (t : ℕ) (x y : ℤ) : cl t x (-y) = cl t x y := by
  rw [swap, symm, swap]

/-- window coordinates: `u = x + t`. -/
def nb (t : ℕ) (u y : ℤ) : Bool := cl t (u - t) y

theorem nb_succ (t : ℕ) (u y : ℤ) : nb (t + 1) u y = R (nb t (u - 1) y) (nb t u y) (nb t (u - 2) y)
    (nb t (u - 1) (y + 1)) (nb t (u - 1) (y - 1)) := by
  unfold nb
  rw [cell_succ]
  have e0 : u - ((t + 1 : ℕ) : ℤ) = (u - 1) - t := by push_cast; ring
  have e1 : u - ((t + 1 : ℕ) : ℤ) + 1 = u - t := by push_cast; ring
  have e2 : u - ((t + 1 : ℕ) : ℤ) - 1 = (u - 2) - t := by push_cast; ring
  rw [e1, e2, e0]

theorem nb_neg (t : ℕ) (u y : ℤ) (h : u < 0) : nb t u y = bg t := by
  unfold nb; apply cone; cases abs_cases (u - t) <;> cases abs_cases y <;> omega

def newRow (D : ℕ) (b : Bool) (rc ra rb : ℕ) : ℕ :=
  let M := 2 ^ (D + 1) - 1
  let f1 := if b then 1 else 0
  let f2 := if b then 3 else 0
  let c := ((rc <<< 1) ||| f1) &&& M
  let r := rc &&& M
  let l := ((rc <<< 2) ||| f2) &&& M
  let u := ((ra <<< 1) ||| f1) &&& M
  let d := ((rb <<< 1) ||| f1) &&& M
  let s0 := r ^^^ l ^^^ u ^^^ d
  let a2 := (r &&& l) ||| (r &&& u) ||| (r &&& d) ||| (l &&& u) ||| (l &&& d) ||| (u &&& d)
  let a3 := (r &&& l &&& u) ||| (r &&& l &&& d) ||| (r &&& u &&& d) ||| (l &&& u &&& d)
  let e0 := M ^^^ (r ||| l ||| u ||| d)
  let e1 := s0 &&& (M ^^^ a2)
  let e2 := a2 &&& (M ^^^ a3)
  let e3 := s0 &&& a2
  let e4 := r &&& l &&& u &&& d
  let nc := M ^^^ c
  (c &&& e0) ||| (nc &&& e1) ||| (nc &&& e4)

theorem R_formula (c r l u d : Bool) :
    ((c && (true ^^ (r || l || u || d))) || ((true ^^ c) && ((r ^^ l ^^ u ^^ d) && (true ^^ ((r && l) || (r && u) || (r && d) || (l && u) || (l && d) || (u && d))))) || ((true ^^ c) && (r && l && u && d))) = R c r l u d := by
  cases c <;> cases r <;> cases l <;> cases u <;> cases d <;> decide

theorem newRow_bit (D : ℕ) (b : Bool) (rc ra rb k : ℕ) (hk : k ≤ D) :
    (newRow D b rc ra rb).testBit k = R (if 1 ≤ k then rc.testBit (k - 1) else b) (rc.testBit k)
      (if 2 ≤ k then rc.testBit (k - 2) else b) (if 1 ≤ k then ra.testBit (k - 1) else b)
      (if 1 ≤ k then rb.testBit (k - 1) else b) := by
  have hM : (2 ^ (D + 1) - 1 : ℕ).testBit k = true := by
    rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true (by omega)
  have h1 : (if b then 1 else 0 : ℕ).testBit k = (decide (k = 0) && b) := by
    cases b
    · simp
    · rw [if_pos rfl, show (1 : ℕ) = 2 ^ 0 from rfl, Nat.testBit_two_pow]; simp [eq_comm]
  have h3 : (if b then 3 else 0 : ℕ).testBit k = (decide (k < 2) && b) := by
    cases b
    · simp
    · rw [if_pos rfl, show (3 : ℕ) = 2 ^ 2 - 1 from rfl, Nat.testBit_two_pow_sub_one]; simp
  simp only [newRow, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft, hM, h1, h3,
    Bool.and_true]
  rw [← R_formula]
  rcases k with _ | _ | k <;> simp

def step (D : ℕ) (b : Bool) (w : List ℕ) : List ℕ :=
  (List.range (2 * D + 1)).map fun yi =>
    newRow D b (w.getD yi 0) (w.getD (yi + 1) 0) (if yi = 0 then 0 else w.getD (yi - 1) 0)

def Wst (D : ℕ) : ℕ → List ℕ
  | 0 => (List.range (2 * D + 1)).map fun yi => if yi = D then 1 else 0
  | t + 1 => step D (bg t) (Wst D t)

def SV (D t : ℕ) (u y : ℤ) : Bool := ((Wst D t).getD (y + D).toNat 0).testBit u.toNat

theorem getD_mapRange {α : Type} (n i : ℕ) (f : ℕ → α) (d : α) (h : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]; simp

theorem correct (D : ℕ) : ∀ t : ℕ, ∀ u y : ℤ, 0 ≤ u → |y| ≤ D - u → nb t u y = SV D t u y := by
  intro t
  induction t with
  | zero =>
    intro u y hu hy
    unfold SV
    rw [show Wst D 0 = (List.range (2 * D + 1)).map fun yi => if yi = D then 1 else 0 from rfl,
      getD_mapRange _ (y + D).toNat _ _ (by cases abs_cases y <;> omega)]
    show decide (u - ((0 : ℕ) : ℤ) = 0 ∧ y = 0) = _
    by_cases h : y = 0
    · subst h
      rw [if_pos (by omega), show (1 : ℕ) = 2 ^ 0 from rfl, Nat.testBit_two_pow]
      simp only [Nat.cast_zero, sub_zero, and_true, decide_eq_decide]
      omega
    · rw [if_neg (show ¬ (y + (D : ℤ)).toNat = D by cases abs_cases y <;> omega)]; simp [h]
  | succ t ih =>
    intro u y hu hy
    have hy' : -(D : ℤ) ≤ y ∧ y ≤ D := by cases abs_cases y <;> constructor <;> omega
    have key : ∀ u' y' : ℤ, (u' < 0 ∨ (0 ≤ u' ∧ |y'| ≤ D - u')) →
        nb t u' y' = (if 0 ≤ u' then SV D t u' y' else bg t) := by
      intro u' y' h
      rcases h with h | ⟨h1, h2⟩
      · rw [nb_neg t u' y' h, if_neg (by omega)]
      · rw [ih u' y' h1 h2, if_pos h1]
    rw [nb_succ]
    unfold SV
    rw [show Wst D (t + 1) = step D (bg t) (Wst D t) from rfl]
    unfold step
    rw [getD_mapRange _ (y + D).toNat _ _ (by omega), newRow_bit _ _ _ _ _ u.toNat (by cases abs_cases y <;> omega)]
    rw [key (u - 1) y (by cases abs_cases y <;> omega), key u y (Or.inr ⟨hu, hy⟩),
      key (u - 2) y (by cases abs_cases y <;> omega),
      key (u - 1) (y + 1) (by cases abs_cases y <;> cases abs_cases (y + 1) <;> omega),
      key (u - 1) (y - 1) (by cases abs_cases y <;> cases abs_cases (y - 1) <;> omega)]
    unfold SV
    have e1 : (y + D).toNat + 1 = (y + 1 + D).toNat := by omega
    have hn : ((u - 1).toNat) = u.toNat - 1 := by omega
    have hn2 : ((u - 2).toNat) = u.toNat - 2 := by omega
    rw [e1, hn, hn2, if_pos hu]
    by_cases h0 : u = 0
    · subst h0; simp
    · have e2 : (if (y + D).toNat = 0 then 0 else (Wst D t).getD ((y + D).toNat - 1) 0) =
          (Wst D t).getD (y - 1 + D).toNat 0 := by
        rw [if_neg (by cases abs_cases y <;> omega)]; congr 1; omega
      rw [e2]
      simp only [show 1 ≤ u.toNat by omega, show 0 ≤ u - 1 by omega, if_true]
      by_cases h2 : u = 1
      · subst h2; simp
      · simp only [show 2 ≤ u.toNat by omega, show 0 ≤ u - 2 by omega, if_true]

def mk (yi : ℕ) : ℕ := 2 ^ (6 - (if yi ≤ 5 then 5 - yi else yi - 5)) - 1

def msk (w : List ℕ) : List ℕ := (List.range 11).map fun yi => w.getD yi 0 &&& mk yi

theorem perOK_t : msk (Wst 5 10) = msk (Wst 5 6) := by decide +kernel

theorem SV_per (u y : ℤ) (hu : 0 ≤ u) (hy : |y| ≤ 5 - u) : SV 5 10 u y = SV 5 6 u y := by
  have hy' : (y + 5).toNat < 11 := by cases abs_cases y <;> omega
  have h := congrArg (fun w => (w.getD (y + 5).toNat 0).testBit u.toNat) perOK_t
  simp only [msk] at h
  rw [getD_mapRange _ _ _ _ hy', getD_mapRange _ _ _ _ hy', Nat.testBit_and, Nat.testBit_and] at h
  have hm : (mk (y + 5).toNat).testBit u.toNat = true := by
    unfold mk; rw [Nat.testBit_two_pow_sub_one]; apply decide_eq_true
    split_ifs <;> cases abs_cases y <;> omega
  rw [hm, Bool.and_true, Bool.and_true] at h
  exact h

theorem per : ∀ t : ℕ, 6 ≤ t → ∀ u y : ℤ, 0 ≤ u → |y| ≤ 5 - u → nb (t + 4) u y = nb t u y := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => intro u y hu hy; rw [correct 5 10 u y hu hy, correct 5 6 u y hu hy]; exact SV_per u y hu hy
  | succ t ht ih =>
    intro u y hu hy
    have key : ∀ u' y' : ℤ, (u' < 0 ∨ (0 ≤ u' ∧ |y'| ≤ 5 - u')) → nb (t + 4) u' y' = nb t u' y' := by
      intro u' y' h
      rcases h with h | ⟨h1, h2⟩
      · rw [nb_neg _ _ _ h, nb_neg _ _ _ h]; rfl
      · exact ih u' y' h1 h2
    rw [show t + 1 + 4 = (t + 4) + 1 by omega, nb_succ (t + 4), nb_succ t,
      key (u - 1) y (by cases abs_cases y <;> omega), key u y (Or.inr ⟨hu, hy⟩),
      key (u - 2) y (by cases abs_cases y <;> omega),
      key (u - 1) (y + 1) (by cases abs_cases y <;> cases abs_cases (y + 1) <;> omega),
      key (u - 1) (y - 1) (by cases abs_cases y <;> cases abs_cases (y - 1) <;> omega)]

theorem per_red (t : ℕ) (ht : 6 ≤ t) (u y : ℤ) (hu : 0 ≤ u) (hy : |y| ≤ 5 - u) :
    nb t u y = nb (6 + (t - 6) % 4) u y := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases h : t < 10
    · congr 1; omega
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 4 := ⟨t - 4, by omega⟩
      rw [per s (by omega) u y hu hy, ih s (by omega) (by omega)]
      congr 2; omega

def MtL : List (List ℕ) := [[0]]

def RtL : List (List ℕ) := [[0]]

def predR (r : ℕ) (x y : ℤ) : Bool :=
  if -0 ≤ x then ((RtL.getD r []).getD (-x).toNat 0).testBit (y + 0).toNat
  else ((MtL.getD r []).getD (x % 1).toNat 0).testBit (y + 0).toNat

theorem predR_mid (r : ℕ) (x x' : ℤ) (hx : x ≤ -1) (hx' : x' ≤ -1) (h : x % 1 = x' % 1) (y : ℤ) :
    predR r x y = predR r x' y := by
  unfold predR; rw [if_neg (by omega), if_neg (by omega), h]

def Phi (t : ℕ) : Prop :=
  ∀ x y : ℤ, 3 ≤ (t : ℤ) + x → x ≤ 0 → |y| ≤ 0 → cl t x y = predR (t % 1) x y

def baseOK : Bool := (List.range 28).all fun i => (List.range 1).all fun j =>
  SV 32 30 ((i : ℤ) + 3) ((j : ℤ) - 0) == predR 0 ((i : ℤ) - 27) ((j : ℤ) - 0)

theorem baseOK_t : baseOK = true := by decide +kernel

theorem phi_base : Phi 30 := by
  intro x y h1 h2 hy
  have h := baseOK_t
  unfold baseOK at h
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have := h (x + 27).toNat (by omega) (y + 0).toNat (by cases abs_cases y <;> omega)
  rw [show (((x + 27).toNat : ℕ) : ℤ) + 3 = x + 30 by omega, show (((x + 27).toNat : ℕ) : ℤ) - 27 = x by omega,
    show (((y + 0).toNat : ℕ) : ℤ) - 0 = y by cases abs_cases y <;> omega] at this
  rw [show 30 % 1 = 0 from rfl, ← this, ← correct 32 30 (x + 30) y (by omega) (by cases abs_cases y <;> omega)]
  unfold nb; congr 1; push_cast; ring

def triOK : Bool := (List.range 4).all fun r => (List.range 2).all fun v => (List.range 1).all fun j =>
  SV 5 (6 + ((32 + r) - 6) % 4) ((v : ℤ) + 3) ((j : ℤ) - 0) ==
    predR ((32 + r) % 1) ((v : ℤ) + 3 - ((32 + r : ℕ) : ℤ)) ((j : ℤ) - 0)

theorem triOK_t : triOK = true := by decide +kernel

theorem tri_part (s : ℕ) (hs : 31 ≤ s) (u y : ℤ) (hu1 : 3 ≤ u) (hu2 : u ≤ 4) (hy : |y| ≤ 0) :
    cl s (u - s) y = predR (s % 1) (u - s) y := by
  have h := triOK_t
  unfold triOK at h
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have := h (s % 4) (Nat.mod_lt _ (by norm_num)) (u - 3).toNat (by omega) (y + 0).toNat
    (by cases abs_cases y <;> omega)
  rw [show (((u - 3).toNat : ℕ) : ℤ) + 3 = u by omega,
    show (((y + 0).toNat : ℕ) : ℤ) - 0 = y by cases abs_cases y <;> omega,
    show (32 + s % 4 - 6) % 4 = (s - 6) % 4 by omega,
    show (32 + s % 4) % 1 = s % 1 by omega] at this
  rw [show cl s (u - s) y = nb s u y from rfl, per_red s (by omega) u y (by omega)
    (by cases abs_cases y <;> omega), correct 5 _ u y (by omega) (by cases abs_cases y <;> omega), this]
  apply predR_mid
  · push_cast; omega
  · omega
  · push_cast; omega

def stepF (r : ℕ) (x y : ℤ) (b : Bool) : Bool :=
  R (predR r x y) (if x = 0 then predR r (-1) y else predR r (x + 1) y) (predR r (x - 1) y)
    (if y + 1 ≤ 0 then predR r x (y + 1) else if -0 ≤ x then predR r (-1) x else b)
    (if -0 ≤ y - 1 then predR r x (y - 1) else if -0 ≤ x then predR r (-1) x else b) == predR ((r + 1) % 1) x y

def stepOK : Bool := (List.range 1).all fun r => (List.range 4).all fun i => (List.range 1).all fun j =>
  stepF r ((i : ℤ) - 3) ((j : ℤ) - 0) false && stepF r ((i : ℤ) - 3) ((j : ℤ) - 0) true

theorem stepOK_t : stepOK = true := by decide +kernel

theorem stepNear (r : ℕ) (hr : r < 1) (x y : ℤ) (h1 : -3 ≤ x) (h2 : x ≤ 0) (hy : |y| ≤ 0) (b : Bool) :
    stepF r x y b = true := by
  have h := stepOK_t
  unfold stepOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  have := h r hr (x + 3).toNat (by omega) (y + 0).toNat (by cases abs_cases y <;> omega)
  rw [show (((x + 3).toNat : ℕ) : ℤ) - 3 = x by omega,
    show (((y + 0).toNat : ℕ) : ℤ) - 0 = y by cases abs_cases y <;> omega] at this
  cases b
  · exact this.1
  · exact this.2

theorem stepAll (r : ℕ) (hr : r < 1) (x y : ℤ) (h2 : x ≤ 0) (hy : |y| ≤ 0) (b : Bool) :
    stepF r x y b = true := by
  by_cases h1 : -3 ≤ x
  · exact stepNear r hr x y h1 h2 hy b
  · have e : stepF r x y b = stepF r (-3 + (x + 3) % 1) y b := by
      unfold stepF
      simp only [show ¬ x = 0 by omega, show ¬ (-3 + (x + 3) % 1 = 0) by omega, show ¬ (-0 ≤ x) by omega,
        show ¬ (-0 ≤ -3 + (x + 3) % 1) by omega, if_false,
        predR_mid r x (-3 + (x + 3) % 1) (by omega) (by omega) (by omega),
        predR_mid r (x + 1) (-3 + (x + 3) % 1 + 1) (by omega) (by omega) (by omega),
        predR_mid r (x - 1) (-3 + (x + 3) % 1 - 1) (by omega) (by omega) (by omega),
        predR_mid ((r + 1) % 1) x (-3 + (x + 3) % 1) (by omega) (by omega) (by omega)]
    rw [e]
    exact stepNear r hr _ y (by omega) (by omega) hy b

theorem phi_step (t : ℕ) (ht : 30 ≤ t) (H : Phi t) : Phi (t + 1) := by
  intro x y h1 h2 hy
  push_cast at h1
  by_cases hu : (t : ℤ) + 1 + x ≤ 4
  · have := tri_part (t + 1) (by omega) ((t : ℤ) + 1 + x) y (by omega) hu hy
    rw [show (t : ℤ) + 1 + x - ((t + 1 : ℕ) : ℤ) = x by push_cast; ring] at this
    exact this
  · have e0 : cl t x y = predR (t % 1) x y := H x y (by omega) h2 hy
    have er : cl t (x + 1) y = if x = 0 then predR (t % 1) (-1) y else predR (t % 1) (x + 1) y := by
      split_ifs with hx
      · subst hx; rw [show (0 : ℤ) + 1 = -(-1) by norm_num, symm]; exact H (-1) y (by omega) (by norm_num) hy
      · exact H (x + 1) y (by omega) (by omega) hy
    have el : cl t (x - 1) y = predR (t % 1) (x - 1) y := H (x - 1) y (by omega) (by omega) hy
    have e3 : -0 ≤ x → cl t x 1 = predR (t % 1) (-1) x := by
      intro hx
      rw [swap, show (1 : ℤ) = -(-1) by norm_num, symm]
      exact H (-1) x (by omega) (by norm_num) (by cases abs_cases x <;> omega)
    have eu : cl t x (y + 1) = if y + 1 ≤ 0 then predR (t % 1) x (y + 1)
        else if -0 ≤ x then predR (t % 1) (-1) x else cl t x 1 := by
      split_ifs with ha hb
      · exact H x (y + 1) (by omega) h2 (by cases abs_cases y <;> cases abs_cases (y + 1) <;> omega)
      · rw [show y + 1 = 1 by cases abs_cases y <;> omega]; exact e3 hb
      · rw [show y + 1 = 1 by cases abs_cases y <;> omega]
    have ed : cl t x (y - 1) = if -0 ≤ y - 1 then predR (t % 1) x (y - 1)
        else if -0 ≤ x then predR (t % 1) (-1) x else cl t x 1 := by
      split_ifs with ha hb
      · exact H x (y - 1) (by omega) h2 (by cases abs_cases y <;> cases abs_cases (y - 1) <;> omega)
      · rw [show y - 1 = -1 by cases abs_cases y <;> omega, negy]; exact e3 hb
      · rw [show y - 1 = -1 by cases abs_cases y <;> omega, negy]
    have hs := stepAll (t % 1) (Nat.mod_lt _ (by norm_num)) x y h2 hy (cl t x 1)
    unfold stepF at hs
    rw [beq_iff_eq] at hs
    rw [cell_succ, e0, er, el, eu, ed, hs]
    congr 1; omega

theorem phi_all : ∀ t : ℕ, 30 ≤ t → Phi t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact phi_base
  | succ t ht ih => exact phi_step t ht ih


def A (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), if cl n ((k : ℤ) - n) 0 then (2 : ℤ) ^ (n - k) else 0

theorem dig (n k : ℕ) (hn : 30 ≤ n) (hk : k ≤ n) :
    cl n ((k : ℤ) - n) 0 = if k ≤ 4 then SV 5 (6 + (n - 6) % 4) k 0 else predR (n % 1) ((k : ℤ) - n) 0 := by
  split_ifs with h
  · rw [show cl n ((k : ℤ) - n) 0 = nb n k 0 from rfl, per_red n (by omega) k 0 (by omega) (by simp; omega),
      correct 5 _ k 0 (by omega) (by simp; omega)]
  · exact phi_all n hn _ 0 (by omega) (by omega) (by norm_num)

def T1 (r : ℕ) : ℤ := ∑ i ∈ Finset.range 5, if predR (r % 1) ((i : ℤ) - 4) 0 then (2 : ℤ) ^ (4 - i) else 0

def T2 (r : ℕ) : ℤ := ∑ i ∈ Finset.range 1, if predR (r % 1) ((i : ℤ) - 0) 0 then (2 : ℤ) ^ (0 - i) else 0

def K (r : ℕ) : ℤ := T1 r - 2 ^ 4 * T2 r

theorem shift (n : ℕ) (hn : 30 ≤ n) : A (n + 4) = 2 ^ 4 * A n + K (n % 4) := by
  unfold A K
  rw [show n + 4 + 1 = (n - 0) + 5 by omega, Finset.sum_range_add, show n + 1 = (n - 0) + 1 by omega,
    Finset.sum_range_add]
  have hh : ∑ k ∈ Finset.range (n - 0), (if cl (n + 4) ((k : ℤ) - ((n + 4 : ℕ) : ℤ)) 0 then (2 : ℤ) ^ (n + 4 - k) else 0) =
      2 ^ 4 * ∑ k ∈ Finset.range (n - 0), (if cl n ((k : ℤ) - n) 0 then (2 : ℤ) ^ (n - k) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    rw [dig (n + 4) k (by omega) (by omega), dig n k hn (by omega), show (n + 4 - 6) % 4 = (n - 6) % 4 by omega,
      show (n + 4) % 1 = n % 1 by omega, predR_mid _ ((k : ℤ) - ((n + 4 : ℕ) : ℤ)) ((k : ℤ) - n) (by push_cast; omega) (by omega) (by push_cast; omega),
      show n + 4 - k = 4 + (n - k) by omega, pow_add]
    split_ifs <;> simp
  have h1 : ∑ i ∈ Finset.range 5, (if cl (n + 4) (((n - 0 + i : ℕ) : ℤ) - ((n + 4 : ℕ) : ℤ)) 0 then (2 : ℤ) ^ (n + 4 - (n - 0 + i)) else 0) =
      T1 (n % 4) := by
    unfold T1
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    rw [dig (n + 4) (n - 0 + i) (by omega) (by omega), if_neg (show ¬ (n - 0 + i ≤ 4) by omega),
      show (n + 4) % 1 = n % 4 % 1 by omega,
      show ((n - 0 + i : ℕ) : ℤ) - ((n + 4 : ℕ) : ℤ) = (i : ℤ) - 4 by push_cast; omega,
      show n + 4 - (n - 0 + i) = 4 - i by omega]
  have h2 : ∑ i ∈ Finset.range 1, (if cl n (((n - 0 + i : ℕ) : ℤ) - (n : ℤ)) 0 then (2 : ℤ) ^ (n - (n - 0 + i)) else 0) =
      T2 (n % 4) := by
    unfold T2
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    rw [dig n (n - 0 + i) hn (by omega), if_neg (show ¬ (n - 0 + i ≤ 4) by omega),
      show n % 1 = n % 4 % 1 by omega,
      show ((n - 0 + i : ℕ) : ℤ) - (n : ℤ) = (i : ℤ) - 0 by push_cast; omega,
      show n - (n - 0 + i) = 0 - i by omega]
  rw [hh, h1, h2]; ring

def aD (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1),
  if (if k ≤ 4 then SV 5 (6 + (n - 6) % 4) k 0 else predR (n % 1) ((k : ℤ) - n) 0) then (2 : ℤ) ^ (n - k) else 0

theorem A_aD (n : ℕ) (hn : 30 ≤ n) : A n = aD n := by
  unfold A aD
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  rw [dig n k hn (by omega)]

def awZ (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), if ((Wst 32 n).getD 32 0).testBit k then (2 : ℤ) ^ (n - k) else 0

theorem A_aw (n : ℕ) (hn : n ≤ 32) : A n = awZ n := by
  unfold A awZ
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  rw [show cl n ((k : ℤ) - n) 0 = nb n k 0 from rfl, correct 32 n k 0 (by omega) (by simp; omega)]
  unfold SV
  rw [show ((0 : ℤ) + ((32 : ℕ) : ℤ)).toNat = 32 from rfl, Int.toNat_natCast]


def av (n : ℕ) : ℤ := if n < 30 then awZ n else aD n

theorem A_av (n : ℕ) : A n = av n := by
  unfold av
  split_ifs with h
  · exact A_aw n (by omega)
  · exact A_aD n (by omega)

def Kl : List ℤ := [0, 0, 0, 0]

theorem Kqc0 : ((List.range 4).all fun i => K (i + 0) == Kl.getD (i + 0) 0) = true := by decide +kernel

theorem Kq_eq (r : ℕ) (hr : r < 4) : K r = Kl.getD r 0 := by
  by_cases c0 : r < 4
  · have h := Kqc0; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (r - 0) (by omega); rwa [show r - 0 + 0 = r by omega] at this
  omega

def Al : List ℤ := [1, 3, 4, 14, 17, 57, 65, 227, 260, 910, 1025, 3585, 4097, 14337, 16385, 57345, 65537, 229377, 262145, 917505, 1048577, 3670017, 4194305, 14680065, 16777217, 58720257, 67108865, 234881025, 268435457, 939524099, 1073741824, 3758096384, 4294967296, 15032385536, 17179869184, 60129542144]

theorem Aqc0 : ((List.range 5).all fun i => av (i + 0) == Al.getD (i + 0) 0) = true := by decide +kernel

theorem Aqc1 : ((List.range 5).all fun i => av (i + 5) == Al.getD (i + 5) 0) = true := by decide +kernel

theorem Aqc2 : ((List.range 5).all fun i => av (i + 10) == Al.getD (i + 10) 0) = true := by decide +kernel

theorem Aqc3 : ((List.range 5).all fun i => av (i + 15) == Al.getD (i + 15) 0) = true := by decide +kernel

theorem Aqc4 : ((List.range 5).all fun i => av (i + 20) == Al.getD (i + 20) 0) = true := by decide +kernel

theorem Aqc5 : ((List.range 5).all fun i => av (i + 25) == Al.getD (i + 25) 0) = true := by decide +kernel

theorem Aqc6 : ((List.range 5).all fun i => av (i + 30) == Al.getD (i + 30) 0) = true := by decide +kernel

theorem Aqc7 : ((List.range 1).all fun i => av (i + 35) == Al.getD (i + 35) 0) = true := by decide +kernel

theorem Aq_eq (r : ℕ) (hr : r < 36) : av r = Al.getD r 0 := by
  by_cases c0 : r < 5
  · have h := Aqc0; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (r - 0) (by omega); rwa [show r - 0 + 0 = r by omega] at this
  by_cases c1 : r < 10
  · have h := Aqc1; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (r - 5) (by omega); rwa [show r - 5 + 5 = r by omega] at this
  by_cases c2 : r < 15
  · have h := Aqc2; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (r - 10) (by omega); rwa [show r - 10 + 10 = r by omega] at this
  by_cases c3 : r < 20
  · have h := Aqc3; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (r - 15) (by omega); rwa [show r - 15 + 15 = r by omega] at this
  by_cases c4 : r < 25
  · have h := Aqc4; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (r - 20) (by omega); rwa [show r - 20 + 20 = r by omega] at this
  by_cases c5 : r < 30
  · have h := Aqc5; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (r - 25) (by omega); rwa [show r - 25 + 25 = r by omega] at this
  by_cases c6 : r < 35
  · have h := Aqc6; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (r - 30) (by omega); rwa [show r - 30 + 30 = r by omega] at this
  by_cases c7 : r < 36
  · have h := Aqc7; simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
    have := h (r - 35) (by omega); rwa [show r - 35 + 35 = r by omega] at this
  omega

theorem A_Al (n : ℕ) (hn : n < 36) : A n = Al.getD n 0 := by rw [A_av]; exact Aq_eq n hn

def Lz0 (n : ℕ) : ℤ := A n - (4) * A (n - 2)

def Lc0 (r : ℕ) : ℤ := Kl.getD r 0 - (4) * Kl.getD ((r + 2) % 4) 0

theorem Lc0_t : ((List.range 4).all fun r => Lc0 r == 0) = true := by decide +kernel

def sm0 (i : ℕ) : ℤ := Al.getD (i + 32) 0 - (4) * Al.getD (i + 32 - 2) 0

theorem sm0_t : ((List.range 4).all fun i => sm0 i == 0) = true := by decide +kernel

theorem Lz0_zero : ∀ n : ℕ, 32 ≤ n → Lz0 n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h : n < 36
    · have hs := sm0_t
      simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hs
      have := hs (n - 32) (by omega)
      unfold sm0 at this
      unfold Lz0
      rw [show n - 32 + 32 = n by omega] at this
      rw [A_Al n (by omega), A_Al (n - 2) (by omega)]
      exact this
    · have hp := ih (n - 4) (by omega) (by omega)
      have hl := Lc0_t
      simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hl
      have hL := hl ((n - 4) % 4) (Nat.mod_lt _ (by norm_num))
      unfold Lc0 at hL
      rw [← Kq_eq _ (Nat.mod_lt _ (by norm_num)), ← Kq_eq _ (Nat.mod_lt _ (by norm_num))] at hL
      unfold Lz0 at hp ⊢
      have s0 := shift (n - 4) (by omega)
      have s2 := shift (n - 4 - 2) (by omega)
      rw [show n - 4 + 4 = n by omega] at s0
      rw [show n - 4 - 2 + 4 = n - 2 by omega, show (n - 4 - 2) % 4 = ((n - 4) % 4 + 2) % 4 by omega] at s2
      rw [s0, s2]
      linear_combination 2 ^ 4 * hp + hL

theorem bridge : ∀ t : ℕ, ∀ i j : ℤ, cell 262 t i j = cl t i j := by
  intro t
  induction t with
  | zero => intro i j; rfl
  | succ t ih =>
    intro i j
    show Nat.testBit 262 ((cell 262 t i j).toNat + 2 * ((cell 262 t (i + 1) j).toNat +
      (cell 262 t (i - 1) j).toNat + (cell 262 t i (j + 1)).toNat + (cell 262 t i (j - 1)).toNat)) = cl (t + 1) i j
    rw [ih, ih, ih, ih, ih]; rfl

theorem a_eq (n : ℕ) : a n = A n := by
  unfold a A; simp only [bridge]

theorem rec0 (n : ℕ) (hn : 32 ≤ n) : (a n : ℚ) = 4 * a (n - 2) := by
  have h := Lz0_zero n (by omega)
  unfold Lz0 at h
  have h' := congrArg (fun z : ℤ => (z : ℚ)) h
  push_cast at h'
  simp only [a_eq]
  push_cast
  linarith

set_option maxHeartbeats 4000000 in
open PowerSeries in
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * (4 * X ^ 2 - 1 : PowerSeries ℚ) = 12 * X ^ 31 + 4 * X ^ 30 + X ^ 29 + 3 * X ^ 28 + 3 * X ^ 27 + 3 * X ^ 26 + 3 * X ^ 25 + 3 * X ^ 24 + 3 * X ^ 23 + 3 * X ^ 22 + 3 * X ^ 21 + 3 * X ^ 20 + 3 * X ^ 19 + 3 * X ^ 18 + 3 * X ^ 17 + 3 * X ^ 16 + 3 * X ^ 15 + 3 * X ^ 14 + 3 * X ^ 13 + 3 * X ^ 12 + 55 * X ^ 11 + 15 * X ^ 10 - 2 * X ^ 9 + X ^ 7 + 3 * X ^ 6 - X ^ 5 - X ^ 4 - 2 * X ^ 3 - 3 * X - 1 := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℚ, f = fun n => (a n : ℚ) := ⟨_, rfl⟩
  have g0 : f 0 = 1 := by simp only [hf, a_eq, A_Al 0 (by norm_num)]; norm_num [Al]
  have g1 : f 1 = 3 := by simp only [hf, a_eq, A_Al 1 (by norm_num)]; norm_num [Al]
  have g2 : f 2 = 4 := by simp only [hf, a_eq, A_Al 2 (by norm_num)]; norm_num [Al]
  have g3 : f 3 = 14 := by simp only [hf, a_eq, A_Al 3 (by norm_num)]; norm_num [Al]
  have g4 : f 4 = 17 := by simp only [hf, a_eq, A_Al 4 (by norm_num)]; norm_num [Al]
  have g5 : f 5 = 57 := by simp only [hf, a_eq, A_Al 5 (by norm_num)]; norm_num [Al]
  have g6 : f 6 = 65 := by simp only [hf, a_eq, A_Al 6 (by norm_num)]; norm_num [Al]
  have g7 : f 7 = 227 := by simp only [hf, a_eq, A_Al 7 (by norm_num)]; norm_num [Al]
  have g8 : f 8 = 260 := by simp only [hf, a_eq, A_Al 8 (by norm_num)]; norm_num [Al]
  have g9 : f 9 = 910 := by simp only [hf, a_eq, A_Al 9 (by norm_num)]; norm_num [Al]
  have g10 : f 10 = 1025 := by simp only [hf, a_eq, A_Al 10 (by norm_num)]; norm_num [Al]
  have g11 : f 11 = 3585 := by simp only [hf, a_eq, A_Al 11 (by norm_num)]; norm_num [Al]
  have g12 : f 12 = 4097 := by simp only [hf, a_eq, A_Al 12 (by norm_num)]; norm_num [Al]
  have g13 : f 13 = 14337 := by simp only [hf, a_eq, A_Al 13 (by norm_num)]; norm_num [Al]
  have g14 : f 14 = 16385 := by simp only [hf, a_eq, A_Al 14 (by norm_num)]; norm_num [Al]
  have g15 : f 15 = 57345 := by simp only [hf, a_eq, A_Al 15 (by norm_num)]; norm_num [Al]
  have g16 : f 16 = 65537 := by simp only [hf, a_eq, A_Al 16 (by norm_num)]; norm_num [Al]
  have g17 : f 17 = 229377 := by simp only [hf, a_eq, A_Al 17 (by norm_num)]; norm_num [Al]
  have g18 : f 18 = 262145 := by simp only [hf, a_eq, A_Al 18 (by norm_num)]; norm_num [Al]
  have g19 : f 19 = 917505 := by simp only [hf, a_eq, A_Al 19 (by norm_num)]; norm_num [Al]
  have g20 : f 20 = 1048577 := by simp only [hf, a_eq, A_Al 20 (by norm_num)]; norm_num [Al]
  have g21 : f 21 = 3670017 := by simp only [hf, a_eq, A_Al 21 (by norm_num)]; norm_num [Al]
  have g22 : f 22 = 4194305 := by simp only [hf, a_eq, A_Al 22 (by norm_num)]; norm_num [Al]
  have g23 : f 23 = 14680065 := by simp only [hf, a_eq, A_Al 23 (by norm_num)]; norm_num [Al]
  have g24 : f 24 = 16777217 := by simp only [hf, a_eq, A_Al 24 (by norm_num)]; norm_num [Al]
  have g25 : f 25 = 58720257 := by simp only [hf, a_eq, A_Al 25 (by norm_num)]; norm_num [Al]
  have g26 : f 26 = 67108865 := by simp only [hf, a_eq, A_Al 26 (by norm_num)]; norm_num [Al]
  have g27 : f 27 = 234881025 := by simp only [hf, a_eq, A_Al 27 (by norm_num)]; norm_num [Al]
  have g28 : f 28 = 268435457 := by simp only [hf, a_eq, A_Al 28 (by norm_num)]; norm_num [Al]
  have g29 : f 29 = 939524099 := by simp only [hf, a_eq, A_Al 29 (by norm_num)]; norm_num [Al]
  have g30 : f 30 = 1073741824 := by simp only [hf, a_eq, A_Al 30 (by norm_num)]; norm_num [Al]
  have g31 : f 31 = 3758096384 := by simp only [hf, a_eq, A_Al 31 (by norm_num)]; norm_num [Al]
  have grec : ∀ k, 32 ≤ k → f k = (4) * f (k - 2) := by
    intro k hk; have h := Lz0_zero k hk; unfold Lz0 at h
    have h' := congrArg (fun z : ℤ => (z : ℚ)) h
    push_cast at h'
    simp only [hf, a_eq]
    push_cast
    linarith
  rw [← hf]
  clear hf
  set F : PowerSeries ℚ := PowerSeries.mk f with hF
  have hD : F * (4 * X ^ 2 - 1 : PowerSeries ℚ) = -(C (1 : ℚ) * (F * X ^ 0)) + C (4 : ℚ) * (F * X ^ 2) := by
    simp only [map_ofNat, map_one]; ring
  have hN : (12 * X ^ 31 + 4 * X ^ 30 + X ^ 29 + 3 * X ^ 28 + 3 * X ^ 27 + 3 * X ^ 26 + 3 * X ^ 25 + 3 * X ^ 24 + 3 * X ^ 23 + 3 * X ^ 22 + 3 * X ^ 21 + 3 * X ^ 20 + 3 * X ^ 19 + 3 * X ^ 18 + 3 * X ^ 17 + 3 * X ^ 16 + 3 * X ^ 15 + 3 * X ^ 14 + 3 * X ^ 13 + 3 * X ^ 12 + 55 * X ^ 11 + 15 * X ^ 10 - 2 * X ^ 9 + X ^ 7 + 3 * X ^ 6 - X ^ 5 - X ^ 4 - 2 * X ^ 3 - 3 * X - 1 : PowerSeries ℚ) = -(C (1 : ℚ) * X ^ 0) - C (3 : ℚ) * X ^ 1 - C (2 : ℚ) * X ^ 3 - C (1 : ℚ) * X ^ 4 - C (1 : ℚ) * X ^ 5 + C (3 : ℚ) * X ^ 6 + C (1 : ℚ) * X ^ 7 - C (2 : ℚ) * X ^ 9 + C (15 : ℚ) * X ^ 10 + C (55 : ℚ) * X ^ 11 + C (3 : ℚ) * X ^ 12 + C (3 : ℚ) * X ^ 13 + C (3 : ℚ) * X ^ 14 + C (3 : ℚ) * X ^ 15 + C (3 : ℚ) * X ^ 16 + C (3 : ℚ) * X ^ 17 + C (3 : ℚ) * X ^ 18 + C (3 : ℚ) * X ^ 19 + C (3 : ℚ) * X ^ 20 + C (3 : ℚ) * X ^ 21 + C (3 : ℚ) * X ^ 22 + C (3 : ℚ) * X ^ 23 + C (3 : ℚ) * X ^ 24 + C (3 : ℚ) * X ^ 25 + C (3 : ℚ) * X ^ 26 + C (3 : ℚ) * X ^ 27 + C (3 : ℚ) * X ^ 28 + C (1 : ℚ) * X ^ 29 + C (4 : ℚ) * X ^ 30 + C (12 : ℚ) * X ^ 31 := by
    simp only [map_ofNat, map_one]; ring
  rw [hD, hN]
  ext k
  simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', hF, coeff_mk, coeff_C, Nat.sub_zero]
  rcases Nat.lt_or_ge k 32 with h | h
  · interval_cases k <;> simp [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31] <;> norm_num
  · simp only [show 0 ≤ k by omega, show 1 ≤ k by omega, show 2 ≤ k by omega, show 3 ≤ k by omega, show 4 ≤ k by omega, show 5 ≤ k by omega, show 6 ≤ k by omega, show 7 ≤ k by omega, show 9 ≤ k by omega, show 10 ≤ k by omega, show 11 ≤ k by omega, show 12 ≤ k by omega, show 13 ≤ k by omega, show 14 ≤ k by omega, show 15 ≤ k by omega, show 16 ≤ k by omega, show 17 ≤ k by omega, show 18 ≤ k by omega, show 19 ≤ k by omega, show 20 ≤ k by omega, show 21 ≤ k by omega, show 22 ≤ k by omega, show 23 ≤ k by omega, show 24 ≤ k by omega, show 25 ≤ k by omega, show 26 ≤ k by omega, show 27 ≤ k by omega, show 28 ≤ k by omega, show 29 ≤ k by omega, show 30 ≤ k by omega, show 31 ≤ k by omega, show k ≠ 0 by omega, show k - 1 ≠ 0 by omega, show k - 3 ≠ 0 by omega, show k - 4 ≠ 0 by omega, show k - 5 ≠ 0 by omega, show k - 6 ≠ 0 by omega, show k - 7 ≠ 0 by omega, show k - 9 ≠ 0 by omega, show k - 10 ≠ 0 by omega, show k - 11 ≠ 0 by omega, show k - 12 ≠ 0 by omega, show k - 13 ≠ 0 by omega, show k - 14 ≠ 0 by omega, show k - 15 ≠ 0 by omega, show k - 16 ≠ 0 by omega, show k - 17 ≠ 0 by omega, show k - 18 ≠ 0 by omega, show k - 19 ≠ 0 by omega, show k - 20 ≠ 0 by omega, show k - 21 ≠ 0 by omega, show k - 22 ≠ 0 by omega, show k - 23 ≠ 0 by omega, show k - 24 ≠ 0 by omega, show k - 25 ≠ 0 by omega, show k - 26 ≠ 0 by omega, show k - 27 ≠ 0 by omega, show k - 28 ≠ 0 by omega, show k - 29 ≠ 0 by omega, show k - 30 ≠ 0 by omega, show k - 31 ≠ 0 by omega, if_true, if_false]
    linear_combination (-1) * grec k h

end OMA.Helpers_oeis_a280415

open OMA.Helpers_oeis_a280415 in
theorem OMA.solution : type_of% @OMA.S_oeis_a280415.main := ⟨rec0, gf⟩
