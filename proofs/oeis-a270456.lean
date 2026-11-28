import OMAStatements.S_oeis_a270456
import Mathlib
/-!
Proof of the conjectures of the statement oeis-a270456 (OEIS A270456), Rule 163.

Method: stage t of the automaton is described exactly by an explicit region of the plane
(defined by linear inequalities and a parity condition); one step of the rule maps the description
at t to the one at t + 1 (a case split on the five cells of the neighbourhood, closed by omega).
The ON cells of the square are then counted row by row in closed form, and every conjecture
reduces to a polynomial identity in n and (-1)^n.
-/
namespace OMA.CA_a270456

open OMA.S_oeis_a270456 PowerSeries

def nxt (code : ℕ) (g : ℤ → ℤ → Bool) : ℤ → ℤ → Bool := fun i j =>
  code.testBit ((g i j).toNat + 2 * ((g (i + 1) j).toNat + (g (i - 1) j).toNat +
    (g i (j + 1)).toNat + (g i (j - 1)).toNat))

theorem cell_succ (code t : ℕ) : cell code (t + 1) = nxt code (cell code t) := by
  funext i j
  rfl

/-- A sum over the rows `i < 2t+1` of a function of `|i - t|`. -/
theorem symsum (t : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range (2 * t + 1), f ((t - i) + (i - t)) =
      f 0 + 2 * ∑ k ∈ Finset.range t, f (k + 1) := by
  rw [show 2 * t + 1 = (t + 1) + t by ring, Finset.sum_range_add, Finset.sum_range_succ]
  have h1 : ∑ x ∈ Finset.range t, f ((t - x) + (x - t)) = ∑ k ∈ Finset.range t, f (k + 1) := by
    rw [← Finset.sum_range_reflect (fun k => f (k + 1)) t]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have := Finset.mem_range.mp hx
    congr 1
    omega
  have h2 : ∑ x ∈ Finset.range t, f ((t - (t + 1 + x)) + (t + 1 + x - t)) =
      ∑ k ∈ Finset.range t, f (k + 1) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    congr 1
    omega
  rw [h1, h2, show (t - t) + (t - t) = 0 by omega]
  ring

theorem dbl' (h : ℕ → ℕ) (n : ℕ) :
    ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range (n - 1 - a), h (a + b + 2) =
      ∑ k ∈ Finset.range n, k * h (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, show n + 1 - 1 - n = 0 by omega,
      Finset.sum_range_zero, add_zero]
    have e : ∀ a ∈ Finset.range n, ∑ b ∈ Finset.range (n + 1 - 1 - a), h (a + b + 2) =
        ∑ b ∈ Finset.range (n - 1 - a), h (a + b + 2) + h (n + 1) := by
      intro a ha
      have := Finset.mem_range.mp ha
      rw [show n + 1 - 1 - a = (n - 1 - a) + 1 by omega, Finset.sum_range_succ,
        show a + (n - 1 - a) + 2 = n + 1 by omega]
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ih, Finset.sum_const, Finset.card_range,
      smul_eq_mul]

theorem dbl (g : ℕ → ℕ) (n : ℕ) (hg : ∀ k, n < k → g k = 0) :
    ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, g (a + 1 + (b + 1)) =
      ∑ k ∈ Finset.range n, k * g (k + 1) := by
  rw [← dbl' g n]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  have := Finset.mem_range.mp ha
  rw [show n = (n - 1 - a) + (a + 1) by omega, Finset.sum_range_add]
  rw [show n - 1 - a + (a + 1) - 1 - a = n - 1 - a by omega]
  have hz : ∑ x ∈ Finset.range (a + 1), g (a + 1 + (n - 1 - a + x + 1)) = 0 :=
    Finset.sum_eq_zero (fun x _ => hg _ (by omega))
  rw [hz, add_zero]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  congr 1
  omega

/-- Sum over the square `[-t, t]²` (index coordinates) of a weight depending on `|x| + |y|`
that vanishes outside the diamond `|x| + |y| ≤ t`. -/
theorem ringsum0 (t : ℕ) (g : ℕ → ℕ) (hg : ∀ k, t < k → g k = 0) :
    ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      g (((t - i) + (i - t)) + ((t - j) + (j - t))) =
      g 0 + ∑ k ∈ Finset.range t, 4 * (k + 1) * g (k + 1) := by
  have hin : ∀ a : ℕ, ∑ j ∈ Finset.range (2 * t + 1), g (a + ((t - j) + (j - t))) =
      g a + 2 * ∑ b ∈ Finset.range t, g (a + (b + 1)) := fun a => symsum t (fun e => g (a + e))
  rw [Finset.sum_congr rfl (fun i _ => hin ((t - i) + (i - t)))]
  rw [symsum t (fun a => g a + 2 * ∑ b ∈ Finset.range t, g (a + (b + 1)))]
  simp only [zero_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [dbl g t hg]
  have e : ∑ k ∈ Finset.range t, 4 * (k + 1) * g (k + 1) =
      4 * ∑ k ∈ Finset.range t, g (k + 1) + 4 * ∑ k ∈ Finset.range t, k * g (k + 1) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [e]
  ring

theorem sum4 (t : ℕ) : ∑ k ∈ Finset.range t, 4 * (k + 1) = 2 * t ^ 2 + 2 * t := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- The same for a weight that is the constant `c` outside the diamond. -/
theorem ringsum (t : ℕ) (w : ℕ → ℕ) (c : ℕ) (hw : ∀ k, t < k → w k = c) :
    ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      w (((t - i) + (i - t)) + ((t - j) + (j - t))) =
      w 0 + ∑ k ∈ Finset.range t, 4 * (k + 1) * w (k + 1) + c * (2 * t ^ 2 + 2 * t) := by
  have split : ∀ k, w k = (if k ≤ t then w k else 0) + c * (if k ≤ t then 0 else 1) := by
    intro k
    by_cases hk : k ≤ t
    · simp [hk]
    · simp [hk, hw k (by omega)]
  have h1 := ringsum0 t (fun k => if k ≤ t then w k else 0) (fun k hk => by simp; omega)
  have h2 := ringsum0 t (fun k => if k ≤ t then 1 else 0) (fun k hk => by simp; omega)
  have hall : ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      ((if ((t - i) + (i - t)) + ((t - j) + (j - t)) ≤ t then 1 else 0) +
       (if ((t - i) + (i - t)) + ((t - j) + (j - t)) ≤ t then 0 else 1)) = (2 * t + 1) ^ 2 := by
    have : ∀ k : ℕ, ((if k ≤ t then 1 else 0) + (if k ≤ t then 0 else 1) : ℕ) = 1 := by
      intro k; split_ifs <;> rfl
    simp only [this, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    ring
  simp only [Finset.sum_add_distrib] at hall
  rw [h2] at hall
  have hs : ∑ k ∈ Finset.range t, 4 * (k + 1) * (if k + 1 ≤ t then 1 else 0) =
      ∑ k ∈ Finset.range t, 4 * (k + 1) := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have := Finset.mem_range.mp hk
    simp [show k + 1 ≤ t by omega]
  have hg := sum4 t
  simp only [hs, hg, show (0 : ℕ) ≤ t from Nat.zero_le t, if_true] at hall
  have h3 : ∑ k ∈ Finset.range t, 4 * (k + 1) * (if k + 1 ≤ t then w (k + 1) else 0) =
      ∑ k ∈ Finset.range t, 4 * (k + 1) * w (k + 1) := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have := Finset.mem_range.mp hk
    simp [show k + 1 ≤ t by omega]
  simp only [h3, Nat.zero_le, if_true] at h1
  conv_lhs => enter [2, i, 2, j]; rw [split]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h1]
  have hout : ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      (if ((t - i) + (i - t)) + ((t - j) + (j - t)) ≤ t then 0 else 1) = 2 * t ^ 2 + 2 * t := by
    have : (2 * t + 1) ^ 2 = (2 * t ^ 2 + 2 * t + 1) + (2 * t ^ 2 + 2 * t) := by ring
    omega
  rw [hout]

/-- Turning a cell sum into a sum of a weight of `|x| + |y|`. -/
theorem to_ring (t : ℕ) (G : ℤ → ℤ → Bool) (w : ℕ → ℕ)
    (hG : ∀ x y : ℤ, (if G x y = true then 1 else 0) = w (x.natAbs + y.natAbs)) :
    ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      (if G ((i : ℤ) - t) ((j : ℤ) - t) = true then 1 else 0) =
    ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      w (((t - i) + (i - t)) + ((t - j) + (j - t))) := by
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [hG]
  congr 1
  omega

/-- Stage `t` of Rule 163: at even times the even cells of the diamond `d = |x| + |y| ≤ t`; at odd
times everything except the odd cells of that diamond. -/
abbrev P (t d : ℕ) : Prop := (t % 2 = 0 ∧ d ≤ t ∧ d % 2 = 0) ∨ (t % 2 = 1 ∧ ¬(d ≤ t ∧ d % 2 = 1))

def F (t : ℕ) (x y : ℤ) : Bool := decide (P t (x.natAbs + y.natAbs))

theorem stA (t d : ℕ) (hd : 1 ≤ d) (n : ℕ) (hn : n = 2 * (decide (P t (d + 1))).toNat + 2 * (decide (P t (d - 1))).toNat) :
    Nat.testBit 163 ((decide (P t d)).toNat + 2 * n) = decide (P (t + 1) d) := by
  subst hn
  rw [Nat.testBit_eq_decide_div_mod_eq]
  apply decide_eq_decide.mpr
  by_cases h0 : P t d <;> by_cases h1 : P t (d + 1) <;> by_cases h2 : P t (d - 1) <;>
    simp only [h0, h1, h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;>
    norm_num <;> simp only [P] at * <;> omega

theorem stB (t d : ℕ) (hd : 1 ≤ d) (n : ℕ) (hn : n = 3 * (decide (P t (d + 1))).toNat + (decide (P t (d - 1))).toNat) :
    Nat.testBit 163 ((decide (P t d)).toNat + 2 * n) = decide (P (t + 1) d) := by
  subst hn
  rw [Nat.testBit_eq_decide_div_mod_eq]
  apply decide_eq_decide.mpr
  by_cases h0 : P t d <;> by_cases h1 : P t (d + 1) <;> by_cases h2 : P t (d - 1) <;>
    simp only [h0, h1, h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;>
    norm_num <;> simp only [P] at * <;> omega

theorem stC (t d : ℕ) (hd : d = 0) (n : ℕ) (hn : n = 4 * (decide (P t (d + 1))).toNat) :
    Nat.testBit 163 ((decide (P t d)).toNat + 2 * n) = decide (P (t + 1) d) := by
  subst hn
  rw [Nat.testBit_eq_decide_div_mod_eq]
  apply decide_eq_decide.mpr
  by_cases h0 : P t d <;> by_cases h1 : P t (d + 1) <;> 
    simp only [h0, h1, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;>
    norm_num <;> simp only [P] at * <;> omega

theorem stepF (t : ℕ) (x y : ℤ) : nxt 163 (F t) x y = F (t + 1) x y := by
  simp only [nxt, F]
  rcases lt_trichotomy x 0 with hx | hx | hx <;> rcases lt_trichotomy y 0 with hy | hy | hy
  · rw [show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega, show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega, show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega, show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega]
    exact stA t _ (by omega) _ (by omega)
  · rw [show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega, show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega, show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega, show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega]
    exact stB t _ (by omega) _ (by omega)
  · rw [show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega, show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega, show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega, show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega]
    exact stA t _ (by omega) _ (by omega)
  · rw [show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega, show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega, show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega, show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega]
    exact stB t _ (by omega) _ (by omega)
  · rw [show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega, show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega, show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega, show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega]
    exact stC t _ (by omega) _ (by omega)
  · rw [show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega, show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega, show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega, show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega]
    exact stB t _ (by omega) _ (by omega)
  · rw [show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega, show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega, show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega, show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega]
    exact stA t _ (by omega) _ (by omega)
  · rw [show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega, show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega, show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega, show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega]
    exact stB t _ (by omega) _ (by omega)
  · rw [show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega, show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega, show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega, show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega]
    exact stA t _ (by omega) _ (by omega)

theorem cellF (t : ℕ) : cell 163 t = F t := by
  induction t with
  | zero =>
    funext x y
    show decide (x = 0 ∧ y = 0) = F 0 x y
    unfold F
    congr 1
    apply propext
    unfold P
    constructor
    · rintro ⟨rfl, rfl⟩
      decide
    · intro h
      omega
  | succ t ih =>
    rw [cell_succ, ih]
    funext x y
    exact stepF t x y

theorem evsum (m : ℕ) : ∑ k ∈ Finset.range (2 * m), 4 * (k + 1) * (if (k + 1) % 2 = 0 then 1 else 0) =
    4 * m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      if_neg (by omega), if_pos (by omega)]
    ring

def wE (m k : ℕ) : ℕ := if k ≤ 2 * m ∧ k % 2 = 0 then 1 else 0

def wO (m k : ℕ) : ℕ := if ¬(k ≤ 2 * m + 1 ∧ k % 2 = 1) then 1 else 0

theorem cE (m : ℕ) (hm : 0 ≤ m) : (onCount 163 (2 * m) : ℚ) = (2 * (m : ℚ) + 1) ^ 2 := by
  have h : onCount 163 (2 * m) = (2 * m + 1) ^ 2 := by
    simp only [onCount, cellF]
    rw [to_ring (2 * m) (F (2 * m)) (wE m) (by
      intro x y
      simp only [F, wE, decide_eq_true_eq]
      split_ifs <;> simp only [P] at * <;> omega)]
    rw [ringsum (2 * m) (wE m) 0 (fun k hk => by simp only [wE]; rw [if_neg (by omega)])]
    have e : ∑ k ∈ Finset.range (2 * m), 4 * (k + 1) * wE m (k + 1) =
        ∑ k ∈ Finset.range (2 * m), 4 * (k + 1) * (if (k + 1) % 2 = 0 then 1 else 0) := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have := Finset.mem_range.mp hk
      simp only [wE]
      split_ifs <;> omega
    rw [e, evsum, show wE m 0 = 1 by simp [wE]]
    ring
  rw [h]
  push_cast
  ring

theorem cO (m : ℕ) (hm : 0 ≤ m) : (onCount 163 (2 * m + 1) : ℚ) =
    1 + 4 * (m : ℚ) * (m + 1) + 2 * (2 * (m : ℚ) + 1) ^ 2 + 2 * (2 * (m : ℚ) + 1) := by
  have h : onCount 163 (2 * m + 1) = 1 + 4 * m * (m + 1) + 2 * (2 * m + 1) ^ 2 + 2 * (2 * m + 1) := by
    simp only [onCount, cellF]
    rw [to_ring (2 * m + 1) (F (2 * m + 1)) (wO m) (by
      intro x y
      simp only [F, wO, decide_eq_true_eq]
      split_ifs <;> simp only [P] at * <;> omega)]
    rw [ringsum (2 * m + 1) (wO m) 1 (fun k hk => by simp only [wO]; rw [if_pos (by omega)])]
    have e : ∑ k ∈ Finset.range (2 * m + 1), 4 * (k + 1) * wO m (k + 1) =
        ∑ k ∈ Finset.range (2 * m), 4 * (k + 1) * (if (k + 1) % 2 = 0 then 1 else 0) := by
      rw [Finset.sum_range_succ]
      rw [show wO m (2 * m + 1) = 0 by simp only [wO]; rw [if_neg (by omega)], mul_zero, add_zero]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have := Finset.mem_range.mp hk
      simp only [wO]
      split_ifs <;> omega
    rw [e, evsum, show wO m 0 = 1 by simp [wO]]
    ring
  rw [h]
  push_cast
  ring

theorem cV0 : (onCount 163 0 : ℚ) = 1 := by
  rw [show (0 : ℕ) = 2 * 0 by norm_num, cE 0 (by norm_num)]
  try norm_num

theorem cV1 : (onCount 163 1 : ℚ) = 5 := by
  rw [show (1 : ℕ) = 2 * 0 + 1 by norm_num, cO 0 (by norm_num)]
  try norm_num

theorem cV2 : (onCount 163 2 : ℚ) = 9 := by
  rw [show (2 : ℕ) = 2 * 1 by norm_num, cE 1 (by norm_num)]
  try norm_num

theorem cV3 : (onCount 163 3 : ℚ) = 33 := by
  rw [show (3 : ℕ) = 2 * 1 + 1 by norm_num, cO 1 (by norm_num)]
  try norm_num

theorem cV4 : (onCount 163 4 : ℚ) = 25 := by
  rw [show (4 : ℕ) = 2 * 2 by norm_num, cE 2 (by norm_num)]
  try norm_num

theorem cV5 : (onCount 163 5 : ℚ) = 85 := by
  rw [show (5 : ℕ) = 2 * 2 + 1 by norm_num, cO 2 (by norm_num)]
  try norm_num

theorem cV6 : (onCount 163 6 : ℚ) = 49 := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num, cE 3 (by norm_num)]
  try norm_num

theorem cV7 : (onCount 163 7 : ℚ) = 161 := by
  rw [show (7 : ℕ) = 2 * 3 + 1 by norm_num, cO 3 (by norm_num)]
  try norm_num

theorem cV8 : (onCount 163 8 : ℚ) = 81 := by
  rw [show (8 : ℕ) = 2 * 4 by norm_num, cE 4 (by norm_num)]
  try norm_num

theorem cV9 : (onCount 163 9 : ℚ) = 261 := by
  rw [show (9 : ℕ) = 2 * 4 + 1 by norm_num, cO 4 (by norm_num)]
  try norm_num

theorem cV10 : (onCount 163 10 : ℚ) = 121 := by
  rw [show (10 : ℕ) = 2 * 5 by norm_num, cE 5 (by norm_num)]
  try norm_num

theorem cV11 : (onCount 163 11 : ℚ) = 385 := by
  rw [show (11 : ℕ) = 2 * 5 + 1 by norm_num, cO 5 (by norm_num)]
  try norm_num

theorem cV12 : (onCount 163 12 : ℚ) = 169 := by
  rw [show (12 : ℕ) = 2 * 6 by norm_num, cE 6 (by norm_num)]
  try norm_num

def G (n : ℕ) : ℚ := ((4 : ℚ) * (n : ℚ) ^ 0 + (4 : ℚ) * (n : ℚ) ^ 1) + (-1 : ℚ) ^ n * ((2 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 2)

theorem aG (n : ℕ) (hn : 0 ≤ n) : (a n : ℚ) = G n := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have h := cE m (by omega)
    have h' := cO m (by omega)
    have h1 : (-1 : ℚ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
    simp only [a, G, h1]
    push_cast
    rw [h, h']
    ring
  · have h := cO m (by omega)
    have h' := cE (m + 1) (by omega)
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring] at h'
    push_cast at h'
    have h1 : (-1 : ℚ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    simp only [a, G, h1]
    push_cast
    rw [h, h']
    ring

theorem aV0 : (a 0 : ℚ) = 4 := by
  simp only [a]
  push_cast
  rw [cV1, cV0]
  norm_num

theorem aV1 : (a 1 : ℚ) = 4 := by
  simp only [a]
  push_cast
  rw [cV2, cV1]
  norm_num

theorem aV2 : (a 2 : ℚ) = 24 := by
  simp only [a]
  push_cast
  rw [cV3, cV2]
  norm_num

theorem aV3 : (a 3 : ℚ) = -8 := by
  rw [aG 3 (by norm_num)]
  norm_num [G]

theorem aV4 : (a 4 : ℚ) = 60 := by
  rw [aG 4 (by norm_num)]
  norm_num [G]

theorem aV5 : (a 5 : ℚ) = -36 := by
  rw [aG 5 (by norm_num)]
  norm_num [G]

theorem aV6 : (a 6 : ℚ) = 112 := by
  rw [aG 6 (by norm_num)]
  norm_num [G]

theorem aV7 : (a 7 : ℚ) = -80 := by
  rw [aG 7 (by norm_num)]
  norm_num [G]

theorem aV8 : (a 8 : ℚ) = 180 := by
  rw [aG 8 (by norm_num)]
  norm_num [G]

theorem aV9 : (a 9 : ℚ) = -140 := by
  rw [aG 9 (by norm_num)]
  norm_num [G]

theorem aV10 : (a 10 : ℚ) = 264 := by
  rw [aG 10 (by norm_num)]
  norm_num [G]

end OMA.CA_a270456

open OMA.CA_a270456 OMA.S_oeis_a270456 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a270456.main := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rcases Nat.lt_or_ge n 0 with h | h
    · interval_cases n
      all_goals first
        | (norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10]; done)
        | (exfalso; revert hp; decide)
    · rw [aG n h]
      simp only [G]
      push_cast
      ring
  · intro n hp
    rcases Nat.lt_or_ge n 0 with h | h
    · interval_cases n
      all_goals first
        | (norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10]; done)
        | (exfalso; revert hp; decide)
    · rw [aG n h]
      simp only [G]
      rw [Even.neg_one_pow hp]
      push_cast
      ring
  · intro n hp
    rcases Nat.lt_or_ge n 0 with h | h
    · interval_cases n
      all_goals first
        | (norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10]; done)
        | (exfalso; revert hp; decide)
    · rw [aG n h]
      simp only [G]
      rw [Odd.neg_one_pow hp]
      push_cast
      ring
  · intro n hn0
    rcases Nat.lt_or_ge n 5 with h | h
    · interval_cases n <;> norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
      rw [show k + 5 - 1 = k + 4 by omega]
      rw [show k + 5 - 2 = k + 3 by omega]
      rw [show k + 5 - 3 = k + 2 by omega]
      rw [show k + 5 - 4 = k + 1 by omega]
      rw [show k + 5 - 5 = k + 0 by omega]
      rw [aG (k + 5) (by omega), aG (k + 4) (by omega), aG (k + 3) (by omega), aG (k + 2) (by omega), aG (k + 1) (by omega), aG (k + 0) (by omega)]
      simp only [G]
      push_cast
      ring
  · have hL : mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X) ^ 3 : PowerSeries ℚ) = mk (fun n => (a n : ℚ)) + X ^ 1 * mk (fun n => (a n : ℚ)) - C 2 * (X ^ 2 * mk (fun n => (a n : ℚ))) - C 2 * (X ^ 3 * mk (fun n => (a n : ℚ))) + X ^ 4 * mk (fun n => (a n : ℚ)) + X ^ 5 * mk (fun n => (a n : ℚ)) := by
      try simp only [map_ofNat]
      ring
    have hR : (4 * (1 + 2 * X + 5 * X ^ 2) : PowerSeries ℚ) = C 4 + C 8 * X ^ 1 + C 20 * X ^ 2 := by
      try simp only [map_ofNat]
      ring
    rw [hL, hR]
    ext k
    simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow, coeff_one, coeff_C]
    rcases Nat.lt_or_ge k 9 with h | h
    · interval_cases k <;> norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 9 := ⟨k - 9, by omega⟩
      rw [if_pos (show 1 ≤ j + 9 by omega)]
      rw [if_pos (show 2 ≤ j + 9 by omega)]
      rw [if_pos (show 3 ≤ j + 9 by omega)]
      rw [if_pos (show 4 ≤ j + 9 by omega)]
      rw [if_pos (show 5 ≤ j + 9 by omega)]
      rw [if_neg (show j + 9 ≠ 0 by omega)]
      rw [if_neg (show j + 9 ≠ 1 by omega)]
      rw [if_neg (show j + 9 ≠ 2 by omega)]
      rw [show j + 9 - 1 = j + 8 by omega]
      rw [show j + 9 - 2 = j + 7 by omega]
      rw [show j + 9 - 3 = j + 6 by omega]
      rw [show j + 9 - 4 = j + 5 by omega]
      rw [show j + 9 - 5 = j + 4 by omega]
      rw [aG (j + 9) (by omega), aG (j + 8) (by omega), aG (j + 7) (by omega), aG (j + 6) (by omega), aG (j + 5) (by omega), aG (j + 4) (by omega)]
      simp only [G]
      push_cast
      ring
