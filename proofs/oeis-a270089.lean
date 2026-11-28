import OMAStatements.S_oeis_a270089
import Mathlib
/-!
Proof of the conjectures of the statement oeis-a270089 (OEIS A270089), Rule 73.

Method: from stage 4 on, the automaton is a uniform background (blinking or not) with a fixed
finite list of exceptional cells, alternating between two phases. Each phase step is checked by
a finite kernel computation on a box around the exceptions (everything farther away sees only
background), the count of ON cells follows from the length of the exception list, and every
conjecture then reduces to a polynomial identity in n and (-1)^n (or 2^n and 4^n).
The exception-list technique follows the merged proof of oeis-a273848 in this repository.
-/

namespace OMA.CA_a270089

open OMA.S_oeis_a270089 PowerSeries

abbrev P := ℤ × ℤ

/-- A pattern: background `b` everywhere except on the finite list `L`, where the value is `!b`. -/
def pic (b : Bool) (L : List P) : ℤ → ℤ → Bool := fun i j => if (i, j) ∈ L then !b else b

/-- One synchronous step of the automaton with Wolfram code `code`. -/
def nxt (code : ℕ) (g : ℤ → ℤ → Bool) : ℤ → ℤ → Bool := fun i j =>
  code.testBit ((g i j).toNat + 2 * ((g (i + 1) j).toNat + (g (i - 1) j).toNat +
    (g i (j + 1)).toNat + (g i (j - 1)).toNat))

theorem cell_succ (code t : ℕ) : cell code (t + 1) = nxt code (cell code t) := by
  funext i j
  rfl

theorem cell_zero (code : ℕ) : cell code 0 = pic false [(0, 0)] := by
  funext i j
  by_cases h : i = 0 ∧ j = 0
  · obtain ⟨rfl, rfl⟩ := h
    rfl
  · have h' : (i, j) ∉ [((0 : ℤ), (0 : ℤ))] := by
      simp only [List.mem_singleton, Prod.mk.injEq]
      exact h
    simp only [cell, pic, if_neg h']
    exact decide_eq_false h

/-- Every point of the list lies in the square `[-R, R]²`. -/
def inR (R : ℕ) (L : List P) : Prop :=
  ∀ p ∈ L, -(R : ℤ) ≤ p.1 ∧ p.1 ≤ R ∧ -(R : ℤ) ≤ p.2 ∧ p.2 ≤ R

instance (R : ℕ) (L : List P) : Decidable (inR R L) := by
  unfold inR
  infer_instance

theorem pic_far {R : ℕ} {L : List P} (hL : inR R L) (b : Bool) (u v : ℤ)
    (h : ¬(-(R : ℤ) ≤ u ∧ u ≤ R ∧ -(R : ℤ) ≤ v ∧ v ≤ R)) : pic b L u v = b := by
  have hm : (u, v) ∉ L := fun hm => h (hL _ hm)
  simp only [pic, if_neg hm]

/-- The coordinates `-(R+1), ..., R+1`. -/
def box (R : ℕ) : List ℤ := List.map (fun k : ℕ => (k : ℤ) - ((R : ℤ) + 1)) (List.range (2 * R + 3))

theorem mem_box (R : ℕ) (x : ℤ) (h1 : -((R : ℤ) + 1) ≤ x) (h2 : x ≤ R + 1) : x ∈ box R := by
  have e : (((x + R + 1).toNat : ℕ) : ℤ) = x + R + 1 := Int.toNat_of_nonneg (by omega)
  refine List.mem_map.mpr ⟨(x + R + 1).toNat, List.mem_range.mpr ?_, ?_⟩
  · have : (((x + R + 1).toNat : ℕ) : ℤ) < ((2 * R + 3 : ℕ) : ℤ) := by push_cast; omega
    exact_mod_cast this
  · omega

theorem step {code R : ℕ} {b b' : Bool} {L L' : List P} (hL : inR R L) (hL' : inR R L')
    (hbg : code.testBit (b.toNat + 2 * (b.toNat + b.toNat + b.toNat + b.toNat)) = b')
    (hbox : ∀ x ∈ box R, ∀ y ∈ box R, nxt code (pic b L) x y = pic b' L' x y) :
    nxt code (pic b L) = pic b' L' := by
  funext x y
  by_cases h : (-((R : ℤ) + 1) ≤ x ∧ x ≤ R + 1) ∧ (-((R : ℤ) + 1) ≤ y ∧ y ≤ R + 1)
  · exact hbox x (mem_box R x h.1.1 h.1.2) y (mem_box R y h.2.1 h.2.2)
  · rw [pic_far hL' b' x y (by omega)]
    simp only [nxt]
    rw [pic_far hL b x y (by omega), pic_far hL b (x + 1) y (by omega),
      pic_far hL b (x - 1) y (by omega), pic_far hL b x (y + 1) (by omega),
      pic_far hL b x (y - 1) (by omega)]
    exact hbg

theorem sum_single (t : ℕ) (p : P) (h : -(t : ℤ) ≤ p.1 ∧ p.1 ≤ t ∧ -(t : ℤ) ≤ p.2 ∧ p.2 ≤ t) :
    ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      (if ((i : ℤ) - t, (j : ℤ) - t) = p then (1 : ℤ) else 0) = 1 := by
  obtain ⟨p1, p2⟩ := p
  simp only at h
  rw [Finset.sum_eq_single (p1 + t).toNat, Finset.sum_eq_single (p2 + t).toNat]
  · rw [if_pos]
    simp only [Prod.mk.injEq]
    constructor <;> omega
  · intro j _ hj
    rw [if_neg]
    simp only [Prod.mk.injEq, not_and]
    intro _ h2
    omega
  · intro hn
    exact absurd (Finset.mem_range.mpr (by omega)) hn
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    simp only [Prod.mk.injEq, not_and]
    intro h1
    omega
  · intro hn
    exact absurd (Finset.mem_range.mpr (by omega)) hn

theorem sum_mem (t : ℕ) (L : List P) (hn : L.Nodup) (hb : inR t L) :
    ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      (if ((i : ℤ) - t, (j : ℤ) - t) ∈ L then (1 : ℤ) else 0) = L.length := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have hp : p ∉ L := (List.nodup_cons.mp hn).1
    have e : ∀ i j : ℕ, (if ((i : ℤ) - t, (j : ℤ) - t) ∈ p :: L then (1 : ℤ) else 0) =
        (if ((i : ℤ) - t, (j : ℤ) - t) = p then 1 else 0) +
        (if ((i : ℤ) - t, (j : ℤ) - t) ∈ L then 1 else 0) := by
      intro i j
      by_cases h1 : ((i : ℤ) - t, (j : ℤ) - t) = p
      · rw [h1]
        simp [hp]
      · simp [h1]
    simp only [e, Finset.sum_add_distrib]
    rw [sum_single t p (hb p List.mem_cons_self),
      ih (List.nodup_cons.mp hn).2 (fun q hq => hb q (List.mem_cons_of_mem _ hq))]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

theorem count_false (code t : ℕ) (L : List P) (hn : L.Nodup) (hb : inR t L)
    (h : cell code t = pic false L) : (onCount code t : ℤ) = L.length := by
  rw [← sum_mem t L hn hb]
  simp only [onCount, h, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  by_cases hm : ((i : ℤ) - t, (j : ℤ) - t) ∈ L <;> simp [pic, hm]

theorem count_true (code t : ℕ) (L : List P) (hn : L.Nodup) (hb : inR t L)
    (h : cell code t = pic true L) :
    (onCount code t : ℤ) = (2 * (t : ℤ) + 1) ^ 2 - L.length := by
  have hs : (onCount code t : ℤ) = ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      ((1 : ℤ) - (if ((i : ℤ) - t, (j : ℤ) - t) ∈ L then (1 : ℤ) else 0)) := by
    simp only [onCount, h, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hm : ((i : ℤ) - t, (j : ℤ) - t) ∈ L <;> simp [pic, hm]
  rw [hs]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
  rw [sum_mem t L hn hb]
  push_cast
  ring

theorem inR_mono {R S : ℕ} {L : List P} (h : inR R L) (hRS : R ≤ S) : inR S L := by
  intro p hp
  have := h p hp
  omega
def L0 : List P := [(0, 0)]
def L1 : List P := [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)]
def L2 : List P := [(-1, 0), (0, -1), (0, 0), (0, 1), (1, 0)]
def L3 : List P := [(-2, 0), (-1, -1), (-1, 1), (0, -2), (0, 0), (0, 2), (1, -1), (1, 1), (2, 0)]
def L4 : List P := []
def L5 : List P := []

theorem lay0 : cell 73 0 = pic false L0 := cell_zero 73

theorem lay1 : cell 73 1 = pic true L1 := by
  rw [cell_succ, lay0]
  exact step (R := 2) (by decide) (by decide) (by decide) (by decide)

theorem lay2 : cell 73 2 = pic false L2 := by
  rw [cell_succ, lay1]
  exact step (R := 2) (by decide) (by decide) (by decide) (by decide)

theorem lay3 : cell 73 3 = pic true L3 := by
  rw [cell_succ, lay2]
  exact step (R := 2) (by decide) (by decide) (by decide) (by decide)

theorem lay4 : cell 73 4 = pic false L4 := by
  rw [cell_succ, lay3]
  exact step (R := 2) (by decide) (by decide) (by decide) (by decide)

theorem lay5 : cell 73 5 = pic true L5 := by
  rw [cell_succ, lay4]
  exact step (R := 2) (by decide) (by decide) (by decide) (by decide)

theorem back : nxt 73 (pic true L5) = pic false L4 :=
  step (R := 2) (by decide) (by decide) (by decide) (by decide)

theorem fwd : nxt 73 (pic false L4) = pic true L5 :=
  step (R := 2) (by decide) (by decide) (by decide) (by decide)

theorem per (k : ℕ) : cell 73 (4 + 2 * k) = pic false L4 ∧
    cell 73 (4 + 2 * k + 1) = pic true L5 := by
  induction k with
  | zero => exact ⟨lay4, lay5⟩
  | succ k ih =>
    have h0 : cell 73 (4 + 2 * (k + 1)) = pic false L4 := by
      rw [show 4 + 2 * (k + 1) = (4 + 2 * k + 1) + 1 by ring, cell_succ, ih.2]
      exact back
    refine ⟨h0, ?_⟩
    rw [cell_succ, h0]
    exact fwd

theorem cE (m : ℕ) (hm : 2 ≤ m) :
    (onCount 73 (2 * m) : ℚ) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 + k := ⟨m - 2, by omega⟩
  have h := (per k).1
  rw [show 4 + 2 * k = 2 * (2 + k) by ring] at h
  have := count_false 73 _ L4 (by decide) (inR_mono (R := 2) (by decide) (by omega)) h
  have h2 : ((onCount 73 (2 * (2 + k)) : ℤ) : ℚ) = 0 := by
    rw [this]
    simp [L4]
    try ring
  exact_mod_cast h2

theorem cO (m : ℕ) (hm : 2 ≤ m) :
    (onCount 73 (2 * m + 1) : ℚ) = (2 * (2 * (m : ℚ) + 1) + 1) ^ 2 - 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 + k := ⟨m - 2, by omega⟩
  have h := (per k).2
  rw [show 4 + 2 * k + 1 = 2 * (2 + k) + 1 by ring] at h
  have := count_true 73 _ L5 (by decide) (inR_mono (R := 2) (by decide) (by omega)) h
  have h2 : ((onCount 73 (2 * (2 + k) + 1) : ℤ) : ℚ) = (2 * (2 * ((2 + k : ℕ) : ℚ) + 1) + 1) ^ 2 - 0 := by
    rw [this]
    simp [L5]
    try ring
  exact_mod_cast h2

theorem cV0 : (onCount 73 0 : ℚ) = 1 := by
  have := count_false 73 0 L0 (by decide) (by decide) lay0
  have h2 : ((onCount 73 0 : ℤ) : ℚ) = 1 := by
    rw [this]
    norm_num [L0]
  exact_mod_cast h2

theorem cV1 : (onCount 73 1 : ℚ) = 4 := by
  have := count_true 73 1 L1 (by decide) (by decide) lay1
  have h2 : ((onCount 73 1 : ℤ) : ℚ) = 4 := by
    rw [this]
    norm_num [L1]
  exact_mod_cast h2

theorem cV2 : (onCount 73 2 : ℚ) = 5 := by
  have := count_false 73 2 L2 (by decide) (by decide) lay2
  have h2 : ((onCount 73 2 : ℤ) : ℚ) = 5 := by
    rw [this]
    norm_num [L2]
  exact_mod_cast h2

theorem cV3 : (onCount 73 3 : ℚ) = 40 := by
  have := count_true 73 3 L3 (by decide) (by decide) lay3
  have h2 : ((onCount 73 3 : ℤ) : ℚ) = 40 := by
    rw [this]
    norm_num [L3]
  exact_mod_cast h2

theorem cV4 : (onCount 73 4 : ℚ) = 0 := by
  have := count_false 73 4 L4 (by decide) (by decide) lay4
  have h2 : ((onCount 73 4 : ℤ) : ℚ) = 0 := by
    rw [this]
    norm_num [L4]
  exact_mod_cast h2

theorem cV5 : (onCount 73 5 : ℚ) = 121 := by
  have := count_true 73 5 L5 (by decide) (by decide) lay5
  have h2 : ((onCount 73 5 : ℤ) : ℚ) = 121 := by
    rw [this]
    norm_num [L5]
  exact_mod_cast h2

theorem cV6 : (onCount 73 6 : ℚ) = 0 := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num, cE 3 (by norm_num)]
  try norm_num

theorem cV7 : (onCount 73 7 : ℚ) = 225 := by
  rw [show (7 : ℕ) = 2 * 3 + 1 by norm_num, cO 3 (by norm_num)]
  try norm_num

theorem cV8 : (onCount 73 8 : ℚ) = 0 := by
  rw [show (8 : ℕ) = 2 * 4 by norm_num, cE 4 (by norm_num)]
  try norm_num

theorem cV9 : (onCount 73 9 : ℚ) = 361 := by
  rw [show (9 : ℕ) = 2 * 4 + 1 by norm_num, cO 4 (by norm_num)]
  try norm_num

theorem cV10 : (onCount 73 10 : ℚ) = 0 := by
  rw [show (10 : ℕ) = 2 * 5 by norm_num, cE 5 (by norm_num)]
  try norm_num

theorem cV11 : (onCount 73 11 : ℚ) = 529 := by
  rw [show (11 : ℕ) = 2 * 5 + 1 by norm_num, cO 5 (by norm_num)]
  try norm_num

theorem cV12 : (onCount 73 12 : ℚ) = 0 := by
  rw [show (12 : ℕ) = 2 * 6 by norm_num, cE 6 (by norm_num)]
  try norm_num

theorem cV13 : (onCount 73 13 : ℚ) = 729 := by
  rw [show (13 : ℕ) = 2 * 6 + 1 by norm_num, cO 6 (by norm_num)]
  try norm_num

theorem cV14 : (onCount 73 14 : ℚ) = 0 := by
  rw [show (14 : ℕ) = 2 * 7 by norm_num, cE 7 (by norm_num)]
  try norm_num

theorem cV15 : (onCount 73 15 : ℚ) = 961 := by
  rw [show (15 : ℕ) = 2 * 7 + 1 by norm_num, cO 7 (by norm_num)]
  try norm_num

theorem cV16 : (onCount 73 16 : ℚ) = 0 := by
  rw [show (16 : ℕ) = 2 * 8 by norm_num, cE 8 (by norm_num)]
  try norm_num

theorem cV17 : (onCount 73 17 : ℚ) = 1225 := by
  rw [show (17 : ℕ) = 2 * 8 + 1 by norm_num, cO 8 (by norm_num)]
  try norm_num

theorem cV18 : (onCount 73 18 : ℚ) = 0 := by
  rw [show (18 : ℕ) = 2 * 9 by norm_num, cE 9 (by norm_num)]
  try norm_num

theorem cV19 : (onCount 73 19 : ℚ) = 1521 := by
  rw [show (19 : ℕ) = 2 * 9 + 1 by norm_num, cO 9 (by norm_num)]
  try norm_num

theorem cV20 : (onCount 73 20 : ℚ) = 0 := by
  rw [show (20 : ℕ) = 2 * 10 by norm_num, cE 10 (by norm_num)]
  try norm_num

theorem cV21 : (onCount 73 21 : ℚ) = 1849 := by
  rw [show (21 : ℕ) = 2 * 10 + 1 by norm_num, cO 10 (by norm_num)]
  try norm_num

theorem cV22 : (onCount 73 22 : ℚ) = 0 := by
  rw [show (22 : ℕ) = 2 * 11 by norm_num, cE 11 (by norm_num)]
  try norm_num

theorem cV23 : (onCount 73 23 : ℚ) = 2209 := by
  rw [show (23 : ℕ) = 2 * 11 + 1 by norm_num, cO 11 (by norm_num)]
  try norm_num

theorem cV24 : (onCount 73 24 : ℚ) = 0 := by
  rw [show (24 : ℕ) = 2 * 12 by norm_num, cE 12 (by norm_num)]
  try norm_num

theorem cV25 : (onCount 73 25 : ℚ) = 2601 := by
  rw [show (25 : ℕ) = 2 * 12 + 1 by norm_num, cO 12 (by norm_num)]
  try norm_num

def G (n : ℕ) : ℚ := (((-29 : ℚ) / 4) * (n : ℚ) ^ 0 + ((11 : ℚ) / 6) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 2 + ((2 : ℚ) / 3) * (n : ℚ) ^ 3) + (-1 : ℚ) ^ n * (((-3 : ℚ) / 4) * (n : ℚ) ^ 0 + (-2 : ℚ) * (n : ℚ) ^ 1 + (-1 : ℚ) * (n : ℚ) ^ 2)

theorem a_succ (n : ℕ) : (a (n + 1) : ℚ) = a n + (onCount 73 (n + 1) : ℚ) := by
  simp only [a]
  rw [Finset.sum_range_succ]
  push_cast
  ring

theorem aV0 : (a 0 : ℚ) = 1 := by
  simp only [a, Finset.sum_range_one]
  exact cV0

theorem aV1 : (a 1 : ℚ) = 5 := by
  rw [a_succ, aV0, cV1]
  norm_num

theorem aV2 : (a 2 : ℚ) = 10 := by
  rw [a_succ, aV1, cV2]
  norm_num

theorem aV3 : (a 3 : ℚ) = 50 := by
  rw [a_succ, aV2, cV3]
  norm_num

theorem aV4 : (a 4 : ℚ) = 50 := by
  rw [a_succ, aV3, cV4]
  norm_num

theorem aV5 : (a 5 : ℚ) = 171 := by
  rw [a_succ, aV4, cV5]
  norm_num

theorem aV6 : (a 6 : ℚ) = 171 := by
  rw [a_succ, aV5, cV6]
  norm_num

theorem aV7 : (a 7 : ℚ) = 396 := by
  rw [a_succ, aV6, cV7]
  norm_num

theorem aV8 : (a 8 : ℚ) = 396 := by
  rw [a_succ, aV7, cV8]
  norm_num

theorem aV9 : (a 9 : ℚ) = 757 := by
  rw [a_succ, aV8, cV9]
  norm_num

theorem aV10 : (a 10 : ℚ) = 757 := by
  rw [a_succ, aV9, cV10]
  norm_num

theorem aV11 : (a 11 : ℚ) = 1286 := by
  rw [a_succ, aV10, cV11]
  norm_num

theorem aV12 : (a 12 : ℚ) = 1286 := by
  rw [a_succ, aV11, cV12]
  norm_num

theorem aV13 : (a 13 : ℚ) = 2015 := by
  rw [a_succ, aV12, cV13]
  norm_num

theorem aV14 : (a 14 : ℚ) = 2015 := by
  rw [a_succ, aV13, cV14]
  norm_num

theorem aV15 : (a 15 : ℚ) = 2976 := by
  rw [a_succ, aV14, cV15]
  norm_num

theorem aV16 : (a 16 : ℚ) = 2976 := by
  rw [a_succ, aV15, cV16]
  norm_num

theorem aV17 : (a 17 : ℚ) = 4201 := by
  rw [a_succ, aV16, cV17]
  norm_num

theorem aV18 : (a 18 : ℚ) = 4201 := by
  rw [a_succ, aV17, cV18]
  norm_num

theorem aV19 : (a 19 : ℚ) = 5722 := by
  rw [a_succ, aV18, cV19]
  norm_num

theorem aV20 : (a 20 : ℚ) = 5722 := by
  rw [a_succ, aV19, cV20]
  norm_num

theorem aV21 : (a 21 : ℚ) = 7571 := by
  rw [a_succ, aV20, cV21]
  norm_num

theorem aV22 : (a 22 : ℚ) = 7571 := by
  rw [a_succ, aV21, cV22]
  norm_num

theorem aV23 : (a 23 : ℚ) = 9780 := by
  rw [a_succ, aV22, cV23]
  norm_num

theorem aG (n : ℕ) (hn : 4 ≤ n) : (a n : ℚ) = G n := by
  induction n, hn using Nat.le_induction with
  | base => rw [aV4]; norm_num [G]
  | succ n hn ih =>
    rw [a_succ, ih]
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · have h := cO m (by omega)
      have h1 : (-1 : ℚ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
      have h2 : (-1 : ℚ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
      rw [h]
      simp only [G, h1, h2]
      push_cast
      ring
    · have h := cE (m + 1) (by omega)
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring] at h
      have h1 : (-1 : ℚ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
      have h2 : (-1 : ℚ) ^ (2 * m + 1 + 1) = 1 := by rw [pow_succ, pow_succ, pow_mul]; norm_num
      rw [h]
      simp only [G, h1, h2]
      push_cast
      ring

end OMA.CA_a270089

open OMA.CA_a270089 OMA.S_oeis_a270089 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a270089.main := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n hn0
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n
      all_goals first
        | (norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11, aV12, aV13, aV14, aV15, aV16, aV17, aV18, aV19, aV20, aV21, aV22, aV23]; done)
        | (exfalso; revert hp; decide)
    · rw [aG n h]
      simp only [G]
      push_cast
      ring
  · intro n hn0 hp
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n
      all_goals first
        | (norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11, aV12, aV13, aV14, aV15, aV16, aV17, aV18, aV19, aV20, aV21, aV22, aV23]; done)
        | (exfalso; revert hp; decide)
    · rw [aG n h]
      simp only [G]
      rw [Even.neg_one_pow hp]
      push_cast
      ring
  · intro n hn0 hp
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n
      all_goals first
        | (norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11, aV12, aV13, aV14, aV15, aV16, aV17, aV18, aV19, aV20, aV21, aV22, aV23]; done)
        | (exfalso; revert hp; decide)
    · rw [aG n h]
      simp only [G]
      rw [Odd.neg_one_pow hp]
      push_cast
      ring
  · intro n hn0
    rcases Nat.lt_or_ge n 11 with h | h
    · interval_cases n <;> norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11, aV12, aV13, aV14, aV15, aV16, aV17, aV18, aV19, aV20, aV21, aV22, aV23]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 11 := ⟨n - 11, by omega⟩
      rw [show k + 11 - 1 = k + 10 by omega]
      rw [show k + 11 - 2 = k + 9 by omega]
      rw [show k + 11 - 3 = k + 8 by omega]
      rw [show k + 11 - 4 = k + 7 by omega]
      rw [show k + 11 - 5 = k + 6 by omega]
      rw [show k + 11 - 6 = k + 5 by omega]
      rw [show k + 11 - 7 = k + 4 by omega]
      rw [aG (k + 11) (by omega), aG (k + 10) (by omega), aG (k + 9) (by omega), aG (k + 8) (by omega), aG (k + 7) (by omega), aG (k + 6) (by omega), aG (k + 5) (by omega), aG (k + 4) (by omega)]
      simp only [G]
      push_cast
      ring
  · have hL : mk (fun n => (a n : ℚ)) * ((1 - X) ^ 4 * (1 + X) ^ 3 : PowerSeries ℚ) = mk (fun n => (a n : ℚ)) - X ^ 1 * mk (fun n => (a n : ℚ)) - C 3 * (X ^ 2 * mk (fun n => (a n : ℚ))) + C 3 * (X ^ 3 * mk (fun n => (a n : ℚ))) + C 3 * (X ^ 4 * mk (fun n => (a n : ℚ))) - C 3 * (X ^ 5 * mk (fun n => (a n : ℚ))) - X ^ 6 * mk (fun n => (a n : ℚ)) + X ^ 7 * mk (fun n => (a n : ℚ)) := by
      try simp only [map_ofNat]
      ring
    have hR : (1 + 4 * X + 2 * X ^ 2 + 28 * X ^ 3 - 12 * X ^ 4 + 13 * X ^ 5 + 14 * X ^ 6 - 22 * X ^ 7 - 5 * X ^ 8 + 9 * X ^ 9 : PowerSeries ℚ) = 1 + C 4 * X ^ 1 + C 2 * X ^ 2 + C 28 * X ^ 3 - C 12 * X ^ 4 + C 13 * X ^ 5 + C 14 * X ^ 6 - C 22 * X ^ 7 - C 5 * X ^ 8 + C 9 * X ^ 9 := by
      try simp only [map_ofNat]
      ring
    rw [hL, hR]
    ext k
    simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow, coeff_one, coeff_C]
    rcases Nat.lt_or_ge k 22 with h | h
    · interval_cases k <;> norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11, aV12, aV13, aV14, aV15, aV16, aV17, aV18, aV19, aV20, aV21, aV22, aV23]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 22 := ⟨k - 22, by omega⟩
      rw [if_pos (show 1 ≤ j + 22 by omega)]
      rw [if_pos (show 2 ≤ j + 22 by omega)]
      rw [if_pos (show 3 ≤ j + 22 by omega)]
      rw [if_pos (show 4 ≤ j + 22 by omega)]
      rw [if_pos (show 5 ≤ j + 22 by omega)]
      rw [if_pos (show 6 ≤ j + 22 by omega)]
      rw [if_pos (show 7 ≤ j + 22 by omega)]
      rw [if_neg (show j + 22 ≠ 0 by omega)]
      rw [if_neg (show j + 22 ≠ 1 by omega)]
      rw [if_neg (show j + 22 ≠ 2 by omega)]
      rw [if_neg (show j + 22 ≠ 3 by omega)]
      rw [if_neg (show j + 22 ≠ 4 by omega)]
      rw [if_neg (show j + 22 ≠ 5 by omega)]
      rw [if_neg (show j + 22 ≠ 6 by omega)]
      rw [if_neg (show j + 22 ≠ 7 by omega)]
      rw [if_neg (show j + 22 ≠ 8 by omega)]
      rw [if_neg (show j + 22 ≠ 9 by omega)]
      rw [show j + 22 - 1 = j + 21 by omega]
      rw [show j + 22 - 2 = j + 20 by omega]
      rw [show j + 22 - 3 = j + 19 by omega]
      rw [show j + 22 - 4 = j + 18 by omega]
      rw [show j + 22 - 5 = j + 17 by omega]
      rw [show j + 22 - 6 = j + 16 by omega]
      rw [show j + 22 - 7 = j + 15 by omega]
      rw [aG (j + 22) (by omega), aG (j + 21) (by omega), aG (j + 20) (by omega), aG (j + 19) (by omega), aG (j + 18) (by omega), aG (j + 17) (by omega), aG (j + 16) (by omega), aG (j + 15) (by omega)]
      simp only [G]
      push_cast
      ring
