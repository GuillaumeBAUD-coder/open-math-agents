import OMAStatements.S_oeis_a270006
import Mathlib
/-!
Proof of the conjectures of the statement oeis-a270006 (OEIS A270006), Rule 5.

Method: from stage 2 on, the automaton is a uniform background (blinking or not) with a fixed
finite list of exceptional cells, alternating between two phases. Each phase step is checked by
a finite kernel computation on a box around the exceptions (everything farther away sees only
background), the count of ON cells follows from the length of the exception list, and every
conjecture then reduces to a polynomial identity in n and (-1)^n (or 2^n and 4^n).
The exception-list technique follows the merged proof of oeis-a273848 in this repository.
-/

namespace OMA.CA_a270006

open OMA.S_oeis_a270006 PowerSeries

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
def L1 : List P := [(0, 0)]
def L2 : List P := []
def L3 : List P := []

theorem lay0 : cell 5 0 = pic false L0 := cell_zero 5

theorem lay1 : cell 5 1 = pic true L1 := by
  rw [cell_succ, lay0]
  exact step (R := 0) (by decide) (by decide) (by decide) (by decide)

theorem lay2 : cell 5 2 = pic false L2 := by
  rw [cell_succ, lay1]
  exact step (R := 0) (by decide) (by decide) (by decide) (by decide)

theorem lay3 : cell 5 3 = pic true L3 := by
  rw [cell_succ, lay2]
  exact step (R := 0) (by decide) (by decide) (by decide) (by decide)

theorem back : nxt 5 (pic true L3) = pic false L2 :=
  step (R := 0) (by decide) (by decide) (by decide) (by decide)

theorem fwd : nxt 5 (pic false L2) = pic true L3 :=
  step (R := 0) (by decide) (by decide) (by decide) (by decide)

theorem per (k : ℕ) : cell 5 (2 + 2 * k) = pic false L2 ∧
    cell 5 (2 + 2 * k + 1) = pic true L3 := by
  induction k with
  | zero => exact ⟨lay2, lay3⟩
  | succ k ih =>
    have h0 : cell 5 (2 + 2 * (k + 1)) = pic false L2 := by
      rw [show 2 + 2 * (k + 1) = (2 + 2 * k + 1) + 1 by ring, cell_succ, ih.2]
      exact back
    refine ⟨h0, ?_⟩
    rw [cell_succ, h0]
    exact fwd

theorem cE (m : ℕ) (hm : 1 ≤ m) :
    (onCount 5 (2 * m) : ℚ) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 1 + k := ⟨m - 1, by omega⟩
  have h := (per k).1
  rw [show 2 + 2 * k = 2 * (1 + k) by ring] at h
  have := count_false 5 _ L2 (by decide) (inR_mono (R := 0) (by decide) (by omega)) h
  have h2 : ((onCount 5 (2 * (1 + k)) : ℤ) : ℚ) = 0 := by
    rw [this]
    simp [L2]
    try ring
  exact_mod_cast h2

theorem cO (m : ℕ) (hm : 1 ≤ m) :
    (onCount 5 (2 * m + 1) : ℚ) = (2 * (2 * (m : ℚ) + 1) + 1) ^ 2 - 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 1 + k := ⟨m - 1, by omega⟩
  have h := (per k).2
  rw [show 2 + 2 * k + 1 = 2 * (1 + k) + 1 by ring] at h
  have := count_true 5 _ L3 (by decide) (inR_mono (R := 0) (by decide) (by omega)) h
  have h2 : ((onCount 5 (2 * (1 + k) + 1) : ℤ) : ℚ) = (2 * (2 * ((1 + k : ℕ) : ℚ) + 1) + 1) ^ 2 - 0 := by
    rw [this]
    simp [L3]
    try ring
  exact_mod_cast h2

theorem cV0 : (onCount 5 0 : ℚ) = 1 := by
  have := count_false 5 0 L0 (by decide) (by decide) lay0
  have h2 : ((onCount 5 0 : ℤ) : ℚ) = 1 := by
    rw [this]
    norm_num [L0]
  exact_mod_cast h2

theorem cV1 : (onCount 5 1 : ℚ) = 8 := by
  have := count_true 5 1 L1 (by decide) (by decide) lay1
  have h2 : ((onCount 5 1 : ℤ) : ℚ) = 8 := by
    rw [this]
    norm_num [L1]
  exact_mod_cast h2

theorem cV2 : (onCount 5 2 : ℚ) = 0 := by
  have := count_false 5 2 L2 (by decide) (by decide) lay2
  have h2 : ((onCount 5 2 : ℤ) : ℚ) = 0 := by
    rw [this]
    norm_num [L2]
  exact_mod_cast h2

theorem cV3 : (onCount 5 3 : ℚ) = 49 := by
  have := count_true 5 3 L3 (by decide) (by decide) lay3
  have h2 : ((onCount 5 3 : ℤ) : ℚ) = 49 := by
    rw [this]
    norm_num [L3]
  exact_mod_cast h2

theorem cV4 : (onCount 5 4 : ℚ) = 0 := by
  rw [show (4 : ℕ) = 2 * 2 by norm_num, cE 2 (by norm_num)]
  try norm_num

theorem cV5 : (onCount 5 5 : ℚ) = 121 := by
  rw [show (5 : ℕ) = 2 * 2 + 1 by norm_num, cO 2 (by norm_num)]
  try norm_num

theorem cV6 : (onCount 5 6 : ℚ) = 0 := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num, cE 3 (by norm_num)]
  try norm_num

theorem cV7 : (onCount 5 7 : ℚ) = 225 := by
  rw [show (7 : ℕ) = 2 * 3 + 1 by norm_num, cO 3 (by norm_num)]
  try norm_num

theorem cV8 : (onCount 5 8 : ℚ) = 0 := by
  rw [show (8 : ℕ) = 2 * 4 by norm_num, cE 4 (by norm_num)]
  try norm_num

theorem cV9 : (onCount 5 9 : ℚ) = 361 := by
  rw [show (9 : ℕ) = 2 * 4 + 1 by norm_num, cO 4 (by norm_num)]
  try norm_num

theorem cV10 : (onCount 5 10 : ℚ) = 0 := by
  rw [show (10 : ℕ) = 2 * 5 by norm_num, cE 5 (by norm_num)]
  try norm_num

theorem cV11 : (onCount 5 11 : ℚ) = 529 := by
  rw [show (11 : ℕ) = 2 * 5 + 1 by norm_num, cO 5 (by norm_num)]
  try norm_num

theorem cV12 : (onCount 5 12 : ℚ) = 0 := by
  rw [show (12 : ℕ) = 2 * 6 by norm_num, cE 6 (by norm_num)]
  try norm_num

theorem cV13 : (onCount 5 13 : ℚ) = 729 := by
  rw [show (13 : ℕ) = 2 * 6 + 1 by norm_num, cO 6 (by norm_num)]
  try norm_num

theorem cV14 : (onCount 5 14 : ℚ) = 0 := by
  rw [show (14 : ℕ) = 2 * 7 by norm_num, cE 7 (by norm_num)]
  try norm_num

theorem cV15 : (onCount 5 15 : ℚ) = 961 := by
  rw [show (15 : ℕ) = 2 * 7 + 1 by norm_num, cO 7 (by norm_num)]
  try norm_num

theorem cV16 : (onCount 5 16 : ℚ) = 0 := by
  rw [show (16 : ℕ) = 2 * 8 by norm_num, cE 8 (by norm_num)]
  try norm_num

theorem cV17 : (onCount 5 17 : ℚ) = 1225 := by
  rw [show (17 : ℕ) = 2 * 8 + 1 by norm_num, cO 8 (by norm_num)]
  try norm_num

theorem cV18 : (onCount 5 18 : ℚ) = 0 := by
  rw [show (18 : ℕ) = 2 * 9 by norm_num, cE 9 (by norm_num)]
  try norm_num

theorem cV19 : (onCount 5 19 : ℚ) = 1521 := by
  rw [show (19 : ℕ) = 2 * 9 + 1 by norm_num, cO 9 (by norm_num)]
  try norm_num

theorem cV20 : (onCount 5 20 : ℚ) = 0 := by
  rw [show (20 : ℕ) = 2 * 10 by norm_num, cE 10 (by norm_num)]
  try norm_num

def G (n : ℕ) : ℚ := (((1 : ℚ) / 2) * (n : ℚ) ^ 0 + (2 : ℚ) * (n : ℚ) ^ 1 + (2 : ℚ) * (n : ℚ) ^ 2) + (-1 : ℚ) ^ n * (((-1 : ℚ) / 2) * (n : ℚ) ^ 0 + (-2 : ℚ) * (n : ℚ) ^ 1 + (-2 : ℚ) * (n : ℚ) ^ 2)

theorem aG (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = G n := by
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · have h := cE m (by omega)
    have h1 : (-1 : ℚ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
    simp only [a, G, h1]
    push_cast
    rw [h]
    ring
  · have h := cO m (by omega)
    have h1 : (-1 : ℚ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    simp only [a, G, h1]
    push_cast
    rw [h]
    ring

theorem aV0 : (a 0 : ℚ) = 1 := by
  simp only [a]
  exact_mod_cast cV0

theorem aV1 : (a 1 : ℚ) = 8 := by
  simp only [a]
  exact_mod_cast cV1

theorem aV2 : (a 2 : ℚ) = 0 := by
  simp only [a]
  exact_mod_cast cV2

theorem aV3 : (a 3 : ℚ) = 49 := by
  simp only [a]
  exact_mod_cast cV3

theorem aV4 : (a 4 : ℚ) = 0 := by
  simp only [a]
  exact_mod_cast cV4

theorem aV5 : (a 5 : ℚ) = 121 := by
  rw [aG 5 (by norm_num)]
  norm_num [G]

theorem aV6 : (a 6 : ℚ) = 0 := by
  rw [aG 6 (by norm_num)]
  norm_num [G]

theorem aV7 : (a 7 : ℚ) = 225 := by
  rw [aG 7 (by norm_num)]
  norm_num [G]

theorem aV8 : (a 8 : ℚ) = 0 := by
  rw [aG 8 (by norm_num)]
  norm_num [G]

theorem aV9 : (a 9 : ℚ) = 361 := by
  rw [aG 9 (by norm_num)]
  norm_num [G]

theorem aV10 : (a 10 : ℚ) = 0 := by
  rw [aG 10 (by norm_num)]
  norm_num [G]

theorem aV11 : (a 11 : ℚ) = 529 := by
  rw [aG 11 (by norm_num)]
  norm_num [G]

theorem aV12 : (a 12 : ℚ) = 0 := by
  rw [aG 12 (by norm_num)]
  norm_num [G]

theorem aV13 : (a 13 : ℚ) = 729 := by
  rw [aG 13 (by norm_num)]
  norm_num [G]

theorem aV14 : (a 14 : ℚ) = 0 := by
  rw [aG 14 (by norm_num)]
  norm_num [G]

theorem aV15 : (a 15 : ℚ) = 961 := by
  rw [aG 15 (by norm_num)]
  norm_num [G]

theorem aV16 : (a 16 : ℚ) = 0 := by
  rw [aG 16 (by norm_num)]
  norm_num [G]

theorem aV17 : (a 17 : ℚ) = 1225 := by
  rw [aG 17 (by norm_num)]
  norm_num [G]

theorem aV18 : (a 18 : ℚ) = 0 := by
  rw [aG 18 (by norm_num)]
  norm_num [G]

end OMA.CA_a270006

open OMA.CA_a270006 OMA.S_oeis_a270006 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a270006.main := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n hn0
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      all_goals first
        | (norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11, aV12, aV13, aV14, aV15, aV16, aV17, aV18]; done)
        | (exfalso; revert hp; decide)
    · rw [aG n h]
      simp only [G]
      push_cast
      ring
  · intro n hn0 hp
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      all_goals first
        | (norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11, aV12, aV13, aV14, aV15, aV16, aV17, aV18]; done)
        | (exfalso; revert hp; decide)
    · rw [aG n h]
      simp only [G]
      rw [Even.neg_one_pow hp]
      push_cast
      ring
  · intro n hn0 hp
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n
      all_goals first
        | (norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11, aV12, aV13, aV14, aV15, aV16, aV17, aV18]; done)
        | (exfalso; revert hp; decide)
    · rw [aG n h]
      simp only [G]
      rw [Odd.neg_one_pow hp]
      push_cast
      ring
  · intro n hn0
    rcases Nat.lt_or_ge n 8 with h | h
    · interval_cases n <;> norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11, aV12, aV13, aV14, aV15, aV16, aV17, aV18]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
      rw [show k + 8 - 2 = k + 6 by omega]
      rw [show k + 8 - 4 = k + 4 by omega]
      rw [show k + 8 - 6 = k + 2 by omega]
      rw [aG (k + 8) (by omega), aG (k + 6) (by omega), aG (k + 4) (by omega), aG (k + 2) (by omega)]
      simp only [G]
      push_cast
      ring
  · have hL : mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3 * (1 + X) ^ 3 : PowerSeries ℚ) = mk (fun n => (a n : ℚ)) - C 3 * (X ^ 2 * mk (fun n => (a n : ℚ))) + C 3 * (X ^ 4 * mk (fun n => (a n : ℚ))) - X ^ 6 * mk (fun n => (a n : ℚ)) := by
      try simp only [map_ofNat]
      ring
    have hR : (1 + 8 * X - 3 * X ^ 2 + 25 * X ^ 3 + 3 * X ^ 4 - 2 * X ^ 5 - X ^ 6 + X ^ 7 : PowerSeries ℚ) = 1 + C 8 * X ^ 1 - C 3 * X ^ 2 + C 25 * X ^ 3 + C 3 * X ^ 4 - C 2 * X ^ 5 - X ^ 6 + X ^ 7 := by
      try simp only [map_ofNat]
      ring
    rw [hL, hR]
    ext k
    simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow, coeff_one, coeff_C]
    rcases Nat.lt_or_ge k 17 with h | h
    · interval_cases k <;> norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11, aV12, aV13, aV14, aV15, aV16, aV17, aV18]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 17 := ⟨k - 17, by omega⟩
      rw [if_pos (show 2 ≤ j + 17 by omega)]
      rw [if_pos (show 4 ≤ j + 17 by omega)]
      rw [if_pos (show 6 ≤ j + 17 by omega)]
      rw [if_neg (show j + 17 ≠ 0 by omega)]
      rw [if_neg (show j + 17 ≠ 1 by omega)]
      rw [if_neg (show j + 17 ≠ 2 by omega)]
      rw [if_neg (show j + 17 ≠ 3 by omega)]
      rw [if_neg (show j + 17 ≠ 4 by omega)]
      rw [if_neg (show j + 17 ≠ 5 by omega)]
      rw [if_neg (show j + 17 ≠ 6 by omega)]
      rw [if_neg (show j + 17 ≠ 7 by omega)]
      rw [show j + 17 - 2 = j + 15 by omega]
      rw [show j + 17 - 4 = j + 13 by omega]
      rw [show j + 17 - 6 = j + 11 by omega]
      rw [aG (j + 17) (by omega), aG (j + 15) (by omega), aG (j + 13) (by omega), aG (j + 11) (by omega)]
      simp only [G]
      push_cast
      ring
