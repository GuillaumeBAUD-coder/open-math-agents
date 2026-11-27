import OMAStatements.S_oeis_a266450
import Mathlib

namespace A266450aux

open OMA.S_oeis_a266450 in
lemma row_succ (n : ℕ) (i : ℤ) :
    row 25 (n + 1) i = rule 25 (row 25 n (i - 1)) (row 25 n i) (row 25 n (i + 1)) := rfl

open OMA.S_oeis_a266450 in
lemma next (s t : ℤ → Bool) (n : ℕ) (hs : row 25 n = s)
    (h : ∀ i, rule 25 (s (i - 1)) (s i) (s (i + 1)) = t i) : row 25 (n + 1) = t := by
  funext i
  rw [row_succ, hs]
  exact h i

open OMA.S_oeis_a266450 in
/-- Row 1: OFF exactly at -1 and 0. -/
def R1 : ℤ → Bool := fun i => decide (i < -1 ∨ 0 < i)

open OMA.S_oeis_a266450 in
/-- Row 2: ON exactly at -1 and 1. -/
def R2 : ℤ → Bool := fun i => decide (i = -1 ∨ i = 1)

open OMA.S_oeis_a266450 in
/-- Row 3: OFF exactly at -2, ..., 1. -/
def R3 : ℤ → Bool := fun i => decide (i < -2 ∨ 1 < i)

open OMA.S_oeis_a266450 in
/-- Even rows 2j with j at least 2: ON exactly at j-4, j-3, j-2 and j. -/
def E (j : ℤ) : ℤ → Bool := fun i => decide ((j - 4 ≤ i ∧ i ≤ j - 2) ∨ i = j)

open OMA.S_oeis_a266450 in
/-- Odd rows 2j+1 with j at least 2: OFF exactly at j-5 and j-3, ..., j. -/
def O (j : ℤ) : ℤ → Bool := fun i => decide (¬ (i = j - 5 ∨ (j - 3 ≤ i ∧ i ≤ j)))

open OMA.S_oeis_a266450 in
lemma tr0 : ∀ i : ℤ, rule 25 (decide (i - 1 = 0)) (decide (i = 0)) (decide (i + 1 = 0))
    = R1 i := by
  intro i
  show rule 25 (decide (i - 1 = 0)) (decide (i = 0)) (decide (i + 1 = 0))
    = decide (i < -1 ∨ 0 < i)
  cases hb1 : decide (i - 1 = 0) <;> cases hb2 : decide (i = 0) <;>
    cases hb3 : decide (i + 1 = 0) <;> cases hb4 : decide (i < -1 ∨ 0 < i) <;>
    first
      | decide
      | (exfalso
         simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hb1 hb2 hb3 hb4
         omega)

open OMA.S_oeis_a266450 in
lemma tr1 : ∀ i : ℤ, rule 25 (R1 (i - 1)) (R1 i) (R1 (i + 1)) = R2 i := by
  intro i
  show rule 25 (decide (i - 1 < -1 ∨ 0 < i - 1)) (decide (i < -1 ∨ 0 < i))
    (decide (i + 1 < -1 ∨ 0 < i + 1)) = decide (i = -1 ∨ i = 1)
  cases hb1 : decide (i - 1 < -1 ∨ 0 < i - 1) <;> cases hb2 : decide (i < -1 ∨ 0 < i) <;>
    cases hb3 : decide (i + 1 < -1 ∨ 0 < i + 1) <;> cases hb4 : decide (i = -1 ∨ i = 1) <;>
    first
      | decide
      | (exfalso
         simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hb1 hb2 hb3 hb4
         omega)

open OMA.S_oeis_a266450 in
lemma tr2 : ∀ i : ℤ, rule 25 (R2 (i - 1)) (R2 i) (R2 (i + 1)) = R3 i := by
  intro i
  show rule 25 (decide (i - 1 = -1 ∨ i - 1 = 1)) (decide (i = -1 ∨ i = 1))
    (decide (i + 1 = -1 ∨ i + 1 = 1)) = decide (i < -2 ∨ 1 < i)
  cases hb1 : decide (i - 1 = -1 ∨ i - 1 = 1) <;> cases hb2 : decide (i = -1 ∨ i = 1) <;>
    cases hb3 : decide (i + 1 = -1 ∨ i + 1 = 1) <;> cases hb4 : decide (i < -2 ∨ 1 < i) <;>
    first
      | decide
      | (exfalso
         simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hb1 hb2 hb3 hb4
         omega)

open OMA.S_oeis_a266450 in
lemma tr3 : ∀ i : ℤ, rule 25 (R3 (i - 1)) (R3 i) (R3 (i + 1)) = E 2 i := by
  intro i
  show rule 25 (decide (i - 1 < -2 ∨ 1 < i - 1)) (decide (i < -2 ∨ 1 < i))
    (decide (i + 1 < -2 ∨ 1 < i + 1)) = decide (((2 : ℤ) - 4 ≤ i ∧ i ≤ 2 - 2) ∨ i = 2)
  cases hb1 : decide (i - 1 < -2 ∨ 1 < i - 1) <;> cases hb2 : decide (i < -2 ∨ 1 < i) <;>
    cases hb3 : decide (i + 1 < -2 ∨ 1 < i + 1) <;>
    cases hb4 : decide (((2 : ℤ) - 4 ≤ i ∧ i ≤ 2 - 2) ∨ i = 2) <;>
    first
      | decide
      | (exfalso
         simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hb1 hb2 hb3 hb4
         omega)

open OMA.S_oeis_a266450 in
lemma trE (j : ℤ) : ∀ i : ℤ, rule 25 (E j (i - 1)) (E j i) (E j (i + 1)) = O j i := by
  intro i
  show rule 25 (decide ((j - 4 ≤ i - 1 ∧ i - 1 ≤ j - 2) ∨ i - 1 = j))
    (decide ((j - 4 ≤ i ∧ i ≤ j - 2) ∨ i = j))
    (decide ((j - 4 ≤ i + 1 ∧ i + 1 ≤ j - 2) ∨ i + 1 = j))
    = decide (¬ (i = j - 5 ∨ (j - 3 ≤ i ∧ i ≤ j)))
  cases hb1 : decide ((j - 4 ≤ i - 1 ∧ i - 1 ≤ j - 2) ∨ i - 1 = j) <;>
    cases hb2 : decide ((j - 4 ≤ i ∧ i ≤ j - 2) ∨ i = j) <;>
    cases hb3 : decide ((j - 4 ≤ i + 1 ∧ i + 1 ≤ j - 2) ∨ i + 1 = j) <;>
    cases hb4 : decide (¬ (i = j - 5 ∨ (j - 3 ≤ i ∧ i ≤ j))) <;>
    first
      | decide
      | (exfalso
         simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hb1 hb2 hb3 hb4
         omega)

open OMA.S_oeis_a266450 in
lemma trO (j : ℤ) : ∀ i : ℤ, rule 25 (O j (i - 1)) (O j i) (O j (i + 1)) = E (j + 1) i := by
  intro i
  show rule 25 (decide (¬ (i - 1 = j - 5 ∨ (j - 3 ≤ i - 1 ∧ i - 1 ≤ j))))
    (decide (¬ (i = j - 5 ∨ (j - 3 ≤ i ∧ i ≤ j))))
    (decide (¬ (i + 1 = j - 5 ∨ (j - 3 ≤ i + 1 ∧ i + 1 ≤ j))))
    = decide ((j + 1 - 4 ≤ i ∧ i ≤ j + 1 - 2) ∨ i = j + 1)
  cases hb1 : decide (¬ (i - 1 = j - 5 ∨ (j - 3 ≤ i - 1 ∧ i - 1 ≤ j))) <;>
    cases hb2 : decide (¬ (i = j - 5 ∨ (j - 3 ≤ i ∧ i ≤ j))) <;>
    cases hb3 : decide (¬ (i + 1 = j - 5 ∨ (j - 3 ≤ i + 1 ∧ i + 1 ≤ j))) <;>
    cases hb4 : decide ((j + 1 - 4 ≤ i ∧ i ≤ j + 1 - 2) ∨ i = j + 1) <;>
    first
      | decide
      | (exfalso
         simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hb1 hb2 hb3 hb4
         omega)

open OMA.S_oeis_a266450 in
lemma r1 : row 25 1 = R1 := next _ _ 0 rfl tr0
open OMA.S_oeis_a266450 in
lemma r2 : row 25 2 = R2 := next _ _ 1 r1 tr1
open OMA.S_oeis_a266450 in
lemma r3 : row 25 3 = R3 := next _ _ 2 r2 tr2
open OMA.S_oeis_a266450 in
lemma r4 : row 25 4 = E 2 := next _ _ 3 r3 tr3

open OMA.S_oeis_a266450 in
lemma st (i : ℕ) : row 25 (2 * i + 4) = E ((i : ℤ) + 2) ∧ row 25 (2 * i + 5) = O ((i : ℤ) + 2) := by
  induction i with
  | zero =>
    have h4 : row 25 (2 * 0 + 4) = E (((0 : ℕ) : ℤ) + 2) := by
      have e : (((0 : ℕ) : ℤ) + 2) = 2 := by norm_num
      rw [e]
      exact r4
    exact ⟨h4, next _ _ _ h4 (trE _)⟩
  | succ i ih =>
    have e : (((i + 1 : ℕ) : ℤ) + 2) = (i : ℤ) + 2 + 1 := by
      push_cast
      ring
    have h4 : row 25 (2 * (i + 1) + 4) = E (((i + 1 : ℕ) : ℤ) + 2) := by
      rw [e, show 2 * (i + 1) + 4 = (2 * i + 5) + 1 by ring]
      exact next _ _ _ ih.2 (trO _)
    exact ⟨h4, next _ _ _ h4 (trE _)⟩

open OMA.S_oeis_a266450 in
lemma off_even (i : ℕ) : off (2 * i + 4) = 4 * i + 5 := by
  unfold off
  rw [(st i).1, Finset.card_filter]
  have key : ∀ k : ℕ, (E ((i : ℤ) + 2) ((k : ℤ) - ((2 * i + 4 : ℕ) : ℤ)) = false) ↔
      ¬ (k = 3 * i + 2 ∨ k = 3 * i + 3 ∨ k = 3 * i + 4 ∨ k = 3 * i + 6) := by
    intro k
    show decide (((i : ℤ) + 2 - 4 ≤ (k : ℤ) - ((2 * i + 4 : ℕ) : ℤ)
      ∧ (k : ℤ) - ((2 * i + 4 : ℕ) : ℤ) ≤ (i : ℤ) + 2 - 2)
      ∨ (k : ℤ) - ((2 * i + 4 : ℕ) : ℤ) = (i : ℤ) + 2) = false ↔ _
    rw [decide_eq_false_iff_not]
    push_cast
    omega
  have hpoint : ∀ k ∈ Finset.range (2 * (2 * i + 4) + 1),
      ((if E ((i : ℤ) + 2) ((k : ℤ) - ((2 * i + 4 : ℕ) : ℤ)) = false then 1 else 0)
        + ((if k = 3 * i + 2 then 1 else 0) + (if k = 3 * i + 3 then 1 else 0)
          + (if k = 3 * i + 4 then 1 else 0) + (if k = 3 * i + 6 then 1 else 0)) : ℕ) = 1 := by
    intro k _
    simp only [key k]
    split_ifs <;> omega
  have hs := Finset.sum_congr rfl hpoint
  rw [Finset.sum_add_distrib] at hs
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range, Finset.sum_const,
    Finset.card_range, smul_eq_mul, mul_one] at hs
  split_ifs at hs <;> omega

open OMA.S_oeis_a266450 in
lemma off_odd (i : ℕ) : off (2 * i + 5) = 5 := by
  unfold off
  rw [(st i).2, Finset.card_filter]
  have key : ∀ k : ℕ, (O ((i : ℤ) + 2) ((k : ℤ) - ((2 * i + 5 : ℕ) : ℤ)) = false) ↔
      (k = 3 * i + 2 ∨ k = 3 * i + 4 ∨ k = 3 * i + 5 ∨ k = 3 * i + 6 ∨ k = 3 * i + 7) := by
    intro k
    show decide (¬ ((k : ℤ) - ((2 * i + 5 : ℕ) : ℤ) = (i : ℤ) + 2 - 5
      ∨ ((i : ℤ) + 2 - 3 ≤ (k : ℤ) - ((2 * i + 5 : ℕ) : ℤ)
        ∧ (k : ℤ) - ((2 * i + 5 : ℕ) : ℤ) ≤ (i : ℤ) + 2))) = false ↔ _
    rw [decide_eq_false_iff_not]
    push_cast
    omega
  have hpoint : ∀ k ∈ Finset.range (2 * (2 * i + 5) + 1),
      ((if O ((i : ℤ) + 2) ((k : ℤ) - ((2 * i + 5 : ℕ) : ℤ)) = false then 1 else 0) : ℕ)
        = (if k = 3 * i + 2 then 1 else 0) + (if k = 3 * i + 4 then 1 else 0)
          + (if k = 3 * i + 5 then 1 else 0) + (if k = 3 * i + 6 then 1 else 0)
          + (if k = 3 * i + 7 then 1 else 0) := by
    intro k _
    simp only [key k]
    split_ifs <;> omega
  rw [Finset.sum_congr rfl hpoint]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs <;> omega

open OMA.S_oeis_a266450 in
lemma off0 : off 0 = 0 := by decide
open OMA.S_oeis_a266450 in
lemma off1 : off 1 = 2 := by decide
open OMA.S_oeis_a266450 in
lemma off2 : off 2 = 3 := by decide
open OMA.S_oeis_a266450 in
lemma off3 : off 3 = 4 := by decide

open OMA.S_oeis_a266450 in
lemma a_succ (n : ℕ) : a (n + 1) = a n + off (n + 1) := by
  unfold a
  rw [Finset.sum_range_succ _ (n + 1)]

open OMA.S_oeis_a266450 in
lemma a0 : a 0 = 0 := by
  unfold a
  simp [off0]

open OMA.S_oeis_a266450 in
lemma a1 : a 1 = 2 := by rw [a_succ, a0, off1]
open OMA.S_oeis_a266450 in
lemma a2 : a 2 = 5 := by rw [a_succ, a1, off2]
open OMA.S_oeis_a266450 in
lemma a3 : a 3 = 9 := by rw [a_succ, a2, off3]
open OMA.S_oeis_a266450 in
lemma a4 : a 4 = 14 := by
  have h : off 4 = 5 := off_even 0
  rw [a_succ, a3, h]
open OMA.S_oeis_a266450 in
lemma a5 : a 5 = 19 := by
  have h : off 5 = 5 := off_odd 0
  rw [a_succ, a4, h]
open OMA.S_oeis_a266450 in
lemma a6 : a 6 = 28 := by
  have h : off 6 = 9 := off_even 1
  rw [a_succ, a5, h]
open OMA.S_oeis_a266450 in
lemma a7 : a 7 = 33 := by
  have h : off 7 = 5 := off_odd 1
  rw [a_succ, a6, h]

open OMA.S_oeis_a266450 in
lemma closed (n : ℕ) (hn : 3 ≤ n) :
    4 * (a n : ℤ) = 2 * (n : ℤ) ^ 2 + 2 * ((-1) ^ n + 3) * (n : ℤ) - 7 * (-1) ^ n - 1 := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [a3]
    norm_num
  | succ n hn ih =>
    rw [a_succ]
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
      have ho : off (2 * (i + 2) + 1) = 5 := by
        rw [show 2 * (i + 2) + 1 = 2 * i + 5 by ring]
        exact off_odd i
      have e1 : (-1 : ℤ) ^ (2 * (i + 2)) = 1 := by
        rw [pow_mul]
        norm_num
      have e2 : (-1 : ℤ) ^ (2 * (i + 2) + 1) = -1 := by
        rw [pow_succ, e1]
        norm_num
      rw [e1] at ih
      rw [e2, ho]
      push_cast at ih ⊢
      linear_combination ih
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have ho : off (2 * (i + 1) + 1 + 1) = 4 * i + 5 := by
        rw [show 2 * (i + 1) + 1 + 1 = 2 * i + 4 by ring]
        exact off_even i
      have e0 : (-1 : ℤ) ^ (2 * (i + 1)) = 1 := by
        rw [pow_mul]
        norm_num
      have e1 : (-1 : ℤ) ^ (2 * (i + 1) + 1) = -1 := by
        rw [pow_succ, e0]
        norm_num
      have e2 : (-1 : ℤ) ^ (2 * (i + 1) + 1 + 1) = 1 := by
        rw [pow_succ, e1]
        norm_num
      rw [e1] at ih
      rw [e2, ho]
      push_cast at ih ⊢
      linear_combination ih

open OMA.S_oeis_a266450 in
lemma off_rec (m : ℕ) : off (m + 8) + off (m + 4) = 2 * off (m + 6) := by
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' m
  · rw [show 2 * i + 8 = 2 * (i + 2) + 4 by ring, show 2 * i + 6 = 2 * (i + 1) + 4 by ring,
      off_even, off_even, off_even]
    omega
  · rw [show 2 * i + 1 + 8 = 2 * (i + 2) + 5 by ring,
      show 2 * i + 1 + 6 = 2 * (i + 1) + 5 by ring,
      show 2 * i + 1 + 4 = 2 * i + 5 by ring, off_odd, off_odd, off_odd]

open OMA.S_oeis_a266450 in
lemma rec8 (m : ℕ) : (a (m + 8) : ℤ)
    = a (m + 7) + 2 * a (m + 6) - 2 * a (m + 5) - a (m + 4) + a (m + 3) := by
  have h8 : a (m + 8) = a (m + 7) + off (m + 8) := a_succ (m + 7)
  have h6 : a (m + 6) = a (m + 5) + off (m + 6) := a_succ (m + 5)
  have h4 : a (m + 4) = a (m + 3) + off (m + 4) := a_succ (m + 3)
  have ho := off_rec m
  omega

open OMA.S_oeis_a266450 in
lemma gf : PowerSeries.mk (fun n => (a n : ℤ))
      * ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X) ^ 2)
    = PowerSeries.X * (1 + PowerSeries.X - PowerSeries.X ^ 2)
      * (2 + PowerSeries.X + PowerSeries.X ^ 2 - PowerSeries.X ^ 3 + PowerSeries.X ^ 4) := by
  have h2 : (2 : PowerSeries ℤ) = PowerSeries.C (2 : ℤ) := (map_ofNat _ 2).symm
  have h3 : (3 : PowerSeries ℤ) = PowerSeries.C (3 : ℤ) := (map_ofNat _ 3).symm
  have hL : PowerSeries.mk (fun n => (a n : ℤ))
        * ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X) ^ 2)
      = PowerSeries.mk (fun n => (a n : ℤ))
        - PowerSeries.X ^ 1 * PowerSeries.mk (fun n => (a n : ℤ))
        - PowerSeries.C (2 : ℤ) * (PowerSeries.X ^ 2 * PowerSeries.mk (fun n => (a n : ℤ)))
        + PowerSeries.C (2 : ℤ) * (PowerSeries.X ^ 3 * PowerSeries.mk (fun n => (a n : ℤ)))
        + PowerSeries.X ^ 4 * PowerSeries.mk (fun n => (a n : ℤ))
        - PowerSeries.X ^ 5 * PowerSeries.mk (fun n => (a n : ℤ)) := by
    rw [← h2]
    ring
  have hR : (PowerSeries.X * (1 + PowerSeries.X - PowerSeries.X ^ 2)
        * (2 + PowerSeries.X + PowerSeries.X ^ 2 - PowerSeries.X ^ 3 + PowerSeries.X ^ 4)
        : PowerSeries ℤ)
      = PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 1 + PowerSeries.C (3 : ℤ) * PowerSeries.X ^ 2
        - PowerSeries.X ^ 4 - PowerSeries.X ^ 5 + PowerSeries.C (2 : ℤ) * PowerSeries.X ^ 6
        - PowerSeries.X ^ 7 := by
    rw [← h2, ← h3]
    ring
  rw [hL, hR]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow, PowerSeries.coeff_mk]
  have hcases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ 8 ≤ n := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
  · norm_num [a0]
  · norm_num [a0, a1]
  · norm_num [a0, a1, a2]
  · norm_num [a0, a1, a2, a3]
  · norm_num [a0, a1, a2, a3, a4]
  · norm_num [a0, a1, a2, a3, a4, a5]
  · norm_num [a1, a2, a3, a4, a5, a6]
  · norm_num [a2, a3, a4, a5, a6, a7]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
      if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega,
      show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega,
      show m + 8 - 5 = m + 3 by omega]
    have hr := rec8 m
    linarith

end A266450aux

theorem OMA.solution : type_of% @OMA.S_oeis_a266450.main := by
  refine ⟨?_, ?_, A266450aux.gf⟩
  · intro n hn
    exact A266450aux.closed n (by omega)
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    rw [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega,
      show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega,
      show m + 8 - 5 = m + 3 by omega]
    exact A266450aux.rec8 m
