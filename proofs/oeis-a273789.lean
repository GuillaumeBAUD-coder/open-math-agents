import OMAStatements.S_oeis_a273789
import Mathlib

namespace A273789Aux

open OMA.S_oeis_a273789 in
def off (L : List (ℤ × ℤ)) : Grid := fun x y => !decide ((x, y) ∈ L)

def inBox (L : List (ℤ × ℤ)) : Prop := ∀ p ∈ L, -1 ≤ p.1 ∧ p.1 ≤ 1 ∧ -1 ≤ p.2 ∧ p.2 ≤ 1

lemma off_far (L : List (ℤ × ℤ)) (hL : inBox L) (u v : ℤ)
    (h : ¬(-1 ≤ u ∧ u ≤ 1 ∧ -1 ≤ v ∧ v ≤ 1)) : off L u v = true := by
  unfold off
  have hm : (u, v) ∉ L := fun hm => h (hL _ hm)
  simp [hm]

def five : List ℤ := [-2, -1, 0, 1, 2]

lemma mem_five (x : ℤ) (h1 : -2 ≤ x) (h2 : x ≤ 2) : x ∈ five := by
  unfold five
  simp
  omega

open OMA.S_oeis_a273789 in
lemma step_off (code : ℕ) (L L' : List (ℤ × ℤ)) (hL : inBox L) (hL' : inBox L')
    (hr : rule code true (bit true + bit true + bit true + bit true) = true)
    (hbox : ∀ x ∈ five, ∀ y ∈ five, step code (off L) x y = off L' x y) :
    step code (off L) = off L' := by
  funext x y
  by_cases h : (-2 ≤ x ∧ x ≤ 2) ∧ (-2 ≤ y ∧ y ≤ 2)
  · exact hbox x (mem_five x h.1.1 h.1.2) y (mem_five y h.2.1 h.2.2)
  · rw [off_far L' hL' x y (by omega)]
    unfold step neighbors
    rw [off_far L hL x y (by omega), off_far L hL (x + 1) y (by omega),
      off_far L hL (x - 1) y (by omega), off_far L hL x (y + 1) (by omega),
      off_far L hL x (y - 1) (by omega)]
    exact hr

open OMA.S_oeis_a273789 in
lemma initial_far (u v : ℤ) (h : ¬(u = 0 ∧ v = 0)) : initial u v = false := by
  unfold initial
  simp only [decide_eq_false_iff_not]
  exact h

open OMA.S_oeis_a273789 in
lemma step_initial (code : ℕ) (L' : List (ℤ × ℤ)) (hL' : inBox L')
    (hr : rule code false (bit false + bit false + bit false + bit false) = true)
    (hbox : ∀ x ∈ five, ∀ y ∈ five, step code initial x y = off L' x y) :
    step code initial = off L' := by
  funext x y
  by_cases h : (-2 ≤ x ∧ x ≤ 2) ∧ (-2 ≤ y ∧ y ≤ 2)
  · exact hbox x (mem_five x h.1.1 h.1.2) y (mem_five y h.2.1 h.2.2)
  · rw [off_far L' hL' x y (by omega)]
    unfold step neighbors
    rw [initial_far x y (by omega), initial_far (x + 1) y (by omega),
      initial_far (x - 1) y (by omega), initial_far x (y + 1) (by omega),
      initial_far x (y - 1) (by omega)]
    exact hr

open OMA.S_oeis_a273789 in
lemma s1 : state 931 1 = off [(-1, 0), (0, -1), (0, 1), (1, 0)] :=
  step_initial 931 _ (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a273789 in
lemma s2 : state 931 2 = off [] := by
  show step 931 (state 931 1) = _
  rw [s1]
  exact step_off 931 _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide)
    (by decide)

open OMA.S_oeis_a273789 in
lemma sN (n : ℕ) : state 931 (n + 2) = off [] := by
  induction n with
  | zero => exact s2
  | succ k ih =>
    show step 931 (state 931 (k + 2)) = _
    rw [ih]
    exact step_off 931 _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide)
      (by decide)

open OMA.S_oeis_a273789 in
lemma t1 : state 901 1 = off [(0, 0)] :=
  step_initial 901 _ (by unfold inBox; decide) (by decide) (by decide)

open OMA.S_oeis_a273789 in
lemma t2 : state 901 2 = off [] := by
  show step 901 (state 901 1) = _
  rw [t1]
  exact step_off 901 _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide)
    (by decide)

open OMA.S_oeis_a273789 in
lemma tN (n : ℕ) : state 901 (n + 2) = off [] := by
  induction n with
  | zero => exact t2
  | succ k ih =>
    show step 901 (state 901 (k + 2)) = _
    rw [ih]
    exact step_off 901 _ _ (by unfold inBox; decide) (by unfold inBox; decide) (by decide)
      (by decide)

open OMA.S_oeis_a273789 in
lemma a_big (n : ℕ) : a (n + 2) = (2 * (n + 2) + 1) ^ 2 := by
  unfold a onCount
  rw [sN]
  simp [off]
  ring

open OMA.S_oeis_a273789 in
lemma b_big (n : ℕ) : A273743 (n + 2) = (2 * (n + 2) + 1) ^ 2 := by
  unfold A273743 onCount
  rw [tN]
  simp [off]
  ring

open OMA.S_oeis_a273789 in
lemma a_cl (n : ℕ) (hn : 2 ≤ n) : (a n : ℤ) = (2 * (n : ℤ) + 1) ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [a_big]
  push_cast
  ring

open OMA.S_oeis_a273789 in
lemma a0 : a 0 = 1 := by decide

open OMA.S_oeis_a273789 in
lemma a1 : a 1 = 5 := by
  unfold a onCount
  rw [s1]
  decide

open PowerSeries in
lemma coeff_term (f : ℕ → ℤ) (c : ℤ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

end A273789Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a273789 A273789Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a273789.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [a_big]; ring
    · rw [b_big]; ring
    · rw [b_big]; rfl
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega]
    rw [a_cl (m + 5) (by omega), a_cl (m + 4) (by omega), a_cl (m + 3) (by omega),
      a_cl (m + 2) (by omega)]
    push_cast
    ring
  · have hD : ((1 : PowerSeries ℤ) - PowerSeries.X) ^ 3 =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-3) * PowerSeries.X ^ 1 +
        PowerSeries.C 3 * PowerSeries.X ^ 2 + PowerSeries.C (-1) * PowerSeries.X ^ 3 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    have hN : (1 + 2 * PowerSeries.X + 13 * PowerSeries.X ^ 2 - 12 * PowerSeries.X ^ 3
        + 4 * PowerSeries.X ^ 4 : PowerSeries ℤ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C 2 * PowerSeries.X ^ 1 +
        PowerSeries.C 13 * PowerSeries.X ^ 2 + PowerSeries.C (-12) * PowerSeries.X ^ 3 +
        PowerSeries.C 4 * PowerSeries.X ^ 4 := by
      simp only [map_one, map_ofNat, map_neg]; ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    have e2 := a_cl 2 (by omega)
    have e3 := a_cl 3 (by omega)
    have e4 := a_cl 4 (by omega)
    rcases n with _ | _ | _ | _ | _ | n
    · simp [a0]
    · simp [a0, a1]
    · simp [a0, a1, e2]
    · simp [a0, a1, e2, e3]
    · simp [a1, e2, e3, e4]
    · have f5 := a_cl (n + 5) (by omega)
      have f4 := a_cl (n + 4) (by omega)
      have f3 := a_cl (n + 3) (by omega)
      have f2 := a_cl (n + 2) (by omega)
      simp [f5, f4, f3, f2]
      ring
