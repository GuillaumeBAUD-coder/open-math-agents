import OMAStatements.S_oeis_a259775
import Mathlib

namespace A259775
open OMA.S_oeis_a259775 in
lemma ps_zero (j : ℕ) : partialSums 0 j = ((j : ℚ) + 1) ^ 2 := by rw [partialSums]

open OMA.S_oeis_a259775 in
lemma ps_succ (r j : ℕ) :
    partialSums (r + 1) j = ∑ t ∈ Finset.range (j + 1), partialSums r t := by rw [partialSums]

open OMA.S_oeis_a259775 in
def q (r j : ℕ) : ℕ := (j + r + 2).choose (r + 2) + (j + r + 1).choose (r + 2)

open OMA.S_oeis_a259775 in
lemma c2 (j : ℕ) : (j + 2).choose 2 + (j + 1).choose 2 = (j + 1) ^ 2 := by
  induction j with
  | zero => decide
  | succ j ih =>
    have h2 : (j + 2).choose 2 = (j + 1) + (j + 1).choose 2 := by
      have h := Nat.choose_succ_succ' (j + 1) 1
      rw [Nat.choose_one_right] at h
      exact h
    have h1 : (j + 3).choose 2 = (j + 2) + (j + 2).choose 2 := by
      have h := Nat.choose_succ_succ' (j + 2) 1
      rw [Nat.choose_one_right] at h
      exact h
    show (j + 3).choose 2 + (j + 2).choose 2 = (j + 2) ^ 2
    rw [h1]
    nlinarith [ih, h2]

open OMA.S_oeis_a259775 in
lemma q_zero (j : ℕ) : q 0 j = (j + 1) ^ 2 := by
  unfold q
  simp only [Nat.add_zero, Nat.zero_add]
  exact c2 j

open OMA.S_oeis_a259775 in
lemma q_base (r : ℕ) : q r 0 = 1 := by
  unfold q
  have h1 : (0 + r + 2).choose (r + 2) = 1 := by
    rw [Nat.zero_add]
    exact Nat.choose_self (r + 2)
  have h2 : (0 + r + 1).choose (r + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  rw [h1, h2]

open OMA.S_oeis_a259775 in
lemma q_rel (r j : ℕ) : q (r + 1) (j + 1) = q (r + 1) j + q r (j + 1) := by
  unfold q
  have e1 : j + 1 + (r + 1) + 2 = (j + r + 2) + 1 + 1 := by omega
  have e2 : j + 1 + (r + 1) + 1 = (j + r + 2) + 1 := by omega
  have e3 : j + (r + 1) + 2 = (j + r + 2) + 1 := by omega
  have e4 : j + (r + 1) + 1 = j + r + 2 := by omega
  have e5 : j + 1 + r + 2 = (j + r + 2) + 1 := by omega
  have e6 : j + 1 + r + 1 = j + r + 2 := by omega
  rw [e1, e2, e3, e4, e5, e6]
  generalize j + r + 2 = N
  have p1 : (N + 1 + 1).choose (r + 1 + 2) = (N + 1).choose (r + 2) + (N + 1).choose (r + 1 + 2) :=
    Nat.choose_succ_succ' (N + 1) (r + 2)
  have p2 : (N + 1).choose (r + 1 + 2) = N.choose (r + 2) + N.choose (r + 1 + 2) :=
    Nat.choose_succ_succ' N (r + 2)
  rw [p1, p2]
  omega

open OMA.S_oeis_a259775 in
lemma ps_eq (r : ℕ) : ∀ j, partialSums r j = (q r j : ℚ) := by
  induction r with
  | zero =>
    intro j
    rw [ps_zero, q_zero]
    push_cast
    ring
  | succ r ih =>
    intro j
    induction j with
    | zero =>
      rw [ps_succ]
      simp [ih, q_base]
    | succ j ihj =>
      rw [ps_succ, Finset.sum_range_succ, ← ps_succ, ihj, ih, q_rel]
      push_cast
      ring

open OMA.S_oeis_a259775 in
lemma path_gen (t : ℕ) :
    path t = ((((t + 1) / 2 + (t / 2 + 1) + 2).choose (t / 2 + 1 + 2) : ℕ) : ℚ)
      + ((((t + 1) / 2 + (t / 2 + 1) + 1).choose (t / 2 + 1 + 2) : ℕ) : ℚ) := by
  unfold path
  rw [ps_eq]
  unfold q
  push_cast
  rfl

open OMA.S_oeis_a259775 in
lemma P0 (s : ℕ) : path (2 * s)
    = (((2 * s + 3).choose (s + 3) : ℕ) : ℚ) + (((2 * s + 2).choose (s + 3) : ℕ) : ℚ) := by
  rw [path_gen]
  have e1 : (2 * s + 1) / 2 + (2 * s / 2 + 1) + 2 = 2 * s + 3 := by omega
  have e2 : 2 * s / 2 + 1 + 2 = s + 3 := by omega
  have e3 : (2 * s + 1) / 2 + (2 * s / 2 + 1) + 1 = 2 * s + 2 := by omega
  rw [e1, e2, e3]

open OMA.S_oeis_a259775 in
lemma P1 (s : ℕ) : path (2 * s + 1)
    = (((2 * s + 4).choose (s + 3) : ℕ) : ℚ) + (((2 * s + 3).choose (s + 3) : ℕ) : ℚ) := by
  rw [path_gen]
  have e1 : (2 * s + 1 + 1) / 2 + ((2 * s + 1) / 2 + 1) + 2 = 2 * s + 4 := by omega
  have e2 : (2 * s + 1) / 2 + 1 + 2 = s + 3 := by omega
  have e3 : (2 * s + 1 + 1) / 2 + ((2 * s + 1) / 2 + 1) + 1 = 2 * s + 3 := by omega
  rw [e1, e2, e3]

open OMA.S_oeis_a259775 in
lemma P2 (s : ℕ) : path (2 * s + 2)
    = (((2 * s + 5).choose (s + 4) : ℕ) : ℚ) + (((2 * s + 4).choose (s + 4) : ℕ) : ℚ) := by
  rw [path_gen]
  have e1 : (2 * s + 2 + 1) / 2 + ((2 * s + 2) / 2 + 1) + 2 = 2 * s + 5 := by omega
  have e2 : (2 * s + 2) / 2 + 1 + 2 = s + 4 := by omega
  have e3 : (2 * s + 2 + 1) / 2 + ((2 * s + 2) / 2 + 1) + 1 = 2 * s + 4 := by omega
  rw [e1, e2, e3]

open OMA.S_oeis_a259775 in
lemma P3 (s : ℕ) : path (2 * s + 3)
    = (((2 * s + 6).choose (s + 4) : ℕ) : ℚ) + (((2 * s + 5).choose (s + 4) : ℕ) : ℚ) := by
  rw [path_gen]
  have e1 : (2 * s + 3 + 1) / 2 + ((2 * s + 3) / 2 + 1) + 2 = 2 * s + 6 := by omega
  have e2 : (2 * s + 3) / 2 + 1 + 2 = s + 4 := by omega
  have e3 : (2 * s + 3 + 1) / 2 + ((2 * s + 3) / 2 + 1) + 1 = 2 * s + 5 := by omega
  rw [e1, e2, e3]

open OMA.S_oeis_a259775 in
lemma P4 (s : ℕ) : path (2 * s + 4)
    = (((2 * s + 7).choose (s + 5) : ℕ) : ℚ) + (((2 * s + 6).choose (s + 5) : ℕ) : ℚ) := by
  rw [path_gen]
  have e1 : (2 * s + 4 + 1) / 2 + ((2 * s + 4) / 2 + 1) + 2 = 2 * s + 7 := by omega
  have e2 : (2 * s + 4) / 2 + 1 + 2 = s + 5 := by omega
  have e3 : (2 * s + 4 + 1) / 2 + ((2 * s + 4) / 2 + 1) + 1 = 2 * s + 6 := by omega
  rw [e1, e2, e3]

open OMA.S_oeis_a259775 in
lemma L1 (n k : ℕ) (h : k ≤ n + 1) :
    (((n + 1).choose k : ℕ) : ℚ) * ((n : ℚ) + 1 - k) = ((n.choose k : ℕ) : ℚ) * ((n : ℚ) + 1) := by
  have h0 := Nat.choose_mul_succ_eq n k
  have h1 : ((n.choose k * (n + 1) : ℕ) : ℚ) = (((n + 1).choose k * (n + 1 - k) : ℕ) : ℚ) := by
    rw [h0]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h] at h1
  push_cast at h1
  linarith

open OMA.S_oeis_a259775 in
lemma L2 (n k : ℕ) (h : k ≤ n) :
    ((n.choose (k + 1) : ℕ) : ℚ) * ((k : ℚ) + 1) = ((n.choose k : ℕ) : ℚ) * ((n : ℚ) - k) := by
  have h0 := Nat.choose_succ_right_eq n k
  have h1 : ((n.choose (k + 1) * (k + 1) : ℕ) : ℚ) = ((n.choose k * (n - k) : ℕ) : ℚ) := by
    rw [h0]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h] at h1
  push_cast at h1
  linarith

end A259775

theorem OMA.solution : type_of% @OMA.S_oeis_a259775.main := by
  intro t
  rcases Nat.even_or_odd' t with ⟨s, rfl | rfl⟩
  · intro n
    have hn : n = 2 * (s : ℚ) + 4 := by
      show ((2 * s : ℕ) : ℚ) + 4 = _
      push_cast
      ring
    rw [hn, A259775.P3, A259775.P2, A259775.P1, A259775.P0]
    have r1 := A259775.L1 (2 * s + 2) (s + 3) (by omega)
    have r2 := A259775.L1 (2 * s + 3) (s + 3) (by omega)
    have r3 := A259775.L2 (2 * s + 4) (s + 3) (by omega)
    have r4 := A259775.L1 (2 * s + 4) (s + 4) (by omega)
    have r5 := A259775.L1 (2 * s + 5) (s + 4) (by omega)
    push_cast at r1 r2 r3 r4 r5
    have hA1 : (((2 * s + 2).choose (s + 3) : ℕ) : ℚ)
        = (((2 * s + 3).choose (s + 3) : ℕ) : ℚ) * (s : ℚ) / (2 * (s : ℚ) + 3) := by
      rw [eq_div_iff (by positivity)]
      linarith
    have hA2 : (((2 * s + 4).choose (s + 3) : ℕ) : ℚ)
        = (((2 * s + 3).choose (s + 3) : ℕ) : ℚ) * (2 * (s : ℚ) + 4) / ((s : ℚ) + 1) := by
      rw [eq_div_iff (by positivity)]
      linarith
    have hA3 : (((2 * s + 4).choose (s + 4) : ℕ) : ℚ)
        = (((2 * s + 4).choose (s + 3) : ℕ) : ℚ) * ((s : ℚ) + 1) / ((s : ℚ) + 4) := by
      rw [eq_div_iff (by positivity)]
      linarith
    have hA4 : (((2 * s + 5).choose (s + 4) : ℕ) : ℚ)
        = (((2 * s + 4).choose (s + 4) : ℕ) : ℚ) * (2 * (s : ℚ) + 5) / ((s : ℚ) + 1) := by
      rw [eq_div_iff (by positivity)]
      linarith
    have hA5 : (((2 * s + 6).choose (s + 4) : ℕ) : ℚ)
        = (((2 * s + 5).choose (s + 4) : ℕ) : ℚ) * (2 * (s : ℚ) + 6) / ((s : ℚ) + 2) := by
      rw [eq_div_iff (by positivity)]
      linarith
    rw [hA5, hA4, hA3, hA2, hA1]
    field_simp
    ring
  · intro n
    have hn : n = 2 * (s : ℚ) + 5 := by
      show ((2 * s + 1 : ℕ) : ℚ) + 4 = _
      push_cast
      ring
    have e3 : 2 * s + 1 + 3 = 2 * s + 4 := by ring
    have e2 : 2 * s + 1 + 2 = 2 * s + 3 := by ring
    have e1 : 2 * s + 1 + 1 = 2 * s + 2 := by ring
    rw [hn, e3, e2, e1, A259775.P4, A259775.P3, A259775.P2, A259775.P1]
    have r2 := A259775.L1 (2 * s + 3) (s + 3) (by omega)
    have r3 := A259775.L2 (2 * s + 4) (s + 3) (by omega)
    have r4 := A259775.L1 (2 * s + 4) (s + 4) (by omega)
    have r5 := A259775.L1 (2 * s + 5) (s + 4) (by omega)
    have r6 := A259775.L2 (2 * s + 6) (s + 4) (by omega)
    have r7 := A259775.L1 (2 * s + 6) (s + 5) (by omega)
    push_cast at r2 r3 r4 r5 r6 r7
    have hA2 : (((2 * s + 4).choose (s + 3) : ℕ) : ℚ)
        = (((2 * s + 3).choose (s + 3) : ℕ) : ℚ) * (2 * (s : ℚ) + 4) / ((s : ℚ) + 1) := by
      rw [eq_div_iff (by positivity)]
      linarith
    have hA3 : (((2 * s + 4).choose (s + 4) : ℕ) : ℚ)
        = (((2 * s + 4).choose (s + 3) : ℕ) : ℚ) * ((s : ℚ) + 1) / ((s : ℚ) + 4) := by
      rw [eq_div_iff (by positivity)]
      linarith
    have hA4 : (((2 * s + 5).choose (s + 4) : ℕ) : ℚ)
        = (((2 * s + 4).choose (s + 4) : ℕ) : ℚ) * (2 * (s : ℚ) + 5) / ((s : ℚ) + 1) := by
      rw [eq_div_iff (by positivity)]
      linarith
    have hA5 : (((2 * s + 6).choose (s + 4) : ℕ) : ℚ)
        = (((2 * s + 5).choose (s + 4) : ℕ) : ℚ) * (2 * (s : ℚ) + 6) / ((s : ℚ) + 2) := by
      rw [eq_div_iff (by positivity)]
      linarith
    have hA6 : (((2 * s + 6).choose (s + 5) : ℕ) : ℚ)
        = (((2 * s + 6).choose (s + 4) : ℕ) : ℚ) * ((s : ℚ) + 2) / ((s : ℚ) + 5) := by
      rw [eq_div_iff (by positivity)]
      linarith
    have hA7 : (((2 * s + 7).choose (s + 5) : ℕ) : ℚ)
        = (((2 * s + 6).choose (s + 5) : ℕ) : ℚ) * (2 * (s : ℚ) + 7) / ((s : ℚ) + 2) := by
      rw [eq_div_iff (by positivity)]
      linarith
    rw [hA7, hA6, hA5, hA4, hA3, hA2]
    field_simp
    ring
