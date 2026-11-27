import OMAStatements.S_oeis_a259914
import Mathlib

namespace A259914
open OMA.S_oeis_a259914 in
lemma ps_zero (j : ℕ) : partialSums 0 j = ((j : ℚ) + 1) ^ 3 := by rw [partialSums]

open OMA.S_oeis_a259914 in
lemma ps_succ (r j : ℕ) :
    partialSums (r + 1) j = ∑ t ∈ Finset.range (j + 1), partialSums r t := by rw [partialSums]

open OMA.S_oeis_a259914 in
def q (r j : ℕ) : ℕ :=
  (j + r + 3).choose (r + 3) + 4 * (j + r + 2).choose (r + 3) + (j + r + 1).choose (r + 3)

open OMA.S_oeis_a259914 in
lemma e2 (n : ℕ) : 2 * (n + 1).choose 2 = n * (n + 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h : (n + 2).choose 2 = (n + 1) + (n + 1).choose 2 := by
      have h' := Nat.choose_succ_succ' (n + 1) 1
      rw [Nat.choose_one_right] at h'
      exact h'
    show 2 * (n + 2).choose 2 = (n + 1) * (n + 2)
    rw [h]
    nlinarith [ih]

open OMA.S_oeis_a259914 in
lemma c3 (j : ℕ) :
    (j + 3).choose 3 + 4 * (j + 2).choose 3 + (j + 1).choose 3 = (j + 1) ^ 3 := by
  induction j with
  | zero => decide
  | succ j ih =>
    have p1 : (j + 4).choose 3 = (j + 3).choose 2 + (j + 3).choose 3 :=
      Nat.choose_succ_succ' (j + 3) 2
    have p2 : (j + 3).choose 3 = (j + 2).choose 2 + (j + 2).choose 3 :=
      Nat.choose_succ_succ' (j + 2) 2
    have p3 : (j + 2).choose 3 = (j + 1).choose 2 + (j + 1).choose 3 :=
      Nat.choose_succ_succ' (j + 1) 2
    have d1 := e2 (j + 2)
    have d2 := e2 (j + 1)
    have d3 := e2 j
    show (j + 4).choose 3 + 4 * (j + 3).choose 3 + (j + 2).choose 3 = (j + 2) ^ 3
    nlinarith [ih, p1, p2, p3, d1, d2, d3]

open OMA.S_oeis_a259914 in
lemma q_zero (j : ℕ) : q 0 j = (j + 1) ^ 3 := by
  unfold q
  simp only [Nat.add_zero, Nat.zero_add]
  exact c3 j

open OMA.S_oeis_a259914 in
lemma q_base (r : ℕ) : q r 0 = 1 := by
  unfold q
  have h1 : (0 + r + 3).choose (r + 3) = 1 := by
    rw [Nat.zero_add]
    exact Nat.choose_self (r + 3)
  have h2 : (0 + r + 2).choose (r + 3) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have h3 : (0 + r + 1).choose (r + 3) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  rw [h1, h2, h3]

open OMA.S_oeis_a259914 in
lemma q_rel (r j : ℕ) : q (r + 1) (j + 1) = q (r + 1) j + q r (j + 1) := by
  unfold q
  have e1 : j + 1 + (r + 1) + 3 = (j + r + 1) + 3 + 1 := by omega
  have e2 : j + 1 + (r + 1) + 2 = (j + r + 1) + 2 + 1 := by omega
  have e3 : j + 1 + (r + 1) + 1 = (j + r + 1) + 1 + 1 := by omega
  have e4 : j + (r + 1) + 3 = (j + r + 1) + 2 + 1 := by omega
  have e5 : j + (r + 1) + 2 = (j + r + 1) + 1 + 1 := by omega
  have e6 : j + (r + 1) + 1 = (j + r + 1) + 1 := by omega
  have e7 : j + 1 + r + 3 = (j + r + 1) + 3 := by omega
  have e8 : j + 1 + r + 2 = (j + r + 1) + 2 := by omega
  have e9 : j + 1 + r + 1 = (j + r + 1) + 1 := by omega
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9]
  generalize j + r + 1 = N
  have p1 : (N + 3 + 1).choose (r + 1 + 3) = (N + 3).choose (r + 3) + (N + 3).choose (r + 1 + 3) :=
    Nat.choose_succ_succ' (N + 3) (r + 3)
  have p2 : (N + 2 + 1).choose (r + 1 + 3) = (N + 2).choose (r + 3) + (N + 2).choose (r + 1 + 3) :=
    Nat.choose_succ_succ' (N + 2) (r + 3)
  have p3 : (N + 1 + 1).choose (r + 1 + 3) = (N + 1).choose (r + 3) + (N + 1).choose (r + 1 + 3) :=
    Nat.choose_succ_succ' (N + 1) (r + 3)
  have s3 : (N + 3).choose (r + 1 + 3) = (N + 2 + 1).choose (r + 1 + 3) := rfl
  have s2 : (N + 2).choose (r + 1 + 3) = (N + 1 + 1).choose (r + 1 + 3) := rfl
  omega

open OMA.S_oeis_a259914 in
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

open OMA.S_oeis_a259914 in
lemma path_gen (t : ℕ) :
    path t = ((((t + 1) / 2 + (t / 2 + 1) + 3).choose (t / 2 + 1 + 3) : ℕ) : ℚ)
      + 4 * ((((t + 1) / 2 + (t / 2 + 1) + 2).choose (t / 2 + 1 + 3) : ℕ) : ℚ)
      + ((((t + 1) / 2 + (t / 2 + 1) + 1).choose (t / 2 + 1 + 3) : ℕ) : ℚ) := by
  unfold path
  rw [ps_eq]
  unfold q
  push_cast
  rfl

open OMA.S_oeis_a259914 in
lemma P0 (s : ℕ) : path (2 * s)
    = (((2 * s + 4).choose (s + 4) : ℕ) : ℚ) + 4 * (((2 * s + 3).choose (s + 4) : ℕ) : ℚ) + (((2 * s + 2).choose (s + 4) : ℕ) : ℚ) := by
  rw [path_gen]
  have e1 : (2 * s + 1) / 2 + ((2 * s) / 2 + 1) + 3 = 2 * s + 4 := by omega
  have e2 : (2 * s) / 2 + 1 + 3 = s + 4 := by omega
  have e3 : (2 * s + 1) / 2 + ((2 * s) / 2 + 1) + 2 = 2 * s + 3 := by omega
  have e4 : (2 * s + 1) / 2 + ((2 * s) / 2 + 1) + 1 = 2 * s + 2 := by omega
  rw [e1, e2, e3, e4]

open OMA.S_oeis_a259914 in
lemma P1 (s : ℕ) : path (2 * s + 1)
    = (((2 * s + 5).choose (s + 4) : ℕ) : ℚ) + 4 * (((2 * s + 4).choose (s + 4) : ℕ) : ℚ) + (((2 * s + 3).choose (s + 4) : ℕ) : ℚ) := by
  rw [path_gen]
  have e1 : (2 * s + 1 + 1) / 2 + ((2 * s + 1) / 2 + 1) + 3 = 2 * s + 5 := by omega
  have e2 : (2 * s + 1) / 2 + 1 + 3 = s + 4 := by omega
  have e3 : (2 * s + 1 + 1) / 2 + ((2 * s + 1) / 2 + 1) + 2 = 2 * s + 4 := by omega
  have e4 : (2 * s + 1 + 1) / 2 + ((2 * s + 1) / 2 + 1) + 1 = 2 * s + 3 := by omega
  rw [e1, e2, e3, e4]

open OMA.S_oeis_a259914 in
lemma P2 (s : ℕ) : path (2 * s + 2)
    = (((2 * s + 6).choose (s + 5) : ℕ) : ℚ) + 4 * (((2 * s + 5).choose (s + 5) : ℕ) : ℚ) + (((2 * s + 4).choose (s + 5) : ℕ) : ℚ) := by
  rw [path_gen]
  have e1 : (2 * s + 2 + 1) / 2 + ((2 * s + 2) / 2 + 1) + 3 = 2 * s + 6 := by omega
  have e2 : (2 * s + 2) / 2 + 1 + 3 = s + 5 := by omega
  have e3 : (2 * s + 2 + 1) / 2 + ((2 * s + 2) / 2 + 1) + 2 = 2 * s + 5 := by omega
  have e4 : (2 * s + 2 + 1) / 2 + ((2 * s + 2) / 2 + 1) + 1 = 2 * s + 4 := by omega
  rw [e1, e2, e3, e4]

open OMA.S_oeis_a259914 in
lemma P3 (s : ℕ) : path (2 * s + 3)
    = (((2 * s + 7).choose (s + 5) : ℕ) : ℚ) + 4 * (((2 * s + 6).choose (s + 5) : ℕ) : ℚ) + (((2 * s + 5).choose (s + 5) : ℕ) : ℚ) := by
  rw [path_gen]
  have e1 : (2 * s + 3 + 1) / 2 + ((2 * s + 3) / 2 + 1) + 3 = 2 * s + 7 := by omega
  have e2 : (2 * s + 3) / 2 + 1 + 3 = s + 5 := by omega
  have e3 : (2 * s + 3 + 1) / 2 + ((2 * s + 3) / 2 + 1) + 2 = 2 * s + 6 := by omega
  have e4 : (2 * s + 3 + 1) / 2 + ((2 * s + 3) / 2 + 1) + 1 = 2 * s + 5 := by omega
  rw [e1, e2, e3, e4]

open OMA.S_oeis_a259914 in
lemma P4 (s : ℕ) : path (2 * s + 4)
    = (((2 * s + 8).choose (s + 6) : ℕ) : ℚ) + 4 * (((2 * s + 7).choose (s + 6) : ℕ) : ℚ) + (((2 * s + 6).choose (s + 6) : ℕ) : ℚ) := by
  rw [path_gen]
  have e1 : (2 * s + 4 + 1) / 2 + ((2 * s + 4) / 2 + 1) + 3 = 2 * s + 8 := by omega
  have e2 : (2 * s + 4) / 2 + 1 + 3 = s + 6 := by omega
  have e3 : (2 * s + 4 + 1) / 2 + ((2 * s + 4) / 2 + 1) + 2 = 2 * s + 7 := by omega
  have e4 : (2 * s + 4 + 1) / 2 + ((2 * s + 4) / 2 + 1) + 1 = 2 * s + 6 := by omega
  rw [e1, e2, e3, e4]

open OMA.S_oeis_a259914 in
lemma L1 (n k : ℕ) :
    (((n + 1).choose k : ℕ) : ℚ) * ((n : ℚ) + 1 - k) = ((n.choose k : ℕ) : ℚ) * ((n : ℚ) + 1) := by
  by_cases h : k ≤ n + 1
  · have h0 := Nat.choose_mul_succ_eq n k
    have h1 : ((n.choose k * (n + 1) : ℕ) : ℚ) = (((n + 1).choose k * (n + 1 - k) : ℕ) : ℚ) := by
      rw [h0]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h] at h1
    push_cast at h1
    linarith
  · have z1 : (n + 1).choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have z2 : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [z1, z2]
    simp

open OMA.S_oeis_a259914 in
lemma L2 (n k : ℕ) (h : k ≤ n) :
    ((n.choose (k + 1) : ℕ) : ℚ) * ((k : ℚ) + 1) = ((n.choose k : ℕ) : ℚ) * ((n : ℚ) - k) := by
  have h0 := Nat.choose_succ_right_eq n k
  have h1 : ((n.choose (k + 1) * (k + 1) : ℕ) : ℚ) = ((n.choose k * (n - k) : ℕ) : ℚ) := by
    rw [h0]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub h] at h1
  push_cast at h1
  linarith

end A259914

theorem OMA.solution : type_of% @OMA.S_oeis_a259914.main := by
  intro t
  rcases Nat.even_or_odd' t with ⟨s, rfl | rfl⟩
  · intro n
    have hn : n = 2 * (s : ℚ) + 4 := by
      show ((2 * s : ℕ) : ℚ) + 4 = _
      push_cast
      ring
    rw [hn, A259914.P3, A259914.P2, A259914.P1, A259914.P0]
    have rB1 := A259914.L1 (2 * s + 3) (s + 4)
    push_cast at rB1
    have hB1 : (((2 * s + 3).choose (s + 4) : ℕ) : ℚ)
        = (((2 * s + 4).choose (s + 4) : ℕ) : ℚ) * (s : ℚ) / (2 * (s : ℚ) + 4) := by
      rw [eq_div_iff (by positivity)]
      linarith
    have rB0 := A259914.L1 (2 * s + 2) (s + 4)
    push_cast at rB0
    have hB0 : (((2 * s + 2).choose (s + 4) : ℕ) : ℚ)
        = (((2 * s + 3).choose (s + 4) : ℕ) : ℚ) * ((s : ℚ) - 1) / (2 * (s : ℚ) + 3) := by
      rw [eq_div_iff (by positivity)]
      linarith
    have rB2 := A259914.L1 (2 * s + 4) (s + 4)
    push_cast at rB2
    have hB2 : (((2 * s + 5).choose (s + 4) : ℕ) : ℚ)
        = (((2 * s + 4).choose (s + 4) : ℕ) : ℚ) * (2 * (s : ℚ) + 5) / ((s : ℚ) + 1) := by
      rw [eq_div_iff (by positivity)]
      linarith
    have rB3 := A259914.L2 (2 * s + 4) (s + 4) (by omega)
    push_cast at rB3
    have hB3 : (((2 * s + 4).choose (s + 5) : ℕ) : ℚ)
        = (((2 * s + 4).choose (s + 4) : ℕ) : ℚ) * (s : ℚ) / ((s : ℚ) + 5) := by
      rw [eq_div_iff (by positivity)]
      linarith
    have rB4 := A259914.L2 (2 * s + 5) (s + 4) (by omega)
    push_cast at rB4
    have hB4 : (((2 * s + 5).choose (s + 5) : ℕ) : ℚ)
        = (((2 * s + 5).choose (s + 4) : ℕ) : ℚ) * ((s : ℚ) + 1) / ((s : ℚ) + 5) := by
      rw [eq_div_iff (by positivity)]
      linarith
    have rB5 := A259914.L1 (2 * s + 5) (s + 5)
    push_cast at rB5
    have hB5 : (((2 * s + 6).choose (s + 5) : ℕ) : ℚ)
        = (((2 * s + 5).choose (s + 5) : ℕ) : ℚ) * (2 * (s : ℚ) + 6) / ((s : ℚ) + 1) := by
      rw [eq_div_iff (by positivity)]
      linarith
    have rB6 := A259914.L1 (2 * s + 6) (s + 5)
    push_cast at rB6
    have hB6 : (((2 * s + 7).choose (s + 5) : ℕ) : ℚ)
        = (((2 * s + 6).choose (s + 5) : ℕ) : ℚ) * (2 * (s : ℚ) + 7) / ((s : ℚ) + 2) := by
      rw [eq_div_iff (by positivity)]
      linarith
    rw [hB6, hB5, hB4, hB3, hB2, hB0, hB1]
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
    rw [hn, e3, e2, e1, A259914.P4, A259914.P3, A259914.P2, A259914.P1]
    have rB1 := A259914.L1 (2 * s + 3) (s + 4)
    push_cast at rB1
    have hB1 : (((2 * s + 3).choose (s + 4) : ℕ) : ℚ)
        = (((2 * s + 4).choose (s + 4) : ℕ) : ℚ) * (s : ℚ) / (2 * (s : ℚ) + 4) := by
      rw [eq_div_iff (by positivity)]
      linarith
    have rB2 := A259914.L1 (2 * s + 4) (s + 4)
    push_cast at rB2
    have hB2 : (((2 * s + 5).choose (s + 4) : ℕ) : ℚ)
        = (((2 * s + 4).choose (s + 4) : ℕ) : ℚ) * (2 * (s : ℚ) + 5) / ((s : ℚ) + 1) := by
      rw [eq_div_iff (by positivity)]
      linarith
    have rB3 := A259914.L2 (2 * s + 4) (s + 4) (by omega)
    push_cast at rB3
    have hB3 : (((2 * s + 4).choose (s + 5) : ℕ) : ℚ)
        = (((2 * s + 4).choose (s + 4) : ℕ) : ℚ) * (s : ℚ) / ((s : ℚ) + 5) := by
      rw [eq_div_iff (by positivity)]
      linarith
    have rB4 := A259914.L2 (2 * s + 5) (s + 4) (by omega)
    push_cast at rB4
    have hB4 : (((2 * s + 5).choose (s + 5) : ℕ) : ℚ)
        = (((2 * s + 5).choose (s + 4) : ℕ) : ℚ) * ((s : ℚ) + 1) / ((s : ℚ) + 5) := by
      rw [eq_div_iff (by positivity)]
      linarith
    have rB5 := A259914.L1 (2 * s + 5) (s + 5)
    push_cast at rB5
    have hB5 : (((2 * s + 6).choose (s + 5) : ℕ) : ℚ)
        = (((2 * s + 5).choose (s + 5) : ℕ) : ℚ) * (2 * (s : ℚ) + 6) / ((s : ℚ) + 1) := by
      rw [eq_div_iff (by positivity)]
      linarith
    have rB6 := A259914.L1 (2 * s + 6) (s + 5)
    push_cast at rB6
    have hB6 : (((2 * s + 7).choose (s + 5) : ℕ) : ℚ)
        = (((2 * s + 6).choose (s + 5) : ℕ) : ℚ) * (2 * (s : ℚ) + 7) / ((s : ℚ) + 2) := by
      rw [eq_div_iff (by positivity)]
      linarith
    have rB7 := A259914.L2 (2 * s + 6) (s + 5) (by omega)
    push_cast at rB7
    have hB7 : (((2 * s + 6).choose (s + 6) : ℕ) : ℚ)
        = (((2 * s + 6).choose (s + 5) : ℕ) : ℚ) * ((s : ℚ) + 1) / ((s : ℚ) + 6) := by
      rw [eq_div_iff (by positivity)]
      linarith
    have rB8 := A259914.L2 (2 * s + 7) (s + 5) (by omega)
    push_cast at rB8
    have hB8 : (((2 * s + 7).choose (s + 6) : ℕ) : ℚ)
        = (((2 * s + 7).choose (s + 5) : ℕ) : ℚ) * ((s : ℚ) + 2) / ((s : ℚ) + 6) := by
      rw [eq_div_iff (by positivity)]
      linarith
    have rB9 := A259914.L1 (2 * s + 7) (s + 6)
    push_cast at rB9
    have hB9 : (((2 * s + 8).choose (s + 6) : ℕ) : ℚ)
        = (((2 * s + 7).choose (s + 6) : ℕ) : ℚ) * (2 * (s : ℚ) + 8) / ((s : ℚ) + 2) := by
      rw [eq_div_iff (by positivity)]
      linarith
    rw [hB9, hB8, hB7, hB6, hB5, hB4, hB3, hB2, hB1]
    field_simp
    ring
