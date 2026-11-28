import OMAStatements.S_oeis_a277930
import Mathlib

namespace LTS_A277930

open Finset OMA.S_oeis_a277930

theorem pascal (n s : ℕ) : C (n + 1) (s + 1) = C n (s + 1) + C (n + 1) s := by
  unfold C
  rw [show n + 1 + (s + 1) = n + (s + 1) + 1 by omega]
  rw [Nat.choose_succ_succ' (n + (s + 1)) n, Nat.choose_succ_succ' (n + (s + 1)) (n + 1)]
  push_cast
  ring

theorem first (n : ℕ) : C n 0 = 1 := by
  simp [C]

theorem diagonal (n : ℕ) : C n n = (catalan n : ℤ) := by
  have h : (Nat.choose (n + n) (n + 1) : ℤ) * ((n : ℤ) + 1) =
      (Nat.choose (n + n) n : ℤ) * n := by
    exact_mod_cast (show (n + n).choose (n + 1) * (n + 1) = (n + n).choose n * n by
      simpa using Nat.choose_succ_right_eq (n + n) n)
  have hcat : ((n : ℤ) + 1) * (catalan n : ℤ) = Nat.choose (n + n) n := by
    exact_mod_cast (show (n + 1) * catalan n = (n + n).choose n by
      simpa [Nat.centralBinom, two_mul] using succ_mul_catalan_eq_centralBinom n)
  unfold C
  apply mul_right_cancel₀ (show (n : ℤ) + 1 ≠ 0 by positivity)
  linear_combination -h - hcat

def F (n : ℕ) (x : ℤ) : ℤ :=
  ∑ s ∈ range (n + 1), C n s * (x + 1)^s

theorem row_step (n : ℕ) (x : ℤ) :
    x * F (n + 1) x = (catalan (n + 1) : ℤ) * (x + 1)^(n + 2) - F n x := by
  let t := ∑ s ∈ range (n + 1), C (n + 1) s * (x + 1)^s
  have hlast : F (n + 1) x = t + (catalan (n + 1) : ℤ) * (x + 1)^(n + 1) := by
    simp only [F, sum_range_succ (n := n + 1), diagonal, t]
  have hzero : C n (n + 1) = 0 := by
    unfold C
    rw [show n + (n + 1) = 2 * n + 1 by omega, Nat.choose_symm_half, sub_self]
  have hshift : (∑ s ∈ range (n + 1), C n (s + 1) * (x + 1)^(s + 1)) = F n x - 1 := by
    rw [F, sum_range_succ, sum_range_succ' (n := n), first, hzero]
    simp
  have hfirst : F (n + 1) x = F n x + (x + 1) * t := by
    rw [F, sum_range_succ' (n := n + 1), first]
    simp only [pow_zero, mul_one, t, mul_sum]
    have hsplit :
        (∑ s ∈ range (n + 1), C (n + 1) (s + 1) * (x + 1)^(s + 1)) =
          (∑ s ∈ range (n + 1), C n (s + 1) * (x + 1)^(s + 1)) +
          ∑ s ∈ range (n + 1), (x + 1) * (C (n + 1) s * (x + 1)^s) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun s _ => ?_
      rw [pascal, pow_succ]
      ring
    rw [hsplit, hshift]
    ring
  rw [pow_succ (x + 1) (n + 1)]
  linear_combination (x + 1) * hlast - hfirst

theorem row_transform (n : ℕ) (x : ℤ) :
    (∑ i ∈ range (n + 1), B n i * x^i) = F n x := by
  simp only [B, sum_mul]
  rw [sum_comm]
  unfold F
  refine sum_congr rfl fun s hs => ?_
  have hsn : s ≤ n := by simpa using hs
  calc
    (∑ i ∈ range (n + 1), (Nat.choose s i : ℤ) * C n s * x^i)
        = ∑ i ∈ range (s + 1), (Nat.choose s i : ℤ) * C n s * x^i := by
          symm
          refine sum_subset (range_subset_range.mpr (by omega)) fun i _ hi => ?_
          have hsi : s < i := by simpa using hi
          simp [Nat.choose_eq_zero_of_lt hsi]
    _ = C n s * ∑ i ∈ range (s + 1), x^i * (Nat.choose s i : ℤ) := by
          rw [mul_sum]
          exact sum_congr rfl fun i _ => by ring
    _ = C n s * (x + 1)^s := by
          rw [add_pow]
          simp

theorem even_step (k n : ℕ) :
    evenCoeff k (n + 1) = evenCoeff k n -
      2 * (catalan (n + 1) : ℤ) * (-(k : ℤ) * ((k : ℤ) + 1))^(n + 2) := by
  simp only [evenCoeff]
  rw [sum_range_succ]
  ring

theorem identity (k n : ℕ) :
    evenCoeff k n = 1 + 2 * (k : ℤ) + 2 * (-(k : ℤ))^(n + 2) * F n k := by
  induction n with
  | zero =>
      simp [evenCoeff, F, first]
      ring
  | succ n ih =>
      rw [even_step, ih, mul_pow, pow_succ (-(k : ℤ)) (n + 2)]
      linear_combination 2 * (-(k : ℤ))^(n + 2) * row_step n k

end LTS_A277930

open OMA.S_oeis_a277930 in
theorem OMA.solution : type_of% @OMA.S_oeis_a277930.main := by
  intro k n
  rw [LTS_A277930.row_transform]
  exact LTS_A277930.identity k n
