import OMAReductions.R_oeis_a384132_R1
import Mathlib

/-! `121 ^ 3` is not a sum of four distinct positive cubes. For each `y < z < w < 121` the kernel
checks a certificate excluding every `x < y`: the three cubes already reach `121 ^ 3`, or the
remainder is at least `y ^ 3`, or a bisection guess `r` has `r ^ 3 < remainder < (r + 1) ^ 3`. -/

namespace OMA.Step_oeis_a384132_R1_H1

/-- `121 ^ 3`. -/
def N : ℕ := 1771561

/-- Bisection for the integer cube root (a guess; only its certificate is used). -/
def bs (rem : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if lo + 1 < hi then
      (if ((lo + hi) / 2) ^ 3 ≤ rem then bs rem f ((lo + hi) / 2) hi else bs rem f lo ((lo + hi) / 2))
    else lo

/-- Certificate that no `x` with `0 < x < y` has `x ^ 3 + y ^ 3 + z ^ 3 + w ^ 3 = N`. -/
def okTriple (y z w : ℕ) : Bool :=
  decide (N ≤ w ^ 3 + z ^ 3 + y ^ 3) || decide (y ^ 3 ≤ N - (w ^ 3 + z ^ 3 + y ^ 3)) ||
    (decide ((bs (N - (w ^ 3 + z ^ 3 + y ^ 3)) 8 0 128) ^ 3 < N - (w ^ 3 + z ^ 3 + y ^ 3)) &&
      decide (N - (w ^ 3 + z ^ 3 + y ^ 3) < (bs (N - (w ^ 3 + z ^ 3 + y ^ 3)) 8 0 128 + 1) ^ 3))

theorem okTriple_spec {x y z w : ℕ} (hx : 0 < x) (hxy : x < y)
    (heq : x ^ 3 + y ^ 3 + z ^ 3 + w ^ 3 = N) (h : okTriple y z w = true) : False := by
  simp only [okTriple, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  have hx3 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ hx
  have hrem : N - (w ^ 3 + z ^ 3 + y ^ 3) = x ^ 3 := by omega
  rw [hrem] at h
  rcases h with (h | h) | ⟨h1, h2⟩
  · omega
  · have : y ≤ x := by
      by_contra hc
      push Not at hc
      exact absurd h (not_le.mpr (Nat.pow_lt_pow_left hc (by norm_num)))
    omega
  · set r := bs (x ^ 3) 8 0 128
    have hrx : r < x := by
      by_contra hc
      exact absurd h1 (not_lt.mpr (Nat.pow_le_pow_left (not_lt.mp hc) 3))
    have hxr : x < r + 1 := by
      by_contra hc
      exact absurd h2 (not_lt.mpr (Nat.pow_le_pow_left (not_lt.mp hc) 3))
    omega

set_option maxHeartbeats 0 in
theorem check : ((List.range 121).all fun w => (List.range w).all fun z =>
    (List.range z).all fun y => okTriple y z w) = true := by decide +kernel

theorem not_sum : ¬ ∃ x y z w : ℕ, 0 < x ∧ x < y ∧ y < z ∧ z < w ∧
    x ^ 3 + y ^ 3 + z ^ 3 + w ^ 3 = 121 ^ 3 := by
  rintro ⟨x, y, z, w, hx, hxy, hyz, hzw, heq⟩
  have heq' : x ^ 3 + y ^ 3 + z ^ 3 + w ^ 3 = N := by rw [heq]; rfl
  have hw : w < 121 := by
    by_contra hc
    push Not at hc
    have := Nat.pow_le_pow_left hc 3
    have : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ hx
    norm_num at *
    omega
  have hc := check
  simp only [List.all_eq_true, List.mem_range] at hc
  exact okTriple_spec hx hxy heq' (hc w hw z hzw y hyz)

end OMA.Step_oeis_a384132_R1_H1

open OMA.S_oeis_a384132 in
theorem OMA.solution : OMA.R_oeis_a384132_R1.H1 := by
  unfold OMA.R_oeis_a384132_R1.H1 IsSumOfFourDistinctCubes
  exact OMA.Step_oeis_a384132_R1_H1.not_sum
