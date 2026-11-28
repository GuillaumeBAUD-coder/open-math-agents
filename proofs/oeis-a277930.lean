import OMAStatements.S_oeis_a277930
import Mathlib

-- Problem: oeis-a277930 (Schulte's identity with the Borel triangle)
-- Credit: @Aijy0264561
-- sum_i B(n,i) k^i = sum_s C(n,s) (k+1)^s (binomial theorem), and the Catalan-triangle Pascal rule
-- C(n+1,t) = C(n+1,t-1) + C(n,t) telescopes k P_{n+1}(k) + P_n(k) to Cat(n+1) (k+1)^(n+2);
-- induction on n adds the Catalan terms (at x = -k(k+1) the Catalan series sums to -k).

namespace OMA.A277930proof

open OMA.S_oeis_a277930 Finset

lemma C_pascal (n t : ℕ) : C (n + 1) (t + 1) = C (n + 1) t + C n (t + 1) := by
  unfold C
  rw [show n + 1 + (t + 1) = (n + t + 1) + 1 by ring, show n + 1 + t = n + t + 1 by ring,
    show n + (t + 1) = n + t + 1 by ring]
  rw [Nat.choose_succ_succ' (n + t + 1) n, Nat.choose_succ_succ' (n + t + 1) (n + 1)]
  rw [show n + t + 1 = (n + t) + 1 by ring, Nat.choose_succ_succ' (n + t) n,
    Nat.choose_succ_succ' (n + t) (n + 1)]
  push_cast; ring

lemma C_diag (m : ℕ) : C m m = (catalan m : ℤ) := by
  unfold C
  have h1 := Nat.choose_succ_right_eq (m + m) m
  have h2 := succ_mul_catalan_eq_centralBinom m
  rw [Nat.centralBinom_eq_two_mul_choose] at h2
  have h1' : ((m + m).choose (m + 1) : ℤ) * (m + 1) = ((m + m).choose m : ℤ) * m := by
    have := h1; rw [show m + m - m = m by omega] at this; exact_mod_cast this
  have h2' : ((m : ℤ) + 1) * (catalan m : ℤ) = ((m + m).choose m : ℤ) := by
    rw [show m + m = 2 * m by ring]; exact_mod_cast h2
  have hm : ((m : ℤ) + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ hm
  linear_combination -h1' - h2'

lemma C_above (n : ℕ) : C n (n + 1) = 0 := by
  unfold C
  rw [show n + (n + 1) = 2 * n + 1 by ring]
  have := Nat.choose_symm_of_eq_add (show 2 * n + 1 = n + (n + 1) by ring)
  rw [this]; ring

lemma C_zero (n : ℕ) : C n 0 = 1 := by unfold C; simp

/-- The polynomial `∑ B(n,i) k^i` as a sum over the Catalan triangle in powers of `k+1`. -/
lemma P_eq (n : ℕ) (y : ℤ) :
    ∑ i ∈ range (n + 1), B n i * y ^ i = ∑ s ∈ range (n + 1), C n s * (y + 1) ^ s := by
  unfold B
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro s hs
  have hs' := mem_range.1 hs
  rw [add_pow, mul_sum]
  have e : ∀ x ∈ range (n + 1), (s.choose x : ℤ) * C n s * y ^ x =
      C n s * (y ^ x * 1 ^ (s - x) * (s.choose x : ℤ)) := by intro x _; ring
  rw [sum_congr rfl e]
  symm
  apply sum_subset (range_subset_range.2 (by omega))
  intro i _ hi
  have : s < i := by simp at hi; omega
  simp [Nat.choose_eq_zero_of_lt this]

/-- The telescoping identity `y P_{n+1} + P_n = Cat(n+1) (y+1)^(n+2)` in the variable `y+1`. -/
lemma tele (n : ℕ) (z : ℤ) :
    (z - 1) * ∑ s ∈ range (n + 2), C (n + 1) s * z ^ s + ∑ s ∈ range (n + 1), C n s * z ^ s =
      (catalan (n + 1) : ℤ) * z ^ (n + 2) := by
  have key : ∑ s ∈ range (n + 2), C (n + 1) s * z ^ s =
      ∑ s ∈ range (n + 1), C (n + 1) s * z ^ (s + 1) + ∑ s ∈ range (n + 1), C n s * z ^ s := by
    rw [sum_range_succ', C_zero]
    have : ∀ s ∈ range (n + 1), C (n + 1) (s + 1) * z ^ (s + 1) =
        C (n + 1) s * z ^ (s + 1) + C n (s + 1) * z ^ (s + 1) := by
      intro s _; rw [C_pascal]; ring
    rw [sum_congr rfl this, sum_add_distrib]
    have h2 : ∑ s ∈ range (n + 1), C n (s + 1) * z ^ (s + 1) =
        ∑ s ∈ range (n + 1), C n s * z ^ s - 1 := by
      have := sum_range_succ' (fun s => C n s * z ^ s) (n + 1)
      rw [sum_range_succ, C_above, C_zero] at this
      simp at this; linarith
    rw [h2]; ring
  rw [key]
  have h3 : ∑ s ∈ range (n + 2), C (n + 1) s * z ^ (s + 1) =
      ∑ s ∈ range (n + 1), C (n + 1) s * z ^ (s + 1) + (catalan (n + 1) : ℤ) * z ^ (n + 2) := by
    rw [sum_range_succ, C_diag]
  have h4 : z * ∑ s ∈ range (n + 2), C (n + 1) s * z ^ s =
      ∑ s ∈ range (n + 2), C (n + 1) s * z ^ (s + 1) := by
    rw [mul_sum]; apply sum_congr rfl; intro s _; ring
  rw [key] at h4
  linear_combination h4 + h3

theorem a277930 : type_of% @OMA.S_oeis_a277930.main := by
  intro k n
  unfold evenCoeff
  set y : ℤ := (k : ℤ)
  suffices h : -(∑ i ∈ range (n + 1), (catalan i : ℤ) * (-y * (y + 1)) ^ (i + 1)) =
      y + (-y) ^ (n + 2) * ∑ i ∈ range (n + 1), B n i * y ^ i by
    linear_combination 2 * h
  induction n with
  | zero =>
    simp [B, C]; ring
  | succ n ih =>
    rw [sum_range_succ, neg_add, ih]
    have ht := tele n (y + 1)
    simp only [show n + 2 = n + 1 + 1 from rfl] at ht
    rw [← P_eq (n + 1) y, ← P_eq n y] at ht
    have hp : (-y * (y + 1)) ^ (n + 1 + 1) = (-y) ^ (n + 1 + 1) * (y + 1) ^ (n + 1 + 1) := by
      rw [mul_pow]
    rw [hp]
    linear_combination (-y) ^ (n + 1 + 1) * ht

end OMA.A277930proof

theorem OMA.solution : type_of% @OMA.S_oeis_a277930.main := OMA.A277930proof.a277930
