import OMAStatements.S_oeis_a026050
import Mathlib

-- Problem: A026050, Mathar generating function.
-- Credit: @jagong-cmu
-- Proof: 6*d(n) = n*(2n^2-15n+109). Then d(n+4) - d(n) is even and r has period 4, so
-- d(n) - r(n) is even and 12*a(n) = 6*d(n) - 6*r(n). The cubic part and the periodic part
-- both satisfy the recurrence of the denominator (x^2+1)*(x-1)^4.

namespace OMAa026050

open OMA.S_oeis_a026050 PowerSeries Finset

/-- The cubic `P(n) = n*(2n^2 - 15n + 109)`, with `6*d(n) = P(n)`. -/
def P (n : ℤ) : ℤ := n * (2 * n ^ 2 - 15 * n + 109)

theorem first_part (m : ℕ) :
    6 * (∑ i ∈ range m, ((i : ℤ) + 1) * (i + 7)) =
      (m : ℤ) * (m + 1) * (2 * m + 1) + 18 * m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, mul_add, ih]
    push_cast
    ring

theorem d_closed (m : ℕ) : 6 * (d (m + 6) : ℤ) = P ((m : ℤ) + 6) := by
  unfold d
  rw [Finset.sum_range_add]
  have h1 : ∑ i ∈ range m, (i + 1) * (if i + 7 ≤ m + 6 then i + 7 else i + 7 - (m + 6)) =
      ∑ i ∈ range m, (i + 1) * (i + 7) := by
    apply sum_congr rfl
    intro i hi
    rw [mem_range] at hi
    rw [if_pos (by omega)]
  have h2 : ∑ j ∈ range 6, (m + j + 1) *
      (if m + j + 7 ≤ m + 6 then m + j + 7 else m + j + 7 - (m + 6)) =
      ∑ j ∈ range 6, (m + j + 1) * (j + 1) := by
    apply sum_congr rfl
    intro j hj
    rw [if_neg (by omega)]
    congr 1
    omega
  rw [h1, h2]
  push_cast
  rw [mul_add, first_part]
  simp only [sum_range_succ, sum_range_zero]
  unfold P
  ring

theorem d_step (n : ℕ) (hn : 6 ≤ n) :
    (d (n + 4) : ℤ) = d n + 2 * (2 * (n : ℤ) ^ 2 - 2 * n + 27) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have h1 := d_closed (m + 4)
  have h0 := d_closed m
  rw [show m + 4 + 6 = m + 6 + 4 by ring] at h1
  unfold P at h0 h1
  push_cast at h0 h1 ⊢
  have : 6 * ((d (m + 6 + 4) : ℤ) - d (m + 6) - 2 * (2 * ((m : ℤ) + 6) ^ 2 -
      2 * (m + 6) + 27)) = 0 := by
    linear_combination h1 - h0
  linarith

theorem r_period (n : ℕ) (hn : 7 ≤ n) : r (n + 4) = r n := by
  unfold r
  rw [show (n + 4 - 7) % 4 = (n - 7) % 4 by omega]

theorem r_le (n : ℕ) : r n ≤ 1 := by
  unfold r; split_ifs <;> omega

theorem even_dr (n : ℕ) (hn : 7 ≤ n) : (2 : ℤ) ∣ (d n : ℤ) - r n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h : 11 ≤ n
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      rw [d_step k (by omega), r_period k (by omega)]
      have h1 := ih k (by omega) (by omega)
      have h2 : (2 : ℤ) ∣ 2 * (2 * (k : ℤ) ^ 2 - 2 * k + 27) := dvd_mul_right _ _
      have e : (d k : ℤ) + 2 * (2 * (k : ℤ) ^ 2 - 2 * k + 27) - r k =
          ((d k : ℤ) - r k) + 2 * (2 * (k : ℤ) ^ 2 - 2 * k + 27) := by ring
      rw [e]
      exact dvd_add h1 h2
    · interval_cases n
      all_goals
        first
        | (have h := d_closed 1; unfold P at h; norm_num at h
           rw [show (d 7 : ℤ) = 119 by omega]; decide)
        | (have h := d_closed 2; unfold P at h; norm_num at h
           rw [show (d 8 : ℤ) = 156 by omega]; decide)
        | (have h := d_closed 3; unfold P at h; norm_num at h
           rw [show (d 9 : ℤ) = 204 by omega]; decide)
        | (have h := d_closed 4; unfold P at h; norm_num at h
           rw [show (d 10 : ℤ) = 265 by omega]; decide)

theorem a_closed (n : ℕ) (hn : 7 ≤ n) : 12 * (a n : ℤ) = P n - 6 * r n := by
  obtain ⟨m, hm⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have hd := d_closed m
  rw [← hm] at hd
  have hrd : r n ≤ d n := by
    have := r_le n
    have hpos : (1 : ℤ) ≤ d n := by
      have : (7 : ℤ) ≤ n := by exact_mod_cast hn
      unfold P at hd
      have hm' : ((m : ℤ) + 6) = n := by rw [hm]; push_cast; ring
      rw [hm'] at hd
      have hq : (1 : ℤ) ≤ 2 * (n : ℤ) ^ 2 - 15 * n + 109 := by nlinarith
      have hp : (7 : ℤ) ≤ (n : ℤ) * (2 * (n : ℤ) ^ 2 - 15 * n + 109) := by nlinarith
      linarith
    omega
  have h2 : (2 : ℕ) ∣ d n - r n := by
    have := even_dr n hn
    rw [← Nat.cast_sub hrd] at this
    exact_mod_cast this
  have h3 : (a n : ℤ) * 2 = d n - r n := by
    unfold a
    rw [← Nat.cast_sub hrd]
    exact_mod_cast Nat.div_mul_cancel h2
  have hm' : ((m : ℤ) + 6) = n := by rw [hm]; push_cast; ring
  rw [hm'] at hd
  linear_combination 6 * h3 + hd

theorem rsum (k : ℕ) :
    (r (k + 13) : ℤ) - 4 * r (k + 12) + 7 * r (k + 11) - 8 * r (k + 10) + 7 * r (k + 9) -
      4 * r (k + 8) + r (k + 7) = 0 := by
  unfold r
  split_ifs <;> omega

theorem step (k : ℕ) :
    (a (k + 13) : ℤ) - 4 * a (k + 12) + 7 * a (k + 11) - 8 * a (k + 10) + 7 * a (k + 9) -
      4 * a (k + 8) + a (k + 7) = 0 := by
  have e13 := a_closed (k + 13) (by omega)
  have e12 := a_closed (k + 12) (by omega)
  have e11 := a_closed (k + 11) (by omega)
  have e10 := a_closed (k + 10) (by omega)
  have e9 := a_closed (k + 9) (by omega)
  have e8 := a_closed (k + 8) (by omega)
  have e7 := a_closed (k + 7) (by omega)
  have hr := rsum k
  unfold P at e13 e12 e11 e10 e9 e8 e7
  push_cast at e13 e12 e11 e10 e9 e8 e7
  have : 12 * ((a (k + 13) : ℤ) - 4 * a (k + 12) + 7 * a (k + 11) - 8 * a (k + 10) +
      7 * a (k + 9) - 4 * a (k + 8) + a (k + 7)) = 0 := by
    linear_combination e13 - 4 * e12 + 7 * e11 - 8 * e10 + 7 * e9 - 4 * e8 + e7 - 6 * hr
  linarith

theorem initials : (a 7 : ℤ) = 59 ∧ (a 8 : ℤ) = 78 ∧ (a 9 : ℤ) = 102 ∧ (a 10 : ℤ) = 132 ∧
    (a 11 : ℤ) = 170 ∧ (a 12 : ℤ) = 217 := by
  have h7 := a_closed 7 (by omega)
  have h8 := a_closed 8 (by omega)
  have h9 := a_closed 9 (by omega)
  have h10 := a_closed 10 (by omega)
  have h11 := a_closed 11 (by omega)
  have h12 := a_closed 12 (by omega)
  simp only [P, r] at h7 h8 h9 h10 h11 h12
  norm_num at h7 h8 h9 h10 h11 h12
  omega

theorem gf : A * ((X ^ 2 + 1) * (X - 1) ^ 4) =
    X ^ 7 * (59 - 158 * X + 203 * X ^ 2 - 202 * X ^ 3 + 145 * X ^ 4 - 45 * X ^ 5) := by
  have product : A * ((X ^ 2 + 1) * (X - 1) ^ 4 : PowerSeries ℤ) =
      A - 4 • (A * X ^ 1) + 7 • (A * X ^ 2) - 8 • (A * X ^ 3) + 7 • (A * X ^ 4) -
        4 • (A * X ^ 5) + A * X ^ 6 := by
    simp only [nsmul_eq_mul]
    push_cast
    ring
  have rhs : (X ^ 7 * (59 - 158 * X + 203 * X ^ 2 - 202 * X ^ 3 + 145 * X ^ 4 - 45 * X ^ 5) :
      PowerSeries ℤ) = 59 • X ^ 7 - 158 • X ^ 8 + 203 • X ^ 9 - 202 • X ^ 10 +
        145 • X ^ 11 - 45 • X ^ 12 := by
    simp only [nsmul_eq_mul]
    push_cast
    ring
  rw [product, rhs]
  ext n
  simp only [A, map_add, map_sub, map_nsmul, coeff_mul_X_pow', coeff_mk, coeff_X_pow]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  by_cases h : 12 < n
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 13 := ⟨n - 13, by omega⟩
    simp only [show 1 ≤ k + 13 by omega, show 2 ≤ k + 13 by omega, show 3 ≤ k + 13 by omega,
      show 4 ≤ k + 13 by omega, show 5 ≤ k + 13 by omega, show 6 ≤ k + 13 by omega,
      show k + 13 ≠ 7 by omega, show k + 13 ≠ 8 by omega, show k + 13 ≠ 9 by omega,
      show k + 13 ≠ 10 by omega, show k + 13 ≠ 11 by omega, show k + 13 ≠ 12 by omega,
      if_true, if_false,
      show k + 13 - 1 = k + 12 by omega, show k + 13 - 2 = k + 11 by omega,
      show k + 13 - 3 = k + 10 by omega, show k + 13 - 4 = k + 9 by omega,
      show k + 13 - 5 = k + 8 by omega, show k + 13 - 6 = k + 7 by omega,
      show ¬ k + 13 < 7 by omega, show ¬ k + 12 < 7 by omega, show ¬ k + 11 < 7 by omega,
      show ¬ k + 10 < 7 by omega, show ¬ k + 9 < 7 by omega, show ¬ k + 8 < 7 by omega,
      show ¬ k + 7 < 7 by omega]
    have := step k
    linarith
  · obtain ⟨h7, h8, h9, h10, h11, h12⟩ := initials
    interval_cases n <;> norm_num [h7, h8, h9, h10, h11, h12]

end OMAa026050

theorem OMA.solution : type_of% @OMA.S_oeis_a026050.main :=
  OMAa026050.gf
