import OMAStatements.S_oeis_a135231
import Mathlib

/-!
Credit: @ivillar
Proof: summing the entry (n, k) of the product over k, the Pascal factor contributes
Sum_k binomial(j, k) = 2^j, so a(n) = Sum_i A103451(n, i) Sum_{j <= i} (-1)^(i-j) 2^j. Only
i = 0 and i = n contribute; the i = 0 term is 1 and 3 Sum_{j <= n} (-1)^(n-j) 2^j
= 2^(n+1) + (-1)^n. So 3 a(n) = 3 + 2^(n+1) + (-1)^n for n >= 1, which gives the recurrence,
a(n) = A001045(n+1) + 1 (as 3 A001045(m) = 2^m - (-1)^m), and with a(0..3) = 1, 2, 4, 6 the g.f.
-/

namespace OMAA135231Helpers
open OMA.S_oeis_a135231

theorem choose_sum (n j : ℕ) (hj : j ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (j.choose k : ℤ) = 2 ^ j := by
  have h1 : ∑ k ∈ Finset.range (j + 1), (j.choose k : ℤ) =
      ∑ k ∈ Finset.range (n + 1), (j.choose k : ℤ) := by
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_range] at hk ⊢
      omega
    · intro k _ hk
      simp only [Finset.mem_range] at hk
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
  rw [← h1]
  exact_mod_cast Nat.sum_range_choose j

theorem rowsum (n : ℕ) : a n = ∑ i ∈ Finset.range (n + 1), A103451 n i *
    ∑ j ∈ Finset.range (n + 1), S i j * 2 ^ j := by
  unfold a T
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.mul_sum, choose_sum n j (by have := Finset.mem_range.mp hj; omega)]
  ring

theorem G0 (n : ℕ) : ∑ j ∈ Finset.range (n + 1), S 0 j * 2 ^ j = 1 := by
  rw [Finset.sum_eq_single 0]
  · simp [S]
  · intro j _ hj
    simp [S, hj]
  · intro h
    simp at h

theorem Gn (n : ℕ) :
    3 * ∑ j ∈ Finset.range (n + 1), S n j * 2 ^ j = 2 ^ (n + 1) + (-1) ^ n := by
  have hS : ∀ m, ∑ j ∈ Finset.range (m + 1), S m j * 2 ^ j =
      ∑ j ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - j) * 2 ^ j := by
    intro m
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    simp [S, show j ≤ m by omega]
  rw [hS]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul]
    have h : ∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n + 1 - j) * 2 ^ j =
        -∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - j) * 2 ^ j := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [show n + 1 - j = (n - j) + 1 by omega, pow_succ]
      ring
    rw [h]
    linear_combination -ih

theorem closed (n : ℕ) (hn : 0 < n) : 3 * a n = 3 + 2 ^ (n + 1) + (-1) ^ n := by
  have hA0 : A103451 n 0 = 1 := by simp [A103451]
  have hAn : A103451 n n = 1 := by simp [A103451]
  have hsum : ∑ i ∈ Finset.range n, A103451 n i *
      ∑ j ∈ Finset.range (n + 1), S i j * 2 ^ j = 1 := by
    rw [Finset.sum_eq_single 0]
    · rw [hA0, G0, one_mul]
    · intro i hi h0
      rw [Finset.mem_range] at hi
      rw [show A103451 n i = 0 by simp [A103451, h0, show i ≠ n by omega], zero_mul]
    · intro h
      exfalso
      simp at h
      omega
  rw [rowsum, Finset.sum_range_succ, hsum, hAn, one_mul, mul_add, Gn]
  ring

theorem J3 (n : ℕ) : 3 * A001045 n = 2 ^ n - (-1) ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · norm_num [A001045]
    · norm_num [A001045]
    · have h1 := ih (n + 1) (by omega)
      have h0 := ih n (by omega)
      have e : A001045 (n + 1 + 1) = A001045 (n + 1) + 2 * A001045 n := rfl
      rw [e]
      linear_combination h1 + 2 * h0

theorem coeff_mk_mul_X_pow (f : ℕ → ℤ) (n k : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X ^ k) =
      if k ≤ n then f (n - k) else 0 := by
  rw [PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk]

theorem coeff_mk_mul_C_X_pow (f : ℕ → ℤ) (r : ℤ) (n k : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * (PowerSeries.C r * PowerSeries.X ^ k)) =
      r * (if k ≤ n then f (n - k) else 0) := by
  rw [mul_left_comm, PowerSeries.coeff_C_mul, coeff_mk_mul_X_pow]

theorem coeff_at (f : ℕ → ℤ) (n k j : ℕ) (h : n = j + k) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X ^ k) = f j := by
  rw [coeff_mk_mul_X_pow, if_pos (by omega), show n - k = j by omega]

theorem coeff_at_C (f : ℕ → ℤ) (r : ℤ) (n k j : ℕ) (h : n = j + k) :
    PowerSeries.coeff n (PowerSeries.mk f * (PowerSeries.C r * PowerSeries.X ^ k)) = r * f j := by
  rw [mul_left_comm, PowerSeries.coeff_C_mul, coeff_at f n k j h]

end OMAA135231Helpers

open PowerSeries OMAA135231Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a135231.main := by
  have hrec : ∀ m : ℕ, OMA.S_oeis_a135231.a (m + 4) = 2 * OMA.S_oeis_a135231.a (m + 3) +
      OMA.S_oeis_a135231.a (m + 2) - 2 * OMA.S_oeis_a135231.a (m + 1) := by
    intro m
    have h4 := closed (m + 4) (by omega)
    have h3 := closed (m + 3) (by omega)
    have h2 := closed (m + 2) (by omega)
    have h1 := closed (m + 1) (by omega)
    have h : 3 * (OMA.S_oeis_a135231.a (m + 4) - (2 * OMA.S_oeis_a135231.a (m + 3) +
        OMA.S_oeis_a135231.a (m + 2) - 2 * OMA.S_oeis_a135231.a (m + 1))) = 0 := by
      linear_combination h4 - 2 * h3 - h2 + 2 * h1
    omega
  refine ⟨?_, ?_, ?_⟩
  · set f : ℕ → ℤ := fun n => OMA.S_oeis_a135231.a n with hfdef
    have hf : PowerSeries.mk OMA.S_oeis_a135231.a = PowerSeries.mk f := rfl
    rw [hf]
    ext n
    have hD : ((X - 1) * (X + 1) * (2 * X - 1) : PowerSeries ℤ) =
        X ^ 0 - C 2 * X ^ 1 - X ^ 2 + C 2 * X ^ 3 := by
      rw [map_ofNat C 2]; ring
    have hN : (-2 * X ^ 3 - X ^ 2 + 1 : PowerSeries ℤ) = X ^ 0 - X ^ 2 - C 2 * X ^ 3 := by
      rw [map_ofNat C 2]; ring
    rw [hD, hN]
    have v0 : f 0 = 1 := by simp [hfdef, OMA.S_oeis_a135231.a, OMA.S_oeis_a135231.T,
      OMA.S_oeis_a135231.A103451, OMA.S_oeis_a135231.S]
    have v1 : f 1 = 2 := by
      have := closed 1 (by omega)
      norm_num at this
      simp only [hfdef]
      omega
    have v2 : f 2 = 4 := by
      have := closed 2 (by omega)
      norm_num at this
      simp only [hfdef]
      omega
    have v3 : f 3 = 6 := by
      have := closed 3 (by omega)
      norm_num at this
      simp only [hfdef]
      omega
    rcases Nat.lt_or_ge n 4 with h | h
    · simp only [mul_add, mul_sub, map_add, map_sub, coeff_mk_mul_C_X_pow, coeff_mk_mul_X_pow,
        coeff_C_mul, coeff_X_pow]
      interval_cases n
      · norm_num [v0]
      · norm_num [v0, v1]
      · norm_num [v0, v1, v2]
      · norm_num [v0, v1, v2, v3]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      simp only [mul_add, mul_sub, map_add, map_sub]
      rw [coeff_at f (m + 4) 0 (m + 4) (by omega), coeff_at_C f 2 (m + 4) 1 (m + 3) (by omega),
        coeff_at f (m + 4) 2 (m + 2) (by omega), coeff_at_C f 2 (m + 4) 3 (m + 1) (by omega),
        coeff_C_mul, coeff_X_pow, coeff_X_pow, coeff_X_pow, if_neg (by omega),
        if_neg (by omega), if_neg (by omega)]
      have hr := hrec m
      simp only [hfdef]
      linear_combination hr
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
      show m + 4 - 3 = m + 1 by omega]
    exact hrec m
  · intro n hn
    have hc := closed n hn
    have hj := J3 (n + 1)
    have h : 3 * (OMA.S_oeis_a135231.a n - (OMA.S_oeis_a135231.A001045 (n + 1) + 1)) = 0 := by
      linear_combination hc - hj
    omega
