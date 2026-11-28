import OMAStatements.S_oeis_a105752

open Finset OMA.S_oeis_a105752

theorem OMA.solution : type_of% @OMA.S_oeis_a105752.main := by
  have Z : ∀ n k, n < k → stirling1 n k = 0 := fun n k h => by
    simp [stirling1, Nat.stirlingFirst_eq_zero_of_lt h]
  have S : ∀ n k, stirling1 (n + 1) (k + 1) = stirling1 n k - n * stirling1 n (k + 1) := by
    intro n k
    rcases lt_trichotomy k n with h | rfl | h
    · obtain ⟨d, rfl⟩ : ∃ d, n = k + 1 + d := ⟨n - k - 1, by omega⟩
      simp only [stirling1, Nat.stirlingFirst_succ_succ, show k + 1 + d + 1 - (k + 1) = d + 1 by omega,
        show k + 1 + d - k = d + 1 by omega, show k + 1 + d - (k + 1) = d by omega]
      push_cast
      ring
    · rw [Z k (k + 1) (by omega)]
      simp [stirling1, Nat.stirlingFirst_succ_succ, Nat.stirlingFirst_eq_zero_of_lt]
    · rw [Z _ _ (by omega), Z _ _ h, Z _ _ (by omega)]
      ring
  have S' : ∀ n k, stirling1 (n + 1) (2 * (k + 1)) =
      stirling1 n (2 * k + 1) - n * stirling1 n (2 * (k + 1)) := fun n k => by
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
    exact S n (2 * k + 1)
  have S0 : ∀ n, stirling1 (n + 1) 0 = 0 := fun n => by simp [stirling1, Nat.stirlingFirst]
  have c1 : ∀ m : ℕ, ((1 : ℤ) - m) * (if m ≤ 1 then 1 else 0) = if m + 1 ≤ 1 then 1 else 0 := by
    rintro (_ | _ | m) <;> simp
  have c2 : ∀ m : ℕ, (m.factorial : ℤ) * (if m ≤ 1 then 1 else 0) = if m ≤ 1 then 1 else 0 := by
    rintro (_ | _ | m) <;> simp
  have key : ∀ n, (∑ k ∈ range (n + 1), stirling1 n (2 * k)) -
        ∑ k ∈ range (n + 1), stirling1 n (2 * k + 1) = (-1) ^ n * n.factorial ∧
      (∑ k ∈ range (n + 1), stirling1 n (2 * k)) +
        ∑ k ∈ range (n + 1), stirling1 n (2 * k + 1) = if n ≤ 1 then 1 else 0 := by
    intro n
    induction n with
    | zero => constructor <;> simp [stirling1, Nat.stirlingFirst]
    | succ n ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have e1 := sum_range_succ' (fun k => stirling1 n (2 * k)) (n + 1)
      have e2 := sum_range_succ (fun k => stirling1 n (2 * k)) (n + 1)
      have e3 := Z n (2 * (n + 1)) (by omega)
      have e4 : (n : ℤ) * stirling1 n (2 * 0) = 0 := by
        cases n <;> simp [S0]
      have hT : ∑ k ∈ range (n + 1 + 1), stirling1 (n + 1) (2 * k) =
          (∑ k ∈ range (n + 1), stirling1 n (2 * k + 1)) -
            n * ∑ k ∈ range (n + 1), stirling1 n (2 * (k + 1)) := by
        rw [sum_range_succ' (fun k => stirling1 (n + 1) (2 * k)), Nat.mul_zero, S0, add_zero, mul_sum,
          ← sum_sub_distrib]
        exact sum_congr rfl fun k _ => S' n k
      have hU : ∑ k ∈ range (n + 1 + 1), stirling1 (n + 1) (2 * k + 1) =
          (∑ k ∈ range (n + 1), stirling1 n (2 * k)) -
            n * ∑ k ∈ range (n + 1), stirling1 n (2 * k + 1) := by
        rw [show ∑ k ∈ range (n + 1 + 1), stirling1 (n + 1) (2 * k + 1) =
            ∑ k ∈ range (n + 1 + 1), (stirling1 n (2 * k) - n * stirling1 n (2 * k + 1)) from
            sum_congr rfl fun k _ => S n (2 * k),
          sum_sub_distrib, ← mul_sum, sum_range_succ (fun k => stirling1 n (2 * k)) (n + 1),
          sum_range_succ (fun k => stirling1 n (2 * k + 1)) (n + 1), Z n (2 * (n + 1)) (by omega),
          Z n (2 * (n + 1) + 1) (by omega)]
        ring
      rw [hT, hU]
      constructor
      · rw [Nat.factorial_succ, pow_succ]
        push_cast
        linear_combination (-(n : ℤ) - 1) * ih1 + e4 + (n : ℤ) * e1 - (n : ℤ) * e2 - (n : ℤ) * e3
      · linear_combination ((1 : ℤ) - n) * ih2 + c1 n + e4 + (n : ℤ) * e1 - (n : ℤ) * e2 - (n : ℤ) * e3
  intro n
  obtain ⟨h1, h2⟩ := key n
  have h3 : (n.factorial : ℤ) * ((if n ≤ 1 then 1 else 0) + (-1) ^ n) =
      2 * ∑ k ∈ range (n + 1), stirling1 n (2 * k) := by
    linear_combination c2 n - h1 - h2
  show (n.factorial : ℤ) * ((if n ≤ 1 then 1 else 0) + (-1) ^ n) / 2 = _
  rw [h3]
  exact Int.mul_ediv_cancel_left _ two_ne_zero
