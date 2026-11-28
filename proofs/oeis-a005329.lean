import OMAStatements.S_oeis_a005329
import Mathlib

namespace OMA.A005329Proof

open OMA.S_oeis_a005329 Finset

theorem kj (m j : ℕ) (x : ℤ) :
    ∑ k ∈ range (m + 1), (m.choose k : ℤ) * (k.choose j : ℤ) * x ^ (m - k) =
      (m.choose j : ℤ) * (x + 1) ^ (m - j) := by
  rcases lt_or_ge m j with hj | hj
  · rw [Nat.choose_eq_zero_of_lt hj, Nat.cast_zero, zero_mul]
    apply sum_eq_zero
    intro k hk
    rw [mem_range] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega : k < j)]
    simp
  · obtain ⟨N, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [show j + N + 1 = j + (N + 1) by ring, sum_range_add]
    have h0 : ∑ k ∈ range j, ((j + N).choose k : ℤ) * (k.choose j : ℤ) * x ^ (j + N - k) = 0 := by
      apply sum_eq_zero
      intro k hk
      rw [mem_range] at hk
      rw [Nat.choose_eq_zero_of_lt hk]
      simp
    rw [h0, zero_add, Nat.add_sub_cancel_left, add_comm x 1, add_pow, mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [mem_range] at hi
    have hc : (j + N).choose (j + i) * (j + i).choose j = (j + N).choose j * N.choose i := by
      rw [Nat.choose_mul (by omega : j ≤ j + i), Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
    have hc' : ((j + N).choose (j + i) : ℤ) * ((j + i).choose j : ℤ) =
        ((j + N).choose j : ℤ) * (N.choose i : ℤ) := by exact_mod_cast hc
    rw [show j + N - (j + i) = N - i by omega, one_pow, one_mul, hc']
    ring

theorem a_succ (k : ℕ) : a (k + 1) = (2 ^ (k + 1) - 1) * a k := by
  unfold a
  rw [prod_Icc_succ_top (by omega : 1 ≤ k + 1)]
  ring

theorem a_zero : a 0 = 1 := by simp [a]

theorem pascal (f : ℕ → ℤ) (n : ℕ) :
    ∑ k ∈ range (n + 2), ((n + 1).choose k : ℤ) * f k =
      ∑ k ∈ range (n + 1), (n.choose k : ℤ) * (f k + f (k + 1)) := by
  have e1 : ∑ k ∈ range (n + 1), (n.choose k : ℤ) * f k =
      ∑ k ∈ range n, (n.choose (k + 1) : ℤ) * f (k + 1) + f 0 := by
    rw [sum_range_succ']; simp
  have e2 : ∑ k ∈ range (n + 1), (n.choose (k + 1) : ℤ) * f (k + 1) =
      ∑ k ∈ range n, (n.choose (k + 1) : ℤ) * f (k + 1) := by
    rw [sum_range_succ]; simp
  rw [sum_range_succ' _ (n + 1)]
  simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, sum_add_distrib, mul_add,
    Nat.choose_zero_right, Nat.cast_one, one_mul]
  rw [e1, e2]
  ring

noncomputable def cp (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), (n.choose k : ℤ) * a k

noncomputable def bp (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), (n.choose k : ℤ) * (2 ^ k * a k)

theorem cp_succ (n : ℕ) : cp (n + 1) = 2 * bp n := by
  unfold cp bp
  rw [pascal, mul_sum]
  apply sum_congr rfl
  intro k _
  rw [a_succ, pow_succ]
  ring

theorem ext_sum (k m : ℕ) (hk : k ≤ m) (g : ℕ → ℤ) :
    ∑ j ∈ range (k + 1), (k.choose j : ℤ) * g j = ∑ j ∈ range (m + 1), (k.choose j : ℤ) * g j := by
  apply sum_subset
  · intro j; simp only [mem_range]; omega
  · intro j _ hj
    rw [mem_range] at hj
    rw [Nat.choose_eq_zero_of_lt (by omega : k < j)]
    simp

theorem bp_sum (m : ℕ) : ∑ k ∈ range (m + 1), (m.choose k : ℤ) * bp k = 2 ^ m * cp m := by
  unfold bp cp
  have h1 : ∑ k ∈ range (m + 1), (m.choose k : ℤ) *
      ∑ j ∈ range (k + 1), (k.choose j : ℤ) * (2 ^ j * a j) =
      ∑ k ∈ range (m + 1), ∑ j ∈ range (m + 1),
        (m.choose k : ℤ) * (k.choose j : ℤ) * 1 ^ (m - k) * (2 ^ j * a j) := by
    apply sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    rw [ext_sum k m (by omega), mul_sum]
    apply sum_congr rfl
    intro j _
    ring
  rw [h1, sum_comm, mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  rw [← sum_mul, kj]
  rw [show (1 : ℤ) + 1 = 2 by norm_num]
  have : (2 : ℤ) ^ (m - j) * 2 ^ j = 2 ^ m := by
    rw [← pow_add]; congr 1; omega
  linear_combination (m.choose j : ℤ) * a j * this

theorem b_eq : ∀ n, b n = bp n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [b, bp, a_zero]
    | succ n =>
      rw [b]
      rw [Fin.sum_univ_eq_sum_range (fun k => ((n + 1).choose k : ℤ) * b k) (n + 1)]
      have hs : ∑ k ∈ range (n + 1), ((n + 1).choose k : ℤ) * b k =
          ∑ k ∈ range (n + 1), ((n + 1).choose k : ℤ) * bp k := by
        apply sum_congr rfl
        intro k hk
        rw [mem_range] at hk
        rw [ih k (by omega)]
      rw [hs, ih n (by omega)]
      have h := bp_sum (n + 1)
      rw [sum_range_succ, Nat.choose_self, Nat.cast_one, one_mul, cp_succ] at h
      rw [pow_succ 2 (n + 1)]
      linear_combination -h

theorem c_eq (n : ℕ) : c n = cp n := by
  cases n with
  | zero => simp [c, cp, a_zero]
  | succ n => rw [c, cp_succ, b_eq]

end OMA.A005329Proof

open OMA.A005329Proof Finset in
theorem OMA.solution : type_of% @OMA.S_oeis_a005329.main := by
  intro n
  simp_rw [c_eq]
  unfold cp
  have h1 : ∑ k ∈ range (n + 1), (-1 : ℤ) ^ (n - k) * (n.choose k : ℤ) *
      ∑ j ∈ range (k + 1), (k.choose j : ℤ) * OMA.S_oeis_a005329.a j =
      ∑ k ∈ range (n + 1), ∑ j ∈ range (n + 1),
        (n.choose k : ℤ) * (k.choose j : ℤ) * (-1) ^ (n - k) * OMA.S_oeis_a005329.a j := by
    apply sum_congr rfl
    intro k hk
    rw [mem_range] at hk
    rw [ext_sum k n (by omega), mul_sum]
    apply sum_congr rfl
    intro j _
    ring
  rw [h1, sum_comm]
  simp_rw [← sum_mul, kj]
  rw [sum_eq_single n]
  · simp
  · intro j hj hjn
    rw [mem_range] at hj
    rw [show (-1 : ℤ) + 1 = 0 by norm_num, zero_pow (by omega)]
    simp
  · intro h; simp at h
