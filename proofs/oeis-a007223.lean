import OMAStatements.S_oeis_a007223
import Mathlib

/-!
Since `gcd (n + 2) n = gcd 2 n`, the divisor sum has the term `k = 1` only for odd `n`, and the
terms `k = 1, 2` for even `n`. Segner's recurrence gives
`∑_{k=1}^{n-1} C_k C_{n-k} = C_{n+1} - 2 C_n`, and the binomial identity
`2 C(2n, n+2) = n (C_{n+1} - 2 C_n)` (from `(m+1) C_m = C(2m, m)` and neighbouring binomials)
matches the `k = 1` term. For `n = 2j` the `k = 2` term is `C(2j, j+1) = j C_j`.
-/

namespace R007223
open OMA.S_oeis_a007223

theorem segner (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 (n - 1), (catalan k : ℚ) * (catalan (n - k) : ℚ)
      = (catalan (n + 1) : ℚ) - 2 * (catalan n : ℚ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 : catalan (m + 1 + 1)
      = ∑ i ∈ Finset.range (m + 1 + 1), catalan i * catalan (m + 1 - i) :=
    (catalan_succ (m + 1)).trans
      (Finset.sum_range (fun i => catalan i * catalan (m + 1 - i))).symm
  have hr : Finset.range (m + 1 + 1) = insert 0 (insert (m + 1) (Finset.Icc 1 m)) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have n0 : (0 : ℕ) ∉ insert (m + 1) (Finset.Icc 1 m) := by
    intro h
    rw [Finset.mem_insert, Finset.mem_Icc] at h
    omega
  have n1 : m + 1 ∉ Finset.Icc 1 m := by
    intro h
    rw [Finset.mem_Icc] at h
    omega
  rw [hr, Finset.sum_insert n0, Finset.sum_insert n1] at h1
  simp only [Nat.sub_zero, Nat.sub_self, catalan_zero, one_mul, mul_one] at h1
  have h2 : (catalan (m + 1 + 1) : ℚ) = (catalan (m + 1) : ℚ) + ((catalan (m + 1) : ℚ)
      + ∑ i ∈ Finset.Icc 1 m, (catalan i : ℚ) * (catalan (m + 1 - i) : ℚ)) := by
    exact_mod_cast h1
  rw [show m + 1 - 1 = m by omega]
  linear_combination (-1 : ℚ) * h2

theorem keyA (n : ℕ) (hn : 1 ≤ n) :
    2 * ((Nat.choose (2 * n) (n + 2) : ℕ) : ℚ)
      = (n : ℚ) * ((catalan (n + 1) : ℚ) - 2 * (catalan n : ℚ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have f1 := succ_mul_catalan_eq_centralBinom (m + 1)
  have f2 := succ_mul_catalan_eq_centralBinom (m + 1 + 1)
  have f3 := Nat.succ_mul_centralBinom_succ (m + 1)
  have f4 := Nat.centralBinom_eq_two_mul_choose (m + 1)
  have f5 := Nat.choose_succ_right_eq (2 * (m + 1)) (m + 1)
  have f6 := Nat.choose_succ_right_eq (2 * (m + 1)) (m + 1 + 1)
  rw [show 2 * (m + 1) - (m + 1) = m + 1 by omega] at f5
  rw [show 2 * (m + 1) - (m + 1 + 1) = m by omega] at f6
  have q1 : ((m : ℚ) + 1 + 1) * (catalan (m + 1) : ℚ) = (Nat.centralBinom (m + 1) : ℚ) := by
    exact_mod_cast f1
  have q2 : ((m : ℚ) + 1 + 1 + 1) * (catalan (m + 1 + 1) : ℚ)
      = (Nat.centralBinom (m + 1 + 1) : ℚ) := by
    exact_mod_cast f2
  have q3 : ((m : ℚ) + 1 + 1) * (Nat.centralBinom (m + 1 + 1) : ℚ)
      = 2 * (2 * ((m : ℚ) + 1) + 1) * (Nat.centralBinom (m + 1) : ℚ) := by
    exact_mod_cast f3
  have q4 : (Nat.centralBinom (m + 1) : ℚ) = ((Nat.choose (2 * (m + 1)) (m + 1) : ℕ) : ℚ) := by
    exact_mod_cast f4
  have q5 : ((Nat.choose (2 * (m + 1)) (m + 1 + 1) : ℕ) : ℚ) * ((m : ℚ) + 1 + 1)
      = ((Nat.choose (2 * (m + 1)) (m + 1) : ℕ) : ℚ) * ((m : ℚ) + 1) := by
    exact_mod_cast f5
  have q6 : ((Nat.choose (2 * (m + 1)) (m + 1 + 1 + 1) : ℕ) : ℚ) * ((m : ℚ) + 1 + 1 + 1)
      = ((Nat.choose (2 * (m + 1)) (m + 1 + 1) : ℕ) : ℚ) * (m : ℚ) := by
    exact_mod_cast f6
  have hm : ((m + 1 : ℕ) : ℚ) = (m : ℚ) + 1 := Nat.cast_add_one m
  rw [show m + 1 + 2 = m + 1 + 1 + 1 by omega, hm]
  have hab : ((m : ℚ) + 2) * ((m : ℚ) + 3) ≠ 0 := by positivity
  apply mul_left_cancel₀ hab
  linear_combination 2 * (m : ℚ) * (q5 - ((m : ℚ) + 1) * q4) + 2 * ((m : ℚ) + 2) * q6
    - ((m : ℚ) + 1) * q3 - ((m : ℚ) + 2) * ((m : ℚ) + 1) * q2
    + 2 * ((m : ℚ) + 3) * ((m : ℚ) + 1) * q1

theorem keyB (j : ℕ) :
    2 * ((Nat.choose (2 * j) (j + 1) : ℕ) : ℚ) = 2 * (j : ℚ) * (catalan j : ℚ) := by
  have g1 := succ_mul_catalan_eq_centralBinom j
  have g2 := Nat.centralBinom_eq_two_mul_choose j
  have g3 := Nat.choose_succ_right_eq (2 * j) j
  rw [show 2 * j - j = j by omega] at g3
  have p1 : ((j : ℚ) + 1) * (catalan j : ℚ) = (Nat.centralBinom j : ℚ) := by
    exact_mod_cast g1
  have p2 : (Nat.centralBinom j : ℚ) = ((Nat.choose (2 * j) j : ℕ) : ℚ) := by
    exact_mod_cast g2
  have p3 : ((Nat.choose (2 * j) (j + 1) : ℕ) : ℚ) * ((j : ℚ) + 1)
      = ((Nat.choose (2 * j) j : ℕ) : ℚ) * (j : ℚ) := by
    exact_mod_cast g3
  have hj : (j : ℚ) + 1 ≠ 0 := by positivity
  apply mul_left_cancel₀ hj
  linear_combination 2 * p3 - 2 * (j : ℚ) * p1 - 2 * (j : ℚ) * p2

theorem solve : ∀ n : ℕ, 1 ≤ n → a007223 n = catalanConj n := by
  intro n hn
  have hS := segner n hn
  have hA := keyA n hn
  have hn0 : (n : ℚ) ≠ 0 := by
    have hn' : n ≠ 0 := by omega
    exact_mod_cast hn'
  unfold a007223 catalanConj
  rw [hS, Nat.gcd_self_add_left]
  rcases Nat.even_or_odd' n with ⟨j, hj | hj⟩
  · subst hj
    have hB := keyB j
    have hd : (2 : ℕ) ∣ 2 * j := dvd_mul_right 2 j
    have h12 : (1 : ℕ) ≠ 2 := by norm_num
    rw [Nat.gcd_eq_left hd, Nat.Prime.divisors Nat.prime_two, Finset.sum_pair h12, if_pos hd,
      Nat.div_one, Nat.div_one, show 2 * (2 * j) / 2 = 2 * j by omega,
      show (2 * j + 2) / 2 = j + 1 by omega, show 2 * j / 2 = j by omega,
      Nat.totient_one, Nat.totient_two, div_eq_div_iff hn0 two_ne_zero]
    push_cast at hA hB ⊢
    linear_combination hA + hB
  · subst hj
    have hg : Nat.gcd 2 (2 * j + 1) = 1 := by
      rw [Nat.gcd_rec, show (2 * j + 1) % 2 = 1 by omega, Nat.gcd_one_left]
    have hd : ¬ (2 : ℕ) ∣ 2 * j + 1 := by omega
    rw [hg, Nat.divisors_one, Finset.sum_singleton, if_neg hd, Nat.div_one, Nat.div_one,
      Nat.totient_one, div_eq_div_iff hn0 two_ne_zero]
    push_cast at hA ⊢
    linear_combination hA

end R007223

theorem OMA.solution : type_of% @OMA.S_oeis_a007223.main := by
  exact R007223.solve
