import OMAStatements.S_oeis_a109516
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

namespace OMA.P_oeis_a109516

open OMA.S_oeis_a109516

/-- Parametric Fibonacci-type polynomial `F(x, m)` with `F(x, 0) = 0`, `F(x, 1) = 1`,
`F(x, m + 2) = x * F(x, m + 1) + x * F(x, m)`. -/
private def F (x : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | m + 2 => x * F x (m + 1) + x * F x m

private lemma mat_pow_eq (x m : ℕ) :
    (!![0, 1; x, x] : Matrix (Fin 2) (Fin 2) ℕ) ^ (m + 1) =
      !![x * F x m, F x (m + 1); x * F x (m + 1), F x (m + 2)] := by
  induction m with
  | zero =>
    simp [F]
  | succ m ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, F] <;> ring

/-- The binomial sum `G(x, n) = ∑_{k=0}^{n} C(n - k, k) * x^(n - k)` equals `F(x, n + 1)`. -/
private def G (x n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), Nat.choose (n - k) k * x ^ (n - k)

private lemma G_eq_half_sum (x n : ℕ) :
    G x n = ∑ k ∈ Finset.range (n / 2 + 1), Nat.choose (n - k) k * x ^ (n - k) := by
  unfold G
  symm
  apply Finset.sum_subset
  · intro k hk
    rw [Finset.mem_range] at hk ⊢
    omega
  · intro k hk hnot
    rw [Finset.mem_range] at hk hnot
    have hlt : n - k < k := by omega
    rw [Nat.choose_eq_zero_of_lt hlt, zero_mul]

private lemma G_zero (x : ℕ) : G x 0 = 1 := by
  simp [G]

private lemma G_one (x : ℕ) : G x 1 = x := by
  simp [G, Finset.sum_range_succ]

private lemma G_succ_succ (x n : ℕ) :
    G x (n + 2) = x * G x (n + 1) + x * G x n := by
  unfold G
  rw [Finset.sum_range_succ']
  simp only [Nat.sub_zero, Nat.choose_zero_right, one_mul]
  -- Split remaining terms k + 1 using Pascal's identity on C(n + 1 - k, k + 1)
  have hsplit :
      ∑ k ∈ Finset.range (n + 2), Nat.choose (n + 2 - (k + 1)) (k + 1) * x ^ (n + 2 - (k + 1)) =
        (∑ k ∈ Finset.range (n + 2), Nat.choose (n - k) (k + 1) * x ^ (n + 1 - k)) +
        (∑ k ∈ Finset.range (n + 2), Nat.choose (n - k) k * x ^ (n + 1 - k)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    by_cases hkn : k ≤ n
    · have h1 : n + 2 - (k + 1) = (n - k) + 1 := by omega
      have h2 : n + 1 - k = (n - k) + 1 := by omega
      rw [h1, h2, Nat.choose_succ_succ, add_mul]
      ring
    · have hkn1 : k = n + 1 := by omega
      subst hkn1
      simp
  rw [hsplit]
  -- First sum plus x^(n+2) equals x * G x (n + 1)
  have hA :
      (∑ k ∈ Finset.range (n + 2), Nat.choose (n - k) (k + 1) * x ^ (n + 1 - k)) + x ^ (n + 2) =
        x * ∑ k ∈ Finset.range (n + 2), Nat.choose (n + 1 - k) k * x ^ (n + 1 - k) := by
    rw [Finset.sum_range_succ' (fun k => Nat.choose (n + 1 - k) k * x ^ (n + 1 - k))]
    simp only [Nat.sub_zero, Nat.choose_zero_right, one_mul, mul_add, Finset.mul_sum]
    rw [show x * x ^ (n + 1) = x ^ (n + 2) by ring]
    congr 1
    rw [Finset.sum_range_succ]
    have hlast : Nat.choose (n - (n + 1)) (n + 1 + 1) * x ^ (n + 1 - (n + 1)) = 0 := by simp
    rw [hlast, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have h1 : n + 1 - (k + 1) = n - k := by omega
    have h2 : n + 1 - k = (n - k) + 1 := by omega
    rw [h1, h2, pow_succ]
    ring
  -- Second sum equals x * G x n
  have hB :
      ∑ k ∈ Finset.range (n + 2), Nat.choose (n - k) k * x ^ (n + 1 - k) =
        x * ∑ k ∈ Finset.range (n + 1), Nat.choose (n - k) k * x ^ (n - k) := by
    rw [Finset.sum_range_succ, Finset.mul_sum]
    have hlast : Nat.choose (n - (n + 1)) (n + 1) * x ^ (n + 1 - (n + 1)) = 0 := by simp
    rw [hlast, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have h2 : n + 1 - k = (n - k) + 1 := by omega
    rw [h2, pow_succ]
    ring
  linarith

private lemma F_succ_eq_G (x : ℕ) : ∀ n : ℕ, F x (n + 1) = G x n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp [F, G_zero]
    | 1 => simp [F, G_one]
    | k + 2 =>
      rw [G_succ_succ, F]
      rw [ih (k + 1) (by omega), ih k (by omega)]

private lemma prove_main :
    ∀ n : ℕ, a109516 (n + 1) =
      ∑ k ∈ Finset.range (n / 2 + 1), Nat.choose (n - k) k * n ^ (n - k) := by
  intro n
  unfold a109516
  have hmat : matA109516 (n + 1) = !![0, 1; n, n] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matA109516]
  rw [hmat, mat_pow_eq n n]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [F_succ_eq_G, G_eq_half_sum]

end OMA.P_oeis_a109516

theorem OMA.solution : type_of% @OMA.S_oeis_a109516.main :=
  OMA.P_oeis_a109516.prove_main
