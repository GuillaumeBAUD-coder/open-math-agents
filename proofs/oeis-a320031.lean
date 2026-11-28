import OMAStatements.S_oeis_a320031
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Werner Schulte's conjecture for OEIS A320031.

Multiplying by `k!`, the claim is `A(n, k) = ∑_{i ≤ n} C(k, i) L(n, i)` with `L = A371898` (the
terms with `i > k` vanish). Both sides satisfy `X(n + 1, k) = 1 + (n + 1) k X(n, k)` and equal `1`
at `n = 0`. For `A` this follows from `C(n + 1, j + 1) (j + 1) = (n + 1) C(n, j)`. For the right
side, `C(k + 1, i + 1) (i + 1) = (k + 1) C(k, i)` turns the recurrence of `L` into
`∑ C(k, i) (L(n, i) + L(n, i + 1)) = ∑ C(k + 1, i) L(n, i)`, which is Pascal's rule together with
`L(n, n + 1) = 0`. -/

namespace OpenMath.A320031

open Finset OMA.S_oeis_a320031

private theorem L_zero : ∀ n i : ℕ, n < i → a371898 n i = 0
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, i + 1, _ => rfl
  | n + 1, i + 1, h => by
    simp [a371898, L_zero n i (by omega), L_zero n (i + 1) (by omega)]

private theorem A_succ (n k : ℕ) : a320031 (n + 1) k = 1 + (n + 1) * k * a320031 n k := by
  unfold a320031
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [Nat.choose_zero_right, Nat.factorial_zero, pow_zero, mul_one]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := Nat.add_one_mul_choose_eq n j
  rw [Nat.factorial_succ, pow_succ]
  calc _ = (Nat.choose (n + 1) (j + 1) * (j + 1)) * j.factorial * k ^ j * k := by ring
    _ = ((n + 1) * Nat.choose n j) * j.factorial * k ^ j * k := by rw [h]
    _ = _ := by ring

private theorem pascal_sum (n k : ℕ) :
    ∑ i ∈ range (n + 1), Nat.choose k i * (a371898 n i + a371898 n (i + 1)) =
      ∑ i ∈ range (n + 1), Nat.choose (k + 1) i * a371898 n i := by
  have hz : a371898 n (n + 1) = 0 := L_zero n (n + 1) (by omega)
  simp only [mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ (fun i => Nat.choose k i * a371898 n (i + 1)), hz, mul_zero,
    add_zero, Finset.sum_range_succ' (fun i => Nat.choose k i * a371898 n i),
    Finset.sum_range_succ' (fun i => Nat.choose (k + 1) i * a371898 n i)]
  simp only [Nat.choose_succ_succ, add_mul, Finset.sum_add_distrib, Nat.choose_zero_right]
  ring

private theorem B_succ (n k : ℕ) :
    ∑ i ∈ range (n + 1 + 1), Nat.choose k i * a371898 (n + 1) i =
      1 + (n + 1) * k * ∑ i ∈ range (n + 1), Nat.choose k i * a371898 n i := by
  rw [Finset.sum_range_succ']
  rcases k with _ | k
  · simp [a371898]
  · simp only [a371898, Nat.choose_zero_right, one_mul]
    rw [← pascal_sum n k, Finset.mul_sum, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := Nat.add_one_mul_choose_eq k i
    calc _ = (Nat.choose (k + 1) (i + 1) * (i + 1)) * (n + 1) *
          (a371898 n i + a371898 n (i + 1)) := by ring
      _ = ((k + 1) * Nat.choose k i) * (n + 1) * (a371898 n i + a371898 n (i + 1)) := by
          rw [h]
      _ = _ := by ring

private theorem AB : ∀ n k : ℕ,
    a320031 n k = ∑ i ∈ range (n + 1), Nat.choose k i * a371898 n i := by
  intro n
  induction n with
  | zero =>
    intro k
    simp [a320031, a371898]
  | succ n ih =>
    intro k
    rw [A_succ, ih k, B_succ]

theorem main :
    ∀ n k : ℕ,
      (a320031 n k : ℚ) / (k.factorial : ℚ) =
        ∑ i ∈ Finset.range (min k n + 1),
          (1 / ((k - i).factorial : ℚ)) * ((a371898 n i : ℚ) / (i.factorial : ℚ)) := by
  intro n k
  have hsub : ∑ i ∈ range (min k n + 1), Nat.choose k i * a371898 n i =
      ∑ i ∈ range (n + 1), Nat.choose k i * a371898 n i := by
    apply Finset.sum_subset
    · intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    · intro i hi hi'
      simp only [Finset.mem_range] at hi hi'
      rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
  rw [AB, ← hsub, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := by
    simp only [Finset.mem_range] at hi
    omega
  rw [Nat.cast_mul, Nat.cast_choose ℚ hik]
  have h1 : (k.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have h2 : (i.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have h3 : ((k - i).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  first
    | (field_simp; ring)
    | field_simp

end OpenMath.A320031

theorem OMA.solution : type_of% @OMA.S_oeis_a320031.main := OpenMath.A320031.main
