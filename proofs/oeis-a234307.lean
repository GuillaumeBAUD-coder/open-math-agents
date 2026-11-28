import OMAStatements.S_oeis_a234307

/- Peter Bala's alternating gcd-sum conjecture, OEIS A234307.
   Proof and Lean formalization by KoaOkano with OpenAI Codex. -/

namespace A234307

open Finset

private theorem fromOne (f : ℕ → ℚ) (m : ℕ) :
    ∑ k ∈ Icc 1 m, f k = ∑ j ∈ range m, f (j + 1) := by
  have interval : Icc 1 m = Ico 1 (m + 1) := by
    ext k
    simp only [mem_Icc, mem_Ico]
    omega
  rw [interval, sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

private theorem pairs (f : ℕ → ℚ) (m : ℕ) :
    ∑ i ∈ range (2 * m), f (i + 1) =
      (∑ j ∈ range m, f (2 * j + 1)) + ∑ j ∈ range m, f (2 * (j + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, sum_range_succ,
      sum_range_succ, ih, sum_range_succ _ m, sum_range_succ _ m]
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega]
    ring

private theorem oddGcd (s n j : ℕ) :
    Nat.gcd (2 * j + 1) (2 ^ s * n) = Nat.gcd (2 * j + 1) n := by
  have cop : Nat.Coprime 2 (2 * j + 1) := Nat.coprime_two_left.mpr ⟨j, rfl⟩
  exact (cop.pow_left s).gcd_mul_left_cancel_right n

end A234307

open A234307 Finset OMA.S_oeis_a234307

theorem OMA.solution : type_of% @OMA.S_oeis_a234307.main := by
  intro n _
  let o (j : ℕ) : ℚ := Nat.gcd (2 * j + 1) n
  let g (k : ℕ) : ℚ := Nat.gcd k (4 * n)
  let h (k : ℕ) : ℚ := (-1) ^ k * (Nat.gcd k (8 * n) : ℚ)
  have hOdd (j : ℕ) : h (2 * j + 1) = -o j := by
    simp [h, o, pow_add, pow_mul]
    exact oddGcd 3 n j
  have hEven (j : ℕ) : h (2 * (j + 1)) = 2 * g (j + 1) := by
    simp [h, g, pow_mul, show 8 * n = 2 * (4 * n) by omega, Nat.gcd_mul_left]
  have gOdd (j : ℕ) : g (2 * j + 1) = o j := by
    exact congrArg (Nat.cast : ℕ → ℚ) (oddGcd 2 n j)
  have gEven (j : ℕ) : g (2 * (j + 1)) = 2 * (Nat.gcd (j + 1) (2 * n) : ℚ) := by
    simp [g, show 4 * n = 2 * (2 * n) by omega, Nat.gcd_mul_left]
  -- The odd indices in the second half give the same gcds as in the first half.
  have period (j : ℕ) : o (n + j) = o j := by
    simp [o, show 2 * (n + j) + 1 = (2 * j + 1) + 2 * n by omega]
  have twiceOdd : ∑ j ∈ range (2 * n), o j = 2 * ∑ j ∈ range n, o j := by
    rw [two_mul, sum_range_add]
    simp only [period]
    ring
  have original : (a n : ℚ) = ∑ j ∈ range n, (Nat.gcd (j + 1) (2 * n) : ℚ) := by
    unfold a
    push_cast
    rw [fromOne]
    apply sum_congr rfl
    intro j hj
    have hjn := mem_range.mp hj
    rw [Nat.gcd_sub_self_left (by omega), Nat.gcd_comm]
  change (a n : ℚ) = 1 / 4 * ∑ k ∈ Icc 1 (4 * n), h k
  rw [original, fromOne, show 4 * n = 2 * (2 * n) by omega, pairs h]
  simp only [hOdd, hEven, sum_neg_distrib, ← mul_sum, twiceOdd]
  rw [pairs g n]
  simp only [gOdd, gEven, ← mul_sum]
  ring
