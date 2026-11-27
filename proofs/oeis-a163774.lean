import OMAStatements.S_oeis_a163774
import Mathlib

/-!
(2i)$ = binomial(2i, i). Swapping the double sum, a(n) = Sum_i (-1)^(n-i) binomial(2i,i)
Sum_{k=0..i} binomial(n-k, n-i), and the inner sum is binomial(n+1, i) by the hockey stick
identity Sum_{k=0..i} binomial(m+i-k, m) = binomial(m+i+1, i).
-/

namespace R163774
open OMA.S_oeis_a163774

theorem swing_two (i : ℕ) : swing (2 * i) = (2 * i).choose i := by
  rw [swing, show 2 * i / 2 = i by omega, Nat.choose_eq_factorial_div_factorial (by omega),
    show 2 * i - i = i by omega, sq]

theorem hockey (m i : ℕ) :
    ∑ k ∈ Finset.range (i + 1), (m + i - k).choose m = (m + i + 1).choose i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ']
    have h : ∑ k ∈ Finset.range (i + 1), (m + (i + 1) - (k + 1)).choose m =
        ∑ k ∈ Finset.range (i + 1), (m + i - k).choose m := by
      apply Finset.sum_congr rfl
      intro k _
      congr 1
      omega
    rw [h, ih, Nat.sub_zero, Nat.choose_symm_add, Nat.choose_succ_succ (m + (i + 1)) i]
    rfl

theorem inner (n i : ℕ) (h : i ≤ n) :
    ∑ k ∈ Finset.range (i + 1), (n - k).choose (n - i) = (n + 1).choose i := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + i := ⟨n - i, by omega⟩
  rw [Nat.add_sub_cancel, hockey]

theorem solve : ∀ n : ℕ, a n = ∑ k ∈ Finset.range (n + 1),
      (-1) ^ (n - k) * ((n + 1).choose k : ℤ) * ((2 * k).choose k : ℤ) := by
  intro n
  unfold a T
  rw [Finset.sum_comm' (t' := Finset.range (n + 1)) (s' := fun i => Finset.range (i + 1))]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [← Finset.sum_mul, ← Finset.mul_sum, swing_two, ← Nat.cast_sum, inner n i (by omega)]
  · intro k i
    simp only [Finset.mem_range, Finset.mem_Icc]
    omega

end R163774

theorem OMA.solution : type_of% @OMA.S_oeis_a163774.main := R163774.solve
