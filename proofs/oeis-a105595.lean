import OMAStatements.S_oeis_a105595
import Mathlib

/-!
Credit: @ivillar
Proof (as in the OEIS entry, Bing Gao): work in ZMod 2, where x mod 2 and x agree. Then the
n-th row sum is Sum_j s_j Sum_{k=0..n} binomial(j, k) = Sum_j s_j 2^j with
s_j = abs(mu(binomial(n, j))), and 2^j = 0 in ZMod 2 for j >= 1, so the sum is
s_0 = abs(mu(1)) = 1.
-/

namespace OMAA105595Helpers

theorem cmod (x : ℤ) : ((x % 2 : ℤ) : ZMod 2) = (x : ZMod 2) := by
  have := ZMod.intCast_mod x 2
  simpa using this

theorem choose_sum (n j : ℕ) (hj : j ≤ n) :
    ∑ k ∈ Finset.range (n + 1), j.choose k = 2 ^ j := by
  have h1 : ∑ k ∈ Finset.range (j + 1), j.choose k = ∑ k ∈ Finset.range (n + 1), j.choose k := by
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_range] at hk ⊢
      omega
    · intro k _ hk
      simp only [Finset.mem_range] at hk
      exact Nat.choose_eq_zero_of_lt (by omega)
  rw [← h1, Nat.sum_range_choose]

end OMAA105595Helpers

open OMAA105595Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a105595.main := by
  intro n
  rw [← ZMod.intCast_eq_one_iff_odd]
  unfold OMA.S_oeis_a105595.a OMA.S_oeis_a105595.T
  simp only [Int.cast_sum, Int.cast_mul, cmod, Int.cast_natCast]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  have h2 : ∀ j ∈ Finset.range (n + 1),
      ((|ArithmeticFunction.moebius (n.choose j)| : ℤ) : ZMod 2) *
        ∑ k ∈ Finset.range (n + 1), ((j.choose k : ℕ) : ZMod 2) =
      ((|ArithmeticFunction.moebius (n.choose j)| : ℤ) : ZMod 2) * 2 ^ j := by
    intro j hj
    rw [← Nat.cast_sum, choose_sum n j (by have := Finset.mem_range.mp hj; omega)]
    push_cast
    ring
  rw [Finset.sum_congr rfl h2, Finset.sum_range_succ']
  have h0 : ∀ j ∈ Finset.range n,
      ((|ArithmeticFunction.moebius (n.choose (j + 1))| : ℤ) : ZMod 2) * 2 ^ (j + 1) = 0 := by
    intro j _
    rw [pow_succ, show (2 : ZMod 2) = 0 by decide, mul_zero, mul_zero]
  rw [Finset.sum_eq_zero h0]
  simp
