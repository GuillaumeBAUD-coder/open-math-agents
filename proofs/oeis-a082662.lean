import OMAStatements.S_oeis_a082662

/-! OEIS A082662, (P1) ⇔ (P7): both sides say `s < 2 ^ (m + 1)`. Cancelling `s > 0`,
`s ^ 2 < 2 (2 ^ m s)` is `s < 2 ^ (m + 1)`, and `σ (2 ^ m) = ∑_{i ≤ m} 2 ^ i = 2 ^ (m + 1) - 1`. -/

namespace OpenMath.A082662

theorem main (m s : ℕ) (_hs : Odd s) (hs0 : 0 < s) :
    s ^ 2 < 2 * (2 ^ m * s) ↔ s ≤ ∑ d ∈ (2 ^ m).divisors, d := by
  have hgeom : ∀ n, ∑ i ∈ Finset.range n, 2 ^ i + 1 = 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      omega
  have key : s ^ 2 < 2 * (2 ^ m * s) ↔ s < 2 * 2 ^ m := by
    rw [show s ^ 2 = s * s by ring, show 2 * (2 ^ m * s) = 2 * 2 ^ m * s by ring]
    exact Nat.mul_lt_mul_right hs0
  rw [key, Nat.sum_divisors_prime_pow Nat.prime_two]
  have h1 := hgeom (m + 1)
  rw [pow_succ] at h1
  constructor <;> intro h <;> omega

end OpenMath.A082662

theorem OMA.solution : type_of% @OMA.S_oeis_a082662.main := OpenMath.A082662.main
