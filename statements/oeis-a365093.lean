import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Lattice.Nat

namespace OMA.S_oeis_a365093

/-- `A365092 n`: recursively replace each prime factor `p` in the canonical prime factorization
of `n` by `(p - 1) + 1`, recursively factorizing `p - 1` (if `p > 2`) and each exponent `e > 1`,
and count the total number of `1`s used (with `A365092 0 = A365092 1 = 0`). -/
def A365092 : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 =>
    ∑ p ∈ (n + 2).primeFactors.attach,
      ((if p.1 = 2 then 2 else 1 + A365092 (p.1 - 1)) + A365092 ((n + 2).factorization p.1))
termination_by n => n
decreasing_by
  · have hp := Nat.mem_primeFactors.mp p.2
    have hle := Nat.le_of_dvd (by omega) hp.2.1
    have h2 := hp.1.two_le
    omega
  · have hp := Nat.mem_primeFactors.mp p.2
    have h2 := hp.1.two_le
    have hpow : p.1 ^ (n + 2).factorization p.1 ≤ n + 2 :=
      Nat.le_of_dvd (by omega) (Nat.ordProj_dvd (n + 2) p.1)
    have hlt : (n + 2).factorization p.1 < 2 ^ (n + 2).factorization p.1 :=
      Nat.lt_two_pow_self
    have hmono : 2 ^ (n + 2).factorization p.1 ≤ p.1 ^ (n + 2).factorization p.1 :=
      Nat.pow_le_pow_left h2 _
    omega

/-- `a(n)` (OEIS A365093): the smallest positive integer `k` such that `A365092 k = n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ A365092 k = n}

/-- Conjecture (OEIS A365093): for all `m, n ≥ 2`, `a(m + n) ≤ a(m) * a(n)`.
(Disproved at `m = 14, n = 14`, where `a(14) = 47`, `a(14) * a(14) = 2209`, and `a(28) = 2447`.) -/
theorem main : ∀ m n : ℕ, 2 ≤ m → 2 ≤ n → a (m + n) ≤ a m * a n := by
  sorry

end OMA.S_oeis_a365093
