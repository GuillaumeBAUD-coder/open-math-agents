import OMAReductions.R_oeis_a007691_R1
import Mathlib

/-! Step oeis-a007691.R1.H1 (Euclid): if `M = 2^(k+1) - 1` is prime then `2^k M` is perfect.
`σ` is multiplicative and `2^k`, `M` are coprime, so `σ(2^k M) = (2^(k+1) - 1)(M + 1) = 2 · 2^k M`. -/

namespace OMA.A007691H1

open ArithmeticFunction

theorem main (k : ℕ) (h : (2 ^ (k + 1) - 1).Prime) : Nat.Perfect (2 ^ k * (2 ^ (k + 1) - 1)) := by
  set M := 2 ^ (k + 1) - 1 with hM
  have h1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  have hodd : Odd M := by
    rcases h.eq_two_or_odd' with h2 | h2
    · exfalso
      have : 2 ^ (k + 1) = 3 := by omega
      have := congrArg (· % 2) this
      simp [pow_succ] at this
    · exact h2
  have hcop : Nat.Coprime (2 ^ k) M := by
    apply Nat.Coprime.pow_left
    exact (Nat.coprime_two_left).2 hodd
  have hpos : 0 < 2 ^ k * M := Nat.mul_pos (by positivity) h.pos
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_apply_prime_pow Nat.prime_two,
    Nat.geomSum_eq (le_refl 2)]
  have hsM : sigma 1 M = M + 1 := by
    have := sigma_one_apply_prime_pow (i := 1) h
    simpa [Finset.sum_range_succ, add_comm] using this
  rw [hsM, show (2 : ℕ) - 1 = 1 from rfl, Nat.div_one]
  have : M + 1 = 2 ^ (k + 1) := by omega
  rw [this, ← hM, pow_succ]
  ring

end OMA.A007691H1

theorem OMA.solution : OMA.R_oeis_a007691_R1.H1 :=
  OMA.A007691H1.main
