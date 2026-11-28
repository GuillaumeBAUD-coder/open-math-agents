import OMAStatements.S_oeis_a126016
import Mathlib

namespace OMA.A126016Proof

open OMA.S_oeis_a126016

lemma sigma_prime {p : ℕ} (hp : p.Prime) : ArithmeticFunction.sigma 1 p = p + 1 := by
  rw [ArithmeticFunction.sigma_one_apply, hp.sum_divisors, add_comm]

/-- For distinct primes, `s(p q) = 1 + p + q`. -/
lemma s_mul {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) : s (p * q) = p + q + 1 := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
  unfold s
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_prime hp,
    sigma_prime hq]
  have : (p + 1) * (q + 1) = p * q + (p + q + 1) := by ring
  rw [this]
  omega

theorem main_proof : ∀ n, InSeq n → Odd n → ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
    p + q = n - 1 → InSeq (p * q) := by
  intro n hn hodd p q hp hq hne hsum
  have hn1 : 1 ≤ n := hn.1
  have hs : s (p * q) = n := by rw [s_mul hp hq hne]; omega
  refine ⟨Nat.mul_pos hp.pos hq.pos, ?_⟩
  intro k
  cases k with
  | zero =>
    simp only [Function.iterate_zero, id]
    have := Nat.mul_le_mul hp.two_le hq.two_le
    omega
  | succ k =>
    rw [Function.iterate_succ_apply, hs]
    exact hn.2 k

end OMA.A126016Proof

open OMA.A126016Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a126016.main := main_proof
