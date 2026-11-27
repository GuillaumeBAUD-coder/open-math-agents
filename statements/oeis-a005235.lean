import Mathlib

/-!
# A005235: Fortunate numbers

Source: https://oeis.org/A005235
Credit: @enzo2

For n ≥ 1, let p_n be the n-th prime and p_n# the product of all primes ≤ p_n.
A005235 lists the least m > 1 such that m + p_n# is prime. Reo F. Fortune
conjectured that a(n) is always prime; that is the statement below.

The index follows the OEIS offset (a(1) = 3). `Nat.primorial p` is Mathlib's
product of the primes ≤ p, and `Nat.nth Nat.Prime (n - 1)` is p_n.
-/

namespace OMA.S_oeis_a005235

noncomputable def fortunate (n : ℕ) : ℕ :=
  letI := Classical.decPred (fun m : ℕ =>
    1 < m ∧ (m + primorial (Nat.nth Nat.Prime (n - 1))).Prime)
  Nat.find (show ∃ m : ℕ, 1 < m ∧
      (m + primorial (Nat.nth Nat.Prime (n - 1))).Prime from by
    obtain ⟨q, hq_ge, hq_prime⟩ :=
      Nat.exists_infinite_primes (primorial (Nat.nth Nat.Prime (n - 1)) + 2)
    refine ⟨q - primorial (Nat.nth Nat.Prime (n - 1)), by omega, ?_⟩
    rw [Nat.sub_add_cancel (by omega)]
    exact hq_prime)

theorem main : ∀ n : ℕ, 1 ≤ n → (fortunate n).Prime := by
  sorry

end OMA.S_oeis_a005235
