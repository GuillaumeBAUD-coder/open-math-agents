import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Lattice.Nat

namespace OMA.S_oeis_a272032

/-- The number of consecutive composite numbers immediately smaller than `n`
(between the previous prime, or `1`, and `n`). -/
noncomputable def prevComp (n : ℕ) : ℕ :=
  n - 1 - sSup {p : ℕ | p < n ∧ (p.Prime ∨ p ≤ 1)}

/-- The number of consecutive composite numbers immediately greater than `n`
(between `n` and the following prime). -/
noncomputable def nextComp (n : ℕ) : ℕ :=
  sInf {p : ℕ | n < p ∧ p.Prime} - n - 1

/-- Conjecture (OEIS A272032): every positive integer `n` such that `q + r > 0` and
`(q^n + r^n) / (q + r)` is an integer prime (where `q = prevComp n` and `r = nextComp n`)
is itself prime. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      let q := prevComp n
      let r := nextComp n
      0 < q + r → (q + r) ∣ (q ^ n + r ^ n) → ((q ^ n + r ^ n) / (q + r)).Prime → n.Prime := by
  sorry

end OMA.S_oeis_a272032
