import Mathlib

/-!
# Take a square root when you can

Source: https://mathoverflow.net/questions/193603 (CC BY-SA 4.0).

For `n > 1` let `P_n = ∑_{p^e ∥ n} e · p²` (the sum of the squares of the prime factors of `n`, with
multiplicity), and `A_n = √P_n` if `P_n` is a perfect square, `A_n = P_n` otherwise. The asker conjectures
that iterating `A` from any `k > 1` eventually reaches a fixed point `A_n = n` (primes, and `27`).

We state the conjecture.

Formalization notes:
* `P n = n.factorization.sum (fun p e => e * p ^ 2)`; `A n = Nat.sqrt (P n)` when `P n` is a square.
* Iterates of `A` from `k > 1` stay `> 1`, so `A` is only ever applied where the question defines it.
* The asker notes the orbits of e.g. `30` and `60` grow to large numbers. Our check agrees: from
  `k = 20` the orbit exceeds `10^25` within 13 steps, so the conjecture is unsettled numerically.
-/

namespace OMA.S_mo_193603

/-- Iterating `A` from any `k > 1` reaches a fixed point of `A`. -/
theorem main :
    ∀ (k : ℕ) (hk : 1 < k),
    let P : ℕ → ℕ := fun n => n.factorization.sum (fun p e => e * p ^ 2)
    let A : ℕ → ℕ := fun n => if IsSquare (P n) then Nat.sqrt (P n) else P n
    ∃ m, A (A^[m] k) = A^[m] k := by
  sorry

end OMA.S_mo_193603
