import Mathlib

/-!
# Ratios of partial zeta sums along OEIS A002387

Source: https://mathoverflow.net/questions/135496 (CC BY-SA 4.0).

Let `ζ_A^B(x) = ∑_{n=A}^{B} n^(-x)` and let `a_n = 1, 2, 4, 11, 31, 83, 227, …` (OEIS A002387, the least
`k` with harmonic number `H_k > n`). Numerical evidence suggests that
`e^(x-1) = lim_{n→∞} ζ_{a_n}^{a_{n+1}}(x) / ζ_{a_{n+1}}^{a_{n+2}}(x)` for all complex `x` except
`x = 1 + 2kπi` with `k ∈ ℤ \ {0}`. The asker asks whether this is known, proven or disproven.

We state the conjectured limit.

Formalization notes:
* `a n = sInf {k | n < H_k}` with `H_k = ∑_{i < k} 1/(i+1)`; this gives `a 0 = 1, a 1 = 2, a 2 = 4, a 3 = 11`.
* Both sums include both endpoints, as written in the question (`A ≤ B`, `ζ_A^B = ∑_{n=A}^B`).
* `m ^ x` is the complex power `(m : ℂ) ^ x` (all `m ≥ 1` here).
* Checked numerically at `n = 8, 10` for `x = 2, 1/2, -1, 1, 1+i, 3+2i`: the ratios agree with `e^(x-1)`
  to 4 or 5 digits, improving with `n`.
-/

namespace OMA.S_mo_135496

/-- `ζ_{a_n}^{a_{n+1}}(x) / ζ_{a_{n+1}}^{a_{n+2}}(x) → e^(x-1)` away from `x = 1 + 2kπi`, `k ≠ 0`. -/
theorem main :
    ∀ (x : ℂ) (hx : ∀ k : ℤ, k ≠ 0 → x ≠ 1 + 2 * k * Real.pi * Complex.I),
    let a : ℕ → ℕ := fun n => sInf {k : ℕ | (n : ℝ) < ∑ i ∈ Finset.range k, 1 / ((i : ℝ) + 1)}
    let z : ℕ → ℕ → ℂ := fun A B => ∑ m ∈ Finset.Icc A B, 1 / (m : ℂ) ^ x
    Filter.Tendsto (fun n => z (a n) (a (n + 1)) / z (a (n + 1)) (a (n + 2))) Filter.atTop
      (nhds (Complex.exp (x - 1))) := by
  sorry

end OMA.S_mo_135496
