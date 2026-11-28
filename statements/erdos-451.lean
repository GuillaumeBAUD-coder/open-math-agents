import Mathlib

/-!
# Erdős Problem 451

Source: https://www.erdosproblems.com/451
Credit: @mgv27

Estimate $n_k$, the smallest integer $>2k$ such that $\prod_{1\leq i\leq k}(n_k-i)$ has no prime
factor in $(k,2k)$.

Formalization notes:
* "Estimate" is not a yes/no question. The source page quotes Erdős [Er79d]: probably
  `n_k < e^{o(k)}` but `n_k > k^d` for every constant `d`. The lower half is now known: van Doorn
  and Tang proved `n_k > exp(c (log k)^2 / log log k)`, which beats every `k^d`. So `main` states
  the open upper half, `n_k < e^{o(k)}`, as `log(n_k) / k → 0`. (Adenwalla's easy bound gives
  `n_k ≤ ∏_{k<p<2k} p = e^{O(k)}`.)
* `n_k` is `sInf` of the set of `n > 2k` such that no prime `p` with `k < p < 2k` divides
  `∏_{i=1}^{k} (n - i)`. Since `n > 2k ≥ i`, the natural-number subtraction `n - i` is exact.
  The set is nonempty (any multiple `> 2k` of `∏_{k<p<2k} p` belongs to it: such `p` cannot
  divide `n - i` because `p ∤ i`), so `sInf` is the true minimum.
* Numeric check (pure Python): `n_1, …, n_15 = 3, 6, 9, 20, 13, 21, 21, 22, 65, 220, 51, 338,
  133, 321, 339`.
-/

namespace OMA.S_erdos_451

open Filter Topology

/-- `n_k`: the smallest integer `n > 2k` such that `∏_{1 ≤ i ≤ k} (n - i)` has no prime factor
in the open interval `(k, 2k)`. -/
noncomputable def nk (k : ℕ) : ℕ :=
  sInf {n : ℕ | 2 * k < n ∧
    ∀ p : ℕ, p.Prime → k < p → p < 2 * k → ¬ p ∣ ∏ i ∈ Finset.Icc 1 k, (n - i)}

/-- Erdős Problem 451 (Erdős's conjectured upper bound): `n_k < e^{o(k)}`, i.e.
`log(n_k) / k → 0`. -/
theorem main : Tendsto (fun k : ℕ => Real.log (nk k : ℝ) / (k : ℝ)) atTop (𝓝 0) := by
  sorry

end OMA.S_erdos_451
