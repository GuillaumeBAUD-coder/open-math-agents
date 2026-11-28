import Mathlib

/-!
# A003313: the Knuth–Stolarsky lower bound for addition chains

Source: https://oeis.org/A003313
Credit: @jagraj28

A003313 is `a(n) = ℓ(n)`, the length of a shortest addition chain for `n`. The entry records the
conjecture of D. E. Knuth, K. Stolarsky et al. that for all `n`:
`floor(log_2(n)) + ceiling(log_2(v(n))) ≤ a(n)`, where `v(n) = A000120(n)` is the number of 1s in
the binary expansion of `n`.

Conventions:
* An addition chain for `n` of length `r` is a sequence `c 0, c 1, ..., c r` with `c 0 = 1`,
  `c r = n`, and every later term a sum `c i = c j + c k` of two earlier terms (`j, k < i`,
  `j = k` allowed). The terms are not required to increase: removing repeated or useless terms
  and sorting turns any chain into an increasing one that is not longer, so the shortest length
  is the same as with the usual increasing chains.
* `ℓ(n)` is the least such `r`. The sequence starts at `n = 1` (`ℓ(1) = 0`), so `main` is
  stated for `n ≥ 1`.
* `floor(log_2 n)` is `Nat.log 2 n` and `ceiling(log_2 m)` is `Nat.clog 2 m`; `v(n)` is the
  sum of the binary digits of `n`.
-/

namespace OMA.S_oeis_a003313

/-- There is an addition chain of length `r` that ends at `n`. -/
def HasChain (n r : ℕ) : Prop :=
  ∃ c : ℕ → ℕ, c 0 = 1 ∧ c r = n ∧
    ∀ i, 1 ≤ i → i ≤ r → ∃ j k, j < i ∧ k < i ∧ c i = c j + c k

/-- `ℓ(n)`, OEIS A003313: the length of a shortest addition chain for `n`. -/
noncomputable def ell (n : ℕ) : ℕ := sInf {r : ℕ | HasChain n r}

/-- `v(n)`, OEIS A000120: the number of 1s in the binary expansion of `n`. -/
def v (n : ℕ) : ℕ := (Nat.digits 2 n).sum

/-- The Knuth–Stolarsky conjecture quoted in OEIS A003313. -/
theorem main : ∀ n : ℕ, 1 ≤ n → Nat.log 2 n + Nat.clog 2 (v n) ≤ ell n := by
  sorry

end OMA.S_oeis_a003313
