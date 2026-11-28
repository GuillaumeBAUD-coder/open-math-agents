import Mathlib

/-!
# A140358: Smallest nonnegative integer k such that n = +-1+-2+-...+-k

Source: https://oeis.org/A140358
Credit: @xor2k

Formalizes the OEIS A140358 conjecture:
Conjecture when n is greater than 0. Choose k so that t(k)<=n<t(k+1) where t(n) is the n-th
triangular number t(n)=n(n+1)/2. If n=t(k), a(n)=k, otherwise if k is odd then a(n)=k+2 if n-t(k) is
odd, a(n)=k+1 if n-t(k) is even, else if k is even than a(n)=k+1 if n-t(k) is odd, a(n)=k+3 if n-t(k)
is even. (This has been verified for n up to 100.)

Conventions:
* Offset 0; the sequence is indexed by natural numbers `n` (the entry also notes a(n) = a(-n) for
  integers, which is not part of the conjecture). The conjecture concerns `n > 0`.
* `a n` is the least `k : ℕ` such that `n = ∑_{i=1..k} ε i * i` for some choice of signs
  `ε i ∈ {1, -1}`, computed in `ℤ`; a sign function is given on all of `ℕ` but only its values on
  `1..k` enter the sum. For `k = 0` the sum is empty, so `a 0 = 0`. The set is nonempty for every
  `n`, so `sInf` is the true minimum.
* `t k = k * (k + 1) / 2` (exact division). The `k` chosen with `t k ≤ n < t (k + 1)` is unique, so it
  is universally quantified under these hypotheses. Since `t k ≤ n`, the natural subtraction
  `n - t k` does not truncate.
-/

namespace OMA.S_oeis_a140358

/-- The `k`-th triangular number `k (k + 1) / 2`. -/
def t (k : ℕ) : ℕ := k * (k + 1) / 2

/-- A140358: the smallest `k` such that `n = ±1 ± 2 ± ... ± k` for some choice of signs. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ ε : ℕ → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
    (n : ℤ) = ∑ i ∈ Finset.Icc 1 k, ε i * (i : ℤ)}

/-- For `n > 0` and `t k ≤ n < t (k + 1)`, the value of `a n` is given by the case formula. -/
theorem main :
    ∀ n k : ℕ, 0 < n → t k ≤ n → n < t (k + 1) →
      a n = if n = t k then k
        else if Odd k then (if Odd (n - t k) then k + 2 else k + 1)
        else (if Odd (n - t k) then k + 1 else k + 3) := by
  sorry

end OMA.S_oeis_a140358
