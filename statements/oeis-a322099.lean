import Mathlib

/-!
# A322099: permutations with `Σ 1/(f(k)^2 - f(k+1)^2) = 0`

Source: https://oeis.org/A322099
Credit: @Lenqth

A322099(n) (offset 1) is the number of permutations `f` of `{1, ..., n}` with `f(1) < f(n)` and
`Σ_{k=1}^{n-1} 1/(f(k)^2 - f(k+1)^2) = 0`. For example `a(8) = 1`, witnessed by
`(4, 5, 2, 7, 3, 1, 6, 8)`.

Formalizes Z.-W. Sun's conjecture in the comments of A322099 (arXiv:1811.10503, MathOverflow
316208): `a(n) > 0` for all `n > 7`.

A permutation of `{1, ..., n}` is encoded as `f : Equiv.Perm (Fin n)`; its value at position
`i + 1` (`0 ≤ i < n`) is `f i + 1`, written `value f i` below. The sum is taken in `ℚ`.
-/

namespace OMA.S_oeis_a322099

/-- The value `f(i + 1)` of the permutation at position `i + 1`, as a natural number in
`{1, ..., n}` (and `0` outside the range, which is never used). -/
def value {n : ℕ} (f : Equiv.Perm (Fin n)) (i : ℕ) : ℕ :=
  if h : i < n then (f ⟨i, h⟩ : ℕ) + 1 else 0

/-- For every `n > 7` there is a permutation `f` of `{1, ..., n}` with `f(1) < f(n)` and
`Σ_{k=1}^{n-1} 1/(f(k)^2 - f(k+1)^2) = 0`. -/
theorem main : ∀ n : ℕ, 7 < n → ∃ f : Equiv.Perm (Fin n),
    value f 0 < value f (n - 1) ∧
    ∑ k ∈ Finset.range (n - 1),
      (1 : ℚ) / ((value f k : ℚ) ^ 2 - (value f (k + 1) : ℚ) ^ 2) = 0 := by
  sorry

end OMA.S_oeis_a322099
