import Mathlib

namespace OMA.S_oeis_a008687

/-- OEIS A008687: number of 1's in 2's complement representation of `-n`,
satisfying `a(0) = 0`, `a(1) = 1`, and `a(n) = (n % 2) + a((n % 2) + n / 2)` for `n ≥ 2`. -/
def a008687 : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => ((n + 2) % 2) + a008687 (((n + 2) % 2) + (n + 2) / 2)
termination_by n => n

/-- The `m`-th interval `((a, b), (c, d))` in the Stern-Brocot subtree on `(0, 1)` (`m ≥ 1`),
starting from `sbInterval 1 = ((0, 1), (1, 1))`, with left child `2*m` and right child `2*m + 1`. -/
def sbInterval : ℕ → (ℕ × ℕ) × (ℕ × ℕ)
  | 0 => ((0, 1), (1, 1))
  | 1 => ((0, 1), (1, 1))
  | n + 2 =>
      let ((a, b), (c, d)) := sbInterval ((n + 2) / 2)
      if (n + 2) % 2 = 0 then ((a, b), (a + c, b + d))
      else ((a + c, b + d), (c, d))
termination_by n => n

/-- The Stern-Brocot fraction `A007305(n) / A007306(n)` for `n ≥ 2` (mediant of `sbInterval (n - 1)`). -/
def sbFrac (n : ℕ) : ℕ × ℕ :=
  let ((a, b), (c, d)) := sbInterval (n - 1)
  (a + c, b + d)

/-- Length of the Hirzebruch (negative) continued fraction `[b_0; b_1, ..., b_{L-1}]^-`
for a positive rational `p / q` (`q ≥ 1`): equals `1` if `q ∣ p`, and otherwise
`1 + hirzLen q ((p / q + 1) * q - p)`. -/
def hirzLen (p q : ℕ) : ℕ :=
  if hq : q = 0 then 0
  else if q ∣ p then 1
  else 1 + hirzLen q ((p / q + 1) * q - p)
termination_by q
decreasing_by
  have hlt : p % q < q := Nat.mod_lt p (Nat.pos_of_ne_zero hq)
  have _hne : p % q ≠ 0 := fun h => ‹¬q ∣ p› (Nat.dvd_of_mod_eq_zero h)
  have hdiv : q * (p / q) + p % q = p := Nat.div_add_mod p q
  have hmul : (p / q + 1) * q = q * (p / q) + q := by ring
  omega

/-- Conjecture on OEIS A008687:
For every `n ≥ 2`, `a008687 n + 1` equals the length of the Hirzebruch (negative)
continued fraction for the Stern-Brocot tree fraction `A007305(n) / A007306(n)`. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n → hirzLen (sbFrac n).1 (sbFrac n).2 = a008687 n + 1 := by
  sorry

end OMA.S_oeis_a008687
