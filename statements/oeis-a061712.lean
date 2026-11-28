import Mathlib

/-!
# A061712: smallest prime with binary Hamming weight n

Source: https://oeis.org/A061712
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A061/A061712.seq
Credit: @Bondyboy2001

`a(n)` is the smallest prime whose binary expansion contains exactly `n` ones. T. D. Noe
conjectured in the OEIS entry that `a(n) < 2^(n+3)`.

The sequence offset is `1`, so the conjecture is stated for positive `n`.
-/

namespace OMA.S_oeis_a061712

/-- The binary Hamming weight of `n`. -/
def weight (n : ℕ) : ℕ := (Nat.digits 2 n).sum

/-- The smallest prime with binary Hamming weight `n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ weight p = n}

theorem main : ∀ n : ℕ, 1 ≤ n → a n < 2 ^ (n + 3) := by
  sorry

end OMA.S_oeis_a061712
