import Mathlib

/-!
# A066840: Sum of positive integers k where k <= n/2 and gcd(k,n) = 1.

Source: https://oeis.org/A066840
Credit: @esracummings31-blip

Conjecture (Thomas Ordowski, Nov 12 2014): a(n) = n*phi(n)/8 + O(n).

`a n` is the sequence for n ≥ 1 (offset 1), exactly as in the PARI program
`a(n) = sum(k=1, n\2, if (gcd(n,k)==1, k))`; `n / 2` is floor division, so `k ≤ n/2`.
"+ O(n)" is read in the standard sense, as `n → ∞`:
`a(n) - n*phi(n)/8 = O(n)`, stated with `Asymptotics.IsBigO` along `Filter.atTop`.
-/

namespace OMA.S_oeis_a066840

/-- A066840: sum of the positive integers `k ≤ n/2` with `gcd(k, n) = 1`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 (n / 2), if Nat.gcd k n = 1 then k else 0

theorem main :
    (fun n : ℕ => (a n : ℝ) - (n : ℝ) * (Nat.totient n : ℝ) / 8) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ)) := by
  sorry

end OMA.S_oeis_a066840
