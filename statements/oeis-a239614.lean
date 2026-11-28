import Mathlib

/-!
Source: https://oeis.org/A239614
Source text: https://github.com/oeis/oeisdata/blob/main/seq/A239/A239614.seq
Additional source: https://oeis.org/A010710
Credit: @Heart-galaxy

The source records all three conjectures as proved by Amiram Eldar on
November 10, 2026. The independent multiplicative formula recorded there
defines this sequence: its local factors are 2*e at the prime 2, and e+1
at every odd prime. The empty product supplies a(1)=1.

The first conjecture a(n)=(4+n mod 2)*tau(n)-2*tau(2*n) is expressed in
the equivalent addition form, so no truncated subtraction occurs. The
sequence has offset one; the even-index formula uses n>0, and the odd-index
formula includes n=0, corresponding to index one.
-/

namespace OMA.S_oeis_a239614

def a (n : ℕ) : ℕ :=
  n.primeFactors.prod (fun p => if p = 2 then 2*n.factorization p else n.factorization p+1)

def tau (n : ℕ) : ℕ := n.divisors.card

theorem main :
    (∀ n : ℕ, 0 < n → a n + 2*tau (2*n) = (4+n%2)*tau n) ∧
    (∀ n : ℕ, 0 < n → a (2*n) = 2*tau n) ∧
    (∀ n : ℕ, a (2*n+1) = tau (2*n+1)) := by
  sorry

end OMA.S_oeis_a239614
