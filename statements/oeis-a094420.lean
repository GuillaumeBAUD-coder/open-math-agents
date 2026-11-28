import Mathlib

/-!
# A094420: Generalized ordered Bell numbers Bo(n,n).

Source: https://oeis.org/A094420
Credit: @xor2k

Velin Yanev (Jul 27 2026), in the formula section of A094420:
  Conjecture: a(n) = polylog(-n, n/(n + 1))/(n + 1) for n > 0.
This is the complete conjecture of the row; it is the only conjecture of the entry.

Conventions:
* Offset 0 as in OEIS. The sequence is defined by the formula of the entry (Seiichi Manyama,
  Jun 12 2020), which is also what the Mathematica, PARI and Magma programs of the entry compute:
  a(n) = Sum_{k=0..n} k! * n^k * Stirling2(n, k), with Stirling2 the Stirling numbers of the
  second kind, here Mathlib's `Nat.stirlingSecond` (defined by the standard recurrence
  S(0,0) = 1, S(0,k+1) = 0, S(n+1,0) = 0, S(n+1,k+1) = (k+1)*S(n,k+1) + S(n,k)).
* The polylogarithm is Li_s(z) = Sum_{j >= 1} z^j / j^s for |z| < 1. For order s = -n with n a
  positive integer this is the convergent series Sum_{j >= 1} j^n * z^j, and the argument
  z = n/(n+1) lies in (0, 1), so polylog(-n, n/(n+1)) is the sum of that series; no analytic
  continuation is involved.
* The claim a(n) = polylog(-n, n/(n+1))/(n+1) is stated as: the series
  Sum_{j >= 0} j^n * (n/(n+1))^j of real numbers converges (unconditionally) and its sum is
  (n+1) * a(n), i.e. `HasSum` of the family with that value. The family is indexed by all
  natural numbers j >= 0; the j = 0 term is 0^n * 1 = 0 because n >= 1, so this is the same
  series as the one over j >= 1.
* The claim is asserted for every n >= 1 (n > 0), as in the conjecture.

Numerical check: a Python copy of the definition gives, for n = 0..19,
1, 1, 10, 219, 8676, 544505, 49729758, 6232661239, 1026912225160, 215270320769109,
55954905981282210, 17662898483917308083, 6655958151527584785900, 2951503248457748982755953,
1521436331153097968932487206, 902143190212525713006814917615,
609729139653483641913607434550800, 465964656815186762758947266546637197,
399797863367182694222398490311454777706, 382694977206197959702510312863837664576939;
compared with DATA: identical for the first 17 terms (all of DATA). Partial sums of the series
(6000 terms, floating point) divided by (n+1)*a(n) give 1 up to rounding for n = 1..7.
-/

namespace OMA.S_oeis_a094420

/-- A094420 (offset 0): a(n) = Sum_{k=0..n} k! * n^k * Stirling2(n, k). -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), k.factorial * n ^ k * Nat.stirlingSecond n k

/-- Yanev's conjecture: a(n) = polylog(-n, n/(n+1))/(n+1) for n > 0, with
polylog(-n, z) = Sum_{j >= 1} j^n z^j for |z| < 1. -/
theorem main : ∀ n : ℕ, 0 < n →
    HasSum (fun j : ℕ => (j : ℝ) ^ n * ((n : ℝ) / ((n : ℝ) + 1)) ^ j)
      (((n : ℝ) + 1) * (a n : ℝ)) := by
  sorry

end OMA.S_oeis_a094420
