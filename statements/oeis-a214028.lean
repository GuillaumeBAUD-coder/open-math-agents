import Mathlib

/-!
# A214028: Entry points for the Pell sequence: smallest k such that n divides A000129(k).

Source: https://oeis.org/A214028
Credit: @xor2k

Unsigned comment of the entry A214028 (entry author Art DuPre, Jul 04 2012):
  Conjecture: A175181(n)/A214027(n) = a(n). This says that the zeros appear somewhat uniformly in a
  period. The second zero in a period is exactly where n divides the first Lucas number, so this
  relationship is not really surprising.

Only the identity A175181(n)/A214027(n) = a(n) is a mathematical claim and it is what is stated; the
two following sentences are informal remarks of the author about it (no precise claim) and are not
formalized.

Conventions:
* `pell` is A000129 (offset 0): pell 0 = 0, pell 1 = 1, pell (k+2) = 2 * pell (k+1) + pell k.
* `a n` is A214028 (offset 1): the smallest k > 0 such that n divides pell k, as `sInf` of the set
  of such k (the Maple and PARI programs of the entry start the search at k = 1).
* `period n` is A175181 (offset 1), the Pisano period of the Pell numbers, by its own definition
  (period of the sequence defined by reading A000129 modulo n): the smallest p > 0 such that
  pell (k + p) ≡ pell k (mod n) for all k ≥ 0, as `sInf` of the set of such p.
* `zeros n` is A214027 (offset 1), by its own definition: the number of zeros in the fundamental
  period of A000129 mod n, that is the number of k with 0 ≤ k < period n and n ∣ pell k.
* `sInf` of an empty set of naturals is 0 in Lean. For n ≥ 1 both sets are nonempty (the sequence
  mod n is purely periodic and pell 0 = 0); this is not assumed, it is part of what a proof has to
  show.
* The quotient is stated without and with division: period n = a n * zeros n, together with the
  exact divisibility zeros n ∣ period n and the natural number quotient period n / zeros n = a n.
  The statement is for every n ≥ 1 (the offset of the three entries); for n = 1 all three are 1.

Numerical check: a Python copy of the definitions gives for n = 1..40
  a:      1, 2, 4, 4, 3, 4, 6, 8, 12, 6, 12, 4, 7, 6, 12, 16, 8, 12, 20, 12, 12, 12, 22, 8, 15, 14,
          36, 12, 5, 12, 30, 32, 12, 8, 6, 12, 19, 20, 28, 24
  period: 1, 2, 8, 4, 12, 8, 6, 8, 24, 12, 24, 8, 28, 6, 24, 16, 16, 24, 40, 12, 24, 24, 22, 8, 60,
          28, 72, 12, 20, 24, 30, 32, 24, 16, 12, 24, 76, 40, 56, 24
  zeros:  1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 2, 2, 2, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 2,
          1, 1, 2, 2, 2, 2, 4, 2, 2, 1
compared with DATA of A214028, A175181 and A214027: identical for the first 40 terms each, and
period n = a n * zeros n for these n.
-/

namespace OMA.S_oeis_a214028

/-- A000129, the Pell numbers (offset 0). -/
def pell : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (k + 2) => 2 * pell (k + 1) + pell k

/-- A214028 (offset 1): the entry point, the smallest k > 0 such that n divides pell k. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | 0 < k ∧ n ∣ pell k}

/-- A175181 (offset 1): the Pisano period of the Pell numbers modulo n, the smallest p > 0 such
that pell (k + p) ≡ pell k (mod n) for all k. -/
noncomputable def period (n : ℕ) : ℕ :=
  sInf {p : ℕ | 0 < p ∧ ∀ k : ℕ, pell (k + p) ≡ pell k [MOD n]}

/-- A214027 (offset 1): the number of zeros in the fundamental period of the Pell numbers mod n. -/
noncomputable def zeros (n : ℕ) : ℕ :=
  ((Finset.range (period n)).filter (fun k => n ∣ pell k)).card

/-- The conjecture A175181(n)/A214027(n) = a(n): the period is the entry point times the number
of zeros, the number of zeros divides the period, and the quotient is the entry point. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    period n = a n * zeros n ∧ zeros n ∣ period n ∧ period n / zeros n = a n := by
  sorry

end OMA.S_oeis_a214028
