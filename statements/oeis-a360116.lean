import Mathlib

/-!
# A360116: a(n) = 1 if there are no prime factors p of n for which the 2-adic valuation of p-1 is less than that of n-1, otherwise 0.

Source: https://oeis.org/A360116 (offset 2)

Data: 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0, 1, ... (n = 2, 3, 4, ...).

Reading of the definition: the OEIS name states the inequality as "v2(p-1) < v2(n-1)", but the data,
the PARI program (`!sum(i=1, #f~, (v < valuation(f[i, 1]-1, 2)))` with `v = valuation(n-1, 2)`) and
the formula a(n) = [A360115(n) = 0] all use the opposite inequality: a(n) = 1 iff every prime factor
p of n satisfies v2(p-1) <= v2(n-1). (For n = 5 the name read literally would give 1, the data gives 0.)
We follow the data and the program.

Conjecture (Sequence Machine, reported by Antti Karttunen, May 14 2025): a(n) = [A333570(n) <= 2],
where A333570(n) is the number of 0 <= c < n with c^n == -c (mod n). (The entry also states
a(n) = [A360112(n) <= 2]; that second formula is not covered here.)
-/

namespace OMA.S_oeis_a360116

/-- A360116 (following its data and PARI program). -/
def a (n : ℕ) : ℕ :=
  if ∀ p ∈ n.primeFactors, padicValNat 2 (p - 1) ≤ padicValNat 2 (n - 1) then 1 else 0

/-- A333570: the number of 0 <= c < n with c^n == -c (mod n). -/
def a333570 (n : ℕ) : ℕ := ((Finset.range n).filter (fun c => n ∣ c ^ n + c)).card

theorem main :
    ∀ n : ℕ, 2 ≤ n → a n = if a333570 n ≤ 2 then 1 else 0 := by
  sorry

end OMA.S_oeis_a360116
