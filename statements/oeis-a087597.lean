import Mathlib

/-!
# OEIS A087597: Triangular numbers m such that A040115(m) is also triangular.

Source: https://oeis.org/A087597
Credit: @unserus

OEIS: "Conjecture: Sequence is infinite."
A040115(n) concatenates the absolute differences of adjacent decimal digits of `n`
(`371 ↦ 46`; leading zeros omitted; a one-digit `n` gives `0`). With Mathlib's little-endian
`Nat.digits`, the adjacent differences come out least significant first, and `Nat.ofDigits`
reads them back as the decimal number (leading zeros vanish automatically).
Triangular numbers are `k (k + 1) / 2` for `k ≥ 0` (so `0` is one, as in the data `0, 1, 3, ...`).
OEIS example: `171` is a term since `A040115(171) = 66 = 11 * 12 / 2`.
-/

namespace OMA.S_oeis_a087597

/-- A040115: the absolute differences of adjacent decimal digits of `n`, read as a number. -/
def a040115 (n : ℕ) : ℕ :=
  let l := Nat.digits 10 n
  Nat.ofDigits 10 (List.zipWith (fun a b => Int.natAbs ((a : ℤ) - b)) l l.tail)

/-- `m` is a triangular number. -/
def IsTriangular (m : ℕ) : Prop := ∃ k : ℕ, m = k * (k + 1) / 2

/-- The terms of A087597: triangular `m` with `A040115(m)` triangular. -/
def a087597Set : Set ℕ := {m : ℕ | IsTriangular m ∧ IsTriangular (a040115 m)}

/-- A087597 is infinite. -/
theorem main : a087597Set.Infinite := by
  sorry

end OMA.S_oeis_a087597
