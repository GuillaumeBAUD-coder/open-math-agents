import Mathlib

/-!
# A377714: Cogrowth sequence for the 8-element group C4 X C2 = <S,T | S^4, T^2, [S,T]>.

Source: https://oeis.org/A377714 (conjectures of Chai Wah Wu, May 16 2026).
Credit: @esracummings31-blip

a(n) is the number of words of length 2n in the letters S and T that equal the identity in
C4 X C2 (all odd lengths give 0). For example a(1) = 1 (TT) and a(2) = 2 (SSSS, TTTT); the data
1, 1, 2, 16, 72, 256, 992, 4096, ... is reproduced by this definition.

The group C4 X C2 is abelian, so it is modelled additively as `ZMod 4 × ZMod 2` with
S = (1, 0) and T = (0, 1); a word is a map `Fin (2 * n) → Fin 2` (letter `0` is S, letter `1`
is T), and it equals the identity when the sum of its letters is `0`.

Conjecture: a(n) = 4*a(n-1) - 4*a(n-2) + 16*a(n-3) for n > 3, and the g.f. is
(4x^3 - 2x^2 + 3x - 1)/((4x - 1)(4x^2 + 1)).
-/

namespace OMA.S_oeis_a377714

/-- The generators: letter `0` is S = (1, 0) and letter `1` is T = (0, 1). -/
def gen : Fin 2 → ZMod 4 × ZMod 2 := ![(1, 0), (0, 1)]

/-- The number of words of length `2 * n` in S and T that equal the identity. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin (2 * n) → Fin 2 => ∑ i, gen (w i) = 0)).card

open PowerSeries in
theorem main :
    (∀ n, 3 < n → (a n : ℤ) = 4 * a (n - 1) - 4 * a (n - 2) + 16 * a (n - 3)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * ((4 * X - 1) * (4 * X ^ 2 + 1)) =
      4 * X ^ 3 - 2 * X ^ 2 + 3 * X - 1 := by
  sorry

end OMA.S_oeis_a377714
