import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Denominators of the convergents to the continued fraction for √7/2

The partial quotients are [1; 3, 10, 3, 2, 3, 10, 3, 2, ...].
Their convergent denominators start with q₀ = 1 and q₁ = 3.
Colin Barker gives the rational generating function and recurrence in
OEIS A294973, where Wolfdieter Lang also supplies a derivation.
The formal power series identity clears a denominator whose constant term is one.

Source: https://oeis.org/A294973 (OEIS Foundation, CC BY-SA 4.0).
Credit: @yukimiyazaki
-/

namespace OMA.S_oeis_a294973

/-- Periodic tail coefficient at a positive index; used only from index two. -/
def tailCoeff (n : ℕ) : ℕ :=
  match n % 4 with
  | 0 => 2
  | 2 => 10
  | _ => 3

/-- Convergent denominators, indexed from zero. -/
def q : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | n + 2 => tailCoeff (n + 2) * q (n + 1) + q n

open PowerSeries in
theorem main :
    (∀ n : ℕ, 8 ≤ n → (q n : ℤ) = 254 * (q (n-4) : ℤ) - (q (n-8) : ℤ)) ∧
    (mk (fun n => (q n : ℤ)) *
      ((1 - 16*X^2 + X^4) * (1 + 16*X^2 + X^4)) =
      (1 + 3*X - X^2) * (1 + 32*X^2 + X^4)) := by
  sorry

end OMA.S_oeis_a294973
