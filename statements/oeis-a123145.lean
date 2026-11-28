import Mathlib

namespace OMA.S_oeis_a123145

/-- OEIS A123145: `a(1) = 1`, `a(n) = a(n-1)` if `n ≡ 1 (mod 4)`, otherwise
`a(n) = n * a(n-1)` for `n ≥ 2` (with `a(0) = 0` unused). -/
def a123145 : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      if (n + 2) % 4 = 1 then a123145 (n + 1)
      else (n + 2) * a123145 (n + 1)

/-- The 5-step continued fraction recurrence for OEIS A123145:
`G(k) = 1 + x/(4*k+1 - x*(4*k+1)/(1 + x - x/(1 + x - x/(x + 1/G(k+1)))))`,
expressed in cleared-denominator form over `PowerSeries ℚ` with `G(k)(0) = 1`. -/
def IsCF123145 (G : ℕ → PowerSeries ℚ) : Prop :=
  ∀ k : ℕ,
    PowerSeries.coeff 0 (G k) = 1 ∧
    ∃ D1 D2 D3 D4 : PowerSeries ℚ,
      PowerSeries.coeff 0 D4 = 1 ∧
      PowerSeries.coeff 0 D3 = 1 ∧
      PowerSeries.coeff 0 D2 = 1 ∧
      PowerSeries.coeff 0 D1 = (4 * (k : ℚ) + 1) ∧
      D4 * G (k + 1) = PowerSeries.X * G (k + 1) + 1 ∧
      D3 * D4 = (1 + PowerSeries.X) * D4 - PowerSeries.X ∧
      D2 * D3 = (1 + PowerSeries.X) * D3 - PowerSeries.X ∧
      D1 * D2 = PowerSeries.C (4 * (k : ℚ) + 1) * (D2 - PowerSeries.X) ∧
      (G k - 1) * D1 = PowerSeries.X

/-- OEIS A123145 conjecture: the exponential generating function of `a(n+1)` equals
`d(G(0))/dx` (equivalently, `G(0) = 1 + ∑_{n ≥ 1} a(n) x^n / n!`), where `G(k)` satisfies
the 5-step continued fraction recurrence `IsCF123145`. -/
theorem main :
    ∀ G : ℕ → PowerSeries ℚ,
      IsCF123145 G →
      PowerSeries.derivative ℚ (G 0) =
        PowerSeries.mk (fun n => (a123145 (n + 1) : ℚ) / (Nat.factorial n : ℚ)) := by
  sorry

end OMA.S_oeis_a123145
