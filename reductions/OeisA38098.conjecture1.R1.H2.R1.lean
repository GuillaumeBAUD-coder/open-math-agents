import OMAReductions.R_OeisA38098_conjecture1_R1

-- Reduction OeisA38098.conjecture1.R1.H2.R1 of step OeisA38098.conjecture1.R1.H2
-- Credit: @senamakel
--
-- Step H2 is Schoenfeld 1976, Corollary 1: under RH, |pi(x) - li(x)| < sqrt x log x/(8 pi) for
-- x >= 2657. The proof splits into an analytic argument (H4) and three inputs.
--
-- N(T) below is the number of zeros of zeta with 0 < Im rho <= T, counted with multiplicity.
-- H1: Rosser 1941, Theorem 19, for T >= 100 (Backlund's unconditional argument: Jensen's
--     formula, Stirling for the Gamma factor, an Euler-Maclaurin bound for zeta):
--     |N(T) - (T/2pi log(T/2pi) - T/2pi + 7/8)| < 0.137 log T + 0.443 log log T + 1.588.
-- H2: the same inequality for 2 <= T <= 100: a finite certificate (the 29 zeros of height at
--     most 100 are simple, on the critical line and in explicit brackets).
-- H3: the finite checks: |psi(x) - x| <= (4/5) sqrt x on [1500, 10^10], Schoenfeld's theta
--     bound on [599, 3*10^4] and his pi - li bound on [2657, 4*10^5].
-- H4: the analytic argument: RH, Rosser's count for every T >= 2 and the three finite checks give
--     the bound for every x >= 2657 (explicit formula for psi, the zero sum bounded with Rosser's
--     count, then partial summation from theta to pi - li).
-- main joins H1 and H2 into Rosser's count for every T >= 2 and applies H4.

namespace OMA.R_OeisA38098_conjecture1_R1_H2_R1

open Real

def H1 : Prop :=
  ∀ T : ℝ, 100 ≤ T →
    |(∑' ρ : ℂ, if 0 < ρ.im ∧ ρ.im ≤ T then ((analyticOrderAt riemannZeta ρ).toNat : ℝ) else 0) -
      (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8)| <
      0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588

def H2 : Prop :=
  ∀ T : ℝ, 2 ≤ T → T ≤ 100 →
    |(∑' ρ : ℂ, if 0 < ρ.im ∧ ρ.im ≤ T then ((analyticOrderAt riemannZeta ρ).toNat : ℝ) else 0) -
      (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8)| <
      0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588

def H3 : Prop :=
  (∀ x : ℝ, 1500 ≤ x → x ≤ 10 ^ 10 → |Chebyshev.psi x - x| ≤ 4 / 5 * Real.sqrt x) ∧
  (∀ x : ℝ, 599 ≤ x → x ≤ 30000 →
    |Chebyshev.theta x - x| < 1 / (8 * Real.pi) * (Real.sqrt x * Real.log x ^ 2)) ∧
  (∀ x : ℝ, 2657 ≤ x → x ≤ 400000 →
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Real.logIntegral x| <
      1 / (8 * Real.pi) * (Real.sqrt x * Real.log x))

def H4 : Prop :=
  RiemannHypothesis →
  (∀ T : ℝ, 2 ≤ T →
    |(∑' ρ : ℂ, if 0 < ρ.im ∧ ρ.im ≤ T then ((analyticOrderAt riemannZeta ρ).toNat : ℝ) else 0) -
      (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8)| <
      0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588) →
  (∀ x : ℝ, 1500 ≤ x → x ≤ 10 ^ 10 → |Chebyshev.psi x - x| ≤ 4 / 5 * Real.sqrt x) →
  (∀ x : ℝ, 599 ≤ x → x ≤ 30000 →
    |Chebyshev.theta x - x| < 1 / (8 * Real.pi) * (Real.sqrt x * Real.log x ^ 2)) →
  (∀ x : ℝ, 2657 ≤ x → x ≤ 400000 →
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Real.logIntegral x| <
      1 / (8 * Real.pi) * (Real.sqrt x * Real.log x)) →
  ∀ x : ℝ, 2657 ≤ x →
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Real.logIntegral x| <
      1 / (8 * Real.pi) * (Real.sqrt x * Real.log x)

theorem main : H1 → H2 → H3 → H4 → OMA.R_OeisA38098_conjecture1_R1.H2 := by
  intro h1 h2 h3 h4 hRH
  obtain ⟨hC, hθ, hπ⟩ := h3
  refine h4 hRH (fun T hT => ?_) hC hθ hπ
  rcases le_or_gt 100 T with h | h
  · exact h1 T h
  · exact h2 T hT h.le

end OMA.R_OeisA38098_conjecture1_R1_H2_R1
