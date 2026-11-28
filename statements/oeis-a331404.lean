import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Choose.Basic

/-!
# Song's conjecture on the exponential generating function of A331404

Source: https://oeis.org/A331404 (Jianing Song, September 30, 2024).
Credit: @NOELOO6

The two inverse identities are identities of analytic germs at 0 and 1.
The formal multilinear series uses the literal exponential generating
coefficients, and its radius is the usual complex convergence radius.
-/

namespace OMA.S_oeis_a331404
open Finset Filter
open scoped Topology
noncomputable section

def a : ℕ → ℤ
  | 0 => 1
  | n+1 => ∑ k : Fin (n+1), (-1:ℤ)^(n-k.val)*(n+1).choose (k.val+1)*
      a k.val*a (n-k.val)
termination_by n => n

def series : FormalMultilinearSeries ℂ ℂ ℂ :=
  .ofScalars ℂ (fun n => (a n : ℂ)/n.factorial)
def h (z : ℂ) := z-z⁻¹-Complex.log z

theorem main :
    (∃ F : ℂ → ℂ, HasFPowerSeriesAt F series 0 ∧
      h ∘ F =ᶠ[𝓝 0] id ∧ F ∘ h =ᶠ[𝓝 1] id) ∧
    series.radius = ENNReal.ofReal (Real.sqrt 3-Real.pi/3) := by
  sorry

end
end OMA.S_oeis_a331404
