import Mathlib

/-!
# The ratio limit of the inverse Thue–Morse sequence

Source: Clark Kimberling, OEIS A225132 (2013), https://oeis.org/A225132.
The source starts its inverse coefficients at index 1. Here `a n` denotes
its coefficient at index `n + 1`, so the ratio is unchanged by reindexing.
The source's convolution example determines the input series: its
coefficient at degree n is the Thue–Morse bit at index n + 1.
The interval in the conclusion states the twelve displayed decimal places.
-/

namespace OMA.S_oeis_a225132

open PowerSeries Filter
open scoped Topology

def digitSum : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) % 2 + digitSum ((n + 1) / 2)
termination_by n => n
decreasing_by omega

noncomputable def thueSeries : ℤ⟦X⟧ :=
  mk fun n => (digitSum (n + 1) % 2 : ℕ)

noncomputable def a (n : ℕ) : ℤ :=
  coeff n (thueSeries.invOfUnit 1)

theorem main :
    ∃ L : ℝ, -(1405177106053 / 10^12 : ℝ) < L ∧
      L < -(1405177106052 / 10^12 : ℝ) ∧
      Tendsto (fun n => (a (n + 1) : ℝ) / (a n : ℝ)) atTop (𝓝 L) := by
  sorry

end OMA.S_oeis_a225132
