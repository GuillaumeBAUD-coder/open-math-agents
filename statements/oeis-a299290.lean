import Mathlib

/-!
# Balls in the tsi net, OEIS A299290

Sources: https://oeis.org/A299290, https://oeis.org/A299289, and
https://rcsr.net/nets/tsi. Submitted by @VestigeClub.

The two vertex types in the RCSR translational cell have square horizontal
layers. The four type-1 to type-2 translation labels are (-1,0,0),
(0,-1,1), (0,0,0), (0,0,1). Taking horizontal coordinates (-x,y) and
layer -2z (type 1) or -2z+1 (type 2) gives alternating prism slabs.
The exact graph-distance shell decomposition for this model is given at
https://the-omega-institute.github.io/trureturing-mdbook/Blueprint/D5/S3/StatisticalMechanics/TsiCoordinationSequence.html.

At positive radius r the central layer has 4r vertices, the two
interior layers of absolute height h each have 4r-2h vertices, and each
extreme layer is a rectangle of sides floor(r/2)+1 and floor((r+1)/2)+1.
This gives A299289 independently of the formulas claimed for the partial
sums. Radius zero consists of the origin alone. The generating function
is stated as an equality of formal power series with its denominator
cleared. The proof checks the first six partial sums.
-/

namespace OMA.S_oeis_a299290

def interiorLayers (r m : ℕ) : ℚ :=
  ∑ j ∈ Finset.range m, (4 * (r : ℚ) - 2 * ((j : ℚ) + 1))

def shell : ℕ → ℚ
  | 0 => 1
  | n + 1 => 4 * ((n : ℚ) + 1) + 2 * interiorLayers (n + 1) n +
      2 * ((((n + 1) / 2 : ℕ) : ℚ) + 1) * ((((n + 2) / 2 : ℕ) : ℚ) + 1)

def a (n : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), shell k

theorem main :
    (let X : PowerSeries ℚ := PowerSeries.X
     PowerSeries.mk a * ((1 - X) ^ 4 * (1 + X)) = 1 + 6 * X + 12 * X ^ 2 + 6 * X ^ 3 + X ^ 4) ∧
    (∀ n : ℕ, Even n → a n = (12 + 34 * (n : ℚ) + 39 * (n : ℚ) ^ 2 + 26 * (n : ℚ) ^ 3) / 12) ∧
    (∀ n : ℕ, Odd n → a n = (9 + 34 * (n : ℚ) + 39 * (n : ℚ) ^ 2 + 26 * (n : ℚ) ^ 3) / 12) ∧
    (∀ n : ℕ, 4 < n → a n = 3 * a (n - 1) - 2 * a (n - 2) - 2 * a (n - 3) +
      3 * a (n - 4) - a (n - 5)) := by
  sorry

end OMA.S_oeis_a299290
