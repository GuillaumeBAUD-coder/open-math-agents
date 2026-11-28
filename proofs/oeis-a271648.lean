import OMAStatements.S_oeis_a271648
import Mathlib

namespace MSL_GFFull
open PowerSeries
private theorem coeff_lags (a : ℕ → ℤ) (S : Finset ℕ) (p : ℕ → ℤ) (n : ℕ) :
    coeff n (((∑ i ∈ S, C (p i) * X ^ i) : ℤ⟦X⟧) * mk a) =
      ∑ i ∈ S, p i * (if i ≤ n then a (n-i) else 0) := by
  rw [Finset.sum_mul]
  simp only [map_sum, mul_assoc, coeff_C_mul, coeff_X_pow_mul', coeff_mk]

-- Turn all integer constants into constant power series, for symbolic GF
-- coefficients at nonzero exponents (do not leave them as opaque casts).
theorem coeff_intCast (n : ℕ) (c : ℤ) :
    (coeff n) (c : ℤ⟦X⟧) = if n = 0 then c else 0 := by
  have hc : (C c : ℤ⟦X⟧) = (c : ℤ⟦X⟧) :=
    map_intCast (PowerSeries.C : ℤ →+* ℤ⟦X⟧) c
  rw [←hc]
  exact PowerSeries.coeff_C n c
end MSL_GFFull

open PowerSeries
namespace MSL_GFTarget_oeis_a271648
def denCoeff : ℕ → ℤ
  | 0 => 1
  | 1 => -7
  | 2 => 21
  | 3 => -35
  | 4 => 35
  | 5 => -21
  | 6 => 7
  | 7 => -1
  | _ => 0

def numCoeff : ℕ → ℤ
  | 0 => 6
  | 1 => 77
  | 2 => 1572
  | 3 => 4378
  | 4 => 1531
  | 5 => 137
  | 6 => -22
  | 7 => 0
  | 8 => 1
  | _ => 0

end MSL_GFTarget_oeis_a271648

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a271648.main) := by
  rintro ⟨hrec, hgf⟩
  let A : ℕ → ℤ := fun n => (OMA.S_oeis_a271648.a n : ℤ)
  let D : ℕ → ℤ := MSL_GFTarget_oeis_a271648.denCoeff
  let N : ℕ → ℤ := MSL_GFTarget_oeis_a271648.numCoeff
  have hden : (((1 - X) ^ 7) : ℤ⟦X⟧) =
      (∑ i ∈ Finset.range 8, C (D i) * X ^ i) := by
    simp [D, MSL_GFTarget_oeis_a271648.denCoeff, Finset.sum_range_succ,
          Finset.sum_range_zero]
    ring
  have hnum_poly : ((6 + 77 * X + 1572 * X ^ 2 + 4378 * X ^ 3 + 1531 * X ^ 4 + 137 * X ^ 5 - 22 * X ^ 6 + X ^ 8 : PowerSeries ℤ)) =
      (∑ i ∈ Finset.range 9, C (N i) * X ^ i) := by
    simp [N, MSL_GFTarget_oeis_a271648.numCoeff, Finset.sum_range_succ,
          Finset.sum_range_zero]
    ring
  have hnum : coeff 8 ((6 + 77 * X + 1572 * X ^ 2 + 4378 * X ^ 3 + 1531 * X ^ 4 + 137 * X ^ 5 - 22 * X ^ 6 + X ^ 8 : PowerSeries ℤ)) = (1 : ℤ) := by
    rw [hnum_poly]
    simp only [map_sum, coeff_C_mul, coeff_X_pow]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero,
          N, MSL_GFTarget_oeis_a271648.numCoeff]
    all_goals (simp [MSL_GFFull.coeff_intCast])
    all_goals norm_num
  have hgf' :
      ((∑ i ∈ Finset.range 8, C (D i) * X ^ i) : ℤ⟦X⟧) * mk A = ((6 + 77 * X + 1572 * X ^ 2 + 4378 * X ^ 3 + 1531 * X ^ 4 + 137 * X ^ 5 - 22 * X ^ 6 + X ^ 8 : PowerSeries ℤ)) := by
    rw [← hden]
    simpa only [A, mul_comm] using hgf
  have hcoeff := congrArg (coeff 8) hgf'
  rw [MSL_GFFull.coeff_lags, hnum] at hcoeff
  simp [D, MSL_GFTarget_oeis_a271648.denCoeff, Finset.sum_range_succ,
        Finset.sum_range_zero] at hcoeff
  have hr := hrec 8 (by norm_num)
  dsimp only [A] at hcoeff
  norm_num at hr hcoeff
  omega

