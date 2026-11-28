import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

namespace OMA.S_mo_277517

/-- Coefficients of the constant series 1. -/
def unitSeries (a : ℕ) : ℤ := if a = 0 then 1 else 0

/-- Coefficientwise definition of multiplication of formal series. -/
def multiply (u v : ℕ → ℤ) (a : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (a+1), u i * v (a-i)

def seriesPower (u : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0 => unitSeries
  | n+1 => multiply (seriesPower u n) u

/-- The MacMahon product through the factor `(1-z^k)^{-k}`.
Factors beyond `k` do not affect coefficients of degree at most `k`. -/
def macMahon : ℕ → ℕ → ℤ
  | 0 => unitSeries
  | k+1 => multiply (macMahon k)
      (seriesPower (fun a => if a % (k+1) = 0 then 1 else 0) (k+1))

abbrev Multiplicities (n : ℕ) := Fin n → Fin (n+1)

def partitions (n : ℕ) : Finset (Multiplicities n) :=
  Finset.univ.filter (fun a => (∑ j : Fin n, (j.val+1) * (a j).val) = n)

def present {n : ℕ} (a : Multiplicities n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => (a j).val ≠ 0)

def weight {n : ℕ} (a : Multiplicities n) (j : Fin n) : ℕ :=
  ∑ i : Fin n, (a i).val * min (i.val+1) (j.val+1)

/-- The number `N_n` defined by the partition sum in the question. -/
def number (n : ℕ) : ℚ :=
  (∑ a ∈ partitions n,
    ((present a).card : ℚ) / ((∑ j : Fin n, (a j).val : ℕ) : ℚ) *
      ∏ j ∈ present a, (seriesPower (macMahon n) (weight a j) (a j).val : ℚ)) / (n : ℚ)

def mobiusCorrection (n : ℕ) : ℚ :=
  ∑ l ∈ n.divisors, (ArithmeticFunction.moebius l : ℚ) / (l : ℚ)^2 * number (n/l)

/-- Integrality assertion in the postscript, expressed by reduced denominator 1. -/
theorem main :
    ∀ n : ℕ, 0 < n → (mobiusCorrection n).den = 1 := by
  sorry

end OMA.S_mo_277517
