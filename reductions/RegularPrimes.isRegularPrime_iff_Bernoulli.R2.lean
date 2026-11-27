import FormalConjectures.Wikipedia.RegularPrimes
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

-- Credit: @Tchikrazi

namespace OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R2

open NumberField

/-- The class number of the maximal real subfield divides the full class number.
This makes their natural-number quotient the relative class number. -/
def H1 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    classNumber (maximalRealSubfield (CyclotomicField p ℚ)) ∣ classNumber (CyclotomicField p ℚ)

/-- The reflection step. If the real class number is divisible by p,
then the relative class number is divisible by p as well. -/
def H2 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    let hPlus := classNumber (maximalRealSubfield (CyclotomicField p ℚ))
    p ∣ hPlus → p ∣ classNumber (CyclotomicField p ℚ) / hPlus

/-- The Bernoulli criterion for the relative class number. -/
def H3 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    let hPlus := classNumber (maximalRealSubfield (CyclotomicField p ℚ))
    p ∣ classNumber (CyclotomicField p ℚ) / hPlus ↔
      ∃ k ∈ Finset.Icc 2 (p - 3), Even k ∧ (p : ℤ) ∣ (bernoulli' k).num

theorem main : H1 → H2 → H3 → type_of% @RegularPrimes.isRegularPrime_iff_Bernoulli := by
  intro hDiv hReflect hBernoulli p hp
  let h := classNumber (CyclotomicField p ℚ)
  let hPlus := classNumber (maximalRealSubfield (CyclotomicField p ℚ))
  have hPrime : Nat.Prime p := hp.out
  have hFactor : h / hPlus * hPlus = h := Nat.div_mul_cancel (@hDiv p hp)
  have hRelative : p ∣ h ↔ p ∣ h / hPlus := by
    constructor
    · intro hd
      rw [← hFactor] at hd
      exact (hPrime.dvd_mul.mp hd).elim id (@hReflect p hp)
    · intro hd
      exact dvd_trans hd (show h / hPlus ∣ h from ⟨hPlus, hFactor.symm⟩)
  have hIrregular := hRelative.trans (@hBernoulli p hp)
  change Nat.Coprime p h ↔ _
  constructor
  · intro hRegular k hk hEven hBad
    exact (hPrime.coprime_iff_not_dvd.mp hRegular) (hIrregular.mpr ⟨k, hk, hEven, hBad⟩)
  · intro hGood
    apply hPrime.coprime_iff_not_dvd.mpr
    intro hd
    obtain ⟨k, hk, hEven, hBad⟩ := hIrregular.mp hd
    exact hGood k hk hEven hBad

end OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R2
