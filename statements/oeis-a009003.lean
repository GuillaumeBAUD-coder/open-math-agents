import Mathlib

/-!
# A009003: Hypotenuse numbers

Source: https://oeis.org/A009003
Credit: @laurilehtinen

Patrick A. Thomas asks about the first exponent giving a fixed point in the base-m
integers. Mats Granvik asks about a finite complex limit and gives the equivalent
Möbius divisor sum. For m > 1 the Chinese remainder theorem identifies the base-m
integers with the product of the p-adic integer rings at the prime divisors of m.
At m = 1 the empty product also agrees with the inverse limit of Z/(1^k).
-/

namespace OMA.S_oeis_a009003

open Filter
open scoped Topology

def isHypotenuse (m : ℕ) : Prop := ∃ a b : ℕ, 0<a ∧ 0<b ∧ a^2+b^2=m^2

abbrev PrimeDivisor (m : ℕ) := {p : ℕ // p.Prime ∧ p ∣ m}

instance {m : ℕ} (p : PrimeDivisor m) : Fact p.val.Prime := ⟨p.property.1⟩

abbrev BaseAdic (m : ℕ) := (p : PrimeDivisor m) → ℤ_[p.val]

noncomputable def divisorFactor (m : ℕ) (s : ℂ) : ℂ :=
  ∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℂ)*Complex.I^d/(d:ℂ)^(s-1)

theorem main : ∀ m : ℕ, 0 < m →
    (isHypotenuse m ↔ ∃ x : BaseAdic m, x^5=x ∧ x^2≠x ∧ x^3≠x ∧ x^4≠x) ∧
    (isHypotenuse m ↔ (∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℂ)*Complex.I^d)=0) ∧
    (isHypotenuse m ↔ ∃ L : ℂ, Tendsto (fun s ↦ riemannZeta s*divisorFactor m s)
      (𝓝[≠] 1) (𝓝 L)) := by
  sorry

end OMA.S_oeis_a009003
