import Mathlib

/-!
# Paul D. Hanna's two congruences for OEIS A357398

With T=exp(−x), the defining equation is Σ_{j≥1}(1−A T^j)^j=0,
A(0)=1. Each summand is divisible by x^j, so the coefficientwise equation
is equivalently the finite congruence in `solution` below. Its truncated
sum contains the j=1 term and the terms j=2 through k+1.
The coefficient of x^n/n! in F is n! times its ordinary coefficient.

Both congruences were proposed by Paul D. Hanna. The conjecture about the
formal logarithm appears in the example section. The companion ordinary
series uses 1+u in place of exp(x).

Sources: https://oeis.org/A357398 and https://oeis.org/A357397
Credit: @rleshner (agent: Codex, model: GPT-6)
-/

namespace OMA.S_oeis_a357398
open PowerSeries

noncomputable def update {R : Type*} [CommRing R] (T A : PowerSeries R) (k : ℕ) :
    PowerSeries R := 1+(1-T)*A + ∑ j ∈ Finset.range k, (1-A*T^(j+2))^(j+2)

/-- A−update is the negative of the indicated finite sum. -/
def solution {R : Type*} [CommRing R] (T A : PowerSeries R) : Prop :=
  constantCoeff A = 1 ∧ ∀ k : ℕ, X^(k+1) ∣ A - update T A k

noncomputable def negExp : PowerSeries ℚ := PowerSeries.evalNegHom (PowerSeries.exp ℚ)

noncomputable def eg (F : PowerSeries ℚ) (n : ℕ) : ℚ := n.factorial * coeff n F

def congr (q : ℚ) (r : ℤ) : Prop := ∃ z : ℤ, q = (z:ℚ) ∧ z ≡ r [ZMOD 10]

def aResidue (n : ℕ) : ℤ := [3,1,3,7][n%4]?.getD 0
def lResidue (n : ℕ) : ℤ := [8,0,2,0][n%4]?.getD 0

theorem main : (∃! A : PowerSeries ℚ, solution negExp A) ∧
    ∀ A : PowerSeries ℚ, solution negExp A →
      (∀ n : ℕ, 1 ≤ n → congr (eg A n) (aResidue n)) ∧
      (∀ n : ℕ, 2 ≤ n → congr (eg (PowerSeries.logOf A) n) (lResidue n)) := by
  sorry

end OMA.S_oeis_a357398
