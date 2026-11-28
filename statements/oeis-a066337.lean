import Mathlib

/-!
# OEIS A066337: the least binary preimage

In A066327 the four low bits of an ordinary binary integer have weights
−1, 1, 3 and 6. All higher bits retain their usual values. The source
definition permits ties. R. J. Mathar's PARI program tries candidate
integers in increasing order and uses the first one, and he observed the
recurring sixteen-term pattern. A066337 takes the decimal value of the
selected string and records −1 when there is no preimage.

Chai Wah Wu proposed the recurrence and generating function on April 18,
2024. The denominator has constant coefficient 1, so the series identity
below is equivalent to the proposed quotient.

Sources: https://oeis.org/A066337 and https://oeis.org/A066327
Credit: @rleshner (agent: Codex, model: GPT-6)
-/

namespace OMA.S_oeis_a066337

def low (r : ℕ) : ℤ :=
  -(r%2 : ℕ) + ((r/2)%2 : ℕ) + 3*((r/4)%2 : ℕ) + 6*((r/8)%2 : ℕ)

def value (m : ℕ) : ℤ := 16*(m/16 : ℕ) + low (m%16)

open Classical in
noncomputable def a (n : ℕ) : ℤ :=
  if h : ∃ m : ℕ, value m = (n:ℤ) then (Nat.find h : ℕ) else -1

def recurrence : Prop := ∀ n : ℕ, 28 < n →
  a n = a (n-1)-a (n-4)+a (n-5)-a (n-8)+a (n-9)-a (n-12)+a (n-13)+a (n-16)-
    a (n-17)+a (n-20)-a (n-21)+a (n-24)-a (n-25)+a (n-28)-a (n-29)

open PowerSeries

noncomputable def numerator : PowerSeries ℤ :=
  X*(-X^27+2*X^26-X^23+3*X^22+2*X^21-X^20+2*X^19+5*X^18+X^17+2*X^16+
     4*X^15+4*X^14+4*X^13+4*X^12+5*X^11-14*X^10+4*X^9+4*X^8+5*X^7+X^6+
     2*X^5+5*X^4+2*X^3-X^2+3*X+2)

noncomputable def denominator : PowerSeries ℤ :=
  (X-1)^2*(X+1)*(X^2+1)*(X^4+1)^2*(X^8+1)^2

def generatingFunction : Prop := denominator * PowerSeries.mk a = numerator

theorem main : recurrence ∧ generatingFunction := by
  sorry

end OMA.S_oeis_a066337
