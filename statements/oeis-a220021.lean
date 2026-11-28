import Mathlib

/-!
# A220021: number of cyclotomic cosets of 11 modulo powers of 10

Source: https://oeis.org/A220021
Sequence by V. Raman. Conjectures by Colin Barker, April 13, 2013.
Credit: @blakestone-x

A cycle includes every residue obtained by iterating multiplication by 11.
The zero residue forms its own cycle. The OEIS sequence begins at index one,
so its ordinary generating function has constant coefficient zero.
-/

namespace OMA.S_oeis_a220021

noncomputable def a (n : ℕ) : ℤ := Nat.cast
  (Nat.card (MulAction.orbitRel.Quotient
    (Subgroup.zpowers (ZMod.unitOfCoprime 11 ((by decide : Nat.Coprime 11 10).pow_right n)))
    (ZMod (10^n))))

noncomputable def series : PowerSeries ℤ :=
  PowerSeries.mk (fun n => if n = 0 then 0 else a n)

open PowerSeries in
theorem main :
    (∀ n : ℕ, 1 < n → a n = 8*(n:ℤ)^2-2*n-1) ∧
    (∀ n : ℕ, 4 < n → a n = 3*a (n-1)-3*a (n-2)+a (n-3)) ∧
    ((X-1)^3 : PowerSeries ℤ) * series = X * (5*X^3-14*X^2+3*X-10) := by
  sorry

end OMA.S_oeis_a220021
