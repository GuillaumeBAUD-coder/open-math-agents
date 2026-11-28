import Mathlib

/-!
# Ordered arrangements with two distinct witnesses, OEIS A183879

Source: https://oeis.org/A183879
Credit: @physbuzz. The word model follows the related A183885 formalization.
For each position in an ordered word of length n+2, choose two distinct
other positions. Their entries must sum to the tested entry modulo 5.
Positions carrying the same value may be chosen if the positions differ.
The sequence starts at one. The claims are Kotesovec's empirical formula
and both of Barker's generating-function and recurrence conjectures.
-/

namespace OMA.S_oeis_a183879

def Valid {N : ℕ} (w : Fin N → Fin 5) : Prop :=
  ∀ i : Fin N, ∃ t : Finset (Fin N), t.card = 2 ∧ i ∉ t ∧
    (∑ j ∈ t, (w j).val) % 5 = (w i).val

instance (N : ℕ) : DecidablePred (@Valid N) := fun w => by
  unfold Valid
  infer_instance

def a (n : ℕ) : ℤ :=
  if n = 0 then 0 else ((Finset.univ.filter (@Valid (n + 2))).card : ℤ)

open PowerSeries in
theorem main :
    (∀ n : ℕ, 2 ≤ n → a n = 5^(n+2) - (10*(n : ℤ)^2+70*(n : ℤ)+124)*2^n + 2*(3*(n : ℤ)+8)*((n : ℤ)^2+5*(n : ℤ)+8)) ∧
    (PowerSeries.mk a * ((1-X)^4*(1-2*X)^3*(1-5*X)) = X*(1 + 10*X + 538*X^2 - 1960*X^3 + 701*X^4 + 4706*X^5 - 7204*X^6 + 4312*X^7 - 960*X^8)) ∧
    (∀ n : ℕ, 9 < n → a n = 15*a (n-1) - 92*a (n-2) + 306*a (n-3) - 609*a (n-4) + 747*a (n-5) - 554*a (n-6) + 228*a (n-7) - 40*a (n-8)) := by
  sorry

end OMA.S_oeis_a183879
