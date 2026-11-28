import Mathlib

/-!
# Ordered arrangements with two distinct witnesses, OEIS A183878

Source: https://oeis.org/A183878
Credit: @physbuzz. The word model follows the related A183885 formalization.
For each position in an ordered word of length n+2, choose two distinct
other positions. Their entries must sum to the tested entry modulo 4.
Positions carrying the same value may be chosen if the positions differ.
The sequence starts at one. The claims are Kotesovec's empirical formula
and both of Barker's generating-function and recurrence conjectures.
-/

namespace OMA.S_oeis_a183878

def Valid {N : ℕ} (w : Fin N → Fin 4) : Prop :=
  ∀ i : Fin N, ∃ t : Finset (Fin N), t.card = 2 ∧ i ∉ t ∧
    (∑ j ∈ t, (w j).val) % 4 = (w i).val

instance (N : ℕ) : DecidablePred (@Valid N) := fun w => by
  unfold Valid
  infer_instance

def a (n : ℕ) : ℤ :=
  if n = 0 then 0 else ((Finset.univ.filter (@Valid (n + 2))).card : ℤ)

open PowerSeries in
theorem main :
    (∀ n : ℕ, 3 ≤ n → a n = 4^(n+2) - (2*(n : ℤ)+7)*2^(n+2) - 2*(n : ℤ)^3 - 9*(n : ℤ)^2 - 10*(n : ℤ) + 3) ∧
    (PowerSeries.mk a * ((1-X)^4*(1-2*X)^2*(1-4*X)) = X*(4 - 13*X + 258*X^2 - 1087*X^3 + 1318*X^4 + 444*X^5 - 2040*X^6 + 1536*X^7 - 384*X^8)) ∧
    (∀ n : ℕ, 9 < n → a n = 12*a (n-1) - 58*a (n-2) + 148*a (n-3) - 217*a (n-4) + 184*a (n-5) - 84*a (n-6) + 16*a (n-7)) := by
  sorry

end OMA.S_oeis_a183878
