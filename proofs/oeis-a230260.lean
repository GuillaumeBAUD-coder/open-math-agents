import OMAStatements.S_oeis_a230260
import Mathlib

/-!
# A230260: the statement fails for `n = 139`

The decompositions of `278` into two primes are
`7 + 271`, `37 + 241`, `67 + 211`, `79 + 199`, `97 + 181`, `127 + 151`, `139 + 139`
(and the same with the summands swapped).  In each of them the two binary digit sums add up to
an even number (for instance `7 = 111₂` and `271 = 100001111₂` give `3 + 5 = 8`), so no
decomposition has an odd total.
-/

namespace OMA.S_oeis_a230260

/-- A finite check over all `p ≤ 278`. -/
lemma no_pair : ∀ p < 279, ¬ (p.Prime ∧ (278 - p).Prime ∧
    Odd ((Nat.digits 2 p).sum + (Nat.digits 2 (278 - p)).sum)) := by
  decide +kernel

end OMA.S_oeis_a230260

open OMA.S_oeis_a230260 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a230260.main) := by
  intro h
  obtain ⟨p, q, hp, hq, hsum, hodd⟩ := h 139 (by norm_num)
  have hq' : q = 278 - p := by omega
  subst hq'
  exact no_pair p (by omega) ⟨hp, hq, hodd⟩
