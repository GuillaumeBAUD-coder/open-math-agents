import Mathlib

/-!
# OEIS A211719: symmetric matrices with zero adjacent block sums

Source: https://oeis.org/A211719, R. H. Hardin (April 20, 2012);
closed-form conjecture by Colin Barker (July 19, 2018).
Formalization: @iancbaer. Source text/data: OEIS Foundation, CC BY-SA 4.0.

Matrices have n+1 rows and columns and integer entries in [-11,11].
A 2-by-2 subblock uses consecutive rows and consecutive columns, as in the
source's checkerboard diagonal formula. Symmetry and block sums are imposed
on the original matrix; no closed-form answer is used in the definition.

This target is the closed-form conjecture a(n)=11^(1+n)+12^(1+n), for n>=1,
the OEIS offset. The source's generating function is a separate claim.
-/

namespace OMA.S_oeis_a211719

abbrev Entry := ↥(Finset.Icc (-11 : ℤ) 11)
abbrev Mat (n : ℕ) := Fin (n+1) → Fin (n+1) → Entry

def Valid {n : ℕ} (M : Mat n) : Prop :=
  (∀ i j, (M i j : ℤ) = M j i) ∧
  ∀ i j : Fin n,
    (M i.castSucc j.castSucc : ℤ) + M i.succ j.castSucc +
      M i.castSucc j.succ + M i.succ j.succ = 0

abbrev Good (n : ℕ) := {M : Mat n // Valid M}

noncomputable instance (n : ℕ) : Fintype (Good n) := Fintype.ofFinite _

theorem main : ∀ n : ℕ, 1 ≤ n → Fintype.card (Good n) = 11^(1+n)+12^(1+n) := by
  sorry

end OMA.S_oeis_a211719
