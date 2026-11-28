import OMAStatements.S_oeis_a052130
import Mathlib

/-! At n=m=2 the proposed inequality is true, but the count changes from
one to four at m=3. The latter four integers are the primes 2, 3, 5, 7. -/
namespace Deldor14.FactorCount
open OMA.S_oeis_a052130
private lemma two : N 2 2 = 1 := by decide +kernel
private lemma three : N 3 2 = 4 := by decide +kernel
theorem refute : ¬(type_of% @OMA.S_oeis_a052130.main) := by
  intro h
  have e := (h 2 2 (by decide) (by decide)).mpr (by decide) 3 (by decide)
  rw [two,three] at e
  contradiction
end Deldor14.FactorCount
theorem OMA.disproof : ¬(type_of% @OMA.S_oeis_a052130.main) := Deldor14.FactorCount.refute
