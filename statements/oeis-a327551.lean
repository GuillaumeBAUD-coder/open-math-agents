import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Field.ZMod

/-!
# OEIS A327551, cycles of the perfect out-shuffle

Source: https://oeis.org/A327551
Sequence by Jeffrey Shallit. Conjecture by N. J. A. Sloane, September 16, 2019.
Credit: @blakestone-x

Write the half-deck size as k+1, so the two other sequences have index k.
Number positions from zero. The bottom card is represented by none. The
other positions are represented by their ordinary residues from 0 to 2k.
A card from the top half goes to an even position. A card from the bottom
half goes to an odd position. Cycles include singletons.
-/

namespace OMA.S_oeis_a327551

abbrev Residue (k : ℕ) := ZMod (2*k+1)

/-- Destination of each card in the interleaved deck. -/
def shuffle (k : ℕ) : Option (Residue k) → Option (Residue k) :=
  Option.map fun i =>
    if i.val < k+1 then ((2*i.val : ℕ) : Residue k)
    else ((2*(i.val-(k+1))+1 : ℕ) : Residue k)

/-- Count distinct forward orbits of the shuffle, including fixed cards. -/
noncomputable def shuffleCycles (k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.image (fun x : Option (Residue k) =>
    Set.range (fun t : ℕ => (shuffle k)^[t] x))).card

/-- A006694 excludes the singleton orbit of zero. -/
noncomputable def nonzeroCosets (k : ℕ) : ℕ := by
  classical
  exact ((Finset.univ.erase (0 : Residue k)).image (fun x =>
    Set.range (fun t : ℕ => (2 : Residue k)^t * x))).card

/-- A081844 counts distinct monic irreducible factors over the two-element field. -/
noncomputable def factorCount (k : ℕ) : ℕ :=
  (UniqueFactorizationMonoid.normalizedFactors
    ((Polynomial.X : Polynomial (ZMod 2))^(2*k+1) - 1)).toFinset.card

theorem main : ∀ k : ℕ, shuffleCycles k = nonzeroCosets k + 2 ∧
    shuffleCycles k = factorCount k + 1 := by
  sorry

end OMA.S_oeis_a327551
