import OMAStatements.S_mo_104161
import Mathlib

/-!
The two cyclic words below are 010101100101101010011010 and
010101101001101010010110, read from index zero. They are obtained by
encoding the bits of two twelve-letter words as 01 or 10. Every full
pair contributes one to a block weight, so the three endpoints govern
what changes between those words. We check the original block multisets
directly for each of the 325 possible ordered length triples.
-/

namespace WordReconstructionCounterexample

open OMA.S_mo_104161

private def firstWord (i : Fin 24) : Bool := (5855850 : ℕ).testBit i.val
private def secondWord (i : Fin 24) : Bool := (6904170 : ℕ).testBit i.val

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
private theorem sameBlocks (p : Fin 25) :
    ∀ q : Fin (25 - p.val),
      cyclicBlockCounts firstWord p.val q.val (24 - p.val - q.val) =
      cyclicBlockCounts secondWord p.val q.val (24 - p.val - q.val) := by
  fin_cases p <;> decide +kernel

private theorem differentRotations :
    ∀ t : Fin 24, ∃ i : Fin 24, cyclicBit firstWord i t.val ≠ secondWord i := by
  decide +kernel

theorem fails : ¬ (type_of% @OMA.S_mo_104161.main) := by
  intro reconstruction
  have agree : ∀ p q r : ℕ, p + q + r = 24 →
      cyclicBlockCounts firstWord p q r = cyclicBlockCounts secondWord p q r := by
    intro p q r h
    have hr : r = 24 - p - q := by omega
    rw [hr]
    exact sameBlocks ⟨p, by omega⟩ ⟨q, by change q < 25 - p; omega⟩
  obtain ⟨t, ht⟩ := reconstruction 24 firstWord secondWord agree
  obtain ⟨i, hi⟩ := differentRotations ⟨t % 24, Nat.mod_lt _ (by decide)⟩
  apply hi
  simpa [cyclicBit, Nat.add_mod] using ht i

end WordReconstructionCounterexample

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_104161.main) :=
  WordReconstructionCounterexample.fails
