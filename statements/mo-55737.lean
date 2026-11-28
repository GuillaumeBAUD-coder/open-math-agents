import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card

/-!
# Shortest relations on two marked generators

Source: https://mathoverflow.net/questions/55737 (Andreas Thom).
Credit: @witeg4

A marked two-generator group is represented by its kernel in the rank-two free
group. A reduced word is counted individually, including its cyclic permutations
and inverse whenever these are different words. The question asks for the
maximum at each length and whether a sequence of groups can improve the stated
random-group benchmark. No exact formula for the maximum is proposed.

We express improvement on the exponential scale: one family outgrows
3^((1/2-ε)n) by an unbounded factor tending to infinity for each fixed ε > 0.
This does not prescribe a random model or a presentation algorithm.
-/

namespace OMA.S_mo_55737

abbrev F := FreeGroup (Fin 2)

def noShort (K : Subgroup F) (n : ℕ) : Prop :=
  ∀ w ∈ K, FreeGroup.norm w ≤ n → w = 1

noncomputable def relationCount (K : Subgroup F) (n : ℕ) : ℕ :=
  {w : F | w ∈ K ∧ FreeGroup.norm w = n + 1}.ncard

def attainable (n : ℕ) : Set ℕ :=
  {m | ∃ K : Subgroup F, K.Normal ∧ noShort K n ∧ relationCount K n = m}

theorem main :
    ∃ K : ℕ → Subgroup F, (∀ n, (K n).Normal ∧ noShort (K n) n ∧
      IsGreatest (attainable n) (relationCount (K n) n)) ∧
      ∀ ε : ℝ, 0 < ε → Filter.Tendsto
        (fun n : ℕ => (relationCount (K n) n : ℝ) /
          (3 : ℝ) ^ (((1 : ℝ) / 2 - ε) * n)) Filter.atTop Filter.atTop := by
  sorry

end OMA.S_mo_55737
