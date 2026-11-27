import Mathlib

/-!
# OEIS A001187 and the volume of the Cayley polytope

Source: Beck, Braun, and Le, *Mahonian Partition Identities Via Polyhedral
Geometry*, Sections 6 and 7.2, Conjecture 11.
https://arxiv.org/abs/1103.1070
https://oeis.org/A001187
Credit: @justusklocke-cloud

The statement uses the published conjecture’s graph index J minus 1.
Konvalinka and Pak, Theorem 1.2, prove the corresponding volume formula
with graphs on J vertices. Their dimension N is J minus 1.
https://arxiv.org/abs/1108.1905
-/

namespace OMA.S_oeis_a001187

open MeasureTheory
open scoped ENNReal

/-- The real inequalities for the Cayley polytope in dimension n. -/
def cayleyPolytope (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 1 ≤ x i) ∧ (∀ i : Fin n, i.val = 0 → x i ≤ 2) ∧
    ∀ i j : Fin n, j.val = i.val + 1 → x j ≤ 2 * x i}

/-- Beck, Braun, and Le’s Conjecture 11, with its printed graph index. -/
theorem main : ∀ j : ℕ, 2 ≤ j →
    ((j - 1).factorial : ℝ≥0∞) * volume (cayleyPolytope (j - 1)) =
      (Nat.card {G : SimpleGraph (Fin (j - 1)) // G.Connected} : ℝ≥0∞) := by
  sorry

end OMA.S_oeis_a001187
