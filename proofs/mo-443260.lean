import OMAStatements.S_mo_443260
import Mathlib.Order.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith

/-!
A five-element counterexample to the finite representability question.
Order subsets by weights (14, 6, 12, 22, 5), exchanging the two consecutive
subset scores 28 and 31. The finite order and disjoint-union axiom are checked
by the Lean kernel. Four balanced strict comparisons rule out real weights.

Nonrepresentable orders of this kind are classical; see the discussion of
Kraft, Pratt and Seidenberg (1959) in Conder and Slinko (2003):
https://www.math.auckland.ac.nz/Research/Reports/Series/509.pdf

Related prior Lean work formalizes the classical qualitative-probability
counterexample in Linglib, using a different five-atom order and a probability
measure representation predicate:
https://github.com/linglib-community/linglib/blob/13f6d206b709d706d5fb6ae9f6d955896951ecc7/Linglib/Logic/ComparativeProbability/Completeness.lean
-/

namespace OMA.S_mo_443260

open scoped BigOperators

private def weight (i : Fin 5) : ℕ :=
  match i.val with
  | 0 => 14
  | 1 => 6
  | 2 => 12
  | 3 => 22
  | _ => 5

private def score (s : Finset (Fin 5)) : ℕ :=
  let t := ∑ i ∈ s, weight i
  if t = 28 then 31 else if t = 31 then 28 else t

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem score_injective : Function.Injective score := by
  decide

private abbrev subsetOrder : LinearOrder (Finset (Fin 5)) :=
  LinearOrder.lift' score score_injective

private abbrev DisjointPair :=
  {p : Finset (Fin 5) × Finset (Fin 5) // Disjoint p.1 p.2}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem pairs_compatible : ∀ p q : DisjointPair,
    score p.val.1 < score q.val.1 → score p.val.2 ≤ score q.val.2 →
      score (p.val.1 ∪ p.val.2) < score (q.val.1 ∪ q.val.2) := by
  decide

private theorem subsetOrder_compatible : ∀ A A' B B' : Finset (Fin 5),
    subsetOrder.lt A A' → subsetOrder.le B B' → Disjoint A B → Disjoint A' B' →
      subsetOrder.lt (A ∪ B) (A' ∪ B') := by
  intro A A' B B' hA hB hAB hAB'
  exact pairs_compatible ⟨(A, B), hAB⟩ ⟨(A', B'), hAB'⟩ hA hB

private theorem no_weights :
    ¬ ∃ f : Fin 5 → ℝ, ∀ A B : Finset (Fin 5),
      subsetOrder.lt A B ↔ (∑ i ∈ A, f i) < ∑ i ∈ B, f i := by
  rintro ⟨f, hf⟩
  have h₁ := (hf {1, 4} {2}).mp (by decide)
  have h₂ := (hf {1, 2} {0, 4}).mp (by decide)
  have h₃ := (hf {3} {1, 2, 4}).mp (by decide)
  have h₄ := (hf {0, 2, 4} {1, 3}).mp (by decide)
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton] at h₁ h₂ h₃ h₄
  linarith

end OMA.S_mo_443260


theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_443260.main) := by
  intro h
  exact OMA.S_mo_443260.no_weights
    (h 5 OMA.S_mo_443260.subsetOrder OMA.S_mo_443260.subsetOrder_compatible)
