import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod

/-!
# OEIS A394659: independent seven-vertex subsets of a triangular grid

Source: https://oeis.org/A394659, revision 11 (March 31, 2026), Eric W. Weisstein.
For every natural n greater than 3, the entry conjectures a closed formula for
the number of independent seven-element vertex subsets in the triangular grid
graph with n edges on each exterior side (the entry's own convention). The
denominator is cleared over the integers.
Credit: Sarkis Avetisyan, Vynet (@vynet-ai). Mathematics with GPT-6.2 Sol and other OpenAI models, checked with Claude.
-/

namespace OMA.S_oeis_a394659

abbrev Vertex := ℕ × ℕ

def vertices (n : ℕ) : Finset Vertex :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
    (fun p => p.1 + p.2 ≤ n)

def adjacent (p q : Vertex) : Prop :=
  let dx : ℤ := (p.1 : ℤ) - (q.1 : ℤ)
  let dy : ℤ := (p.2 : ℤ) - (q.2 : ℤ)
  dx.natAbs + dy.natAbs + (dx + dy).natAbs = 2

instance (p q : Vertex) : Decidable (adjacent p q) := by
  unfold adjacent
  infer_instance

def count (n : ℕ) : ℕ :=
  ((vertices n).powersetCard 7).filter
    (fun s => ∀ p ∈ s, ∀ q ∈ s, ¬adjacent p q) |>.card

def numerator (n : ℤ) : ℤ :=
  (n - 4) * (n^13 + 25*n^12 + 9*n^11 - 3555*n^10 - 7745*n^9
    + 260563*n^8 + 291075*n^7 - 11898033*n^6 + 10339924*n^5
    + 303368632*n^4 - 909281184*n^3 - 2609966352*n^2
    + 16737321600*n - 23213352960)

theorem main :
    ∀ n : ℕ, 3 < n → 645120 * (count n : ℤ) = numerator (n : ℤ) := by
  sorry

end OMA.S_oeis_a394659
