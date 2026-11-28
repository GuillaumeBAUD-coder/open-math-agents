import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace OMA.S_mo_242940

def cutoff (m : ℕ) : ℕ :=
  (m.choose 2 + 1) / 2

/-- The recurrence starting at row `base`, with that row initialized to
`δ(n,0)` and negative-index terms treated as zero. The printed recurrence
starts at row 0, while the author's MATLAB code starts at row 1. -/
def count (base : ℕ) : ℕ → ℕ → ℕ
  | 0, n => if n = 0 then 1 else 0
  | m+1, n =>
    if base ≤ m then
      (if n ≤ cutoff (m+1) then count base m n else 0) +
        (if m+1 ≤ n then count base m (n-(m+1)) else 0)
    else count base m n

def weight (S : Finset ℕ) : ℕ :=
  ∑ j ∈ S, j

/-- An omitted index imposes its cutoff on the selected prefix. -/
def Allowed (base m : ℕ) (S : Finset ℕ) : Prop :=
  ∀ i ∈ Finset.Icc (base+1) m, i ∉ S → weight (S.filter (fun j => j ≤ i)) ≤ cutoff i

noncomputable def allowedSubsets (base m : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.Icc (base+1) m).powerset.filter (Allowed base m)

noncomputable def generating (base m : ℕ) : Polynomial ℕ :=
  ∑ S ∈ allowedSubsets base m, (Polynomial.X : Polynomial ℕ) ^ weight S

/-- A nonrecursive generating polynomial for each row of the recurrence. -/
theorem main :
    ∀ base m n : ℕ, (generating base m).coeff n = count base m n := by
  sorry

end OMA.S_mo_242940
