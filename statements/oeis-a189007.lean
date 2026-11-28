import Mathlib

/-!
# A189007: Number of ON cells of Layman's diamond automaton

Sources: https://oeis.org/A189007 and https://oeis.org/A056791
(OEIS Foundation, CC BY-SA 4.0).

At time zero only the origin is ON. Each later cell is ON when exactly
one of its two horizontal neighbors is ON or exactly one of its two
vertical neighbors is ON, allowing both conditions to hold. Time zero
here corresponds to generation 1 in the OEIS numbering.

Michael De Vlieger's conjectured count for positive time t is two raised
to the sum of the binary length and binary weight of t. The finite
square in the definition contains all cells that can be reached by
time t, since each update uses neighbors at distance one.
-/

namespace OMA.S_oeis_a189007

/-- State at integer coordinates after t updates. -/
def grid : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y =>
      (grid t (x - 1) y != grid t (x + 1) y) ||
      (grid t x (y - 1) != grid t x (y + 1))

/-- The number of ON cells at time t, corresponding to A189007(t+1). -/
noncomputable def onCount (t : ℕ) : ℕ :=
  (((Finset.Icc (-(t : ℤ)) t) ×ˢ (Finset.Icc (-(t : ℤ)) t)).filter
    (fun xy => grid t xy.1 xy.2 = true)).card

theorem main : onCount 0 = 1 ∧ ∀ t : ℕ, 0 < t →
    onCount t = 2 ^ ((Nat.digits 2 t).length + (Nat.digits 2 t).sum) := by
  sorry

end OMA.S_oeis_a189007
