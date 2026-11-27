import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Callan's final-ascent conjecture for A001764

Source: https://oeis.org/A001764 (David Callan, 22 July 2008).
The index `n` is positive, since the two final positions must exist.
Positions and values use `Fin`, so the classical patterns use zero-based ranks.
-/

namespace OMA.S_oeis_a001764

/-- A classical pattern occurs on a strictly increasing sequence of positions. -/
def Contains {k m : ℕ} (pattern : Fin k → ℕ) (p : Equiv.Perm (Fin m)) : Prop :=
  ∃ positions : Fin k → Fin m, StrictMono positions ∧
    ∀ i j, pattern i < pattern j ↔ p (positions i) < p (positions j)

instance {k m : ℕ} (pattern : Fin k → ℕ) (p : Equiv.Perm (Fin m)) :
    Decidable (Contains pattern p) := by
  change Decidable (∃ positions : Fin k → Fin m,
    (∀ i j : Fin k, i < j → positions i < positions j) ∧
    ∀ i j : Fin k, pattern i < pattern j ↔ p (positions i) < p (positions j))
  infer_instance

/-- The qualifying permutations of length `n + 1`. -/
def finalAscentAvoiders (n : ℕ) (hn : 0 < n) :
    Finset (Equiv.Perm (Fin (n + 1))) :=
  Finset.univ.filter fun p =>
    ¬ Contains ![3, 1, 2, 0] p ∧ ¬ Contains ![3, 1, 4, 0, 2] p ∧
    p ⟨n - 1, by omega⟩ < p (Fin.last n)

theorem main : ∀ (n : ℕ) (hn : 0 < n),
    (finalAscentAvoiders n hn).card = (3 * n).choose n / (2 * n + 1) := by
  sorry

end OMA.S_oeis_a001764
