import Mathlib

/-!
# Erdős Problem 1212

Source: https://www.erdosproblems.com/1212
Credit: @joshuadc11

Let `G` be the graph with vertex set those pairs `(x, y) ∈ ℕ²` with `gcd(x, y) = 1`, in which
we join two vertices if they differ in only one coordinate, and there by `± 1`.
Is there a path going to infinity on `G`, say `P`, such that for all `(x, y) ∈ P` both
`min(x, y) > 1` and at least one of `x` or `y` is composite?

Formalization notes:
- A path going to infinity in `G` is represented as an injective sequence `p : ℕ → ℕ × ℕ` of
  vertices of `G` (`Nat.Coprime (p n).1 (p n).2`) with consecutive vertices adjacent
  (`LatticeAdj (p n) (p (n + 1))`). Since `ℕ × ℕ` has only finitely many points in any bounded
  region, injectivity ensures the path goes to infinity.
- Since both coordinates satisfy `1 < x` and `1 < y`, being composite is equivalent to `¬ Prime`.
-/

namespace OMA.S_erdos_1212

/-- Two lattice points in `ℕ × ℕ` are adjacent if they differ in exactly one coordinate
by `± 1`. -/
def LatticeAdj (u v : ℕ × ℕ) : Prop :=
  (u.1 = v.1 ∧ (u.2 + 1 = v.2 ∨ v.2 + 1 = u.2)) ∨
  (u.2 = v.2 ∧ (u.1 + 1 = v.1 ∨ v.1 + 1 = u.1))

theorem main :
    ∃ p : ℕ → ℕ × ℕ,
      Function.Injective p ∧
      (∀ n, Nat.Coprime (p n).1 (p n).2) ∧
      (∀ n, LatticeAdj (p n) (p (n + 1))) ∧
      (∀ n, 1 < min (p n).1 (p n).2) ∧
      (∀ n, ¬ (p n).1.Prime ∨ ¬ (p n).2.Prime) := by
  sorry

end OMA.S_erdos_1212
