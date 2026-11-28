import FormalConjectures.OEIS.«38098»

/-!
# Reduction OeisA38098.conjecture2.R2

Zhi-Wei Sun's conjecture (ii) on A038098 is a conjunction of two independent claims about the
ratio `pi(n^2) / n^2`:

* `H1` -- the injectivity claim: the values `pi(n^2) / n^2` are pairwise distinct for
  `n >= 1` (no two of them are equal).
* `H2` -- the monotonicity claim: the ratio is strictly decreasing for `n > 15646`.

Neither implies the other (injectivity of a sequence says nothing about its eventual
monotonicity, and eventual strict decrease does not preclude an earlier coincidence), so this
splits the open problem into two separate sub-problems; `main` is their conjunction.
-/

namespace OMA.R_OeisA38098_conjecture2_R2

/-- The injectivity half: `pi(m^2) / m^2 = pi(n^2) / n^2` with `m, n >= 1` forces `m = n`. -/
def H1 : Prop :=
  ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
    (Nat.primeCounting (m ^ 2) : ℚ) / (m ^ 2 : ℚ) =
    (Nat.primeCounting (n ^ 2) : ℚ) / (n ^ 2 : ℚ) → m = n

/-- The monotonicity half: the ratio strictly decreases for `n > 15646`. -/
def H2 : Prop :=
  ∀ n : ℕ, 15646 < n →
    (Nat.primeCounting ((n + 1) ^ 2) : ℚ) / ((n + 1) ^ 2 : ℚ) <
    (Nat.primeCounting (n ^ 2) : ℚ) / (n ^ 2 : ℚ)

theorem main : H1 → H2 → type_of% @OeisA38098.conjecture2 := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_OeisA38098_conjecture2_R2
