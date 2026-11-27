import OMAStatements.S_oeis_a113249

-- Credit: @yuka30240
open OMA.S_oeis_a113249

theorem OMA.solution : type_of% @OMA.S_oeis_a113249.main := by
  intro m n
  let d : ℤ := 4 - (m : ℤ) ^ 2
  -- X and Y are the coefficients of (2 + t)(x + yt) modulo t² = d.
  let X (x y : ℤ) := 2 * x + d * y
  let Y (x y : ℤ) := x + 2 * y
  let E (x y : ℤ) := -(x ^ 2) - d * x * y - d * y ^ 2
  -- Advancing the pair (x,y) once accounts for two steps of the recurrence.
  have block (k : ℕ) : ∃ x y : ℤ,
      a m (2 * k) = E x y ∧ a m (2 * k + 1) = (X x y) ^ 2 ∧
      a m (2 * k + 2) = E (X x y) (Y x y) ∧
      a m (2 * k + 3) = (X (X x y) (Y x y)) ^ 2 := by
    induction k with
    | zero =>
      refine ⟨1, 0, ?_⟩
      norm_num [a, E, X, Y, d]
      constructor <;> ring
    | succ k ih =>
      obtain ⟨x, y, h₀, h₁, h₂, h₃⟩ := ih
      refine ⟨X x y, Y x y, h₂, h₃, ?_, ?_⟩ <;>
        simp only [Nat.mul_succ, Nat.add_assoc, Nat.reduceAdd, a, h₀, h₁, h₂, h₃, E, X, Y, d] <;>
        ring
  obtain ⟨x, y, _, h, _⟩ := block n
  exact ⟨X x y, h.trans (pow_two _)⟩
