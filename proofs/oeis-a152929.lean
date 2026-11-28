import OMAStatements.S_oeis_a152929

-- Problem: A152929: Number of sets (in the Hausdorff metric geometry) at each location between two sets defining a polygonal configuration consisting of two 4-gonal polygonal components chained with string components of length l as l varies.
-- Upstream: formal-conjectures statements/oeis-a152929.lean:0 (declaration OMA.S_oeis_a152929.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Both sides satisfy the Fibonacci recurrence and agree at n = 1 and n = 2, so the identity follows
by induction on consecutive pairs. -/

namespace A152929Aux

open OMA.S_oeis_a152929

theorem both (n : ℕ) :
    2 * a (n + 1) = 163 * (Nat.fib (n + 1) : ℤ) + 63 * lucas (n + 1) ∧
      2 * a (n + 2) = 163 * (Nat.fib (n + 2) : ℤ) + 63 * lucas (n + 2) := by
  induction n with
  | zero => exact ⟨by simp [a, lucas], by simp [a, lucas]⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    have ea : a (k + 1 + 2) = a (k + 2) + a (k + 1) := rfl
    have el : lucas (k + 1 + 2) = lucas (k + 2) + lucas (k + 1) := rfl
    have ef : (Nat.fib (k + 1 + 2) : ℤ) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
      rw [Nat.fib_add_two]
      push_cast
      ring
    rw [ea, el, ef]
    linarith

end A152929Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a152929.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (A152929Aux.both m).1
