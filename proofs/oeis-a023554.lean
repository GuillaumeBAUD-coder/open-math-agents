import OMAStatements.S_oeis_a023554
import Mathlib

-- Problem: A023554, convolution of the natural numbers >= 3 with the Fibonacci numbers.
-- Upstream: formal-conjectures statements/oeis-a023554.lean (declaration OMA.S_oeis_a023554.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here. Proof: splitting F(m+2) = F(m+1) + F(m) inside the convolution gives
-- a(n+2) = a(n+1) + a(n) + 2n + 7, and A022308(n+4) - 2(n+5) satisfies the same recurrence with
-- the same first two values.

namespace OMA.P_oeis_a023554

open OMA.S_oeis_a023554

theorem a_rec (n : ℕ) : a (n + 2) = a (n + 1) + a n + 2 * (n : ℤ) + 7 := by
  have e1 : a (n + 2) = (∑ k ∈ Finset.range (n + 1), ((k : ℤ) + 3) * (Nat.fib (n + 2 - k + 1) : ℤ))
      + ((n : ℤ) + 4) := by
    unfold a
    rw [Finset.sum_range_succ, show n + 2 - (n + 1) + 1 = 2 by omega, Nat.fib_two]
    push_cast
    ring
  have e2 : ∑ k ∈ Finset.range (n + 1), ((k : ℤ) + 3) * (Nat.fib (n + 2 - k + 1) : ℤ) =
      a (n + 1) + ∑ k ∈ Finset.range (n + 1), ((k : ℤ) + 3) * (Nat.fib (n - k + 1) : ℤ) := by
    unfold a
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [show n + 2 - k + 1 = (n - k + 1) + 2 by omega, show n + 1 - k + 1 = (n - k + 1) + 1 by omega,
      Nat.fib_add_two]
    push_cast
    ring
  have e3 : ∑ k ∈ Finset.range (n + 1), ((k : ℤ) + 3) * (Nat.fib (n - k + 1) : ℤ) =
      a n + ((n : ℤ) + 3) := by
    unfold a
    rw [Finset.sum_range_succ, show n - n + 1 = 1 by omega, Nat.fib_one]
    push_cast
    ring
  rw [e1, e2, e3]
  ring

theorem A_rec (n : ℕ) : A022308 (n + 2) = A022308 (n + 1) + A022308 n + 1 := rfl

theorem key : ∀ n : ℕ, (2 * ((n : ℤ) + 5) = A022308 (n + 4) - a (n + 1)) ∧
    (2 * (((n + 1 : ℕ) : ℤ) + 5) = A022308 (n + 1 + 4) - a (n + 1 + 1))
  | 0 => by
    refine ⟨?_, ?_⟩ <;> simp [A022308, a, Finset.sum_range_succ, Nat.fib]
  | n + 1 => by
    obtain ⟨h1, h2⟩ := key n
    refine ⟨h2, ?_⟩
    rw [show n + 1 + 1 + 4 = (n + 4) + 2 by ring, A_rec, show n + 1 + 1 + 1 = (n + 1) + 2 by ring,
      a_rec]
    rw [show n + 4 + 1 = n + 1 + 4 by ring] at *
    push_cast at h1 h2 ⊢
    linarith

theorem main' : ∀ n : ℕ, 2 * ((n : ℤ) + 5) = A022308 (n + 4) - a (n + 1) := fun n => (key n).1

end OMA.P_oeis_a023554

theorem OMA.solution : type_of% @OMA.S_oeis_a023554.main := OMA.P_oeis_a023554.main'
