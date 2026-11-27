import OMAStatements.S_oeis_a195915
import Mathlib
open OMA.S_oeis_a195915

theorem a195915_zero : ∀ n k : ℕ, n ≤ k → entry n k = 0
  | 0, _, _ => by simp [entry]
  | n+1, 0, h => absurd h (by omega)
  | n+1, k+1, h => by
      have h1 := a195915_zero n k (by omega)
      have h2 := a195915_zero n (k+1) (by omega)
      show Nat.xor (entry n k) (entry n (k+1)) = 0
      rw [h1, h2]
      rfl

theorem a195915_key (j : ℕ) :
    ∀ m k : ℕ, entry (m + 2^j) (k + 2^j) = entry m k ^^^ entry m (k + 2^j) := by
  induction j with
  | zero => intro m k; rfl
  | succ j ih =>
    intro m k
    have h1 : m + 2^(j+1) = (m + 2^j) + 2^j := by ring
    have h2 : k + 2^(j+1) = (k + 2^j) + 2^j := by ring
    rw [h1, h2, ih (m + 2^j) (k + 2^j), ih m k, ih m (k + 2^j)]
    rw [Nat.xor_assoc, ← Nat.xor_assoc (entry m (k + 2^j)), Nat.xor_self, Nat.zero_xor]

theorem OMA.solution : type_of% @OMA.S_oeis_a195915.main := by
  intro j n k _ hn
  rw [Nat.add_comm (2^j) n, Nat.add_comm (2^j) k, a195915_key,
    a195915_zero n (k + 2^j) (by omega), Nat.xor_zero]
