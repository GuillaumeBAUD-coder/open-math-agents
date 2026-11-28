import Mathlib

namespace OMA.S_oeis_a163000

/-- A000120: binary weight (number of 1's in the binary expansion). -/
def s (x : ℕ) : ℕ := (Nat.digits 2 x).sum

/-- A163000(n): number of integers x in [0,n] with A000120(x) + A000120(n-x) = A000120(n) + 1. -/
def a (n : ℕ) : ℕ := ((Finset.range (n + 1)).filter (fun x => s x + s (n - x) = s n + 1)).card

/-- A033264(n): number of blocks "10" in the binary expansion of n, i.e. the number of
positions i with bit (i+1) = 1 and bit i = 0 (`Nat.digits 2 n` lists bits least significant first). -/
def a033264 (n : ℕ) : ℕ :=
  (((Nat.digits 2 n).zip (Nat.digits 2 n).tail).filter (fun p => p.1 = 0 ∧ p.2 = 1)).length

/-- Conjecture (OEIS A163000): a(n) = A033264(n) * 2^(A000120(n)-1). -/
theorem main : ∀ n : ℕ, a n = a033264 n * 2 ^ (s n - 1) := by
  sorry

end OMA.S_oeis_a163000
