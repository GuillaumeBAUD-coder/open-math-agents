import OMAStatements.S_oeis_a195915

-- Credit: @dwilfand-sys. The triangle was formalized by @senamakel.
-- Source: OEIS A195915, the power-of-two shift conjecture.

namespace OMA.XorTriangle

open OMA.S_oeis_a195915

lemma outside (n k : ℕ) (h : n ≤ k) : entry n k = 0 := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k =>
      change (entry n k ^^^ entry n (k + 1)) = 0
      rw [ih k (by omega), ih (k + 1) (by omega), Nat.xor_zero]

lemma cancelMiddle (a b c : ℕ) :
    Nat.xor (Nat.xor a b) (Nat.xor b c) = Nat.xor a c := by
  change ((a ^^^ b) ^^^ (b ^^^ c)) = a ^^^ c
  rw [Nat.xor_assoc a b, ← Nat.xor_assoc b b, Nat.xor_self, Nat.zero_xor]

lemma shift (j n k : ℕ) :
    entry (n + 2^j) (k + 2^j) = Nat.xor (entry n k) (entry n (k + 2^j)) := by
  induction j generalizing n k with
  | zero => rfl
  | succ j ih =>
    simp only [pow_succ, Nat.mul_two, ← Nat.add_assoc]
    rw [ih (n + 2^j) (k + 2^j), ih n k, ih n (k + 2^j), cancelMiddle]

end OMA.XorTriangle

open OMA.S_oeis_a195915 OMA.XorTriangle

theorem OMA.solution : type_of% @OMA.S_oeis_a195915.main := by
  intro j n k _ hn
  rw [Nat.add_comm (2^j) n, Nat.add_comm (2^j) k, shift,
    outside n (k + 2^j) (by omega)]
  exact Nat.xor_zero _
