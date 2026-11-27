import OMAStatements.S_oeis_a195915
import Mathlib

namespace A195915Proof
open OMA.S_oeis_a195915

lemma entry_out : ∀ n k : ℕ, n ≤ k → entry n k = 0
  | 0, _, _ => by simp [entry]
  | n+1, 0, h => by omega
  | n+1, k+1, h => by
      rw [entry, entry_out n k (by omega), entry_out n (k+1) (by omega)]
      rfl

lemma step (n k : ℕ) : entry (n+1) (k+1) = Nat.xor (entry n k) (entry n (k+1)) := by
  rw [entry]

lemma xor_cancel (a b c : ℕ) : Nat.xor (Nat.xor a b) (Nat.xor b c) = Nat.xor a c := by
  show (a ^^^ b) ^^^ (b ^^^ c) = a ^^^ c
  rw [Nat.xor_assoc, ← Nat.xor_assoc b b c, Nat.xor_self, Nat.zero_xor]

lemma double (j : ℕ) : ∀ n k : ℕ,
    entry (n + 2^j) (k + 2^j) = Nat.xor (entry n k) (entry n (k + 2^j)) := by
  induction j with
  | zero =>
    intro n k
    simpa using step n k
  | succ j ih =>
    intro n k
    have e : 2^(j+1) = 2^j + 2^j := by ring
    rw [e, ← add_assoc, ← add_assoc, ih (n + 2^j) (k + 2^j), ih n k, ih n (k + 2^j)]
    exact xor_cancel _ _ _

end A195915Proof

open OMA.S_oeis_a195915 A195915Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a195915.main := by
  intro j n k hkn hn
  rw [add_comm (2^j) n, add_comm (2^j) k, double, entry_out n (k + 2^j) (by omega)]
  show entry n k ^^^ 0 = entry n k
  exact Nat.xor_zero _
