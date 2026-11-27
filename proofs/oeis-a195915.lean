import OMAStatements.S_oeis_a195915

namespace OMA.A195915Proof

open OMA.S_oeis_a195915

private lemma entry_eq_zero_of_le (m c : ℕ) (h : m ≤ c) : entry m c = 0 := by
  induction m generalizing c with
  | zero => simp [entry]
  | succ m ih =>
    cases c with
    | zero => omega
    | succ c => simp [entry, ih c (by omega), ih (c + 1) (by omega)]

private lemma entry_add_pow_two (j m k : ℕ) :
    entry (m + 2 ^ j) (k + 2 ^ j) = Nat.xor (entry m k) (entry m (k + 2 ^ j)) := by
  induction j generalizing m k with
  | zero => simp [entry]
  | succ j ih =>
    have hpow : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [Nat.pow_succ, Nat.mul_two]
    rw [hpow, ← Nat.add_assoc m, ← Nat.add_assoc k]
    rw [ih (m + 2 ^ j) (k + 2 ^ j), ih m k, ih m (k + 2 ^ j)]
    have hxor : ∀ a b : ℕ, Nat.xor a b = a ^^^ b := fun _ _ => rfl
    simp only [hxor]
    rw [Nat.xor_assoc, ← Nat.xor_assoc (entry m (k + 2 ^ j)), Nat.xor_self, Nat.zero_xor]

end OMA.A195915Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a195915.main := by
  intro j n k _ hn
  have hxor : ∀ a b : ℕ, Nat.xor a b = a ^^^ b := fun _ _ => rfl
  rw [Nat.add_comm (2 ^ j) n, Nat.add_comm (2 ^ j) k]
  rw [OMA.A195915Proof.entry_add_pow_two]
  rw [OMA.A195915Proof.entry_eq_zero_of_le n (k + 2 ^ j) (by omega), hxor, Nat.xor_zero]
