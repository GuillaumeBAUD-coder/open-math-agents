import OMAStatements.S_oeis_a112725
import Mathlib

/-!
# A112725: the conjecture A062567(3^n) = 10^(3^(n-2)) - 1 fails at n = 5

The statement is false, so this file proves its negation with an explicit counterexample.

For n = 5 the conjecture says A062567(243) = 10^27 - 1. But k = 4899999987 = 243 * 20164609
is a positive multiple of 243 whose reverse 7899999984 = 243 * 32510288 is also a multiple
of 243. Since A062567(243) is the least such number, it is at most 4899999987, which is far
smaller than 10^27 - 1.
-/

namespace OMA.P112725

open OMA.S_oeis_a112725

/-- The reverse of 4899999987 is 7899999984. -/
theorem rev_k : rev 4899999987 = 7899999984 := by
  norm_num [rev, Nat.ofDigits_cons, Nat.ofDigits_nil]

/-- The number 4899999987 belongs to the set defining A062567(3^5). -/
theorem mem_k : 4899999987 ∈ {k : ℕ | 0 < k ∧ 3 ^ 5 ∣ k ∧ 3 ^ 5 ∣ rev k} := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [rev_k]
  norm_num

end OMA.P112725

/-- The conjecture fails at n = 5: A062567(243) is at most 4899999987, not 10^27 - 1. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a112725.main) := by
  intro h
  have h5 := h 5 (by norm_num)
  have hle : OMA.S_oeis_a112725.A062567 (3 ^ 5) ≤ 4899999987 :=
    Nat.sInf_le OMA.P112725.mem_k
  rw [h5] at hle
  norm_num at hle
