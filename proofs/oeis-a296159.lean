import OMAStatements.S_oeis_a296159
import Mathlib

-- Problem: A296159: Sum of the smaller parts in the partitions of n into two distinct parts with the larger part odd.
-- Upstream: formal-conjectures :0 (declaration OMA.S_oeis_a296159.main)
-- Credit: @Mapika (the owner of the agent is credited as the solver)

/-!
Proof of Colin Barker's recurrence for A296159.

Passing from `n` to `n + 4` (for `n ≥ 1`) the summation range `1..(n-1)/2` gains the two indices
`m + 1, m + 2` with `m = (n-1)/2`, and the parity factor `(n - i) mod 2` does not change, so
`a(n+4) = a(n) + g(n)` where `g(n)` is the one new index of the right parity. Moreover
`g(k+4) = g(k) + 2`. The recurrence is
`[a(n)-a(n-4)] - [a(n-1)-a(n-5)] - [a(n-4)-a(n-8)] + [a(n-5)-a(n-9)] = 0`.
-/

namespace A296159Proof

open OMA.S_oeis_a296159 Finset

/-- The single new index of the right parity when passing from `n` to `n + 4`. -/
def g (n : ℕ) : ℕ :=
  if (n + 3 - (n - 1) / 2) % 2 = 1 then (n - 1) / 2 + 1 else (n - 1) / 2 + 2

lemma step (n : ℕ) (hn : 1 ≤ n) : a (n + 4) = a n + g n := by
  unfold a
  have hm : (n + 4 - 1) / 2 = (n - 1) / 2 + 1 + 1 := by omega
  rw [hm, sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega)]
  have hsame : ∑ i ∈ Icc 1 ((n - 1) / 2), i * ((n + 4 - i) % 2) =
      ∑ i ∈ Icc 1 ((n - 1) / 2), i * ((n - i) % 2) := by
    apply sum_congr rfl
    intro i hi
    have := (mem_Icc.mp hi).2
    congr 1
    omega
  rw [hsame, add_assoc]
  congr 1
  unfold g
  split_ifs with h
  · rw [show (n + 4 - ((n - 1) / 2 + 1)) % 2 = 1 by omega,
      show (n + 4 - ((n - 1) / 2 + 1 + 1)) % 2 = 0 by omega]
    ring
  · rw [show (n + 4 - ((n - 1) / 2 + 1)) % 2 = 0 by omega,
      show (n + 4 - ((n - 1) / 2 + 1 + 1)) % 2 = 1 by omega]
    ring

lemma g_step (k : ℕ) (hk : 1 ≤ k) : g (k + 4) = g k + 2 := by
  unfold g
  split_ifs <;> omega

end A296159Proof

open A296159Proof OMA.S_oeis_a296159

theorem OMA.solution : type_of% @OMA.S_oeis_a296159.main := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 10 := ⟨n - 10, by omega⟩
  simp only [show j + 10 - 1 = j + 9 by omega, show j + 10 - 4 = j + 6 by omega,
    show j + 10 - 5 = j + 5 by omega, show j + 10 - 8 = j + 2 by omega,
    show j + 10 - 9 = j + 1 by omega]
  have s1 := step (j + 6) (by omega)
  have s2 := step (j + 5) (by omega)
  have s3 := step (j + 2) (by omega)
  have s4 := step (j + 1) (by omega)
  have g1 := g_step (j + 2) (by omega)
  have g2 := g_step (j + 1) (by omega)
  rw [show j + 6 + 4 = j + 10 by omega] at s1
  rw [show j + 5 + 4 = j + 9 by omega] at s2
  rw [show j + 2 + 4 = j + 6 by omega] at s3 g1
  rw [show j + 1 + 4 = j + 5 by omega] at s4 g2
  omega
