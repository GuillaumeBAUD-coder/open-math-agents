import Mathlib

/-!
# Every finite binary word occurs in some power of three

Source: https://oeis.org/A400127
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A400/A400127.seq
Credit: @Heart-galaxy

A word of length n is represented by a natural number w below 2^n. The
offset counts positions from the least significant bit. The lower bound on
the value ensures that all n selected positions belong to its ordinary binary
representation, including when the selected word starts with zero.

The statement gives exactly the finiteness condition for A400127 at every
index n in its domain. David Rabahy proved finiteness in the OEIS entry in
October 2026 by density of leading binary digits.
-/

namespace OMA.S_oeis_a400127

def occurs (n w value : ℕ) : Prop :=
  ∃ offset : ℕ, 2 ^ (offset + n - 1) ≤ value ∧
    (value / 2 ^ offset) % 2 ^ n = w

theorem main : ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ,
    ∀ w < 2 ^ n, ∃ k ≤ m, occurs n w (3 ^ k) := by
  sorry

end OMA.S_oeis_a400127
