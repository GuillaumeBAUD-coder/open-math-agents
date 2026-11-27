import Mathlib

/-!
# A051250: Numbers whose reduced residue system consists of 1 and prime powers only.

Source: https://oeis.org/A051250
Credit: @darealpandaboi

Conjecture (Reinhard Zumkeller, Oct 27 2010): the sequence is finite and 60 is the largest term
(empirically verified up to 10^7).

Translation notes.
* n is a term when every k with 1 <= k < n and gcd(k, n) = 1 is 1 or a prime power
  (IsPrimePow excludes 1, so 1 is allowed separately).
* This reading reproduces the listed data exactly:
  1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 18, 20, 24, 30, 42, 60 (checked by computer up to 500).
* Since 60 is a term, finite with largest term 60 is the same as: every term is at most 60.
-/

namespace OMA.S_oeis_a051250

/-- n is in A051250: its reduced residues below n are 1 or prime powers. -/
def IsTerm (n : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k < n → Nat.Coprime k n → k = 1 ∨ IsPrimePow k

theorem main : ∀ n : ℕ, IsTerm n → n ≤ 60 := by
  sorry

end OMA.S_oeis_a051250
