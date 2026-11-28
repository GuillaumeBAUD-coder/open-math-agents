import Mathlib

/-!
# A051250: numbers whose reduced residue system consists of 1 and prime powers only

Source: https://oeis.org/A051250 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry (Labos Elemer), offset 1:
Numbers whose reduced residue system consists of 1 and prime powers only. Data
1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 18, 20, 24, 30, 42, 60

Comment (Reinhard Zumkeller, Oct 27 2010): Conjecture: the sequence is finite and 60 is the
largest term, empirically verified up to 10^7.
Status: known result. A later comment of the entry gives a proof with Dusart's bounds.

Formalization notes.
* The reduced residue system of n is the set of the k with 1 <= k <= n and gcd(k, n) = 1.
* A prime power is p^e with p prime and e >= 1 (`IsPrimePow`), so the primes are prime powers.
* `main` states that 60 is a term and that every term is at most 60. This gives that the
  sequence is finite and that 60 is its largest term.
-/

namespace OMA.S_oeis_a051250

/-- n is a term of A051250: every k in the reduced residue system of n is 1 or a prime power. -/
def IsTerm (n : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ n → Nat.Coprime k n → k = 1 ∨ IsPrimePow k

/-- Zumkeller's conjecture: 60 is the largest term. -/
theorem main : IsTerm 60 ∧ ∀ n : ℕ, 1 ≤ n → IsTerm n → n ≤ 60 := by
  sorry

end OMA.S_oeis_a051250
