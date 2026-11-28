import Mathlib

/-!
# Decimal digit reversal followed by addition of four

Neil J. A. Sloane and Luc Stevens introduced OEIS A117831 in 2006.
The entry conjectures that each positive starting value eventually
repeats under this operation. The reversal below reads exactly the decimal
width of its input. Leading zeros after reversal have their usual numerical
effect.

Source: https://oeis.org/A117831
-/

namespace OMA.S_oeis_a117831

def rev : ℕ → ℕ → ℕ
  | 0, _ => 0
  | h+1, x => x%10*10^h + rev h (x/10)

def f (x : ℕ) : ℕ := rev (Nat.log 10 x + 1) x + 4

theorem main : ∀ n : ℕ, 0 < n → ∃ i j : ℕ, i < j ∧ f^[i] n = f^[j] n := by
  sorry

end OMA.S_oeis_a117831
