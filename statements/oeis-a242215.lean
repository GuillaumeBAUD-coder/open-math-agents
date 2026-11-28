import Mathlib.Data.Set.Finite.Basic
import Mathlib.NumberTheory.Fermat

/-!
# OEIS A242215

The conjecture asks for infinitely many composite Fermat numbers with no
divisor in the sequence 18k + 5 for natural numbers k starting at zero.
Source: https://oeis.org/A242215
-/

namespace OMA.S_oeis_a242215

theorem main :
    {m : ℕ | (∃ n : ℕ, m = Nat.fermatNumber n) ∧ 1 < m ∧ ¬ m.Prime ∧
      ∀ k : ℕ, ¬ (18 * k + 5 ∣ m)}.Infinite := by
  sorry

end OMA.S_oeis_a242215
