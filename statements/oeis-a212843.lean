import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.ModEq

namespace OMA.S_oeis_a212843

/-- A positive integer `n` is a Carmichael number if `n > 1` is composite and
`a^(n - 1) ≡ 1 (mod n)` for every `a` coprime to `n`. -/
def IsCarmichael (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ a : ℕ, Nat.Coprime a n → a ^ (n - 1) ≡ 1 [MOD n]

/-- OEIS A212843 Conjectures 1 & 2:
1. Only Carmichael numbers `C ≡ 1 (mod 10)` can have all prime divisors of the form `10k + 1`,
   and not all Carmichael numbers `C ≡ 1 (mod 10)` have only prime divisors of the form `10k + 1`.
2. Every Carmichael number `C` whose prime divisors are all of the form `10k + 1` can be
   written in one of the three nontrivial factorizations `(30a+1)(30b+1)(30c+1)` (`a,b,c > 0`),
   `(30a+11)(30b+11)(30c+11)`, or `(30a+1)(30b+11)(30c+11)` (`a > 0`). -/
theorem main :
    (∀ C : ℕ, IsCarmichael C → (∀ p : ℕ, p.Prime → p ∣ C → p % 10 = 1) → C % 10 = 1) ∧
    (∃ C : ℕ, IsCarmichael C ∧ C % 10 = 1 ∧ ∃ p : ℕ, p.Prime ∧ p ∣ C ∧ p % 10 ≠ 1) ∧
    (∀ C : ℕ, IsCarmichael C → (∀ p : ℕ, p.Prime → p ∣ C → p % 10 = 1) →
      (∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ C = (30 * a + 1) * (30 * b + 1) * (30 * c + 1)) ∨
      (∃ a b c : ℕ, C = (30 * a + 11) * (30 * b + 11) * (30 * c + 11)) ∨
      (∃ a b c : ℕ, 0 < a ∧ C = (30 * a + 1) * (30 * b + 11) * (30 * c + 11))) := by
  sorry

end OMA.S_oeis_a212843
