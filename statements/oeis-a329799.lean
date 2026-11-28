import Mathlib

/-!
# OEIS A329799: Odd composite numbers with maximal-order base b^((k-1)/2) ≡ -1 (mod k)

Source: https://oeis.org/A329799 (OEIS Foundation, CC BY-SA 4.0).
Definition: Odd squarefree composite numbers `k` such that `(p - 1) ∣ (k - 1)` and
`¬ (p - 1) ∣ (k - 1) / 2` for every prime `p ∣ k`.

Conjecture (OEIS A329799): These are precisely the odd composite numbers `k` for which there
exists a base `b : (ZMod k)ˣ` with `orderOf b = Monoid.exponent (ZMod k)ˣ` (the Carmichael
function `λ(k)`) such that `b ^ ((k - 1) / 2) = -1` in `ZMod k`.
-/

namespace OMA.S_oeis_a329799

/-- Conjecture on OEIS A329799: an odd composite number `k` satisfies `Squarefree k` and
`∀ p, p.Prime → p ∣ k → (p - 1) ∣ (k - 1) ∧ ¬ (p - 1) ∣ (k - 1) / 2` if and only if there
exists `b : (ZMod k)ˣ` of maximal order `Monoid.exponent (ZMod k)ˣ` with
`((b : ZMod k) ^ ((k - 1) / 2)) = -1`. -/
theorem main : ∀ k : ℕ, 1 < k → Odd k → ¬ k.Prime →
    ((Squarefree k ∧ ∀ p : ℕ, p.Prime → p ∣ k → (p - 1) ∣ (k - 1) ∧ ¬ (p - 1) ∣ (k - 1) / 2) ↔
      ∃ b : (ZMod k)ˣ, orderOf b = Monoid.exponent (ZMod k)ˣ ∧
        ((b : ZMod k) ^ ((k - 1) / 2)) = -1) := by
  sorry

end OMA.S_oeis_a329799
