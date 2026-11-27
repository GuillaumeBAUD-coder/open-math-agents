import Mathlib

/-!
# A000364: Periodicity of the secant numbers

Source: https://oeis.org/A000364, conjecture by Peter Bala (May 8, 2023).
The counting definition uses David Callan's description of A000364 on the same page.
-/

namespace OMA.S_oeis_a000364

/-- Count the down-up permutations of `2 * n` elements, starting with a descent. -/
def secantNumber (n : ℕ) : ℕ :=
  (Finset.univ.filter fun σ : Equiv.Perm (Fin (2 * n)) =>
    ∀ i : Fin (2 * n),
      if h : i.val + 1 < 2 * n then
        if Even i.val then σ ⟨i.val + 1, h⟩ < σ i else σ i < σ ⟨i.val + 1, h⟩
      else True).card

/-- For each positive modulus, A000364 from index one has a period dividing the totient. -/
theorem main :
    ∀ k : ℕ, 0 < k → ∃ p : ℕ, 0 < p ∧ p ∣ k.totient ∧
      ∀ n : ℕ, 1 ≤ n → Nat.ModEq k (secantNumber (n + p)) (secantNumber n) := by
  sorry

end OMA.S_oeis_a000364
