import Mathlib

/-!
# A069208: a(n) = Sum_{ d divides n } phi(n)/phi(d).

Source: https://oeis.org/A069208 (conjecture of Werner Schulte, Jan 23 2025).
Credit: @esracummings31-blip

Conjecture: Let (f(n)), n > 0, be a multiplicative sequence. Then
  (1) p(f; n) = Sum_{d powerful number (A001694) dividing n} f(d) is multiplicative;
  (2) p(f; n) equals the inverse Moebius transform of A112526(n) * f(n), where A112526 is the
      characteristic function of the powerful numbers.

A number d >= 1 is powerful (A001694, which includes 1) when p^2 divides d for every prime p
dividing d. A sequence is multiplicative when f(1) = 1 and f(m*n) = f(m)*f(n) for coprime m, n.
The values are taken in `ℂ`.
-/

namespace OMA.S_oeis_a069208

/-- Powerful numbers A001694. -/
def IsPowerful (d : ℕ) : Prop := 0 < d ∧ ∀ p ∈ d.primeFactors, p ^ 2 ∣ d

instance : DecidablePred IsPowerful := fun d => by unfold IsPowerful; infer_instance

/-- A112526: the characteristic function of the powerful numbers. -/
def A112526 (d : ℕ) : ℕ := if IsPowerful d then 1 else 0

/-- Multiplicative sequences. -/
def IsMult (f : ℕ → ℂ) : Prop := f 1 = 1 ∧ ∀ m n, Nat.Coprime m n → f (m * n) = f m * f n

/-- `p(f; n)`: the sum of `f d` over the powerful divisors `d` of `n`. -/
def P (f : ℕ → ℂ) (n : ℕ) : ℂ := ∑ d ∈ n.divisors with IsPowerful d, f d

theorem main :
    ∀ f : ℕ → ℂ, IsMult f →
      IsMult (P f) ∧ ∀ n, 1 ≤ n → P f n = ∑ d ∈ n.divisors, (A112526 d : ℂ) * f d := by
  sorry

end OMA.S_oeis_a069208
