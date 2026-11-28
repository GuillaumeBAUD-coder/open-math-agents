import Mathlib

/-!
# A352796: Numbers m such that {d + m/d : d | m} contains no consecutive integers

Source: https://oeis.org/A352796

Conjecture (OEIS A352796):
A positive integer `m` belongs to A352796 (i.e., `{d + m / d : d ∣ m}` contains
no two consecutive integers) if and only if `m` is not a bipronic number
(OEIS A072389: numbers of the form `x * (x + 1) * y * (y + 1)` with `x, y ≥ 1`).

Conventions:
- Offset: `1`; positive bipronic numbers (A072389) begin `4, 12, 24, 36, 40, 60, ...`.
- Verified computationally for all `1 ≤ m ≤ 500`.
-/

namespace OMA.S_oeis_a352796

/-- Predicate stating that `{d + m / d : d ∣ m}` contains two consecutive integers. -/
def HasConsecDivSum (m : ℕ) : Prop :=
  ∃ d₁ d₂ : ℕ, d₁ ∣ m ∧ d₂ ∣ m ∧ d₁ + m / d₁ + 1 = d₂ + m / d₂

/-- Predicate stating that `m` is a positive bipronic number (OEIS A072389). -/
def IsBipronic (m : ℕ) : Prop :=
  ∃ x y : ℕ, 1 ≤ x ∧ 1 ≤ y ∧ m = x * (x + 1) * y * (y + 1)

/-- The set of positive integers `m` for which `{d + m / d : d ∣ m}` contains no
consecutive integers (OEIS A352796). -/
def S : Set ℕ :=
  {m : ℕ | 1 ≤ m ∧ ¬ HasConsecDivSum m}

/-- Conjecture: A352796 is the complement of the positive bipronic numbers A072389. -/
theorem main : ∀ m : ℕ, 1 ≤ m → (m ∈ S ↔ ¬ IsBipronic m) := by
  sorry

end OMA.S_oeis_a352796
