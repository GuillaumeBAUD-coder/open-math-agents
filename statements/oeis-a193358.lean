import Mathlib

/-!
# A193358: a(0)=1; a(1)=2 and for n>1: a(n)=a(n-a(n-2))+2.

Source: https://oeis.org/A193358
Credit: @ShoQo

Conjectures: "Every positive integer is in this sequence." and "Odd numbers are not repeated."
(Chai Wah Wu, Jun 06 2016: "Both conjectures are true.")

Formalization notes:
* The recurrence refers to a(n - a(n-2)), so instead of a Lean definition (whose termination
  would depend on the values) the statement quantifies over every `f : ℕ → ℕ` with f(0) = 1,
  f(1) = 2 and f(n) = f(n - f(n-2)) + 2 for n ≥ 2. Such an f is unique (f(n-2) = 0 would give
  f(n) = f(n) + 2, so every self-reference is to a smaller index), and the first conjunct says
  one exists, so the statement is about A193358 itself.
* "Every positive integer is in this sequence": every k ≥ 1 equals some f(n).
* "Odd numbers are not repeated": f(m) = f(n) with f(m) odd forces m = n.
-/

namespace OMA.S_oeis_a193358

/-- `f` satisfies the defining recurrence of A193358. -/
def IsA193358 (f : ℕ → ℕ) : Prop :=
  f 0 = 1 ∧ f 1 = 2 ∧ ∀ n : ℕ, 2 ≤ n → f n = f (n - f (n - 2)) + 2

theorem main :
    (∃ f : ℕ → ℕ, IsA193358 f) ∧
    ∀ f : ℕ → ℕ, IsA193358 f →
      (∀ k : ℕ, 1 ≤ k → ∃ n : ℕ, f n = k) ∧
      (∀ m n : ℕ, f m = f n → f m % 2 = 1 → m = n) := by
  sorry

end OMA.S_oeis_a193358
