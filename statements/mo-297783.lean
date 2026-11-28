import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Prime.Basic

/-!
# Paseman's skipping prime conjecture

Source: https://mathoverflow.net/q/297783
Sieve definition: https://mathoverflow.net/q/248146
Credit: @Gh0stBlock

A prime stone initially sits at its prime. At each position the occupying stone
moves to its first unoccupied later multiple. At a composite position, the
occupying stone is the prime divisor whose last move was earliest. The first
visit of a prime to its own position has timestamp zero.

The source gives a strict inequality in its squared formulation.
-/

namespace OMA.S_mo_297783

/-- The possible stone labels at position `n`. -/
def primeDivisors (n : ℕ) : List ℕ :=
  (List.range (n + 1)).filter fun p => decide (p.Prime ∧ p ∣ n)

/-- Choose the prime divisor with the earliest previous visit. -/
def select (last : ℕ → ℕ) (n : ℕ) : ℕ :=
  ((primeDivisors n).argmin last).getD 0

/-- The most recent visit strictly before `n`, or zero before the first visit. -/
def lastVisit : ℕ → ℕ → ℕ
  | 0 => fun _ => 0
  | n + 1 =>
    let last := lastVisit n
    let p := select last n
    fun q => if q = p then n else last q

/-- The label of the stone at position `n`. -/
def sieve (n : ℕ) : ℕ := select (lastVisit n) n

/-- A jump that skips its first possible landing position satisfies the squared bound. -/
def Conjecture : Prop :=
  ∀ p k l : ℕ, p.Prime → 0 < k → k + 1 < l →
    sieve (k * p) = p → sieve (l * p) = p →
    (∀ j : ℕ, k < j → j < l → sieve (j * p) ≠ p) →
    (l * p - k * p) ^ 2 < 16 * (k * p)

theorem main : True ↔ Conjecture := by
  sorry

end OMA.S_mo_297783
