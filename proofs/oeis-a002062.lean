import OMAStatements.S_oeis_a002062
import Mathlib

/-!
# A002062: `F(n+2) + (n+2) = 2 F(n+3) - (L(n+2) - (n+2))`

The Lucas numbers satisfy `L(n + 1) = F(n + 2) + F(n)` (two-step induction), hence
`L(n + 2) = F(n + 3) + F(n + 1) = 2 F(n + 3) - F(n + 2)`, which is the claim after cancelling
`n + 2`.
-/

namespace OMA.S_oeis_a002062

/-- `L(n + 1) = F(n + 2) + F(n)`. -/
lemma lucas_succ (n : ℕ) : lucas (n + 1) = Nat.fib (n + 2) + Nat.fib n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih1 ih2 =>
    have hl : lucas (n + 3) = lucas (n + 2) + lucas (n + 1) := rfl
    have h1 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    have h2 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
    have h3 : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := Nat.fib_add_two
    have ih2' : lucas (n + 2) = Nat.fib (n + 3) + Nat.fib (n + 1) := ih2
    show lucas (n + 3) = Nat.fib (n + 4) + Nat.fib (n + 2)
    omega

end OMA.S_oeis_a002062

open OMA.S_oeis_a002062 in
theorem OMA.solution : type_of% @OMA.S_oeis_a002062.main := by
  intro n
  have hl : lucas (n + 2) = Nat.fib (n + 3) + Nat.fib (n + 1) := lucas_succ (n + 1)
  have h2 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
  have hA : A006355 (n + 4) = 2 * Nat.fib (n + 3) := rfl
  have hB : A066982 (n + 1) = (lucas (n + 2) : ℤ) - ((n : ℤ) + 1 + 1) := by
    unfold A066982
    push_cast
    rfl
  unfold A002062
  rw [hA, hB, hl]
  push_cast
  omega
