import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# OEIS A351716: four consecutive Lucas-Niven numbers

Amiram Eldar's conjecture, 17 February 2022: 1 is the only positive integer
starting a run of four Lucas-Niven numbers. A116543 counts summands by
repeatedly removing the largest Lucas number no greater than the remainder.
The denominations in increasing order are 1, 2, 3, 4, 7, 11, ...

Sources: https://oeis.org/A351716 and https://oeis.org/A351714.
Credit: @LoopsGod
-/

namespace OMA.S_oeis_a351716

/-- Lucas denominations from 3 onwards, after the small denominations 1 and 2. -/
def lucasTail : ℕ → ℕ
  | 0 => 3
  | 1 => 4
  | k + 2 => lucasTail (k + 1) + lucasTail k

/-- Largest Lucas number at most n, with zero for n=0. The index bound n
is sufficient because the tail begins at 3 and increases strictly. -/
def largestLucas (n : ℕ) : ℕ :=
  if n ≤ 2 then n else lucasTail (Nat.findGreatest (fun k => lucasTail k ≤ n) n)

/-- Number of summands in the greedy Lucas representation, A116543. -/
def greedyWeight (n : ℕ) : ℕ :=
  if h : n = 0 then 0 else 1 + greedyWeight (n - largestLucas n)
termination_by n
decreasing_by
  apply Nat.sub_lt (by omega)
  unfold largestLucas
  split
  · omega
  · have pos (k : ℕ) : 0 < lucasTail k := by
      induction k using Nat.twoStepInduction with
      | zero => decide
      | one => decide
      | more k h₀ h₁ => rw [lucasTail]; omega
    exact pos _

/-- Positive integers divisible by their greedy Lucas summand count, A351714. -/
def IsLucasNiven (n : ℕ) : Prop := 0 < n ∧ greedyWeight n ∣ n

theorem main : ∀ n : ℕ, (∀ i : Fin 4, IsLucasNiven (n + i.val)) ↔ n = 1 := by
  sorry

end OMA.S_oeis_a351716
