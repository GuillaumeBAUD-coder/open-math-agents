import Mathlib.Data.Nat.Basic

/-! OEIS A400868, Daniel Okwor. Source: https://oeis.org/A400868
Formalization: @pblivin0x. The sequence starts at n = 1.
The number of endless deals is zero exactly when no ordinary deal plays forever.
Alternately dealing a permutation with player one first gives every pair of ordered
hands of the indicated sizes. All ranks are distinct, so every turn has a winner. -/
namespace OMA.S_oeis_a400868

abbrev Position := List ℕ × List ℕ

def ordinary (n : ℕ) (s : Position) : Prop :=
  (s.1 ++ s.2).length = n ∧ (List.range' 1 n).all (fun x => (s.1 ++ s.2).count x == 1) = true ∧
  s.1.length = (n + 1) / 2 ∧ s.2.length = n / 2

def live (s : Position) : Bool := !s.1.isEmpty && !s.2.isEmpty

/-- Both reveal their front card. The higher rank collects the loser, then the winner. -/
def move : Position → Position
  | (a :: as, b :: bs) => if a > b then (as ++ [b,a], bs) else (as, bs ++ [a,b])
  | s => s

def after : ℕ → Position → Position
  | 0, s => s
  | t+1, s => after t (move s)

/-- An empty hand ends the game. -/
def endless (s : Position) : Prop := ∀ t : ℕ, live (after t s) = true

theorem main : ∀ n : ℕ, 0 < n →
    ((¬ ∃ s : Position, ordinary n s ∧ endless s) ↔ (∃ k : ℕ, n = 2^k)) := by sorry

end OMA.S_oeis_a400868
