import Mathlib

namespace OMA.S_opg_a_game_on_an_n_x_n_grid

abbrev Cell (n : ℕ) := Fin n × Fin n

/-- Four occupied corners of an axis-parallel square of positive side length. -/
def HasSquare {n : ℕ} (marks : Finset (Cell n)) : Prop :=
  ∃ x₁ x₂ y₁ y₂ : Fin n,
    x₁ < x₂ ∧ y₁ < y₂ ∧ x₂.val - x₁.val = y₂.val - y₁.val ∧
    (x₁, y₁) ∈ marks ∧ (x₁, y₂) ∈ marks ∧
    (x₂, y₁) ∈ marks ∧ (x₂, y₂) ∈ marks

def Unoccupied {n : ℕ} (cell : Cell n) (first second : Finset (Cell n)) : Prop :=
  cell ∉ first ∧ cell ∉ second

/-- An inductive winning strategy tree for the first player.
True means it is the first player's turn. -/
inductive FirstForcesWin (n : ℕ) :
    Bool → Finset (Cell n) → Finset (Cell n) → Prop
  | won {turn : Bool} {first second : Finset (Cell n)} :
      HasSquare first → ¬ HasSquare second → FirstForcesWin n turn first second
  | firstMove {first second : Finset (Cell n)} {cell : Cell n} :
      ¬ HasSquare first → ¬ HasSquare second → Unoccupied cell first second →
      FirstForcesWin n false (insert cell first) second → FirstForcesWin n true first second
  | secondMove {first second : Finset (Cell n)} :
      ¬ HasSquare first → ¬ HasSquare second →
      (∃ cell : Cell n, Unoccupied cell first second) →
      (∀ cell : Cell n, Unoccupied cell first second →
        FirstForcesWin n true first (insert cell second)) →
      FirstForcesWin n false first second

/-- Five is the least board size with a guaranteed first-player win. -/
theorem main :
    IsLeast {n : ℕ | 0 < n ∧ FirstForcesWin n true ∅ ∅} 5 := by
  sorry

end OMA.S_opg_a_game_on_an_n_x_n_grid
