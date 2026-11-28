import Mathlib

/-!
Proposed exact statement of Conjecture 11, Bhagat--Kulkarni--Larsson--Murali,
arXiv:2510.24280v2 (20 January 2026), Definition 2 and Conjecture 11 (page 10).
This is a NEW proposal; it is not registered or accepted by Left to Solve.

The two positive ordered actions are a,b. Each mover maximizes their pocket;
when tied, friendly=true maximizes the other pocket, false minimizes it.
Conventions swap at a recursive move. The ratio b/a=(k+1)/k is expressed by
exact integer cross multiplication with a,k positive. Heap h is unrestricted.
The guarded zero-action branch makes the definition total and is excluded
by the positivity assumptions and ratio condition of the conjecture.
-/

namespace OMA.S_arxiv_2510_24280_conjecture11

def move (s : ℕ) (v : ℕ × ℕ) : ℕ × ℕ := (s + v.2, v.1)

def choose (friendly : Bool) (u v : ℕ × ℕ) : ℕ × ℕ :=
  if u.1 < v.1 then v else if v.1 < u.1 then u
  else if friendly then (u.1, max u.2 v.2) else (u.1, min u.2 v.2)

def outcome (a b : ℕ) (c₁ c₂ : Bool) (h : ℕ) : ℕ × ℕ :=
  if h < a then (0, 0) else
    let u := move a (if h - a < h then outcome a b c₂ c₁ (h-a) else (0, 0))
    if h < b then u else
      choose c₁ u (move b (if h - b < h then outcome a b c₂ c₁ (h-b) else (0, 0)))
termination_by h

theorem main : ∀ a b k h : ℕ, 0 < a → 0 < k → b * k = a * (k + 1) →
    outcome a b true true h = outcome a b false false h := by
  sorry

end OMA.S_arxiv_2510_24280_conjecture11
