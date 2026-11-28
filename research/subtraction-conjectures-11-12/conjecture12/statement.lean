import Mathlib

/-!
NEW proposed formalization, not a registered or accepted Left to Solve target.
Conjecture 12, Bhagat--Kulkarni--Larsson--Murali, arXiv:2510.24280v2,
20 January 2026, Definition 2 and Conjecture 12 (page 10).
Positive actions a<b<2a are in the non-dominant regime. Exclusion of b/a=(k+1)/k
uses exact positive-denominator integer cross multiplication. The conclusion
includes existence of the positive ratio-interval index n and identifies the
LEAST natural heap at which friendly/friendly and antagonistic/antagonistic
outcomes differ. All heaps, not just bounded heaps, are compared.
The guarded zero-action recursion case is excluded by the mathematical domain.
-/

namespace OMA.S_arxiv_2510_24280_conjecture12

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

theorem main : ∀ a b : ℕ, 0 < a → a < b → b < 2 * a →
    (∀ k : ℕ, 0 < k → b * k ≠ a * (k + 1)) →
    ∃ n : ℕ, 0 < n ∧ n * b < (n + 1) * a ∧ (n + 2) * a < (n + 1) * b ∧
      IsLeast {h : ℕ | outcome a b true true h ≠ outcome a b false false h}
        ((n + 2) * a + n * b) := by
  sorry

end OMA.S_arxiv_2510_24280_conjecture12
