import Mathlib

/-!
# Erdős Problem 475

Source: https://www.erdosproblems.com/475
Credit: @jeonbik

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_erdos_475

-- definitions the statement needs (no sorry, no axiom)

theorem main : ∀ (p : ℕ), p.Prime →
    ∀ A : Finset (ZMod p), (0 : ZMod p) ∉ A →
    ∃ l : List (ZMod p), l.Nodup ∧ l.toFinset = A ∧
      ((l.scanl (· + ·) (0 : ZMod p)).tail).Nodup := by
  sorry

end OMA.S_erdos_475
