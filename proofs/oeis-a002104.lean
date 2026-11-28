import OMAStatements.S_oeis_a002104
import Mathlib

/-!
# A002104: Mathar's three-term recurrence

By induction a(m) ≤ a(m+1) and 2a(m+1) ≤ a(m+2), so the natural subtractions in the definition and
in the stated recurrence never truncate. Subtracting a(n−1) = (n−1)a(n−2) − (n−2)a(n−3) + 1 from
a(n) = n·a(n−1) − (n−1)a(n−2) + 1 eliminates the constant and gives
a(n) = (n+1)a(n−1) − 2(n−1)a(n−2) + (n−2)a(n−3).
-/

namespace PA002104
open OMA.S_oeis_a002104

theorem step (m : ℕ) : a (m + 2) = (m + 2) * a (m + 1) - (m + 1) * a m + 1 := by
  rw [a]

theorem growth (m : ℕ) : a m ≤ a (m + 1) ∧ 2 * a (m + 1) ≤ a (m + 2) := by
  induction m with
  | zero => simp [a]
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨by rw [show m + 1 + 1 = m + 2 by ring]; omega, ?_⟩
    have e := step (m + 1)
    rw [show m + 1 + 2 = m + 3 by ring, show m + 1 + 1 = m + 2 by ring] at e
    rw [show m + 1 + 1 = m + 2 by ring, show m + 1 + 2 = m + 3 by ring, e]
    have hle : (m + 2) * a (m + 1) ≤ (m + 3) * a (m + 2) := by nlinarith
    zify [hle]
    have h2' : (2 : ℤ) * a (m + 1) ≤ a (m + 2) := by exact_mod_cast h2
    nlinarith

end PA002104

theorem OMA.solution : type_of% @OMA.S_oeis_a002104.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega, show k + 3 - 3 = k by omega]
  have e3 := PA002104.step (k + 1)
  have e2 := PA002104.step k
  rw [show k + 1 + 2 = k + 3 by ring, show k + 1 + 1 = k + 2 by ring] at e3
  obtain ⟨g1, g2⟩ := PA002104.growth k
  obtain ⟨g3, g4⟩ := PA002104.growth (k + 1)
  rw [show k + 1 + 1 = k + 2 by ring] at g3 g4
  have i3 : (k + 2) * OMA.S_oeis_a002104.a (k + 1) ≤ (k + 3) * OMA.S_oeis_a002104.a (k + 2) := by
    nlinarith
  have i2 : (k + 1) * OMA.S_oeis_a002104.a k ≤ (k + 2) * OMA.S_oeis_a002104.a (k + 1) := by
    nlinarith
  have i1 : 2 * (k + 2) * OMA.S_oeis_a002104.a (k + 1) ≤
      (k + 3 + 1) * OMA.S_oeis_a002104.a (k + 2) := by
    nlinarith
  zify [i3, i2, i1] at e3 e2 ⊢
  linear_combination e3 - e2
