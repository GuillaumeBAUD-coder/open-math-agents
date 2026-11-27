import OMAStatements.S_oeis_a066223
import Mathlib

/-!
Credit: @ivillar
Proof: three steps of the involution recurrence t(k+2) = t(k+1) + (k+1)*t(k) eliminate the
odd-index terms t(2m+1) and t(2m+3), giving Mathar's recurrence for the bisection.
-/

namespace OMAA066223Helpers
open OMA.S_oeis_a066223

theorem t_rec (j k l : ℕ) (hk : k = l + 1) (hj : j = l + 2) :
    t j = t k + ((l : ℤ) + 1) * t l := by
  subst hk hj
  rfl

end OMAA066223Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a066223.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 from by omega, show m + 2 - 2 = m from by omega]
  unfold OMA.S_oeis_a066223.a
  have e4 := OMAA066223Helpers.t_rec (2 * (m + 2)) (2 * m + 3) (2 * (m + 1)) (by ring) (by ring)
  have e3 := OMAA066223Helpers.t_rec (2 * m + 3) (2 * (m + 1)) (2 * m + 1) (by ring) (by ring)
  have e2 := OMAA066223Helpers.t_rec (2 * (m + 1)) (2 * m + 1) (2 * m) (by ring) (by ring)
  push_cast at e2 e3 e4 ⊢
  linear_combination e4 + e3 - (2 * (m : ℤ) + 2) * e2
