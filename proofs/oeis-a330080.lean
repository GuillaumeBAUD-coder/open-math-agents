import OMAStatements.S_oeis_a330080
import Mathlib

/-!
The shift (x,y,z) ↦ (y,z,(y+z)/x) preserves a symmetric polynomial relation.
At fixed x and y+z, replacing y and z by their mean gives a necessary
inequality. Its left side has a strictly positive sum-of-squares certificate
for x ≥ 6.
-/

namespace OMA.A330080

open OMA.S_oeis_a330080

def invariant (x y z : ℚ) : Prop :=
  (1+x)*(1+y)*(1+z)*(x+y+z) = 24*x*y*z

lemma invariant_step {x y z : ℚ} (hx : 0 < x) (h : invariant x y z) :
    invariant y z ((z+y)/x) := by
  unfold invariant at *
  field_simp [ne_of_gt hx]
  linear_combination (y + z) * h

lemma along_orbit (n : ℕ) :
    0 < term n ∧ 0 < term (n+1) ∧ 0 < term (n+2) ∧
      invariant (term n) (term (n+1)) (term (n+2)) := by
  induction n with
  | zero => norm_num [term, invariant]
  | succ n ih =>
    obtain ⟨hx, hy, hz, h⟩ := ih
    change 0 < term (n+1) ∧ 0 < term (n+2) ∧
      0 < (term (n+2) + term (n+1)) / term n ∧ _
    exact ⟨hy, hz, div_pos (add_pos hz hy) hx, invariant_step hx h⟩

lemma lt_six {x y z : ℚ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : invariant x y z) : x < 6 := by
  by_contra! hlarge
  let t := (y+z)/2
  have ht : 0 < t := by dsimp [t]; positivity
  let f := (x+1)*(t+1)^2*(x+2*t) - 24*x*t^2
  have transfer : 4*y*z*f + (y-z)^2*(1+y+z)*(x+1)*(x+y+z) = 0 := by
    dsimp [f, t]
    unfold invariant at h
    linear_combination (y+z)^2 * h
  have fpos : 0 < f := by
    have certificate : f =
        14*t*(t-3)^2 + 10*(t-7/5)^2 + 112/5 +
        (x-6)*(t*(2*(t-2)^2 + t + 20) + 13) +
        ((x-6)*(t+1))^2 := by dsimp [f]; ring
    rw [certificate]
    have hnon : 0 ≤ x-6 := by linarith
    positivity
  have hpos : 0 < 4*y*z*f := by positivity
  have hn : 0 ≤ (y-z)^2*(1+y+z)*(x+1)*(x+y+z) := by positivity
  linarith

end OMA.A330080

theorem OMA.solution : type_of% @OMA.S_oeis_a330080.main := by
  intro n
  obtain ⟨hx, hy, hz, h⟩ := OMA.A330080.along_orbit n
  exact ⟨Int.floor_nonneg.mpr hx.le, by
    have := Int.floor_lt.mpr (show OMA.S_oeis_a330080.term n < (6 : ℤ) from
      by exact_mod_cast OMA.A330080.lt_six hx hy hz h)
    omega⟩
