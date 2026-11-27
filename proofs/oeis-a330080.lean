import OMAStatements.S_oeis_a330080
import Mathlib

namespace A330080Proof
open OMA.S_oeis_a330080

lemma key (x y z : ℚ) (hx : 6 ≤ x) (hy : 0 < y) (hz : 0 < z) :
    24*x*y*z < (x+1)*(y+1)*(z+1)*(x+y+z) := by
  obtain ⟨u, rfl⟩ : ∃ u, x = u + 6 := ⟨x - 6, by ring⟩
  have hu : 0 ≤ u := by linarith
  have hg : 0 < (7*(y+z)*((y+z) - 37/7)^2 + 3/7*(y+z) + 168)
          + u*((y+z)*((y+z) - 7/2)^2 + 175/4*(y+z) + 52)
          + u^2*((y+z)+2)^2 := by positivity
  have h2 : 0 < 4*(u+6+1)*((y+z)+1)*(u+6+(y+z)) := by positivity
  by_cases hA : 0 ≤ (u+6+1)*(u+6+(y+z)) - 24*(u+6)
  · have h1 : 0 ≤ 4*(y*z)*((u+6+1)*(u+6+(y+z)) - 24*(u+6)) :=
      mul_nonneg (by positivity) hA
    nlinarith
  · have hA' : (u+6+1)*(u+6+(y+z)) - 24*(u+6) ≤ 0 := by linarith
    have h3 : 4*(y*z) - (y+z)^2 ≤ 0 := by nlinarith [sq_nonneg (y-z)]
    have h4 := mul_nonneg_of_nonpos_of_nonpos h3 hA'
    nlinarith

lemma inv (n : ℕ) : 0 < term n ∧ 0 < term (n+1) ∧ 0 < term (n+2) ∧
    (term n + 1)*(term (n+1) + 1)*(term (n+2) + 1)*(term n + term (n+1) + term (n+2))
      = 24 * term n * term (n+1) * term (n+2) := by
  induction n with
  | zero => norm_num [term]
  | succ n ih =>
    obtain ⟨hx, hy, hz, h⟩ := ih
    have hw : term (n+3) = (term (n+2) + term (n+1)) / term n := by rw [term]
    show 0 < term (n+1) ∧ 0 < term (n+2) ∧ 0 < term (n+3) ∧
      (term (n+1) + 1)*(term (n+2) + 1)*(term (n+3) + 1)*(term (n+1) + term (n+2) + term (n+3))
        = 24 * term (n+1) * term (n+2) * term (n+3)
    rw [hw]
    generalize term n = x at *
    generalize term (n+1) = y at *
    generalize term (n+2) = z at *
    refine ⟨hy, hz, by positivity, ?_⟩
    have hx0 : x ≠ 0 := hx.ne'
    have key2 : (y+1)*(z+1)*((z+y)/x+1)*(y+z+(z+y)/x) - 24*y*z*((z+y)/x)
        = (y+z)/x^2 * ((x+1)*(y+1)*(z+1)*(x+y+z) - 24*x*y*z) := by
      field_simp
      ring
    have h0 : (y+1)*(z+1)*((z+y)/x+1)*(y+z+(z+y)/x) - 24*y*z*((z+y)/x) = 0 := by
      rw [key2, h, sub_self, mul_zero]
    linarith

end A330080Proof

open OMA.S_oeis_a330080 A330080Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a330080.main := by
  intro n
  obtain ⟨hx, hy, hz, h⟩ := inv n
  have h6 : term n < 6 := by
    by_contra hc
    have := key (term n) _ _ (not_lt.mp hc) hy hz
    linarith
  have hfl : ⌊term n⌋ < 6 := Int.floor_lt.mpr (by exact_mod_cast h6)
  exact ⟨Int.floor_nonneg.mpr hx.le, by omega⟩
