import Mathlib

/-!
# A236332: The number of orbits of 4-tuples of the dihedral group of order 2n acting on {1,2,...,n}.

Source: https://oeis.org/A236332
Credit: @rtflynn

The conjectures listed in the entry (Colin Barker, Jan 2014), stated below as one conjunction:
* a(n) = (9 + 7*(-1)^n + 2*n^3)/4.
* G.f.: -x*(4*x^4-12*x^3+8*x^2-5*x-1) / ((x-1)^4*(x+1)).

Conventions:
* The set {1, 2, ..., n} is the vertex set of the regular n-gon, labelled here by `ZMod n`
  (vertex j + 1 of the entry is `j : ZMod n`). The dihedral group of order 2n is Mathlib's
  `DihedralGroup n`, acting by its symmetries: the rotation `r i` sends x to x + i and the
  reflection `sr i` sends x to -i - x (these formulas respect the multiplication of
  `DihedralGroup n`, see `instance` below, and give all 2n symmetries of the n-gon).
* The group acts on 4-tuples (words of length 4) coordinatewise (Mathlib's `Pi.mulAction`), and
  a(n) is the number of orbits, `Nat.card` of the orbit quotient; offset 1, data
  1, 8, 14, 36, 63, 112, 172, 260, 365, 504, ...
* The g.f. of the entry is the series sum over n ≥ 1 of a(n) x^n, so its coefficient at x^0 is 0.
-/

namespace OMA.S_oeis_a236332

/-- The symmetries of the regular n-gon with vertices `ZMod n`: `r i` is the rotation x ↦ x + i,
`sr i` the reflection x ↦ -i - x. -/
def act (n : ℕ) : DihedralGroup n → ZMod n → ZMod n
  | .r i, x => x + i
  | .sr i, x => -i - x

instance (n : ℕ) : MulAction (DihedralGroup n) (ZMod n) where
  smul := act n
  one_smul x := show act n (DihedralGroup.r 0) x = x by simp [act]
  mul_smul g h x := show act n (g * h) x = act n g (act n h x) by
    cases g <;> cases h <;> simp only [act, DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr] <;> ring

/-- A236332(n): the number of orbits of 4-tuples of vertices of the n-gon under the dihedral group of order 2n. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card (MulAction.orbitRel.Quotient (DihedralGroup n) (Fin 4 → ZMod n))

open PowerSeries in
/-- Barker's conjectures for A236332. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (9 + 7 * (-1) ^ n + 2 * (n : ℚ) ^ 3) / 4) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) * ((X - 1) ^ 4 * (X + 1) : ℚ⟦X⟧) =
      -X * (4 * X ^ 4 - 12 * X ^ 3 + 8 * X ^ 2 - 5 * X - 1) := by
  sorry

end OMA.S_oeis_a236332
