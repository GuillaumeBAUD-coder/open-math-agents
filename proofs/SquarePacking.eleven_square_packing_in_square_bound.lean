import FormalConjectures.Wikipedia.SquarePacking

/-!
# Eleven unit squares in a square of side 3.877084

We move the centres of Walter Trump's eleven-square arrangement slightly apart
and replace its common tilt by a rational rotation. Projecting onto the four
edge directions gives an exact rational certificate of disjointness for each
pair. The horizontal and vertical projections also certify containment.

Source for the approximate arrangement:
https://github.com/evand/square-packing/blob/main/site/www/data/p/square-11.json
-/

open EuclideanGeometry SquarePacking

namespace ElevenSquares

/-- An isometry sends the centre of the unit square to (x,y)
and rotates its axes to (c,s) and (-s,c). -/
noncomputable def placement (x y c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : ℝ² ≃ᵢ ℝ² :=
  IsometryEquiv.mk'
    (fun p ↦ !₂[x + c * (p 0 - 1 / 2) - s * (p 1 - 1 / 2),
                  y + s * (p 0 - 1 / 2) + c * (p 1 - 1 / 2)])
    (fun q ↦ !₂[c * (q 0 - x) + s * (q 1 - y) + 1 / 2,
                  -s * (q 0 - x) + c * (q 1 - y) + 1 / 2])
    (by
      intro q
      ext i
      fin_cases i
      · change x + c * (c * (q 0 - x) + s * (q 1 - y) + 1 / 2 - 1 / 2) -
          s * (-s * (q 0 - x) + c * (q 1 - y) + 1 / 2 - 1 / 2) = q 0
        linear_combination (q 0 - x) * h
      · change y + s * (c * (q 0 - x) + s * (q 1 - y) + 1 / 2 - 1 / 2) +
          c * (-s * (q 0 - x) + c * (q 1 - y) + 1 / 2 - 1 / 2) = q 1
        linear_combination (q 1 - y) * h)
    (by
      apply isometry_iff_dist_eq.mpr
      intro p q
      apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
      simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2) * h)

structure Pose where
  x : ℚ
  y : ℚ
  c : ℚ
  s : ℚ

def centre (P : Pose) (a b : ℚ) : ℚ := 2 * (a * P.x + b * P.y)

def width (P : Pose) (a b : ℚ) : ℚ := |a * P.c + b * P.s| + |b * P.c - a * P.s|

def lower (P : Pose) (a b : ℚ) : ℚ := centre P a b - width P a b

def upper (P : Pose) (a b : ℚ) : ℚ := centre P a b + width P a b

noncomputable def imageOf (P : Pose) (h : P.c ^ 2 + P.s ^ 2 = 1) : ℝ² ≃ᵢ ℝ² :=
  placement P.x P.y P.c P.s (by exact_mod_cast h)

/-- The projection of a placed square onto any axis lies in its rational support interval.
The interval and its argument are both doubled to avoid half-widths. -/
lemma projection (P : Pose) (h : P.c ^ 2 + P.s ^ 2 = 1) (a b : ℚ) (p : ℝ²)
    (hp : p ∈ UnitSquare) :
    let z := imageOf P h p
    (lower P a b : ℝ) ≤ 2 * (a * z 0 + b * z 1) ∧
      2 * (a * z 0 + b * z 1) ≤ (upper P a b : ℝ) := by
  change 0 < p 0 ∧ p 0 < 1 ∧ 0 < p 1 ∧ p 1 < 1 at hp
  obtain ⟨hx, hx', hy, hy'⟩ := hp
  have hu : |2 * p 0 - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hv : |2 * p 1 - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  let A : ℝ := a * P.c + b * P.s
  let B : ℝ := b * P.c - a * P.s
  have hab : |A * (2 * p 0 - 1) + B * (2 * p 1 - 1)| ≤ |A| + |B| := by
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) hu)
      (mul_le_of_le_one_right (abs_nonneg _) hv)
  obtain ⟨hl, hr⟩ := abs_le.mp hab
  dsimp [imageOf, placement, IsometryEquiv.mk', lower, upper, centre, width]
  push_cast
  dsimp [A, B] at hl hr
  constructor
  · linarith only [hl]
  · linarith only [hr]

-- Centres are on the 10⁻⁹ grid. The five turned squares share a rational
-- point of the unit circle, obtained from the tangent half-angle parametrization.
def cosTilt : ℚ := 236816615 / 367034137

def sinTilt : ℚ := 280413888 / 367034137

def upright (x y : ℚ) : Pose := ⟨x, y, 1, 0⟩

def tilted (x y : ℚ) : Pose := ⟨x, y, cosTilt, sinTilt⟩

def poses : Fin 11 → Pose := ![
  upright 0.500000053 0.500000053,
  upright 0.500000053 3.377083947,
  upright 3.377083947 2.532558582,
  upright 2.377083841 0.500000053,
  upright 3.377083947 0.500000053,
  upright 3.377083947 1.500000159,
  tilted 1.452558328 1.272254031,
  tilted 0.704608244 1.936475099,
  tilted 2.188525121 1.959613035,
  tilted 1.440575038 2.623834103,
  tilted 2.340796657 3.172475756]

def axes : Fin 4 → ℚ × ℚ := ![(1, 0), (0, 1), (cosTilt, sinTilt), (-sinTilt, cosTilt)]

def side : ℚ := 3.877084

lemma unitRotations : ∀ i : Fin 11, (poses i).c ^ 2 + (poses i).s ^ 2 = 1 := by decide +kernel

lemma walls : ∀ i : Fin 11,
    0 < lower (poses i) 1 0 ∧ upper (poses i) 1 0 < 2 * side ∧
    0 < lower (poses i) 0 1 ∧ upper (poses i) 0 1 < 2 * side := by decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 3500000 in
lemma separated : ∀ i j : Fin 11, i ≠ j → ∃ k : Fin 4,
    let a := (axes k).1
    let b := (axes k).2
    upper (poses i) a b < lower (poses j) a b ∨
      upper (poses j) a b < lower (poses i) a b := by decide +kernel

end ElevenSquares

open ElevenSquares

theorem OMA.solution : type_of% @SquarePacking.eleven_square_packing_in_square_bound := by
  refine ⟨⟨fun i ↦ imageOf (poses i) (unitRotations i), ?_, ?_⟩⟩
  · intro i j hij
    obtain ⟨k, h⟩ := separated i j hij
    apply Set.disjoint_left.mpr
    rintro z ⟨p, hp, rfl⟩ ⟨q, hq, heq⟩
    have hi := projection (poses i) (unitRotations i) (axes k).1 (axes k).2 p hp
    have hj := projection (poses j) (unitRotations j) (axes k).1 (axes k).2 q hq
    dsimp only at hi hj h
    rw [heq] at hj
    rcases h with h | h
    · exact (not_lt_of_ge (hj.1.trans hi.2)) (by exact_mod_cast h)
    · exact (not_lt_of_ge (hi.1.trans hj.2)) (by exact_mod_cast h)
  · intro i z hz
    obtain ⟨p, hp, rfl⟩ := hz
    have hx := projection (poses i) (unitRotations i) 1 0 p hp
    have hy := projection (poses i) (unitRotations i) 0 1 p hp
    dsimp only at hx hy
    simp only [Rat.cast_one, Rat.cast_zero, one_mul, zero_mul, add_zero, zero_add] at hx hy
    obtain ⟨hxl, hxu, hyl, hyu⟩ := walls i
    have hsize : ((2 * side : ℚ) : ℝ) = 2 * 3.877084 := by norm_num [side]
    have hxl' := Rat.cast_lt (K := ℝ) |>.mpr hxl
    have hxu' := Rat.cast_lt (K := ℝ) |>.mpr hxu
    have hyl' := Rat.cast_lt (K := ℝ) |>.mpr hyl
    have hyu' := Rat.cast_lt (K := ℝ) |>.mpr hyu
    rw [hsize] at hxu' hyu'
    simp only [Rat.cast_zero] at hxl' hyl'
    change 0 < _ ∧ _ < 3.877084 ∧ 0 < _ ∧ _ < 3.877084
    exact ⟨by linarith [hx.1], by linarith [hx.2], by linarith [hy.1], by linarith [hy.2]⟩
