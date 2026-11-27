import FormalConjectures.Arxiv.«2607.27197».MaxwellConjecture
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Iterating the Maxwell charge construction

We formalize Proposition 1 of Philip Arathoon, Gavin Ball and Matthew D. Kvalheim
(arXiv:2607.27197). The initial equilateral triangle has four nondegenerate
equilibria. Each pair of axial charges produces 21 equilibria near the origin,
while any chosen finite family of old equilibria away from the origin persists.
The cubic term of the potential is preserved and the quadratic coefficient stays
positive, so the construction can be repeated. Moving one unit charge to a
regular value makes all equilibria nondegenerate and preserves the lower bound.

The quartic classification is due to @luciusacarr (project PR #836). The
Coulomb derivative follows @harshshah1618 (#289). The continuation, edge and
regular-value arguments adapt @PanPapag's five-charge proofs (#1378, #1450,
#1507 and #1756).
-/

section

open Matrix
open Arxiv.«2607.27197»
open scoped Gradient

namespace OMA.Quartic

abbrev E := EuclideanSpace ℝ (Fin 3)

private noncomputable abbrev coord (i : Fin 3) : E →L[ℝ] ℝ :=
  EuclideanSpace.proj i

private theorem coord_apply (i : Fin 3) (p : E) : coord i p = p.ofLp i := rfl

private theorem fderiv_phi (p v : E) :
    let x := p.ofLp 0
    let y := p.ofLp 1
    let z := p.ofLp 2
    let H := 5 + 36 * (x ^ 2 + y ^ 2) - 144 * z ^ 2
    16 * fderiv ℝ phiZero p v =
      (x * H + 90 * (x ^ 2 - y ^ 2)) * v.ofLp 0 +
      (y * (H - 180 * x)) * v.ofLp 1 +
      (z * (-10 - 144 * (x ^ 2 + y ^ 2) + 96 * z ^ 2)) * v.ofLp 2 := by
  change 16 * fderiv ℝ (fun q : E =>
      5 / 32 * ((coord 0 q ^ 2 + coord 1 q ^ 2) - 2 * coord 2 q ^ 2) +
      15 / 8 * (coord 0 q ^ 3 - 3 * coord 0 q * coord 1 q ^ 2) +
      3 / 16 * (3 * (coord 0 q ^ 2 + coord 1 q ^ 2) ^ 2 -
        24 * (coord 0 q ^ 2 + coord 1 q ^ 2) * coord 2 q ^ 2 +
        8 * coord 2 q ^ 4)) p v = _
  simp (disch := fun_prop) only [fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul, fderiv_const_apply, ContinuousLinearMap.zero_apply,
    fderiv_fun_pow, ContinuousLinearMap.fderiv, _root_.add_apply,
    _root_.sub_apply, _root_.smul_apply, smul_eq_mul]
  simp only [coord_apply]
  ring

theorem critical_iff (p : E) :
    ∇ phiZero p = 0 ↔
      let x := p.ofLp 0
      let y := p.ofLp 1
      let z := p.ofLp 2
      let H := 5 + 36 * (x ^ 2 + y ^ 2) - 144 * z ^ 2
      x * H + 90 * (x ^ 2 - y ^ 2) = 0 ∧
      y * (H - 180 * x) = 0 ∧
      z * (-10 - 144 * (x ^ 2 + y ^ 2) + 96 * z ^ 2) = 0 := by
  have hgrad : ∇ phiZero p = 0 ↔ fderiv ℝ phiZero p = 0 := by
    rw [← toDual_gradient]
    exact (InnerProductSpace.toDual ℝ E).map_eq_zero_iff.symm
  rw [hgrad]
  constructor
  · intro h
    have atVec (v : E) := fderiv_phi p v
    simp only [h, ContinuousLinearMap.zero_apply, mul_zero] at atVec
    exact ⟨by simpa using (atVec (WithLp.toLp 2 ![1, 0, 0])).symm,
      by simpa using (atVec (WithLp.toLp 2 ![0, 1, 0])).symm,
      by simpa using (atVec (WithLp.toLp 2 ![0, 0, 1])).symm⟩
  · dsimp only
    rintro ⟨hx, hy, hz⟩
    ext v
    have heq := fderiv_phi p v
    dsimp only at heq
    rw [hx, hy, hz] at heq
    simpa using heq

noncomputable def hessianMatrix (p : E) : Matrix (Fin 3) (Fin 3) ℝ :=
  let x := p.ofLp 0
  let y := p.ofLp 1
  let z := p.ofLp 2
  let H := 5 + 36 * (x ^ 2 + y ^ 2) - 144 * z ^ 2
  let a := H + 72 * x ^ 2 + 180 * x
  let b := 72 * x * y - 180 * y
  let c := -288 * x * z
  let d := H + 72 * y ^ 2 - 180 * x
  let e := -288 * y * z
  let f := -10 - 144 * (x ^ 2 + y ^ 2) + 288 * z ^ 2
  !![a, b, c; b, d, e; c, e, f]

private theorem fderiv_smul_coord (f : E → ℝ) (p v w : E) (i : Fin 3)
    (hf : DifferentiableAt ℝ f p) :
    fderiv ℝ (fun q => f q • coord i) p v w = fderiv ℝ f p v * coord i w := by
  rw [fderiv_fun_smul hf (differentiableAt_const (coord i)), fderiv_const_apply, smul_zero, zero_add,
    ContinuousLinearMap.smulRight_apply, _root_.smul_apply, smul_eq_mul]

private theorem second_derivative (p v w : E) :
    16 * iteratedFDeriv ℝ 2 phiZero p ![v, w] =
      w.ofLp ⬝ᵥ (hessianMatrix p *ᵥ v.ofLp) := by
  have heq : fderiv ℝ phiZero = fun q : E =>
      let x := coord 0 q
      let y := coord 1 q
      let z := coord 2 q
      let H := 5 + 36 * (x ^ 2 + y ^ 2) - 144 * z ^ 2
      ((x * H + 90 * (x ^ 2 - y ^ 2)) / 16) • coord 0 +
      ((y * (H - 180 * x)) / 16) • coord 1 +
      ((z * (-10 - 144 * (x ^ 2 + y ^ 2) + 96 * z ^ 2)) / 16) • coord 2 := by
    funext q
    ext u
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    have h := fderiv_phi q u
    dsimp only at h ⊢
    simp only [coord_apply]
    linear_combination h / 16
  rw [iteratedFDeriv_two_apply, heq]
  simp only [div_eq_mul_inv]
  simp (disch := fun_prop) only [Matrix.cons_val_zero, Matrix.cons_val_one,
    fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul, fderiv_fun_pow, fderiv_smul_coord,
    fderiv_const_apply, ContinuousLinearMap.fderiv,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.smulRight_apply,
    _root_.add_apply, _root_.sub_apply, _root_.smul_apply, smul_eq_mul, zero_add, add_zero, smul_zero,
    hessianMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.of_apply, Matrix.head_cons, Matrix.tail_cons]
  simp only [coord_apply]
  ring


def radial (x y z : ℝ) : ℝ := 5 + 36 * (x ^ 2 + y ^ 2) - 144 * z ^ 2

def stationary (x y z : ℝ) : Prop :=
  x * radial x y z + 90 * (x ^ 2 - y ^ 2) = 0 ∧
  y * (radial x y z - 180 * x) = 0 ∧
  z * (-10 - 144 * (x ^ 2 + y ^ 2) + 96 * z ^ 2) = 0

def direction (s x y : ℝ) : Prop :=
  (x = s ∧ y = 0) ∨ (x = -s / 2 ∧ y ^ 2 = 3 * s ^ 2 / 4)

theorem radial_classification {x y z : ℝ} (h : stationary x y z) :
    (x = 0 ∧ y = 0 ∧ (z = 0 ∨ z ^ 2 = 5 / 48)) ∨
    ∃ s ≠ 0, direction s x y ∧
      ((z = 0 ∧ 36 * s ^ 2 + 90 * s + 5 = 0) ∨
        (z ^ 2 = 5 / 48 + 3 / 2 * s ^ 2 ∧ (s = 1 / 6 ∨ s = 1 / 3))) := by
  rcases h with ⟨hx, hy, hz⟩
  have hreduce (s : ℝ) (hs : s ≠ 0) (hdir : direction s x y)
      (hr : x ^ 2 + y ^ 2 = s ^ 2) (hlin : radial x y z + 90 * s = 0) :
      ∃ s ≠ 0, direction s x y ∧
        ((z = 0 ∧ 36 * s ^ 2 + 90 * s + 5 = 0) ∨
          (z ^ 2 = 5 / 48 + 3 / 2 * s ^ 2 ∧ (s = 1 / 6 ∨ s = 1 / 3))) := by
    refine ⟨s, hs, hdir, ?_⟩
    rw [radial, hr] at hlin
    rcases mul_eq_zero.mp hz with hz0 | hzn
    · exact Or.inl ⟨hz0, by rw [hz0] at hlin; linarith⟩
    · rw [hr] at hzn
      have hzsq : z ^ 2 = 5 / 48 + 3 / 2 * s ^ 2 := by linarith
      have hprod : (s - 1 / 6) * (s - 1 / 3) = 0 := by
        linear_combination (hlin + 144 * hzsq) * (-1 / 180)
      exact Or.inr ⟨hzsq, (mul_eq_zero.mp hprod).imp (by intro h; linarith)
        (by intro h; linarith)⟩
  by_cases hy0 : y = 0
  · subst y
    by_cases hx0 : x = 0
    · subst x
      refine Or.inl ⟨rfl, rfl, (mul_eq_zero.mp hz).imp id ?_⟩
      intro h
      norm_num at h
      linarith
    · apply Or.inr
      apply hreduce x hx0 (Or.inl ⟨rfl, rfl⟩) (by ring)
      apply (mul_eq_zero.mp (show x * (radial x 0 z + 90 * x) = 0 by
        linear_combination hx)).resolve_left hx0
  · have hrad : radial x y z - 180 * x = 0 := (mul_eq_zero.mp hy).resolve_left hy0
    have hyx : y ^ 2 = 3 * x ^ 2 := by linear_combination - hx / 90 + x * hrad / 90
    have hx0 : x ≠ 0 := by
      intro h
      rw [h] at hyx
      exact hy0 (by nlinarith [sq_nonneg y])
    apply Or.inr
    refine hreduce (-2 * x) (by intro h; apply hx0; linarith) ?_ ?_ ?_
    · exact Or.inr ⟨by ring, by linarith [hyx, show 3 * (-2 * x) ^ 2 / 4 = 3 * x ^ 2 by ring]⟩
    · linear_combination hyx
    · linear_combination hrad

theorem stationary_of_direction {s x y z : ℝ} (hdir : direction s x y)
    (hz : (z = 0 ∧ 36 * s ^ 2 + 90 * s + 5 = 0) ∨
      (z ^ 2 = 5 / 48 + 3 / 2 * s ^ 2 ∧ (s = 1 / 6 ∨ s = 1 / 3))) :
    stationary x y z := by
  have hr : x ^ 2 + y ^ 2 = s ^ 2 := by
    rcases hdir with ⟨rfl, rfl⟩ | ⟨hx, hy⟩
    · ring
    · rw [hx, hy]
      ring
  have hrad : radial x y z = -90 * s := by
    rw [radial, hr]
    rcases hz with ⟨rfl, hp⟩ | ⟨hz, hs | hs⟩
    · linarith
    · rw [hz, hs]
      norm_num
    · rw [hz, hs]
      norm_num
  unfold stationary
  rw [hrad, hr]
  refine ⟨?_, ?_, ?_⟩
  · rcases hdir with ⟨rfl, rfl⟩ | ⟨hx, hy⟩
    · ring
    · rw [hx, hy]
      ring
  · rcases hdir with ⟨rfl, rfl⟩ | ⟨hx, _⟩
    · ring
    · rw [hx]
      ring
  · rcases hz with ⟨rfl, _⟩ | ⟨hz, _⟩
    · ring
    · rw [hz]
      ring

def hessianDet (x y z : ℝ) : ℝ :=
  let a := radial x y z + 72 * x ^ 2 + 180 * x
  let b := 72 * x * y - 180 * y
  let c := -288 * x * z
  let d := radial x y z + 72 * y ^ 2 - 180 * x
  let e := -288 * y * z
  let f := -10 - 144 * (x ^ 2 + y ^ 2) + 288 * z ^ 2
  a * d * f + 2 * b * c * e - a * e ^ 2 - d * c ^ 2 - f * b ^ 2

theorem hessianDet_radial {s x y z : ℝ}
    (hdir : direction s x y) (hlin : radial x y z = -90 * s) :
    hessianDet x y z = (-270 * s) *
      ((72 * s ^ 2 + 90 * s) * (-10 - 144 * s ^ 2 + 288 * z ^ 2) -
        (-288 * s * z) ^ 2) := by
  rcases hdir with ⟨rfl, rfl⟩ | ⟨hx, hy⟩
  · simp only [hessianDet, hlin, zero_pow, Nat.succ_ne_zero, add_zero, mul_zero,
      zero_mul, sub_zero]
    ring
  · have hr : x ^ 2 + y ^ 2 = s ^ 2 := by rw [hx, hy]; ring
    unfold hessianDet
    dsimp only
    rw [hlin, hr, hx, hy]
    calc
      _ = (y ^ 2) *
          (2 * (-36 * s - 180) * (144 * s * z) * (-288 * z) -
            (18 * s ^ 2 - 180 * s) * (-288 * z) ^ 2 -
            (-10 - 144 * s ^ 2 + 288 * z ^ 2) * (-36 * s - 180) ^ 2) +
          (18 * s ^ 2 - 180 * s) * (54 * s ^ 2) *
            (-10 - 144 * s ^ 2 + 288 * z ^ 2) -
          (54 * s ^ 2) * (144 * s * z) ^ 2 := by ring
      _ = _ := by rw [hy]; ring

theorem hessianDet_ne_zero {x y z : ℝ} (h : stationary x y z) :
    hessianDet x y z ≠ 0 := by
  rcases radial_classification h with ⟨rfl, rfl, hz | hz⟩ | ⟨s, hs, hdir, hz⟩
  · norm_num [hz, hessianDet, radial]
  · simp [hessianDet, radial, hz]
    norm_num
  · have hlin : radial x y z = -90 * s := by
      rcases hdir with ⟨rfl, rfl⟩ | ⟨hx, hy⟩
      · have hfactor : x * (radial x 0 z + 90 * x) = 0 := by
          linear_combination h.1
        have := (mul_eq_zero.mp hfactor).resolve_left hs
        linarith
      · have hy' : y ≠ 0 := by
          intro hy0
          rw [hy0] at hy
          have hs' : s ^ 2 = 0 := by linarith
          exact hs (by nlinarith [hs'])
        have hfactor := (mul_eq_zero.mp h.2.1).resolve_left hy'
        linarith
    rw [hessianDet_radial hdir hlin]
    apply mul_ne_zero (mul_ne_zero (by norm_num) hs)
    rcases hz with ⟨rfl, hp⟩ | ⟨hz, hs' | hs'⟩
    · have hpos : 0 < 10 + 144 * s ^ 2 := by positivity
      have hprod : (72 * s ^ 2 + 90 * s) ≠ 0 := by
        intro heq
        have hfactor : s * (72 * s + 90) = 0 := by linear_combination heq
        have hsval : s = -5 / 4 := by
          have := (mul_eq_zero.mp hfactor).resolve_left hs
          linarith
        rw [hsval] at hp
        norm_num at hp
      have hneg : -10 - 144 * s ^ 2 ≠ 0 := by linarith
      simpa using mul_ne_zero hprod hneg
    · rw [hs'] at hz ⊢
      have heq : z ^ 2 = (7 / 48 : ℝ) := by linear_combination hz
      ring_nf
      rw [heq]
      norm_num
    · rw [hs'] at hz ⊢
      have heq : z ^ 2 = (13 / 48 : ℝ) := by linear_combination hz
      ring_nf
      rw [heq]
      norm_num


private noncomputable def planarRadii : Bool → ℝ
  | false => (-90 - Real.sqrt 7380) / 72
  | true => (-90 + Real.sqrt 7380) / 72

private theorem planarRadii_spec (s : ℝ) :
    36 * s ^ 2 + 90 * s + 5 = 0 ↔ ∃ b, s = planarRadii b := by
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7380)
  have hf : 36 * s ^ 2 + 90 * s + 5 =
      36 * (s - planarRadii false) * (s - planarRadii true) := by
    dsimp [planarRadii]
    linear_combination hsqrt / 144
  rw [hf, mul_eq_zero, mul_eq_zero]
  simp only [OfNat.ofNat_ne_zero, false_or, sub_eq_zero, Bool.exists_bool]

private theorem planarRadii_neg (b : Bool) : planarRadii b < 0 := by
  have hpos := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 7380)
  have hlt : Real.sqrt 7380 < 90 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7380)
    nlinarith
  cases b <;> simp only [planarRadii] <;> linarith

private theorem planarRadii_inj : Function.Injective planarRadii := by
  have hpos := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 7380)
  intro a b h
  cases a <;> cases b <;> simp [planarRadii] at h ⊢ <;> linarith only [h, hpos]

private noncomputable def angular (s : ℝ) : Fin 3 → ℝ × ℝ :=
  ![(s, 0), (-s / 2, Real.sqrt 3 * s / 2), (-s / 2, -(Real.sqrt 3 * s / 2))]

private theorem square_eq_sq_iff (a b : ℝ) : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b := by
  have h : (a - b) * (a + b) = a ^ 2 - b ^ 2 := by ring
  rw [← sub_eq_zero, ← h, mul_eq_zero]
  constructor
  · rintro (h' | h')
    · exact Or.inl (by linarith only [h'])
    · exact Or.inr (by linarith only [h'])
  · rintro (h' | h')
    · exact Or.inl (by linarith only [h'])
    · exact Or.inr (by linarith only [h'])

private theorem angular_spec (s x y : ℝ) :
    ((x = s ∧ y = 0) ∨ (x = -s / 2 ∧ y ^ 2 = 3 * s ^ 2 / 4)) ↔
      ∃ i, (x, y) = angular s i := by
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have h : 3 * s ^ 2 / 4 = (Real.sqrt 3 * s / 2) ^ 2 := by
    linear_combination -s ^ 2 / 4 * hsq
  rw [h, square_eq_sq_iff]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp [angular] at hi <;> simp [hi.1, hi.2]

private theorem angular_inj {s t : ℝ} (hs : s ≠ 0) (ht : t ≠ 0)
    {i j : Fin 3} (h : angular s i = angular t j) : s = t ∧ i = j := by
  have hpos := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)
  have helim (u : ℝ) (hu : u ≠ 0) : Real.sqrt 3 * u / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero hpos.ne' hu) (by norm_num)
  fin_cases i <;> fin_cases j <;> simp [angular] at h ⊢
  all_goals
    first
    | exact h.1
    | exact h
    | exact False.elim (hs h.2)
    | exact False.elim (ht h.2)
    | exact False.elim (helim t ht (by linarith only [h.2]))
    | exact False.elim (helim s hs (by linarith only [h.2]))
    | exfalso
      apply helim s hs
      have heq : s = t := by linarith only [h.1]
      rw [← heq] at h
      linarith only [h.2]

private noncomputable def signedRoot (r : ℝ) (b : Bool) : ℝ :=
  if b then Real.sqrt r else -Real.sqrt r

private theorem signedRoot_spec (r z : ℝ) (hr : 0 ≤ r) :
    z ^ 2 = r ↔ ∃ b, z = signedRoot r b := by
  rw [← Real.sq_sqrt hr, square_eq_sq_iff]
  simp [signedRoot, Bool.exists_bool, or_comm]

private theorem signedRoot_inj {r : ℝ} (hr : 0 < r) : Function.Injective (signedRoot r) := by
  have hpos := Real.sqrt_pos.2 hr
  intro a b h
  cases a <;> cases b <;> simp [signedRoot] at h ⊢ <;> linarith only [h, hpos]

private theorem signedRoot_ne_zero {r : ℝ} (hr : 0 < r) (b : Bool) :
    signedRoot r b ≠ 0 := by
  have hpos := Real.sqrt_pos.2 hr
  cases b <;> simp [signedRoot, hpos.ne']

private noncomputable def axialHeight : Fin 3 → ℝ :=
  ![0, signedRoot (5 / 48) false, signedRoot (5 / 48) true]

private theorem axialHeight_spec (z : ℝ) :
    z = 0 ∨ z ^ 2 = 5 / 48 ↔ ∃ i, z = axialHeight i := by
  rw [signedRoot_spec _ _ (by norm_num)]
  constructor
  · rintro (rfl | ⟨b, rfl⟩)
    · exact ⟨0, rfl⟩
    · cases b
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr ⟨false, rfl⟩
    · exact Or.inr ⟨true, rfl⟩

private theorem axialHeight_inj : Function.Injective axialHeight := by
  intro i j h
  have hp : 0 < Real.sqrt (5 / 48 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  fin_cases i <;> fin_cases j <;> simp [axialHeight, signedRoot] at h ⊢ <;>
    linarith only [h, hp, show 0 < Real.sqrt 5 / Real.sqrt 48 by positivity]

private noncomputable def offRadius (b : Bool) : ℝ := if b then 1 / 3 else 1 / 6

private theorem offRadius_pos (b : Bool) : 0 < offRadius b := by
  cases b <;> norm_num [offRadius]

private theorem offRadius_inj : Function.Injective offRadius := by
  intro a b h
  cases a <;> cases b <;> norm_num [offRadius] at *

private noncomputable def offHeightSq (s : ℝ) : ℝ := 5 / 48 + 3 / 2 * s ^ 2

private theorem offHeightSq_pos (s : ℝ) : 0 < offHeightSq s := by
  unfold offHeightSq
  positivity

private theorem angular_ne_origin {s : ℝ} (hs : s ≠ 0) (i : Fin 3) : angular s i ≠ (0, 0) := by
  intro h
  have hx := congrArg Prod.fst h
  fin_cases i <;> simp [angular] at hx <;> exact hs hx

private abbrev CriticalIndex := Fin 3 ⊕ ((Bool × Fin 3) ⊕ (Bool × Bool × Fin 3))

private noncomputable def criticalCoordinates : CriticalIndex → (ℝ × ℝ) × ℝ
  | .inl i => ((0, 0), axialHeight i)
  | .inr (.inl (b, i)) => (angular (planarRadii b) i, 0)
  | .inr (.inr (b, e, i)) =>
      (angular (offRadius b) i, signedRoot (offHeightSq (offRadius b)) e)

private theorem criticalCoordinates_inj : Function.Injective criticalCoordinates := by
  intro a b h
  rcases a with a | (⟨a, i⟩ | ⟨a, e, i⟩) <;>
    rcases b with b | (⟨b, j⟩ | ⟨b, f, j⟩) <;>
    simp only [criticalCoordinates, Prod.mk.injEq] at h
  · exact congrArg Sum.inl (axialHeight_inj h.2)
  · exact False.elim (angular_ne_origin (planarRadii_neg b).ne j h.1.symm)
  · exact False.elim (angular_ne_origin (offRadius_pos b).ne' j h.1.symm)
  · exact False.elim (angular_ne_origin (planarRadii_neg a).ne i h.1)
  · obtain ⟨hab, hij⟩ := angular_inj (planarRadii_neg a).ne (planarRadii_neg b).ne h.1
    rw [planarRadii_inj hab, hij]
  · exact False.elim (signedRoot_ne_zero (offHeightSq_pos _) f h.2.symm)
  · exact False.elim (angular_ne_origin (offRadius_pos a).ne' i h.1)
  · exact False.elim (signedRoot_ne_zero (offHeightSq_pos _) e h.2)
  · obtain ⟨hab, hij⟩ := angular_inj (offRadius_pos a).ne' (offRadius_pos b).ne' h.1
    obtain rfl := offRadius_inj hab
    obtain rfl := signedRoot_inj (offHeightSq_pos _) h.2
    rw [hij]


private theorem stationary_iff_coordinates (x y z : ℝ) :
    stationary x y z ↔ ∃ i, ((x, y), z) = criticalCoordinates i := by
  constructor
  · intro h
    rcases radial_classification h with ⟨rfl, rfl, hz⟩ | ⟨s, _, hdir, hz⟩
    · obtain ⟨i, hi⟩ := (axialHeight_spec z).mp hz
      exact ⟨Sum.inl i, by simp [criticalCoordinates, hi]⟩
    · obtain ⟨i, hi⟩ := (angular_spec s x y).mp hdir
      rcases hz with ⟨rfl, hp⟩ | ⟨hz, hs | hs⟩
      · obtain ⟨b, rfl⟩ := (planarRadii_spec s).mp hp
        exact ⟨Sum.inr (Sum.inl (b, i)), by simp [criticalCoordinates, hi]⟩
      · have he : s = offRadius false := hs
        obtain ⟨b, hb⟩ := (signedRoot_spec (offHeightSq s) z (offHeightSq_pos s).le).mp hz
        exact ⟨Sum.inr (Sum.inr (false, b, i)), by rw [criticalCoordinates, ← he, ← hi, ← hb]⟩
      · have he : s = offRadius true := hs
        obtain ⟨b, hb⟩ := (signedRoot_spec (offHeightSq s) z (offHeightSq_pos s).le).mp hz
        exact ⟨Sum.inr (Sum.inr (true, b, i)), by rw [criticalCoordinates, ← he, ← hi, ← hb]⟩
  · rintro ⟨i, hi⟩
    rcases i with i | (⟨b, i⟩ | ⟨b, e, i⟩) <;>
      simp only [criticalCoordinates, Prod.mk.injEq] at hi
    · rcases hi with ⟨⟨rfl, rfl⟩, hz⟩
      rcases (axialHeight_spec z).mpr ⟨i, hz⟩ with rfl | hz
      · norm_num [stationary, radial]
      · unfold stationary radial
        rw [hz]
        norm_num
    · apply stationary_of_direction ((angular_spec _ _ _).mpr ⟨i, hi.1⟩)
      exact Or.inl ⟨hi.2, (planarRadii_spec _).mpr ⟨b, rfl⟩⟩
    · apply stationary_of_direction ((angular_spec _ _ _).mpr ⟨i, hi.1⟩)
      refine Or.inr ⟨(signedRoot_spec _ _ (offHeightSq_pos _).le).mpr ⟨e, hi.2⟩, ?_⟩
      cases b <;> norm_num [offRadius]

private noncomputable def criticalPoint (i : CriticalIndex) : E :=
  let p := criticalCoordinates i
  WithLp.toLp 2 ![p.1.1, p.1.2, p.2]

private theorem criticalPoint_inj : Function.Injective criticalPoint := by
  intro i j h
  apply criticalCoordinates_inj
  apply Prod.ext
  · apply Prod.ext
    · exact congrArg (fun p : E => p.ofLp 0) h
    · exact congrArg (fun p : E => p.ofLp 1) h
  · exact congrArg (fun p : E => p.ofLp 2) h

private theorem criticalPoint_range :
    {p : E | ∇ phiZero p = 0} = Set.range criticalPoint := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_range, critical_iff]
  change stationary (p.ofLp 0) (p.ofLp 1) (p.ofLp 2) ↔ _
  rw [stationary_iff_coordinates]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    apply WithLp.ofLp_injective
    funext j
    rcases Prod.mk.inj hi with ⟨hxy, hz⟩
    rcases Prod.mk.inj hxy with ⟨hx, hy⟩
    fin_cases j
    · exact hx.symm
    · exact hy.symm
    · exact hz.symm
  · rintro ⟨i, rfl⟩
    exact ⟨i, by cases h : criticalCoordinates i with | mk xy z => cases xy; simp [criticalPoint, h]⟩

private theorem nondegenerate_at_critical (p : E) (hp : ∇ phiZero p = 0) :
    HasNondegenerateHessianAt phiZero p := by
  have hstat : stationary (p.ofLp 0) (p.ofLp 1) (p.ofLp 2) := (critical_iff p).mp hp
  have hdet : (hessianMatrix p).det ≠ 0 := by
    have hval : (hessianMatrix p).det = hessianDet (p.ofLp 0) (p.ofLp 1) (p.ofLp 2) := by
      simp only [hessianMatrix, Matrix.det_fin_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.of_apply, Matrix.head_cons, Matrix.tail_cons, hessianDet, radial]
      ring
    exact hval.symm ▸ hessianDet_ne_zero hstat
  have hmul := Matrix.mulVec_injective_iff_isUnit.mpr
    ((hessianMatrix p).isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hdet))
  intro v hv
  let u := hessianMatrix p *ᵥ v.ofLp
  have hu : u ≠ 0 := by
    intro h
    apply hv
    apply WithLp.ofLp_injective
    apply hmul
    simpa [u] using h
  refine ⟨WithLp.toLp 2 u, ?_⟩
  intro h
  have hh := second_derivative p v (WithLp.toLp 2 u)
  rw [h, mul_zero] at hh
  apply hu
  exact dotProduct_self_eq_zero.mp hh.symm

end OMA.Quartic

open OMA.Quartic in
private theorem quarticCriticalPoints :
    {p : EuclideanSpace ℝ (Fin 3) | ∇ phiZero p = 0}.encard = 21 ∧
      ∀ p, ∇ phiZero p = 0 → HasNondegenerateHessianAt phiZero p := by
  constructor
  · rw [criticalPoint_range, ← Set.image_univ, criticalPoint_inj.encard_image, Set.encard_univ]
    norm_num [ENat.card_eq_coe_natCard, Nat.card_eq_fintype_card, CriticalIndex]
  · exact nondegenerate_at_critical

end

/-! ## Smooth remainders and continuation of nondegenerate critical points -/

namespace OMA.Center
open Arxiv.«2607.27197» Filter InnerProductSpace
open scoped Topology Gradient

abbrev E := EuclideanSpace ℝ (Fin 3)

def radicand (t a b : ℝ) := 1 + t * (-2*a + t*b)
noncomputable def c2 (a b : ℝ) := (3*a^2 - b)/2
noncomputable def c3 (a b : ℝ) := (5*a^3 - 3*a*b)/2
noncomputable def c4 (a b : ℝ) := (35*a^4 - 30*a^2*b + 3*b^2)/8

/-- Remainder after degree four in the expansion of the reciprocal square root at one. -/
noncomputable def sqrtRem (s : ℝ) :=
  -(35*s^4 + 175*s^3 + 345*s^2 + 325*s + 128) / (128*s*(s+1)^5)

lemma sqrt_identity {u : ℝ} (hu : 0 < 1+u) :
    1 / Real.sqrt (1+u) =
    1-u/2+3*u^2/8-5*u^3/16+35*u^4/128+u^5*sqrtRem (Real.sqrt (1+u)) := by
  let s := Real.sqrt (1+u)
  have hs : 0 < s := Real.sqrt_pos.2 hu
  have he : u = s^2 - 1 := by linarith [Real.sq_sqrt hu.le]
  change 1/s = 1-u/2+3*u^2/8-5*u^3/16+35*u^4/128+u^5*sqrtRem s
  rw [he]
  unfold sqrtRem
  field_simp [hs.ne', show s+1 ≠ 0 by positivity]
  ring

noncomputable def rem5 (t a b : ℝ) :=
  -5*a*b*(14*a^2-3*b)/8 + t*(5*b^2*(21*a^2-b)/16 +
    t*(-35*a*b^3/16+t*(35*b^4/128))) +
    (-2*a+t*b)^5*sqrtRem (Real.sqrt (radicand t a b))

lemma expand_inv {t a b : ℝ} (h : 0 < radicand t a b) :
    1 / Real.sqrt (radicand t a b) = 1+t*a+t^2*c2 a b+t^3*c3 a b+
      t^4*c4 a b+t^5*rem5 t a b := by
  unfold radicand
  rw [sqrt_identity (u := t*(-2*a+t*b)) h]
  unfold c2 c3 c4 rem5 radicand
  ring

def normSq (x : E) := x.ofLp 0^2 + x.ofLp 1^2 + x.ofLp 2^2
noncomputable def dPlus (x : E) := -x.ofLp 0/2 + Real.sqrt 3*x.ofLp 1/2
noncomputable def dMinus (x : E) := -x.ofLp 0/2 - Real.sqrt 3*x.ofLp 1/2

noncomputable abbrev proj (i : Fin 3) : E →L[ℝ] ℝ :=
  (EuclideanSpace.proj i)

lemma rem5_smooth {t a b : ℝ × E → ℝ} {p : ℝ × E}
    (ht : ContDiffAt ℝ ⊤ t p) (ha : ContDiffAt ℝ ⊤ a p) (hb : ContDiffAt ℝ ⊤ b p)
    (hz : t p = 0) : ContDiffAt ℝ ⊤ (fun q => rem5 (t q) (a q) (b q)) p := by
  have hh : radicand (t p) (a p) (b p) = 1 := by simp [radicand, hz]
  have hs : ContDiffAt ℝ ⊤ (fun q => Real.sqrt (radicand (t q) (a q) (b q))) p := by
    apply ContDiffAt.sqrt
    · unfold radicand
      fun_prop
    · rw [hh]; norm_num
  unfold rem5 sqrtRem
  fun_prop (disch := simp [hh])

abbrev Dual := E →L[ℝ] ℝ

lemma grad_zero {V : E → ℝ} {x} :
    ∇ V x = 0 ↔ fderiv ℝ V x = 0 := by
  rw [← toDual_gradient]
  exact (toDual ℝ _).map_eq_zero_iff.symm

lemma hessian_iff (V : E → ℝ) (x : E) :
    HasNondegenerateHessianAt V x ↔ (fderiv ℝ (fderiv ℝ V) x).IsInvertible := by
  let L := fderiv ℝ (fderiv ℝ V) x
  change (∀ v : E, v ≠ 0 → ∃ w, iteratedFDeriv ℝ 2 V x ![v,w] ≠ 0) ↔ L.IsInvertible
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  change (∀ v : E, v ≠ 0 → ∃ w, L v w ≠ 0) ↔ L.IsInvertible
  constructor
  · intro h
    have hk : L.ker = ⊥ := by
      apply LinearMap.ker_eq_bot'.mpr
      intro v hv
      by_contra hn
      obtain ⟨w, hw⟩ := h v hn
      change L v = 0 at hv
      exact hw (by rw [hv]; rfl)
    have hdim : Module.finrank ℝ E = Module.finrank ℝ Dual :=
      (toDual ℝ E).toLinearEquiv.finrank_eq
    have hr : L.range = ⊤ := LinearMap.range_eq_top.mpr
      ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp (LinearMap.ker_eq_bot.mp hk))
    exact ⟨ContinuousLinearEquiv.ofBijective L hk hr, rfl⟩
  · rintro ⟨A,hA⟩ v hv
    by_contra! h
    apply hv
    apply A.injective
    rw [map_zero]
    change (A : E →L[ℝ] Dual) v = 0
    rw [hA]
    ext w
    exact h w

noncomputable def spatialField (V : ℝ → E → ℝ) (p : ℝ × E) :=
  fderiv ℝ (V p.1) p.2

lemma field_smooth {V : ℝ → E → ℝ} {p : ℝ × E}
    (h : ContDiffAt ℝ ⊤ (Function.uncurry V) p) :
    ContDiffAt ℝ ⊤ (spatialField V) p := by
  rcases p with ⟨e,x⟩
  apply ContDiffAt.fderiv (n := ⊤) (f := fun q : ℝ × E => V q.1) (g := Prod.snd)
  · have hh : ContDiffAt ℝ ⊤ (fun q : (ℝ × E) × E => (q.1.1,q.2)) ((e,x),x) := by fun_prop
    exact h.comp ((e,x),x) hh
  · exact contDiffAt_snd
  · simp

lemma partial_hessian {V : ℝ → E → ℝ} {p : ℝ × E}
    (h : DifferentiableAt ℝ (spatialField V) p) :
    fderiv ℝ (fderiv ℝ (V p.1)) p.2 =
    (fderiv ℝ (spatialField V) p).comp (.inr ℝ ℝ E) := by
  rcases p with ⟨e,x⟩
  have h' := (h.hasFDerivAt.comp x (hasFDerivAt_prodMk_right (𝕜 := ℝ) e x)).fderiv
  exact h'

/-- The implicit function for the spatial differential preserves nondegeneracy. -/
lemma branch {V : ℝ → E → ℝ} {x : E}
    (hs : ContDiffAt ℝ ⊤ (Function.uncurry V) (0,x))
    (hc : fderiv ℝ (V 0) x = 0) (hn : HasNondegenerateHessianAt (V 0) x) :
    ∃ g : ℝ → E, Tendsto g (𝓝 0) (𝓝 x) ∧
      ∀ᶠ e in 𝓝 0, fderiv ℝ (V e) (g e) = 0 ∧ HasNondegenerateHessianAt (V e) (g e) := by
  let p : ℝ × E := (0,x)
  have h := field_smooth hs
  have h1 : ContDiffAt ℝ 1 (spatialField V) p := h.of_le (by simp)
  have hi := (hessian_iff _ _).mp hn
  change (fderiv ℝ (fderiv ℝ (V p.1)) p.2).IsInvertible at hi
  rw [partial_hessian (h1.differentiableAt (by simp))] at hi
  let g := h1.implicitFunction one_ne_zero hi
  have hg : Tendsto g (𝓝 0) (𝓝 x) :=
    (h1.hasStrictFDerivAt one_ne_zero).tendsto_implicitFunctionOfProdDomain hi
  refine ⟨g, hg, ?_⟩
  have hh : ContinuousAt (fun q : ℝ × E =>
      (fderiv ℝ (spatialField V) q).comp (.inr ℝ ℝ E)) p := by
    have hf := (h.fderiv_right (m := 1) (by simp)).continuousAt
    fun_prop
  have hopen : IsOpen {L : E →L[ℝ] Dual | L.IsInvertible} :=
    ContinuousLinearEquiv.isOpen
  have hinv := hh.tendsto (hopen.mem_nhds hi)
  have hd : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ (spatialField V) q :=
    (h1.eventually (by norm_num)).mono fun q hq => hq.differentiableAt one_ne_zero
  have hp : Tendsto (fun e => (e,g e)) (𝓝 0) (𝓝 p) :=
    tendsto_id.prodMk_nhds hg
  filter_upwards [h1.eventually_apply_implicitFunction one_ne_zero hi, hp hinv, hp hd] with e he hei hed
  refine ⟨he.trans hc, (hessian_iff _ _).mpr ?_⟩
  rw [partial_hessian hed]
  exact hei

lemma transport {V W : E → ℝ} {x : E} (A : E ≃L[ℝ] E) {b c : ℝ} (hc : c ≠ 0)
    (he : V ∘ A =ᶠ[𝓝 x] fun y => b + c*W y)
    (hs : ContDiffAt ℝ 2 W x) (hg : fderiv ℝ W x = 0) (hn : HasNondegenerateHessianAt W x) :
    fderiv ℝ V (A x) = 0 ∧ HasNondegenerateHessianAt V (A x) := by
  have hd := he.fderiv_eq (𝕜 := ℝ)
  rw [A.comp_right_fderiv] at hd
  have hdW := hs.differentiableAt (by norm_num)
  have hright : fderiv ℝ (fun y => b + c*W y) x = 0 := by
    have h := (hdW.hasFDerivAt.const_mul c).const_add b
    rw [h.fderiv, hg]
    simp
  rw [hright] at hd
  constructor
  · ext v
    obtain ⟨w, rfl⟩ := A.surjective v
    exact congrArg (fun L : E →L[ℝ] ℝ => L w) hd
  · intro v hv
    obtain ⟨u,rfl⟩ := A.surjective v
    obtain ⟨w,hw⟩ := hn u (fun h => hv (by simp [h]))
    refine ⟨A w, ?_⟩
    have hsrc := (he.iteratedFDeriv (𝕜 := ℝ) 2).self_of_nhds
    have ha := A.iteratedFDerivWithin_comp_right V uniqueDiffOn_univ (Set.mem_univ (A x)) 2
    simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at ha
    have htwo : ContDiffAt ℝ (2 : ℕ) (fun y => c • W y) x := by
      change ContDiffAt ℝ 2 (fun y => c * W y) x
      fun_prop
    change iteratedFDeriv ℝ 2 (V ∘ A) x =
      iteratedFDeriv ℝ 2 (fun y => b + c • W y) x at hsrc
    rw [fun_iteratedFDeriv_add_apply contDiffAt_const htwo,
      iteratedFDeriv_const_of_ne (by decide : (2 : ℕ) ≠ 0), iteratedFDeriv_const_smul_apply' hs] at hsrc
    simp only [Pi.zero_apply, zero_add] at hsrc
    rw [ha] at hsrc
    have hh := congrArg (fun L : E [×2]→L[ℝ] ℝ => L ![u,w]) hsrc
    change iteratedFDeriv ℝ 2 V (A x) (fun i => A (![u,w] i)) =
      c * iteratedFDeriv ℝ 2 W x ![u,w] at hh
    have hvec : (fun i => A (![u,w] i)) = ![A u,A w] := by
      funext i
      fin_cases i <;> rfl
    rw [hvec] at hh
    exact hh.trans_ne (mul_ne_zero hc hw)

/-- Finitely many branches with distinct limits remain pairwise distinct. -/
lemma eventually_injective {ι : Type*} [Finite ι] {a : ι → E} (ha : Function.Injective a)
    {g : ι → ℝ → E} (hg : ∀ i, Tendsto (g i) (𝓝 0) (𝓝 (a i))) :
    ∀ᶠ e in 𝓝 0, Function.Injective (fun i => g i e) := by
  apply eventually_all.mpr
  intro i
  apply eventually_all.mpr
  intro j
  by_cases h : i = j
  · exact Eventually.of_forall fun _ _ => h
  · have hn : (a i,a j) ∈ (Set.diagonal E)ᶜ := fun he => h (ha he)
    have hu := (hg i).prodMk_nhds (hg j)
    filter_upwards [hu (isClosed_diagonal.isOpen_compl.mem_nhds hn)] with e he
    exact fun hij => (he hij).elim

end OMA.Center

/-! ## The three equilibria away from the center of the initial triangle -/

namespace OMA.Edge
open Arxiv.«2607.27197» InnerProductSpace Filter
open scoped RealInnerProductSpace Gradient Topology

abbrev E := EuclideanSpace ℝ (Fin 3)

lemma dist_derivative (a x : E) (h : x ≠ a) :
    HasFDerivAt (fun y => dist y a) ((dist x a)⁻¹ • innerSL ℝ (x-a)) x := by
  have hn := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)
  have hs : HasFDerivAt (fun y : E => ‖y-a‖^2) (2 • innerSL ℝ (x-a)) x := by
    simpa using ((hasFDerivAt_id x).sub_const a).norm_sq
  convert! hs.sqrt (pow_ne_zero 2 hn) using 1
  · funext y
    simp [dist_eq_norm, Real.sqrt_sq (norm_nonneg _)]
  · simp only [dist_eq_norm, Real.sqrt_sq (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    field_simp
    <;> norm_num

noncomputable def dCharge (q : ℝ) (a x : E) : E →L[ℝ] ℝ :=
  (-q / dist x a ^ 3) • innerSL ℝ (x-a)

lemma charge_derivative (q : ℝ) (a x : E) (h : x ≠ a) :
    HasFDerivAt (fun y => q / dist y a) (dCharge q a x) x := by
  have hn : dist x a ≠ 0 := dist_ne_zero.mpr h
  have hd := dist_derivative a x h
  convert! ((hasDerivAt_inv hn).comp_hasFDerivAt x hd).const_mul q using 1
  dsimp [dCharge]
  rw [smul_smul, smul_smul]
  congr 1
  field_simp

lemma coef_derivative (q : ℝ) (a x : E) (h : x ≠ a) :
    HasFDerivAt (fun y => -q / dist y a ^ 3)
      ((3*q / dist x a ^ 5) • innerSL ℝ (x-a)) x := by
  have hn : dist x a ≠ 0 := dist_ne_zero.mpr h
  have hd := dist_derivative a x h
  have hc := (hasDerivAt_const (dist x a) (-q)).div ((hasDerivAt_id (dist x a)).pow 3) (pow_ne_zero 3 hn)
  convert! hc.comp_hasFDerivAt x hd using 1
  dsimp
  rw [smul_smul]
  congr 1
  field_simp
  <;> ring

lemma potential_derivative {n : ℕ} (q : Fin n → ℝ) (a : Fin n → E) (x : E)
    (hx : ∀ j, x ≠ a j) :
    fderiv ℝ (potential q a) x = ∑ j, dCharge (q j) (a j) x := by
  exact (HasFDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => charge_derivative (q j) (a j) x (hx j))).fderiv

noncomputable def ddCharge (q : ℝ) (a x v w : E) : ℝ :=
  (3*q / dist x a ^ 5) * ⟪x-a,v⟫_ℝ * ⟪x-a,w⟫_ℝ - (q / dist x a ^ 3) * ⟪v,w⟫_ℝ

lemma potential_hessian {n : ℕ} (q : Fin n → ℝ) (a : Fin n → E) (x v w : E)
    (hx : ∀ j, x ≠ a j) :
    iteratedFDeriv ℝ 2 (potential q a) x ![v,w] = ∑ j, ddCharge (q j) (a j) x v w := by
  have hnear : ∀ᶠ y in 𝓝 x, ∀ j, y ≠ a j :=
    eventually_all.mpr fun j => isOpen_compl_singleton.mem_nhds (hx j)
  have heq : fderiv ℝ (potential q a) =ᶠ[𝓝 x] (fun y => ∑ j, dCharge (q j) (a j) y) :=
    hnear.mono fun y hy => potential_derivative q a y hy
  have hi (j : Fin n) := ((innerSL ℝ (E := E)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const (a j)))
  have hd (j : Fin n) := (coef_derivative (q j) (a j) x (hx j)).smul (hi j)
  rw [iteratedFDeriv_two_apply, heq.fderiv_eq]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hsum := (HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => hd j)).fderiv
  change fderiv ℝ (fun y => ∑ j, dCharge (q j) (a j) y) x = _ at hsum
  rw [hsum]
  simp [ddCharge, smul_eq_mul, innerSL_apply_apply, inner_sub_left, -Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  change -q j / _ * ⟪v,w⟫_ℝ + _ * (⟪x,w⟫_ℝ - ⟪a j,w⟫_ℝ) = _
  ring

/-! ### Radial force and uniform bounds on the three diagonal entries -/

noncomputable def weight (e : ℝ) := 3 / 4 * e ^ 3 - 5 / 32 * e ^ 5
noncomputable def baseDist (t : ℝ) := Real.sqrt ((t + 1/2)^2 + 3/4)
noncomputable def poleDist (e t : ℝ) := Real.sqrt (t^2 + e^2)
noncomputable def force (e t : ℝ) :=
  1 / (1-t)^2 - 2 * (t+1/2) / (baseDist t)^3 - 2 * weight e * t / (poleDist e t)^3

lemma weight_bounds {e : ℝ} (he : e ∈ Set.Ioo 0 (1/100 : ℝ)) :
    0 < weight e ∧ weight e < 1/1000000 := by
  have h := he.1
  have h' := he.2
  have he2 : e ^ 2 < (1/100 : ℝ)^2 := by gcongr
  have he3 : e ^ 3 < (1/100 : ℝ)^3 := by gcongr
  dsimp [weight]
  constructor
  · have hh : 0 < 3/4 - 5/32 * e^2 := by linarith
    nlinarith only [mul_pos (pow_pos h 3) hh]
  · nlinarith only [he3, pow_pos h 5]

lemma base_bounds {t : ℝ} (ht : t ∈ Set.Icc (-1/3 : ℝ) (-1/4)) :
    7/8 < baseDist t ∧ baseDist t < 91/100 := by
  have hl : (1/6 : ℝ) ≤ t+1/2 := by linarith [ht.1]
  have hu : t+1/2 ≤ 1/4 := by linarith [ht.2]
  have hl2 : (1/6 : ℝ)^2 ≤ (t+1/2)^2 := by gcongr
  have hu2 : (t+1/2)^2 ≤ (1/4 : ℝ)^2 := by gcongr
  have h := Real.sq_sqrt (show 0 ≤ (t+1/2)^2+3/4 by positivity)
  dsimp [baseDist]
  constructor <;> nlinarith only [h, hl2, hu2, Real.sqrt_nonneg ((t+1/2)^2+3/4),
    sq_nonneg (Real.sqrt ((t+1/2)^2+3/4) - 7/8),
    sq_nonneg (Real.sqrt ((t+1/2)^2+3/4) - 91/100)]

lemma pole_lower {t e : ℝ} (ht : t ≤ -1/4) : 1/4 ≤ poleDist e t := by
  apply Real.le_sqrt_of_sq_le
  have h : (1/4 : ℝ)^2 ≤ (-t)^2 := by gcongr; linarith
  nlinarith only [h, sq_nonneg e]

lemma weight_bounds_closed {e : ℝ} (he : e ∈ Set.Ico 0 (1/100 : ℝ)) :
    0 ≤ weight e ∧ weight e < 1/1000000 := by
  rcases he.1.eq_or_lt with h | h
  · rw [← h]; norm_num [weight]
  · exact ⟨(weight_bounds ⟨h,he.2⟩).1.le,(weight_bounds ⟨h,he.2⟩).2⟩

lemma force_root {e : ℝ} (he : e ∈ Set.Ico 0 (1/100 : ℝ)) :
    ∃ t ∈ Set.Icc (-1/3 : ℝ) (-1/4), force e t = 0 := by
  have hw := weight_bounds_closed he
  have hd (t : ℝ) (ht : t ∈ Set.Icc (-1/3 : ℝ) (-1/4)) : 0 < baseDist t :=
    lt_trans (by norm_num) (base_bounds ht).1
  have hp (t : ℝ) (ht : t ∈ Set.Icc (-1/3 : ℝ) (-1/4)) : 0 < poleDist e t :=
    lt_of_lt_of_le (by norm_num) (pole_lower ht.2)
  have hc : ContinuousOn (force e) (Set.Icc (-1/3 : ℝ) (-1/4)) := by
    intro t ht
    have ha : 1-t ≠ 0 := by linarith [ht.2]
    have hb := (hd t ht).ne'
    have hz := (hp t ht).ne'
    apply ContinuousAt.continuousWithinAt
    unfold force baseDist poleDist at *
    fun_prop (disch := first | positivity | assumption | apply pow_ne_zero; assumption | unfold baseDist poleDist at *; positivity)
  have hI : (-1/3 : ℝ) ≤ -1/4 := by norm_num
  have hL := (base_bounds (Set.left_mem_Icc.mpr hI)).1
  have hR := (base_bounds (Set.right_mem_Icc.mpr hI)).2
  have hbL : (7/8 : ℝ)^3 < (baseDist (-1/3))^3 := by gcongr
  have hbR : (baseDist (-1/4))^3 < (91/100 : ℝ)^3 := by gcongr; exact (hd _ (Set.right_mem_Icc.mpr hI)).le
  have hcR : (1/4 : ℝ)^3 ≤ (poleDist e (-1/4))^3 := by gcongr; exact pole_lower le_rfl
  apply intermediate_value_Icc' hI hc
  constructor
  · have h1 : (66/100 : ℝ) < (1/2) / (baseDist (-1/4))^3 := by
      apply (lt_div_iff₀ (pow_pos (hd _ (Set.right_mem_Icc.mpr hI)) 3)).2
      linarith
    have h2 : weight e / 2 / (poleDist e (-1/4))^3 < 1/100 := by
      apply (div_lt_iff₀ (pow_pos (hp _ (Set.right_mem_Icc.mpr hI)) 3)).2
      linarith [hw.2]
    unfold force
    norm_num at h1 h2 ⊢
    ring_nf at h1 h2 ⊢
    linarith
  · have h1 : (1/3 : ℝ) / (baseDist (-1/3))^3 < 9/16 := by
      apply (div_lt_iff₀ (pow_pos (hd _ (Set.left_mem_Icc.mpr hI)) 3)).2
      linarith
    have h2 : 0 ≤ weight e / (poleDist e (-1/3))^3 := div_nonneg hw.1 (pow_pos (hp _ (Set.left_mem_Icc.mpr hI)) 3).le
    unfold force
    norm_num at h1 h2 ⊢
    ring_nf at h1 h2 ⊢
    linarith

noncomputable def diagX (e t : ℝ) :=
  2 / (1-t)^3 + (4*(t+1/2)^2-3/2) / (baseDist t)^5 +
    (4*t^2-2*e^2)*weight e / (poleDist e t)^5

noncomputable def diagY (e t : ℝ) :=
  -1 / (1-t)^3 + (3-2*(t+1/2)^2) / (baseDist t)^5 - 2*weight e / (poleDist e t)^3

noncomputable def diagZ (e t : ℝ) :=
  -1 / (1-t)^3 - 2 / (baseDist t)^3 + (4*e^2-2*t^2)*weight e / (poleDist e t)^5

lemma diagonal_signs {e t : ℝ} (he : e ∈ Set.Ico 0 (1/100 : ℝ))
    (ht : t ∈ Set.Icc (-1/3 : ℝ) (-1/4)) :
    diagX e t < 0 ∧ 0 < diagY e t ∧ diagZ e t < 0 := by
  obtain ⟨hw, hw'⟩ := weight_bounds_closed he
  obtain ⟨hb, hb'⟩ := base_bounds ht
  have hz := pole_lower (e := e) ht.2
  have A : (5/4 : ℝ) ≤ 1-t := by linarith [ht.2]
  have A3 : (5/4 : ℝ)^3 ≤ (1-t)^3 := by gcongr
  have ha3 : 0 < (1-t)^3 := by linarith
  have B : 0 < baseDist t := by linarith
  have B5 : baseDist t ^5 < 1 := by simpa using (pow_lt_pow_left₀ (by linarith : baseDist t < 1) B.le (by decide : 5 ≠ 0))
  have Z : 0 < poleDist e t := by linarith
  have Z3 : (1/4 : ℝ)^3 ≤ (poleDist e t)^3 := by gcongr
  have Z5 : (1/4 : ℝ)^5 ≤ (poleDist e t)^5 := by gcongr
  have t2 : t^2 ≤ (1/3 : ℝ)^2 := by
    have : (-t)^2 ≤ (1/3 : ℝ)^2 := by gcongr <;> linarith [ht.1, ht.2]
    simpa using this
  have t2' : (1/4 : ℝ)^2 ≤ t^2 := by
    have : (1/4 : ℝ)^2 ≤ (-t)^2 := by gcongr <;> linarith [ht.2]
    simpa using this
  have u : 0 ≤ t+1/2 := by linarith [ht.1]
  have u2 : (t+1/2)^2 ≤ (1/4 : ℝ)^2 := by gcongr <;> linarith [ht.2]
  have e2 : e^2 ≤ (1/100 : ℝ)^2 := by gcongr <;> first | exact he.1 | exact he.2.le
  have hA : 2 / (1-t)^3 < 6/5 := (div_lt_iff₀ ha3).2 (by linarith)
  have hXb : (4*(t+1/2)^2-3/2) / (baseDist t)^5 < -5/4 :=
    (div_lt_iff₀ (pow_pos B _)).2 (by linarith)
  have hXc : (4*t^2-2*e^2)*weight e / (poleDist e t)^5 < 1/100 :=
    (div_lt_iff₀ (pow_pos Z _)).2 (by
      have : (4*t^2-2*e^2)*weight e ≤ 1*weight e :=
        mul_le_mul_of_nonneg_right (by nlinarith only [t2, sq_nonneg e]) hw
      linarith)
  have hYa : -1 / (1-t)^3 > -1 := (lt_div_iff₀ ha3).2 (by linarith)
  have hYb : 2 < (3-2*(t+1/2)^2) / (baseDist t)^5 :=
    (lt_div_iff₀ (pow_pos B _)).2 (by linarith)
  have hYc : 2*weight e / (poleDist e t)^3 < 1/100 :=
    (div_lt_iff₀ (pow_pos Z _)).2 (by linarith)
  have hZc : (4*e^2-2*t^2)*weight e / (poleDist e t)^5 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) hw) (pow_pos Z _).le
  exact ⟨by unfold diagX; linarith, by unfold diagY; linarith, by
    unfold diagZ
    have h1 : -1 / (1-t)^3 < 0 := div_neg_of_neg_of_pos (by norm_num) ha3
    have h2 : 0 < 2 / baseDist t ^ 3 := by positivity
    linarith only [h1, h2, hZc]⟩

/-! ### Evaluation of both derivatives on the negative x-axis -/

noncomputable def axis (t : ℝ) : E := !₂[t,0,0]

lemma distances {e t : ℝ} (ht : t ∈ Set.Icc (-1/3 : ℝ) (-1/4)) (j : Fin 5) :
    dist (axis t) (counterexamplePositions e j) =
    ![1-t, baseDist t, baseDist t, poleDist e t, poleDist e t] j := by
  have h : t - 1 < 0 := by linarith [ht.2]
  fin_cases j <;> norm_num [axis, counterexamplePositions, EuclideanSpace.dist_eq, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    Real.dist_eq, baseDist, poleDist, div_pow, Real.sq_sqrt, abs_of_neg h] <;>
    first | congr 1 <;> ring | linarith
  rw [show 1 - t * 2 + t ^ 2 = (1-t)^2 by ring, Real.sqrt_sq (by linarith)]

lemma axis_away {e t : ℝ} (ht : t ∈ Set.Icc (-1/3 : ℝ) (-1/4)) (j : Fin 5) :
    axis t ≠ counterexamplePositions e j := by
  apply dist_pos.mp
  rw [distances ht]
  have ha : 0 < 1-t := by linarith [ht.2]
  have hb : 0 < baseDist t := lt_trans (by norm_num) (base_bounds ht).1
  have hc : 0 < poleDist e t := lt_of_lt_of_le (by norm_num) (pole_lower ht.2)
  fin_cases j <;> assumption

lemma scalar_gradient {e t : ℝ} (ht : t ∈ Set.Icc (-1/3 : ℝ) (-1/4)) (v : E) :
    fderiv ℝ (potential (counterexampleCharges e) (counterexamplePositions e)) (axis t) v =
      force e t * v.ofLp 0 := by
  rw [potential_derivative _ _ _ (axis_away ht)]
  simp only [_root_.sum_apply, dCharge, _root_.smul_apply, smul_eq_mul, innerSL_apply_apply,
    distances ht]
  have ha : 1-t ≠ 0 := by linarith [ht.2]
  have h : 1 / (1-t)^2 = (1-t)/(1-t)^3 := by field_simp
  unfold force
  rw [h]
  simp [axis, counterexampleCharges, counterexamplePositions, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.head_cons, Matrix.tail_cons, dotProduct, Fin.sum_univ_succ, weight]
  <;> ring

lemma div_cube (c d : ℝ) (hd : d ≠ 0) : c/d^3 = (c*d^2)/d^5 := by
  field_simp

lemma scalar_hessian {e t : ℝ} (ht : t ∈ Set.Icc (-1/3 : ℝ) (-1/4)) (v w : E) :
    iteratedFDeriv ℝ 2 (potential (counterexampleCharges e) (counterexamplePositions e))
      (axis t) ![v,w] =
        diagX e t * v.ofLp 0 * w.ofLp 0 + diagY e t * v.ofLp 1 * w.ofLp 1 +
        diagZ e t * v.ofLp 2 * w.ofLp 2 := by
  rw [potential_hessian _ _ _ _ _ (axis_away ht)]
  simp only [ddCharge, distances ht]
  have ha : 1-t ≠ 0 := by linarith [ht.2]
  have hb : baseDist t ≠ 0 := ne_of_gt (lt_trans (by norm_num) (base_bounds ht).1)
  have hc : poleDist e t ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (pole_lower ht.2))
  have hb2 : baseDist t ^ 2 = (t+1/2)^2 + 3/4 := Real.sq_sqrt (by positivity)
  have hc2 : poleDist e t ^ 2 = t^2 + e^2 := Real.sq_sqrt (by positivity)
  simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty,
    Fin.succ_zero_eq_one, add_zero]
  simp [axis, counterexampleCharges, counterexamplePositions, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    dotProduct, Fin.sum_univ_three, diagX, diagY, diagZ, weight, div_cube _ _ ha, div_cube _ _ hb,
    div_cube _ _ hc, hb2, hc2, -one_div]
  ring_nf
  norm_num [Real.sq_sqrt]
  <;> ring

/-! ### The triangle symmetries preserve nondegenerate equilibria -/

lemma grad_zero_iff {V : EuclideanSpace ℝ (Fin 3) → ℝ} {x} :
    ∇ V x = 0 ↔ fderiv ℝ V x = 0 := by
  rw [← toDual_gradient]
  exact (toDual ℝ _).map_eq_zero_iff.symm

lemma map_equilibrium {n : ℕ} {q : Fin n → ℝ} {a : Fin n → EuclideanSpace ℝ (Fin 3)}
    (g : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3))
    (σ : Equiv.Perm (Fin n)) (ha : ∀ j, a (σ j) = g (a j)) (hq : ∀ j, q (σ j) = q j)
    {x} (hx : x ∈ nondegenerateEquilibria q a) : g x ∈ nondegenerateEquilibria q a := by
  let V := potential q a
  have hV : V ∘ g.toContinuousLinearEquiv = V := by
    funext y
    change (∑ j, q j / dist (g y) (a j)) = _
    rw [← Equiv.sum_comp σ (fun j => q j / dist (g y) (a j))]
    simp only [ha, hq, g.dist_map]
    rfl
  refine ⟨⟨?_, grad_zero_iff.mpr ?_⟩, ?_⟩
  · rintro ⟨j, hj⟩
    obtain ⟨k, rfl⟩ := σ.surjective j
    exact hx.1.1 ⟨k, g.injective ((ha k).symm.trans hj)⟩
  · have hd := g.toContinuousLinearEquiv.comp_right_fderiv (f := V) (x := x)
    rw [hV, show fderiv ℝ V x = 0 from grad_zero_iff.mp hx.1.2] at hd
    ext v
    obtain ⟨w, rfl⟩ := g.surjective v
    exact (congrArg (fun L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ => L w) hd).symm
  · intro v hv
    obtain ⟨u, rfl⟩ := g.surjective v
    obtain ⟨w, hw⟩ := hx.2 u (fun h => hv (by simp [h]))
    refine ⟨g w, ?_⟩
    have hd := g.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right V
      uniqueDiffOn_univ (Set.mem_univ (g x)) 2
    simp only [Set.preimage_univ, iteratedFDerivWithin_univ, hV] at hd
    rw [hd] at hw
    change iteratedFDeriv ℝ 2 V (g x) (fun i => g (![u,w] i)) ≠ 0 at hw
    have hvec : (fun i => g (![u,w] i)) = ![g u, g w] := by
      funext i
      fin_cases i <;> rfl
    exact hvec ▸ hw

noncomputable def edgeMirror (e : ℝ) (k : Fin 5) :=
  (Submodule.span ℝ {counterexamplePositions e k}).reflection

def edgeSwaps (k : Fin 5) := (Equiv.swap (0 : Fin 5) k).trans (Equiv.swap 3 4)

lemma edgeMirror_charges (e : ℝ) (k : Fin 5) (hk : k = 1 ∨ k = 2) (j : Fin 5) :
    counterexampleCharges e (edgeSwaps k j) = counterexampleCharges e j := by
  rcases hk with rfl | rfl <;> fin_cases j <;> rfl

lemma edgeMirror_positions (e : ℝ) {k l : Fin 5}
    (hkl : (k = 1 ∧ l = 2) ∨ (k = 2 ∧ l = 1)) (j : Fin 5) :
    counterexamplePositions e (edgeSwaps k j) = edgeMirror e l (counterexamplePositions e j) := by
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have swap1 (i : Fin 5) : edgeSwaps 1 i = ![1,0,2,4,3] i := by fin_cases i <;> rfl
  have swap2 (i : Fin 5) : edgeSwaps 2 i = ![2,1,0,4,3] i := by fin_cases i <;> rfl
  rw [edgeMirror, Submodule.reflection_singleton_apply]
  rcases hkl with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> fin_cases j <;>
    ext i <;> fin_cases i <;>
    norm_num [swap1, swap2, counterexamplePositions, EuclideanSpace.real_norm_sq_eq,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three, div_pow, h3] <;>
    ring_nf <;> norm_num [pow_succ, ← mul_assoc, h3] <;> nlinarith only [congrArg (fun x : ℝ => x * Real.sqrt 3) h3]

/-! ### Three distinct equilibria outside the open ball of radius 1/4 -/

lemma axis_equilibrium {e t : ℝ} (he : e ∈ Set.Ico 0 (1/100 : ℝ))
    (ht : t ∈ Set.Icc (-1/3 : ℝ) (-1/4)) (hf : force e t = 0) :
    axis t ∈ nondegenerateEquilibria (counterexampleCharges e) (counterexamplePositions e) := by
  refine ⟨⟨?_, grad_zero_iff.mpr ?_⟩, ?_⟩
  · rintro ⟨j,h⟩
    exact axis_away ht j h.symm
  · ext v
    rw [scalar_gradient ht, hf]
    simp
  · obtain ⟨hx, hy, hz⟩ := diagonal_signs he ht
    intro v hv
    by_contra! h
    apply hv
    have hh (w : E) := (scalar_hessian (e := e) ht v w).symm.trans (h w)
    have h0 : v.ofLp 0 = 0 := by
      simpa [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hx.ne, hy.ne', hz.ne] using hh (!₂[1,0,0])
    have h1 : v.ofLp 1 = 0 := by
      simpa [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hx.ne, hy.ne', hz.ne] using hh (!₂[0,1,0])
    have h2 : v.ofLp 2 = 0 := by
      simpa [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hx.ne, hy.ne', hz.ne] using hh (!₂[0,0,1])
    ext i
    fin_cases i <;> assumption

lemma axis_eq_vertex (e t : ℝ) : axis t = t • counterexamplePositions e 0 := by
  ext i
  fin_cases i <;> simp [axis, counterexamplePositions]

lemma three_points {e t : ℝ} (ht : t ∈ Set.Icc (-1/3 : ℝ) (-1/4))
    (hx : axis t ∈ nondegenerateEquilibria (counterexampleCharges e) (counterexamplePositions e)) :
    3 ≤ ((nondegenerateEquilibria (counterexampleCharges e) (counterexamplePositions e)) \
      Metric.ball 0 (1/4 : ℝ)).encard := by
  let p (i : Fin 5) := t • counterexamplePositions e i
  let S := nondegenerateEquilibria (counterexampleCharges e) (counterexamplePositions e) \
    Metric.ball 0 (1/4 : ℝ)
  have p0 : axis t = p 0 := axis_eq_vertex e t
  have far : axis t ∉ Metric.ball 0 (1/4 : ℝ) := by
    simp [Metric.mem_ball, dist_zero_right, axis, EuclideanSpace.norm_eq, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Real.sqrt_sq_eq_abs, abs_of_nonpos (by linarith [ht.2] : t ≤ 0)]
    <;> linarith [ht.2]
  have m0 : p 0 ∈ S := p0 ▸ And.intro hx far
  have mir {k l : Fin 5} (hkl : (k = 1 ∧ l = 2) ∨ (k = 2 ∧ l = 1)) :
      p k ∈ S := by
    let g := edgeMirror e l
    have hk : k = 1 ∨ k = 2 := hkl.imp And.left And.left
    have hpos := edgeMirror_positions e hkl
    have h0 : edgeSwaps k 0 = k := by rcases hk with rfl | rfl <;> rfl
    have hmap : g (axis t) = p k := by
      rw [p0]
      dsimp [p]
      rw [map_smul, ← hpos, h0]
    rw [← hmap]
    exact ⟨map_equilibrium g (edgeSwaps k) hpos (edgeMirror_charges e k hk) hx, by
      simpa only [Metric.mem_ball, dist_zero_right, g.norm_map] using far⟩
  have m1 : p 1 ∈ S := mir (Or.inl ⟨rfl,rfl⟩ : (1 = (1:Fin 5) ∧ 2 = (2:Fin 5)) ∨ _)
  have m2 : p 2 ∈ S := mir (Or.inr ⟨rfl,rfl⟩ : _ ∨ (2 = (2:Fin 5) ∧ 1 = (1:Fin 5)))
  obtain ⟨d01,d12,d02⟩ := counterexamplePositions_dist_vertices e
  have split {i j : Fin 5} (h : dist (counterexamplePositions e i) (counterexamplePositions e j) = Real.sqrt 3) : p i ≠ p j :=
    (smul_right_injective E (by linarith [ht.2] : t ≠ 0)).ne (dist_pos.mp (h.symm ▸ Real.sqrt_pos.2 (by norm_num)))
  have hcard : ({p 0, p 1, p 2} : Set E).encard = 3 :=
    Set.encard_eq_three.mpr ⟨_, _, _, split d01, split d02, split d12, rfl⟩
  rw [← hcard]
  apply Set.encard_mono
  exact Set.insert_subset m0 (Set.insert_subset m1 (Set.singleton_subset_iff.mpr m2))

end OMA.Edge

/-! ## A regular displacement of one charge yields a finite Morse configuration -/

namespace OMA.Morse

open Arxiv.«2607.27197» Filter InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace

abbrev E := EuclideanSpace ℝ (Fin 3)

noncomputable def coulomb (v : E) : E := (‖v‖ ^ 3)⁻¹ • v
noncomputable def undo (w : E) : E := (Real.sqrt ‖w‖ ^ 3)⁻¹ • w

lemma norm_coulomb (v : E) : ‖coulomb v‖ = (‖v‖⁻¹)^2 := by
  by_cases h : v = 0
  · simp [h, coulomb]
  rw [coulomb, norm_smul, Real.norm_of_nonneg (by positivity)]
  field_simp [norm_ne_zero_iff.mpr h]

lemma undo_coulomb (v : E) : undo (coulomb v) = v := by
  by_cases h : v = 0
  · simp [h, coulomb, undo]
  rw [undo, norm_coulomb, Real.sqrt_sq (by positivity), coulomb, smul_smul]
  simp [norm_ne_zero_iff.mpr h]

lemma coulomb_undo (v : E) : coulomb (undo v) = v := by
  by_cases h : v = 0
  · simp [h, coulomb, undo]
  have hs := Real.sqrt_pos.mpr (norm_pos_iff.mpr h)
  have hn : ‖undo v‖ = (Real.sqrt ‖v‖)⁻¹ := by
    rw [undo, norm_smul, Real.norm_of_nonneg (by positivity)]
    field_simp
    nlinarith [Real.sq_sqrt (norm_nonneg v)]
  rw [coulomb, hn, undo, smul_smul]
  simp [hs.ne']

lemma coulomb_smooth {v : E} (h : v ≠ 0) : ContDiffAt ℝ 1 coulomb v := by
  have hn : ContDiffAt ℝ 1 (fun z : E => ‖z‖) v := contDiffAt_id.norm ℝ h
  exact ((hn.pow 3).inv (pow_ne_zero 3 (norm_ne_zero_iff.mpr h))).smul contDiffAt_id

lemma undo_smooth {v : E} (h : v ≠ 0) : ContDiffAt ℝ 1 undo v := by
  have hn : ContDiffAt ℝ 1 (fun z : E => ‖z‖) v := contDiffAt_id.norm ℝ h
  have hp := norm_pos_iff.mpr h
  exact (((hn.sqrt hp.ne').pow 3).inv (pow_ne_zero 3 (Real.sqrt_pos.mpr hp).ne')).smul contDiffAt_id

noncomputable def force {n : ℕ} (q : Fin n → ℝ) (a : Fin n → E) (x : E) :=
  ∑ j, q j • coulomb (x - a j)

lemma force_smooth {n : ℕ} (q : Fin n → ℝ) (a : Fin n → E) {x : E}
    (hx : ∀ j, x ≠ a j) : ContDiffAt ℝ 1 (force q a) x := by
  unfold force
  apply ContDiffAt.sum
  intro j _
  have hs : ContDiffAt ℝ 1 (fun y : E => y - a j) x := contDiffAt_id.sub contDiffAt_const
  have hk := (coulomb_smooth (sub_ne_zero.mpr (hx j))).comp x hs
  exact (contDiffAt_const (c := q j)).smul hk

lemma deriv_force {n : ℕ} (q : Fin n → ℝ) (a : Fin n → E) {x : E}
    (hx : ∀ j, x ≠ a j) :
    fderiv ℝ (potential q a) x = (innerSL ℝ) (-force q a x) := by
  rw [OMA.Edge.potential_derivative _ _ _ hx, force, map_neg, map_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp [OMA.Edge.dCharge, coulomb, map_smul, smul_smul, dist_eq_norm, div_eq_mul_inv]

lemma mem_eq {n : ℕ} (q : Fin n → ℝ) (a : Fin n → E) (x : E) :
    x ∈ equilibria q a ↔ (∀ j, x ≠ a j) ∧ force q a x = 0 := by
  change (x ∉ Set.range a ∧ _) ↔ _
  have haway : x ∉ Set.range a ↔ ∀ j, x ≠ a j := by simp [eq_comm]
  rw [haway]
  apply and_congr_right
  intro hx
  rw [OMA.Center.grad_zero, deriv_force q a hx]
  change (toDual ℝ E) (-force q a x) = 0 ↔ _
  simp

lemma hessian_iff_inj {n : ℕ} (q : Fin n → ℝ) (a : Fin n → E) {x : E}
    (hx : ∀ j, x ≠ a j) :
    HasNondegenerateHessianAt (potential q a) x ↔ Function.Injective (fderiv ℝ (force q a) x) := by
  have hh : fderiv ℝ (potential q a) =ᶠ[𝓝 x] fun y => innerSL ℝ (-force q a y) := by
    filter_upwards [eventually_all.mpr (fun j => isOpen_compl_singleton.mem_nhds (hx j))] with y hy
    exact deriv_force q a hy
  have hd := (innerSL ℝ (E := E)).hasFDerivAt.comp x
    ((force_smooth q a hx).differentiableAt one_ne_zero).hasFDerivAt.neg
  rw [OMA.Center.hessian_iff, hh.fderiv_eq]
  change (fderiv ℝ (innerSL ℝ (E := E) ∘ (-force q a)) x).IsInvertible ↔ _
  rw [hd.fderiv]
  let L := fderiv ℝ (force q a) x
  constructor
  · rintro ⟨A, hA⟩ v w h
    apply A.injective
    change (A : E →L[ℝ] (E →L[ℝ] ℝ)) v = (A : E →L[ℝ] (E →L[ℝ] ℝ)) w
    rw [hA]
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, h]
  · intro h
    have hsur := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := L.toLinearMap) rfl).mp h
    let B := ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr h)
      (LinearMap.range_eq_top.mpr hsur)
    refine ⟨(B.trans (ContinuousLinearEquiv.neg ℝ)).trans (toDual ℝ E).toContinuousLinearEquiv, ?_⟩
    rfl

end OMA.Morse

namespace OMA.Morse
open Arxiv.«2607.27197» Filter
open scoped Topology

variable {n : ℕ} (q : Fin n → ℝ) (a : Fin n → E)

noncomputable def sourceMap (x : E) := x + undo (force q a x)

def domain : Set E := {x | (∀ i, x ≠ a i) ∧ force q a x ≠ 0}

lemma domain_nhds {x : E} (h : x ∈ domain q a) : domain q a ∈ 𝓝 x := by
  exact Filter.inter_mem (eventually_all.mpr fun i => isOpen_compl_singleton.mem_nhds (h.1 i))
    ((force_smooth q a h.1).continuousAt.tendsto (isOpen_compl_singleton.mem_nhds h.2))

lemma source_smooth {x : E} (hx : x ∈ domain q a) : ContDiffAt ℝ 1 (sourceMap q a) x :=
  contDiffAt_id.add ((undo_smooth hx.2).comp x (force_smooth q a hx.1))

lemma coulomb_neg (v : E) : coulomb (-v) = -coulomb v := by simp [coulomb]

lemma source_force (b x : E) :
    force (Fin.cons 1 q) (Fin.cons b a) x =
      coulomb (sourceMap q a x - x) - coulomb (b-x) := by
  have ho : coulomb (x - b) = -coulomb (b - x) := by rw [← neg_sub b x, coulomb_neg]
  simp only [force, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, one_smul, sourceMap,
    add_sub_cancel_left, coulomb_undo, ho]
  abel

lemma equilibrium_param (b x : E) :
    x ∈ equilibria (Fin.cons 1 q) (Fin.cons b a) ↔ x ∈ domain q a ∧ sourceMap q a x = b := by
  rw [mem_eq, source_force, sub_eq_zero, (Function.LeftInverse.injective undo_coulomb).eq_iff]
  rw [Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have h0 : undo (0 : E) = 0 := by simp [undo]
  constructor
  · rintro ⟨⟨hb, ha⟩, he⟩
    have hmap : sourceMap q a x = b := sub_left_injective he
    refine ⟨⟨ha, ?_⟩, hmap⟩
    intro hz
    simpa [sourceMap, hz, h0, hb] using hmap
  · rintro ⟨h, rfl⟩
    refine ⟨⟨?_, h.1⟩, rfl⟩
    intro he
    have hu : undo (force q a x) = 0 := by
      have := congrArg (fun y => y - x) he
      simpa [sourceMap] using this.symm
    apply h.2
    rw [← coulomb_undo (force q a x), hu]
    simp [coulomb]

lemma kernel_injective {v : E} (hv : v ≠ 0) : Function.Injective (fderiv ℝ coulomb v) := by
  have hw : coulomb v ≠ 0 := by
    intro h
    have := undo_coulomb v
    exact hv (by simpa [h, undo] using this.symm)
  have hd := ((undo_smooth hw).differentiableAt one_ne_zero).hasFDerivAt.comp v
    ((coulomb_smooth hv).differentiableAt one_ne_zero).hasFDerivAt
  have he : undo ∘ coulomb = id := funext undo_coulomb
  rw [he] at hd
  have hid := hd.unique (hasFDerivAt_id v)
  intro x y h
  have hvv := congrArg (fun L : E →L[ℝ] E => L x) hid
  have hww := congrArg (fun L : E →L[ℝ] E => L y) hid
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, h] using hvv.symm.trans
    (show ((fderiv ℝ undo (coulomb v)).comp (fderiv ℝ coulomb v)) x = y by
      simpa only [ContinuousLinearMap.comp_apply, h, ContinuousLinearMap.id_apply] using hww)

lemma regular_iff {b x : E} (he : x ∈ equilibria (Fin.cons 1 q) (Fin.cons b a)) :
    HasNondegenerateHessianAt (potential (Fin.cons 1 q) (Fin.cons b a)) x ↔
      Function.Injective (fderiv ℝ (sourceMap q a) x) := by
  obtain ⟨hdom, hm⟩ := (equilibrium_param q a b x).mp he
  obtain ⟨ha, _⟩ := (mem_eq _ _ _).mp he
  have hbx : b-x ≠ 0 := sub_ne_zero.mpr (ha 0).symm
  let K := fderiv ℝ coulomb (b-x)
  let T := fderiv ℝ (sourceMap q a) x
  have hC : HasFDerivAt coulomb K (b-x) := ((coulomb_smooth hbx).differentiableAt one_ne_zero).hasFDerivAt
  have hT : HasFDerivAt (sourceMap q a) T x := ((source_smooth q a hdom).differentiableAt one_ne_zero).hasFDerivAt
  have hC' : HasFDerivAt coulomb K (sourceMap q a x - x) := hm ▸ hC
  have h1 := hC'.comp (f := sourceMap q a - id) x (hT.sub (hasFDerivAt_id x))
  have h2 := hC.comp (f := (fun _ : E => b) - id) x ((hasFDerivAt_const b x).sub (hasFDerivAt_id x))
  have hh : HasFDerivAt (force (Fin.cons 1 q) (Fin.cons b a)) (K.comp T) x := by
    convert! h1.sub h2 using 1
    · funext y
      exact source_force q a b y
    · ext v : 1
      simp
  rw [hessian_iff_inj _ _ ha, hh.fderiv]
  exact ⟨fun h u v huv => h (congrArg K huv), (kernel_injective hbx).comp⟩

end OMA.Morse

namespace OMA.Morse
open Arxiv.«2607.27197» Filter InnerProductSpace Metric
open scoped Topology RealInnerProductSpace

variable {n : ℕ}

lemma equilibria_bounded (q : Fin (n+1) → ℝ) (a : Fin (n+1) → E) (hq : ∀ i, 0 < q i) :
    Bornology.IsBounded (equilibria q a) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨∑ i, ‖a i‖, fun x hx => ?_⟩
  obtain ⟨ha, hf⟩ := (mem_eq q a x).mp hx
  by_contra! h
  have hb (i : Fin (n+1)) : ‖a i‖ < ‖x‖ := lt_of_le_of_lt
    (Finset.single_le_sum (f := fun j => ‖a j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)) h
  have hp : 0 < ‖x‖ := lt_of_le_of_lt (norm_nonneg _) (hb 0)
  have hi (j : Fin (n+1)) : 0 < ⟪q j • coulomb (x-a j), x⟫_ℝ := by
    rw [coulomb, real_inner_smul_left, real_inner_smul_left, inner_sub_left, real_inner_self_eq_norm_sq]
    have ht := real_inner_le_norm (a j) x
    have hpos := norm_pos_iff.mpr (sub_ne_zero.mpr (ha j))
    exact mul_pos (hq j) (mul_pos (by positivity)
      (by nlinarith [mul_lt_mul_of_pos_right (hb j) hp]))
  have hs := Finset.sum_pos (s := Finset.univ) (fun j _ => hi j) Finset.univ_nonempty
  rw [← sum_inner] at hs
  change 0 < ⟪force q a x,x⟫_ℝ at hs
  simp [hf] at hs

lemma no_equilibria_near_pole (q : Fin (n+1) → ℝ) (a : Fin (n+1) → E) (ha : Function.Injective a)
    (hq : ∀ i, 0 < q i) (i : Fin (n+1)) : ∀ᶠ x in 𝓝 (a i), x ∉ equilibria q a := by
  classical
  let rest (x : E) := ∑ j ∈ Finset.univ.erase i, q j • coulomb (x - a j)
  have hc : ContinuousAt rest (a i) := by
    suffices hh : ContDiffAt ℝ 1 rest (a i) from hh.continuousAt
    unfold rest
    apply ContDiffAt.sum
    intro j hj
    have hu : ContDiffAt ℝ 1 (fun x : E => x - a j) (a i) := contDiffAt_id.sub contDiffAt_const
    have hk := (coulomb_smooth (sub_ne_zero.mpr (ha.ne (Finset.ne_of_mem_erase hj).symm))).comp
      (f := fun x : E => x - a j) (a i) hu
    exact (contDiffAt_const (c := q j)).smul hk
  have hh : ContinuousAt (fun x : E => ‖rest x‖ * ‖x-a i‖^2) (a i) :=
    hc.norm.mul ((continuousAt_id.sub continuousAt_const).norm.pow 2)
  have hlt : ‖rest (a i)‖ * ‖a i-a i‖^2 < q i := by simpa using hq i
  filter_upwards [hh.eventually_lt continuousAt_const hlt] with x hx
  intro he
  obtain ⟨haw,hf⟩ := (mem_eq q a x).mp he
  have hz : q i • coulomb (x-a i) + rest x = 0 := by
    rw [← hf]
    exact Finset.add_sum_erase _ (fun j => q j • coulomb (x - a j)) (Finset.mem_univ i)
  have hn := congrArg norm (eq_neg_of_add_eq_zero_left hz)
  rw [norm_smul, Real.norm_of_nonneg (hq i).le, norm_coulomb, norm_neg] at hn
  have hdist : ‖x-a i‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr (haw i))
  field_simp [hdist] at hn
  linarith

lemma equilibria_closed (q : Fin (n+1) → ℝ) (a : Fin (n+1) → E) (ha : Function.Injective a)
    (hq : ∀ i, 0 < q i) : IsClosed (equilibria q a) := by
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  by_cases hp : x ∈ Set.range a
  · obtain ⟨i,rfl⟩ := hp
    exact no_equilibria_near_pole q a ha hq i
  · have haw : ∀ i, x ≠ a i := fun i he => hp ⟨i,he.symm⟩
    have hn : force q a x ≠ 0 := fun he => hx ((mem_eq q a _).mpr ⟨haw,he⟩)
    filter_upwards [(force_smooth q a haw).continuousAt.tendsto
      (isOpen_compl_singleton.mem_nhds hn)] with y hy
    exact fun he => hy ((mem_eq q a _).mp he).2

noncomputable def equivOfInj (L : E →L[ℝ] E) (h : Function.Injective L) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr h)
    (LinearMap.range_eq_top.mpr ((LinearMap.injective_iff_surjective (f := L.toLinearMap)).mp h))

lemma finite_equilibria (q : Fin (n+1) → ℝ) (a : Fin (n+1) → E) (ha : Function.Injective a)
    (hq : ∀ i, 0 < q i) (hn : ∀ x ∈ equilibria q a, HasNondegenerateHessianAt (potential q a) x) :
    (equilibria q a).Finite := by
  apply (isCompact_iff_isClosed_bounded.mpr ⟨equilibria_closed q a ha hq, equilibria_bounded q a hq⟩).finite
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro x hx
  obtain ⟨ha',h0⟩ := (mem_eq q a x).mp hx
  let L := equivOfInj _ ((hessian_iff_inj q a ha').mp (hn x hx))
  have hd : HasStrictFDerivAt (force q a) (L : E →L[ℝ] E) x :=
    (force_smooth q a ha').hasStrictFDerivAt one_ne_zero
  let e := hd.toOpenPartialHomeomorph (force q a)
  have hs : x ∈ e.source := hd.mem_toOpenPartialHomeomorph_source
  refine ⟨e.source, e.open_source, Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hs,hx⟩, ?_⟩⟩
  intro y hy
  exact e.injOn hy.1 hs (((mem_eq q a y).mp hy.2).2.trans h0.symm)

end OMA.Morse

namespace OMA.Morse
open Arxiv.«2607.27197» Filter MeasureTheory Set
open scoped Topology

variable {n : ℕ} (q : Fin n → ℝ) (a : Fin n → E)

lemma persistent_point {b x : E} (hx : x ∈ nondegenerateEquilibria (Fin.cons 1 q) (Fin.cons b a)) :
    ∃ g : E → E, Tendsto g (𝓝 b) (𝓝 x) ∧
      ∀ᶠ c in 𝓝 b, g c ∈ equilibria (Fin.cons 1 q) (Fin.cons c a) := by
  obtain ⟨hd, hm⟩ := (equilibrium_param q a b x).mp hx.1
  let L := equivOfInj _ ((regular_iff q a hx.1).mp hx.2)
  have h : HasStrictFDerivAt (sourceMap q a) (L : E →L[ℝ] E) x :=
    (source_smooth q a hd).hasStrictFDerivAt one_ne_zero
  let g := h.localInverse (sourceMap q a) L x
  have hg : Tendsto g (𝓝 b) (𝓝 x) := hm ▸ h.localInverse_tendsto
  have hr : ∀ᶠ c in 𝓝 b, sourceMap q a (g c) = c := hm ▸ h.eventually_right_inverse
  refine ⟨g,hg,?_⟩
  filter_upwards [hg (domain_nhds q a hd), hr] with c hc he
  exact (equilibrium_param q a c _).mpr ⟨hc,he⟩

lemma persistent_count {k : ℕ} {b : E} (h : (k : ℕ∞) ≤ (nondegenerateEquilibria (Fin.cons 1 q) (Fin.cons b a)).encard) :
    ∀ᶠ c in 𝓝 b, (k : ℕ∞) ≤ (equilibria (Fin.cons 1 q) (Fin.cons c a)).encard := by
  classical
  obtain ⟨s, hs, hcard⟩ := Set.exists_subset_encard_eq h
  have hf := Set.finite_of_encard_eq_coe (k := k) hcard
  letI := hf.fintype
  choose g hg hm using fun i : s => persistent_point q a (hs i.2)
  have hinj : ∀ᶠ c in 𝓝 b, Function.Injective (fun i : s => g i c) := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases hij : i = j
    · exact Eventually.of_forall fun _ _ => hij
    · have hn : (i.val,j.val) ∈ (Set.diagonal E)ᶜ := fun he => hij (Subtype.ext he)
      filter_upwards [(hg i).prodMk_nhds (hg j) (isClosed_diagonal.isOpen_compl.mem_nhds hn)] with c hc
      exact fun he => (hc he).elim
  filter_upwards [hinj, eventually_all.mpr hm] with c hc hpoints
  have hsub : Set.range (fun i : s => g i c) ⊆ equilibria (Fin.cons 1 q) (Fin.cons c a) :=
    Set.range_subset_iff.mpr hpoints
  calc
    (k : ℕ∞) = s.encard := hcard.symm
    _ ≤ (Set.range (fun i : s => g i c)).encard := hc.encard_range
    _ ≤ _ := Set.encard_mono hsub

/-- Critical values of the source-position map have volume zero. -/
lemma regular_near {b : E} {U : Set E} (hU : U ∈ 𝓝 b) :
    ∃ c ∈ U, ∀ x ∈ equilibria (Fin.cons 1 q) (Fin.cons c a),
      HasNondegenerateHessianAt (potential (Fin.cons 1 q) (Fin.cons c a)) x := by
  let T := sourceMap q a
  let bad := {x ∈ domain q a | ¬ Function.Injective (fderiv ℝ T x)}
  have null : volume (T '' bad) = 0 := by
    apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun x => fderiv ℝ T x)
    · exact fun x hx => ((source_smooth q a hx.1).differentiableAt one_ne_zero).hasFDerivAt.hasFDerivWithinAt
    · intro x hx
      exact LinearMap.det_eq_zero_iff_ker_ne_bot.mpr (fun hk => hx.2 (LinearMap.ker_eq_bot.mp hk))
  have hsub : ¬ U ⊆ T '' bad := by
    intro h
    exact (Measure.measure_pos_of_mem_nhds volume hU).not_ge (null ▸ measure_mono h)
  obtain ⟨c,hc,hreg⟩ := Set.not_subset.mp hsub
  refine ⟨c,hc,fun x hx => (regular_iff q a hx).mpr ?_⟩
  by_contra hn
  obtain ⟨hd,he⟩ := (equilibrium_param q a c x).mp hx
  exact hreg ⟨x,⟨hd,hn⟩,he⟩

lemma perturb {k : ℕ} {b : E} (ha : Function.Injective (Fin.cons b a)) (hq : ∀ i, 0 < q i)
    (h24 : (k : ℕ∞) ≤ (nondegenerateEquilibria (Fin.cons 1 q) (Fin.cons b a)).encard) :
    ∃ c : E, Function.Injective (Fin.cons c a) ∧
      (∀ x ∈ equilibria (Fin.cons 1 q) (Fin.cons c a), HasNondegenerateHessianAt (potential (Fin.cons 1 q) (Fin.cons c a)) x) ∧
      (equilibria (Fin.cons 1 q) (Fin.cons c a)).Finite ∧ (k : ℕ∞) ≤ (equilibria (Fin.cons 1 q) (Fin.cons c a)).encard := by
  obtain ⟨hb, htail⟩ := Fin.cons_injective_iff.mp ha
  have hn : ∀ᶠ c in 𝓝 b, c ∉ Set.range a := (Set.finite_range a).isClosed.isOpen_compl.mem_nhds hb
  have hu := hn.and (persistent_count q a h24)
  obtain ⟨c, ⟨hc, hcount⟩, hreg⟩ := regular_near q a hu
  have hinj := Fin.cons_injective_of_injective hc htail
  have hp : ∀ i : Fin (n+1), 0 < (Fin.cons (1 : ℝ) q : Fin (n+1) → ℝ) i := by
    rw [Fin.forall_fin_succ]
    exact ⟨by norm_num, hq⟩
  exact ⟨c,hinj,hreg,finite_equilibria _ _ hinj hp hreg,hcount⟩

end OMA.Morse

/-! ## The axial pair preserves the cubic term of the potential -/

namespace OMA.Iter
open OMA.Center Arxiv.«2607.27197» Filter
open scoped Topology

noncomputable def quad (x : E) := x.ofLp 0 ^ 2 + x.ofLp 1 ^ 2 - 2 * x.ofLp 2 ^ 2
noncomputable def cubic (x : E) := 15 / 8 * (x.ofLp 0 ^ 3 - 3*x.ofLp 0*x.ofLp 1^2)
noncomputable def pole (d : ℝ) : E := !₂[0,0,d]
noncomputable def pairTail (t : ℝ) (x : E) := 2*c4 (x.ofLp 2) (normSq x) +
  t * (rem5 t (x.ofLp 2) (normSq x) + rem5 t (-x.ofLp 2) (normSq x))
noncomputable def pairValue (t : ℝ) (x : E) :=
  1 / Real.sqrt (radicand t (x.ofLp 2) (normSq x)) +
  1 / Real.sqrt (radicand t (-x.ofLp 2) (normSq x))

lemma pair_expansion {t : ℝ} {x : E} (h : 0 < radicand t (x.ofLp 2) (normSq x))
    (h' : 0 < radicand t (-x.ofLp 2) (normSq x)) :
    pairValue t x = 2 - t^2*quad x + t^4*pairTail t x := by
  rw [pairValue, expand_inv h, expand_inv h']
  unfold quad pairTail c2 c3 c4 normSq
  ring

lemma pair_expansion_near (x : E) : ∀ᶠ p : ℝ × E in 𝓝 (0,x),
    pairValue p.1 p.2 = 2 - p.1^2*quad p.2 + p.1^4*pairTail p.1 p.2 := by
  have H (f : E → ℝ) (hf : Continuous f) : ∀ᶠ p : ℝ × E in 𝓝 (0,x),
      0 < radicand p.1 (f p.2) (normSq p.2) := by
    have hc : Continuous (fun p : ℝ × E => radicand p.1 (f p.2) (normSq p.2)) := by
      unfold radicand normSq; fun_prop
    exact continuousAt_const.eventually_lt hc.continuousAt (by simp [radicand])
  filter_upwards [H (fun y => y.ofLp 2) (by fun_prop), H (fun y => -y.ofLp 2) (by fun_prop)] with p ha hb
  exact pair_expansion ha hb

lemma tail_smooth (x : E) : ContDiffAt ℝ ⊤ (Function.uncurry pairTail) (0,x) := by
  have h (i : Fin 3) : ContDiffAt ℝ ⊤ (fun p : ℝ × E => p.2.ofLp i) (0,x) :=
    (proj i).contDiff.contDiffAt.comp _ contDiffAt_snd
  have hb : ContDiffAt ℝ ⊤ (fun p : ℝ × E => normSq p.2) (0,x) := by unfold normSq; fun_prop
  have hr : ContDiffAt ℝ ⊤ (fun p : ℝ × E => rem5 p.1 (p.2.ofLp 2) (normSq p.2)) (0,x) := by
    apply rem5_smooth <;> first | fun_prop | rfl
  have hl : ContDiffAt ℝ ⊤ (fun p : ℝ × E => rem5 p.1 (-p.2.ofLp 2) (normSq p.2)) (0,x) := by
    apply rem5_smooth <;> first | fun_prop | rfl
  unfold Function.uncurry pairTail c4
  fun_prop

lemma pair_kernel (s d : ℝ) (hd : 0 < d) (x : E) :
    1 / dist (s • x) (pole d) + 1 / dist (s • x) (pole (-d)) = pairValue (s/d) x / d := by
  have eqn (a b : ℝ) : Real.sqrt (d^2 * radicand (s/d) a b) = d * Real.sqrt (radicand (s/d) a b) := by
    rw [Real.sqrt_mul (sq_nonneg d), Real.sqrt_sq hd.le]
  have eqp : dist (s • x) (pole d) = d * Real.sqrt (radicand (s/d) (x.ofLp 2) (normSq x)) := by
    rw [← eqn]
    simp [pole, EuclideanSpace.dist_eq, Fin.sum_univ_three, Real.dist_eq, normSq, radicand]
    congr 1 <;> field_simp <;> ring
  have eqm : dist (s • x) (pole (-d)) = d * Real.sqrt (radicand (s/d) (-x.ofLp 2) (normSq x)) := by
    rw [← eqn]
    simp [pole, EuclideanSpace.dist_eq, Fin.sum_univ_three, Real.dist_eq, normSq, radicand]
    congr 1 <;> field_simp <;> ring
  rw [eqp,eqm,pairValue]; simp [div_eq_mul_inv, mul_add, add_mul, mul_comm]

/-- The first two nonconstant homogeneous terms, with a smooth remainder at every rescaled point. -/
def Jet (V : E → ℝ) (A : ℝ) : Prop := ∃ B : ℝ, ∃ R : ℝ → E → ℝ,
  (∀ x, ContDiffAt ℝ ⊤ (Function.uncurry R) (0,x)) ∧ ∀ x : E, ∀ᶠ p : ℝ × E in 𝓝 (0,x),
    V (p.1 • p.2) = B + A*p.1^2*quad p.2 + p.1^3*cubic p.2 + p.1^4*R p.1 p.2

noncomputable def weight (A G e : ℝ) := (A-G*e^2)*e^3
noncomputable def added (V : E → ℝ) (A G e : ℝ) (y : E) := V y + weight A G e *
  (1 / dist y (pole e) + 1 / dist y (pole (-e)))

lemma jet_added {V : E → ℝ} {A : ℝ} (h : Jet V A) (G e : ℝ) (he : 0 < e) :
    Jet (added V A G e) (G*e^2) := by
  obtain ⟨B,R,hR,hj⟩ := h
  refine ⟨B + 2*(A-G*e^2)*e^2, fun t x => R t x + ((A-G*e^2)/e^2)*pairTail (t/e) x, ?_, ?_⟩
  · intro x
    have hs : ContDiffAt ℝ ⊤ (fun p : ℝ × E => (p.1/e,p.2)) (0,x) := by fun_prop
    have hbase : ContDiffAt ℝ ⊤ (Function.uncurry pairTail) ((0 : ℝ)/e,x) := by simpa using tail_smooth x
    have hh := ContDiffAt.comp (f := fun p : ℝ × E => (p.1/e,p.2)) (0,x) hbase hs
    exact (hR x).add (contDiffAt_const.mul hh)
  · intro x
    have ht : Tendsto (fun p : ℝ × E => (p.1/e,p.2)) (𝓝 (0,x)) (𝓝 (0,x)) := by
      simpa using (show Continuous (fun p : ℝ × E => (p.1/e,p.2)) by fun_prop).continuousAt.tendsto (x := (0,x))
    filter_upwards [hj x, ht (pair_expansion_near x)] with p hp hpair
    rw [added, pair_kernel _ _ he, hp, hpair]
    unfold weight; field_simp; ring

end OMA.Iter

namespace OMA.Iter
open OMA.Center Arxiv.«2607.27197» Filter
open scoped Topology Gradient

noncomputable def scaled (A G L : ℝ) (R : ℝ → E → ℝ) (e : ℝ) (x : E) :=
  phiZero x + e^2 * L * (R (L*e^2) x - 2*G*c4 (x.ofLp 2) (normSq x)) +
    e*(A-G*e^2)*L^2*(rem5 (L*e) (x.ofLp 2) (normSq x) + rem5 (L*e) (-x.ofLp 2) (normSq x))

lemma scaled_zero (A G L : ℝ) (R : ℝ → E → ℝ) : scaled A G L R 0 = phiZero := by
  funext x; simp [scaled]

lemma scaled_smooth (A G L : ℝ) (R : ℝ → E → ℝ) (x : E)
    (hR : ContDiffAt ℝ ⊤ (Function.uncurry R) (0,x)) :
    ContDiffAt ℝ ⊤ (Function.uncurry (scaled A G L R)) (0,x) := by
  have h (i : Fin 3) : ContDiffAt ℝ ⊤ (fun p : ℝ × E => p.2.ofLp i) (0,x) :=
    (proj i).contDiff.contDiffAt.comp _ contDiffAt_snd
  have hb : ContDiffAt ℝ ⊤ (fun p : ℝ × E => normSq p.2) (0,x) := by unfold normSq; fun_prop
  have hr : ContDiffAt ℝ ⊤ (fun p : ℝ × E => rem5 (L*p.1) (p.2.ofLp 2) (normSq p.2)) (0,x) := by
    apply rem5_smooth <;> first | fun_prop | simp
  have hl : ContDiffAt ℝ ⊤ (fun p : ℝ × E => rem5 (L*p.1) (-p.2.ofLp 2) (normSq p.2)) (0,x) := by
    apply rem5_smooth <;> first | fun_prop | simp
  have hbase : ContDiffAt ℝ ⊤ (Function.uncurry R) (L*(0:ℝ)^2,x) := by simpa using hR
  have harg : ContDiffAt ℝ ⊤ (fun p : ℝ × E => (L*p.1^2,p.2)) (0,x) := by fun_prop
  have hcomp : ContDiffAt ℝ ⊤ (fun p : ℝ × E => R (L*p.1^2) p.2) (0,x) := ContDiffAt.comp (f := fun p : ℝ × E => (L*p.1^2,p.2)) (0,x) hbase harg
  unfold Function.uncurry scaled phiZero c4
  dsimp only
  fun_prop

lemma phi_split (x : E) : phiZero x = 5/32 * quad x + cubic x + 3/2*c4 (x.ofLp 2) (normSq x) := by
  unfold phiZero quad cubic c4 normSq; dsimp only; ring

lemma rescale_near (V : E → ℝ) (A G L B : ℝ) (R : ℝ → E → ℝ) (x : E)
    (hL : A*L = 3/4) (hG : G = 5/32*L)
    (hj : ∀ᶠ p : ℝ × E in 𝓝 (0,x), V (p.1 • p.2) = B + A*p.1^2*quad p.2 +
      p.1^3*cubic p.2 + p.1^4*R p.1 p.2) :
    ∀ᶠ p : ℝ × E in 𝓝 (0,x), 0 < p.1 → added V A G p.1 ((L*p.1^2) • p.2) =
      B + 2*(A-G*p.1^2)*p.1^2 + (p.1^6*L^3)*scaled A G L R p.1 p.2 := by
  have ht (f : ℝ → ℝ) (hc : Continuous f) (hf : f 0 = 0) :
      Tendsto (fun p : ℝ × E => (f p.1,p.2)) (𝓝 (0,x)) (𝓝 (0,x)) := by
    simpa [hf] using (show Continuous (fun p : ℝ × E => (f p.1,p.2)) by fun_prop).continuousAt.tendsto (x := (0,x))
  filter_upwards [ht (fun e => L*e^2) (by fun_prop) (by simp) hj,
    ht (fun e => L*e) (by fun_prop) (by simp) (pair_expansion_near x)] with p hV hpair
  rcases p with ⟨e,y⟩; dsimp only at *; intro he
  rw [added,pair_kernel _ _ he, show L*e^2/e = L*e by field_simp, hpair, hV,
    scaled, phi_split, pairTail, weight]
  field_simp
  linear_combination (norm := ring_nf) (128*e^6*L^3*c4 (y.ofLp 2) (normSq y))*hL + (64*e^6*L^2*quad y)*hG

end OMA.Iter

namespace OMA.Iter
open OMA.Center Arxiv.«2607.27197» Filter
open scoped Topology Gradient

noncomputable def charges {n : ℕ} (q : Fin n → ℝ) (A G e : ℝ) : Fin (n+2) → ℝ :=
  Fin.snoc (Fin.snoc q (weight A G e)) (weight A G e)
noncomputable def places {n : ℕ} (a : Fin n → E) (e : ℝ) : Fin (n+2) → E :=
  Fin.snoc (Fin.snoc a (pole e)) (pole (-e))

lemma potential_add {n : ℕ} (q : Fin n → ℝ) (a : Fin n → E) (A G e : ℝ) :
    potential (charges q A G e) (places a e) = added (potential q a) A G e := by
  funext x
  simp [potential, charges, places, added, Fin.sum_univ_castSucc, -one_div, div_eq_mul_inv]
  ring

lemma pole_cont : Continuous pole := by unfold pole; fun_prop
lemma pole_zero : pole 0 = 0 := by ext i; fin_cases i <;> rfl
lemma pole_inj : Function.Injective pole := fun _ _ h => congrArg (fun y : E => y.ofLp 2) h

lemma away_center {n : ℕ} {a : Fin n → E} (ha : 0 ∉ Set.range a) (L : ℝ) (x : E) :
    ∀ᶠ p : ℝ × E in 𝓝 (0,x), 0 < p.1 → (L*p.1^2) • p.2 ∉ Set.range (places a p.1) := by
  have ht : Tendsto (fun p : ℝ × E => (L*p.1^2) • p.2) (𝓝 (0,x)) (𝓝 0) := by
    simpa using (show Continuous (fun p : ℝ × E => (L*p.1^2) • p.2) by fun_prop).continuousAt.tendsto (x := (0,x))
  have hc : Continuous (fun p : ℝ × E => |L*p.1*p.2.ofLp 2|) := by fun_prop
  filter_upwards [ht ((Set.finite_range a).isClosed.isOpen_compl.mem_nhds ha),
    hc.continuousAt.eventually_lt continuousAt_const (show |L*(0:ℝ)*x.ofLp 2| < 1 by simp)] with p hp hz
  rcases p with ⟨e,y⟩; dsimp only at *; intro he
  rw [places,Fin.range_snoc,Fin.range_snoc]
  simp only [Set.mem_insert_iff, not_or]
  refine ⟨?_,?_,hp⟩ <;> intro hh <;> have hh' := congrArg (fun v : E => v.ofLp 2) hh
  · change (L*e^2)*y.ofLp 2 = -e at hh'
    rw [abs_lt] at hz
    nlinarith only [mul_pos he (show 0 < 1+L*e*y.ofLp 2 by linarith [hz.1]),hh']
  · change (L*e^2)*y.ofLp 2 = e at hh'
    rw [abs_lt] at hz
    nlinarith only [mul_pos he (show 0 < 1-L*e*y.ofLp 2 by linarith [hz.2]),hh']

lemma places_good {n : ℕ} {a : Fin n → E} (ha : Function.Injective a) (h0 : 0 ∉ Set.range a) :
    ∀ᶠ e : ℝ in 𝓝 0, 0 < e → Function.Injective (places a e) ∧ 0 ∉ Set.range (places a e) := by
  have hN := (Set.finite_range a).isClosed.isOpen_compl.mem_nhds h0
  have hp : Tendsto pole (𝓝 0) (𝓝 0) := pole_zero ▸ pole_cont.continuousAt.tendsto
  have hm : Tendsto (fun e : ℝ => pole (-e)) (𝓝 0) (𝓝 0) := hp.comp (by simpa using (continuous_neg.continuousAt (x := (0:ℝ))).tendsto)
  filter_upwards [hp hN, hm hN] with e he hm'; intro h
  have hne : pole (-e) ≠ pole e := pole_inj.ne (by linarith)
  have hpe : 0 ≠ pole e := pole_zero ▸ pole_inj.ne h.ne
  have hme : 0 ≠ pole (-e) := pole_zero ▸ pole_inj.ne (by linarith)
  refine ⟨Fin.snoc_injective_iff.mpr ⟨Fin.snoc_injective_iff.mpr ⟨ha,he⟩, ?_⟩,?_⟩
  · simpa [Fin.range_snoc,hne] using hm'
  · simp [places,Fin.range_snoc,hme,hpe,h0]

lemma positive_weights {n : ℕ} {q : Fin n → ℝ} {A : ℝ} (hq : ∀ i, 0 < q i) (hA : 0 < A) (G : ℝ) :
    ∀ᶠ e : ℝ in 𝓝 0, 0 < e → ∀ i, 0 < charges q A G e i := by
  have hc : Continuous (fun e : ℝ => A-G*e^2) := by fun_prop
  filter_upwards [continuousAt_const.eventually_lt hc.continuousAt (show 0 < A-G*(0:ℝ)^2 by simpa)] with e he h
  have hw := mul_pos he (pow_pos h 3)
  intro i; refine Fin.lastCases ?_ (fun j => Fin.lastCases ?_ (fun k => ?_) j) i
  · simpa [charges,weight] using hw
  · simpa [charges,weight] using hw
  · simpa [charges] using hq k

lemma eventually_apart {f g : ℝ → E} {x y : E} (hf : Tendsto f (𝓝 0) (𝓝 x))
    (hg : Tendsto g (𝓝 0) (𝓝 y)) (hne : x ≠ y) : ∀ᶠ e in 𝓝 0, f e ≠ g e :=
  (hf.prodMk_nhds hg) (isClosed_diagonal.isOpen_compl.mem_nhds (show (x,y) ∉ Set.diagonal E from hne))

lemma exterior_branch {n : ℕ} {q : Fin n → ℝ} {a : Fin n → E} {x : E} (hx : x ∈ nondegenerateEquilibria q a)
    (h0 : x ≠ 0) (A G : ℝ) : ∃ g : ℝ → E, Tendsto g (𝓝 0) (𝓝 x) ∧ ∀ᶠ e in 𝓝 0,
      g e ∈ nondegenerateEquilibria (charges q A G e) (places a e) := by
  have ha : ∀ i, x ≠ a i := fun i h => hx.1.1 ⟨i,h.symm⟩
  have hv : ContDiffAt ℝ ⊤ (fun p : ℝ × E => potential q a p.2) (0,x) := by
    unfold potential; apply ContDiffAt.sum; intro i _
    exact contDiffAt_const.div ((contDiffAt_snd.sub contDiffAt_const).norm ℝ (sub_ne_zero.mpr (ha i)))
      (dist_ne_zero.mpr (ha i))
  have hpol : pole = fun d : ℝ => d • pole 1 := by funext d; ext i; fin_cases i <;> simp [pole]
  have hs : ContDiff ℝ ⊤ pole := by rw [hpol]; fun_prop
  have hp : ContDiffAt ℝ ⊤ (fun p : ℝ × E => dist p.2 (pole p.1)) (0,x) :=
    (contDiffAt_snd.sub (hs.contDiffAt.comp _ contDiffAt_fst)).norm ℝ (sub_ne_zero.mpr (by simpa [pole_zero] using h0))
  have hm : ContDiffAt ℝ ⊤ (fun p : ℝ × E => dist p.2 (pole (-p.1))) (0,x) :=
    (contDiffAt_snd.sub (hs.contDiffAt.comp _ contDiffAt_fst.neg)).norm ℝ (sub_ne_zero.mpr (by simpa [pole_zero] using h0))
  have hsm : ContDiffAt ℝ ⊤ (Function.uncurry (added (potential q a) A G)) (0,x) := by
    have hd : dist x (pole 0) ≠ 0 := dist_ne_zero.mpr (by simpa [pole_zero] using h0)
    unfold Function.uncurry added weight; fun_prop (disch := first | exact hd | simpa using hd)
  have hV : added (potential q a) A G 0 = potential q a := by funext y; simp [added,weight]
  obtain ⟨g,hg,hmem⟩ := branch hsm (by rw [hV]; exact grad_zero.mp hx.1.2) (by rw [hV]; exact hx.2)
  refine ⟨g,hg,?_⟩
  have pneg : Tendsto (fun e : ℝ => pole (-e)) (𝓝 0) (𝓝 0) := by
    simpa [Function.comp_def,pole_zero] using (pole_cont.comp continuous_neg).continuousAt.tendsto (x := (0:ℝ))
  have ppos : Tendsto pole (𝓝 0) (𝓝 0) := by simpa [pole_zero] using pole_cont.continuousAt.tendsto (x := (0:ℝ))
  filter_upwards [hmem,hg ((Set.finite_range a).isClosed.isOpen_compl.mem_nhds hx.1.1),
    eventually_apart hg pneg h0,eventually_apart hg ppos h0] with e h he hneg hpos
  refine ⟨⟨?_,?_⟩,?_⟩
  · simpa [places,Fin.range_snoc,hneg,hpos] using he
  · rw [potential_add,grad_zero]; exact h.1
  · rw [potential_add]; exact h.2

end OMA.Iter

/-! ## The initial triangle and the inductive count -/

namespace OMA.Iter
open OMA.Center Arxiv.«2607.27197» Filter InnerProductSpace
open scoped Topology Gradient RealInnerProductSpace

noncomputable def triangle : Fin 3 → E := ![!₂[1,0,0], !₂[-1/2,Real.sqrt 3/2,0], !₂[-1/2,-(Real.sqrt 3/2),0]]
noncomputable def unitQ : Fin 3 → ℝ := fun _ => 1
noncomputable def projTri (i : Fin 3) (x : E) := ![x.ofLp 0,dPlus x,dMinus x] i

lemma tri_dist (s : ℝ) (x : E) (i : Fin 3) : dist (s • x) (triangle i) =
    Real.sqrt (radicand s (projTri i x) (normSq x)) := by
  fin_cases i <;> simp [triangle,projTri,EuclideanSpace.dist_eq,Fin.sum_univ_three,Real.dist_eq,
    radicand,normSq,dPlus,dMinus] <;> congr 1 <;> ring_nf <;> norm_num [Real.sq_sqrt] <;> ring

lemma triangle_jet : Jet (potential unitQ triangle) (3/4) := by
  let tail (s : ℝ) (x : E) := ∑ i, (c4 (projTri i x) (normSq x) + s*rem5 s (projTri i x) (normSq x))
  have h (i : Fin 3) : ContDiff ℝ ⊤ (projTri i) := by
    fin_cases i
    · exact (proj 0).contDiff
    · change ContDiff ℝ ⊤ dPlus; unfold dPlus; fun_prop
    · change ContDiff ℝ ⊤ dMinus; unfold dMinus; fun_prop
  have hb : ContDiff ℝ ⊤ normSq := by unfold normSq; fun_prop
  refine ⟨3,tail,?_,?_⟩
  · intro x
    apply ContDiffAt.sum; intro i _
    have ha := (h i).contDiffAt.comp (f := (Prod.snd : ℝ × E → E)) (0,x) contDiffAt_snd
    have hc := hb.contDiffAt.comp (f := (Prod.snd : ℝ × E → E)) (0,x) contDiffAt_snd
    have hr : ContDiffAt ℝ ⊤ (fun p : ℝ × E => rem5 p.1 (projTri i p.2) (normSq p.2)) (0,x) :=
      rem5_smooth contDiffAt_fst ha hc rfl
    unfold c4; fun_prop
  · intro x
    have pos (i : Fin 3) : ∀ᶠ p : ℝ × E in 𝓝 (0,x), 0 < radicand p.1 (projTri i p.2) (normSq p.2) := by
      have hc : Continuous (fun p : ℝ × E => radicand p.1 (projTri i p.2) (normSq p.2)) := by
        have := (h i).continuous; have := hb.continuous; unfold radicand; fun_prop
      exact continuousAt_const.eventually_lt hc.continuousAt (by simp [radicand])
    filter_upwards [eventually_all.mpr pos] with p hp
    simp only [potential,unitQ,tri_dist,expand_inv (hp _),tail,Fin.sum_univ_three]
    unfold quad cubic c2 c3 projTri dPlus dMinus normSq
    simp; ring_nf; norm_num [Real.sq_sqrt]; ring

lemma tri_unit (i : Fin 3) : dist (0:E) (triangle i) = 1 := by
  simpa [radicand] using tri_dist 0 0 i
lemma tri_away : 0 ∉ Set.range triangle := by
  rintro ⟨i,hi⟩; have := tri_unit i; simp [hi] at this
lemma tri_inj : Function.Injective triangle := by
  intro i j hij
  have h1 := congrArg (fun v : E => v.ofLp 0) hij
  have h2 := congrArg (fun v : E => v.ofLp 1) hij
  have h3 : 0 < Real.sqrt 3 := by positivity
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso <;> norm_num [triangle] at h1 <;> norm_num [triangle] at h2 <;> linarith)

lemma tri_center : (0:E) ∈ nondegenerateEquilibria unitQ triangle := by
  have ha (i : Fin 3) : (0:E) ≠ triangle i := fun h => tri_away ⟨i,h.symm⟩
  refine ⟨⟨tri_away,grad_zero.mpr ?_⟩,?_⟩
  · ext v
    rw [OMA.Edge.potential_derivative _ _ _ ha]
    simp only [_root_.sum_apply, OMA.Edge.dCharge, tri_unit]
    simp [unitQ, triangle, Fin.sum_univ_three, innerSL_apply_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
    <;> ring
  · have Hess (v w : E) : iteratedFDeriv ℝ 2 (potential unitQ triangle) 0 ![v,w] =
        3/2*v.ofLp 0*w.ofLp 0 + 3/2*v.ofLp 1*w.ofLp 1 - 3*v.ofLp 2*w.ofLp 2 := by
      rw [OMA.Edge.potential_hessian _ _ _ _ _ ha]
      simp only [OMA.Edge.ddCharge,tri_unit]
      simp [unitQ,triangle,Fin.sum_univ_three,EuclideanSpace.inner_eq_star_dotProduct,dotProduct]
      ring_nf; norm_num [Real.sq_sqrt]; ring
    intro v hv; by_contra! hz; apply hv
    have h0 := hz (!₂[1,0,0]); have h1 := hz (!₂[0,1,0]); have h2 := hz (!₂[0,0,1])
    rw [Hess] at h0 h1 h2
    simp at h0 h1 h2
    ext i; fin_cases i <;> simp_all

end OMA.Iter

namespace OMA.Iter
open OMA.Center Arxiv.«2607.27197» Set

lemma triangle_count : 4 ≤ (nondegenerateEquilibria unitQ triangle).encard := by
  have he : (0:ℝ) ∈ Ico 0 (1/100:ℝ) := ⟨le_rfl,by norm_num⟩
  obtain ⟨t,ht,hf⟩ := OMA.Edge.force_root he
  have hc := OMA.Edge.three_points ht (OMA.Edge.axis_equilibrium he ht hf)
  let S := nondegenerateEquilibria (counterexampleCharges 0) (counterexamplePositions 0) \ Metric.ball 0 (1/4:ℝ)
  have hpot : potential (counterexampleCharges 0) (counterexamplePositions 0) = potential unitQ triangle := by
    funext x; simp [potential, counterexampleCharges,counterexamplePositions,unitQ,triangle,Fin.sum_univ_succ]
  have hsub : S ⊆ nondegenerateEquilibria unitQ triangle := by
    intro x hx
    refine ⟨⟨?_,hpot ▸ hx.1.1.2⟩,hpot ▸ hx.1.2⟩
    rintro ⟨i,hi⟩
    apply hx.1.1.1
    exact ⟨i.castSucc.castSucc, (show counterexamplePositions 0 i.castSucc.castSucc = triangle i by fin_cases i <;> rfl).trans hi⟩
  have hzero : (0:E) ∉ S := fun h => h.2 (Metric.mem_ball_self (by norm_num))
  calc
    4 = (3 : ℕ∞) + 1 := by norm_num
    _ ≤ S.encard + 1 := add_le_add hc le_rfl
    _ = (insert 0 S).encard := (Set.encard_insert_of_notMem hzero).symm
    _ ≤ _ := Set.encard_mono (Set.insert_subset tri_center hsub)

end OMA.Iter

namespace OMA.Iter
open OMA.Center Arxiv.«2607.27197» Filter Set
open scoped Topology Gradient

lemma inner_branch {n : ℕ} (q : Fin n → ℝ) (a : Fin n → E) (A G L B : ℝ) (R : ℝ → E → ℝ)
    (h0 : 0 ∉ range a) (hL : 0 < L) (hAL : A*L = 3/4) (hG : G = 5/32*L) {x : E}
    (hR : ContDiffAt ℝ ⊤ (Function.uncurry R) (0,x))
    (hj : ∀ᶠ p : ℝ × E in 𝓝 (0,x), potential q a (p.1 • p.2) = B + A*p.1^2*quad p.2 +
      p.1^3*cubic p.2 + p.1^4*R p.1 p.2)
    (hc : ∇ phiZero x = 0) (hn : HasNondegenerateHessianAt phiZero x) :
    ∃ g : ℝ → E, Tendsto g (𝓝 0) (𝓝 x) ∧ ∀ᶠ e in 𝓝 0, 0 < e →
      (L*e^2) • g e ∈ nondegenerateEquilibria (charges q A G e) (places a e) := by
  let F := scaled A G L R
  have hF : F 0 = phiZero := scaled_zero _ _ _ _
  have hs := scaled_smooth A G L R x hR
  obtain ⟨g,hg,hm⟩ := branch hs (by rw [scaled_zero]; exact grad_zero.mp hc) (by rwa [scaled_zero])
  refine ⟨g,hg,?_⟩
  have hp : Tendsto (fun e => (e,g e)) (𝓝 0) (𝓝 (0,x)) := tendsto_id.prodMk_nhds hg
  have h2 : ContDiffAt ℝ 2 (Function.uncurry F) (0,x) := hs.of_le (by simp)
  have heq := rescale_near _ A G L B R x hAL hG hj
  filter_upwards [hm,hp (away_center h0 L x),hp heq.eventually_nhds,hp (h2.eventually (by norm_num))] with e hcrit haw heq' hs'
  intro he
  have hle : L*e^2 ≠ 0 := mul_ne_zero hL.ne' (pow_ne_zero 2 he.ne')
  let T : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (G := ℝˣ) (Units.mk0 (L*e^2) hle)
  have hl : added (potential q a) A G e ∘ T =ᶠ[𝓝 (g e)] fun y =>
      B + 2*(A-G*e^2)*e^2 + (e^6*L^3)*F e y := by
    have hcst : ContinuousAt (fun y : E => (e,y)) (g e) := continuousAt_const.prodMk continuousAt_id
    filter_upwards [hcst.tendsto heq'] with y hy
    exact hy he
  have hslice : ContDiffAt ℝ 2 (F e) (g e) :=
    (show ContDiffAt ℝ 2 (Function.uncurry F) (e,g e) from hs').comp (f := fun y : E => (e,y)) _ (by fun_prop)
  obtain ⟨hgrad,hnd⟩ := transport T (mul_ne_zero (pow_ne_zero 6 he.ne') (pow_ne_zero 3 hL.ne')) hl hslice hcrit.1 hcrit.2
  refine ⟨⟨haw he,?_⟩,?_⟩
  · rw [potential_add,grad_zero]; exact hgrad
  · rw [potential_add]; exact hnd


lemma gain {n k : ℕ} {q : Fin n → ℝ} {a : Fin n → E} {A : ℝ}
    (h0 : 0 ∉ range a) (hA : 0 < A) (jet : Jet (potential q a) A)
    (hold : ((k+1 : ℕ) : ℕ∞) ≤ (nondegenerateEquilibria q a).encard) :
    ∃ G > 0, ∀ᶠ e in 𝓝 0, 0 < e → (↑(k+21) : ℕ∞) ≤
      (nondegenerateEquilibria (charges q A G e) (places a e)).encard := by
  classical
  let L : ℝ := (3/4)/A
  let G : ℝ := 5/32*L
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨G,by dsimp [G]; positivity,?_⟩
  have hAL : A*L = 3/4 := by dsimp [L]; field_simp
  obtain ⟨B,R,hR,hj⟩ := jet
  let S := nondegenerateEquilibria q a
  have hrem : (k : ℕ∞) ≤ (S \ {0}).encard := by
    have h := Set.encard_tsub_one_le_encard_sdiff_singleton S 0
    apply le_trans _ h
    have hh := tsub_le_tsub_right hold (1 : ℕ∞)
    simpa [S] using hh
  obtain ⟨s,hsub,hcard⟩ := Set.exists_subset_encard_eq hrem
  have hf := Set.finite_of_encard_eq_coe (k := k) hcard
  letI := hf.fintype
  choose out hout houtmem using fun i : s => exterior_branch (hsub i.2).1 (fun h => (hsub i.2).2 h) A G
  let C := {x : E | ∇ phiZero x = 0}
  obtain ⟨cCard,cND⟩ := quarticCriticalPoints
  have cf := Set.finite_of_encard_eq_coe (k := 21) cCard
  letI : Fintype C := cf.fintype
  choose inn hinn hinmem using fun i : C => inner_branch q a A G L B R h0 hL hAL rfl (hR i) (hj i) i.2 (cND i i.2)
  let fin (i : C) (e : ℝ) := (L*e^2) • inn i e
  have hfin (i : C) : Tendsto (fin i) (𝓝 0) (𝓝 0) := by
    simpa [fin] using ((tendsto_const_nhds (x := L)).mul ((tendsto_id (α := ℝ) (x := 𝓝 0)).pow 2)).smul (hinn i)
  have hsep (i : s) (j : C) := eventually_apart (hout i) (hfin j) (fun h => (hsub i.2).2 h)
  filter_upwards [eventually_injective (a := fun i : s => (i:E)) Subtype.val_injective hout,
    eventually_injective (a := fun i : C => (i:E)) Subtype.val_injective hinn,
    eventually_all.mpr houtmem, eventually_all.mpr hinmem,
    eventually_all.mpr fun i => eventually_all.mpr (hsep i)] with e ho hi hmo hmi hsj
  intro he
  have hfInj : Function.Injective (fun j : C => fin j e) := fun i j h =>
    hi ((smul_right_injective E (mul_ne_zero hL.ne' (pow_ne_zero 2 he.ne'))) h)
  let O := range (fun i : s => out i e)
  let I := range (fun j : C => fin j e)
  have hd : Disjoint O I := by
    apply Set.disjoint_left.mpr; rintro _ ⟨i,rfl⟩ ⟨j,hj'⟩; exact hsj i j hj'.symm
  calc
    (↑(k+21) : ℕ∞) = s.encard + C.encard := by rw [hcard,show C.encard = 21 from cCard]; norm_num
    _ ≤ O.encard + I.encard := add_le_add ho.encard_range hfInj.encard_range
    _ = (O ∪ I).encard := (Set.encard_union_eq hd).symm
    _ ≤ _ := Set.encard_mono (Set.union_subset (Set.range_subset_iff.mpr hmo) (Set.range_subset_iff.mpr (fun j => hmi j he)))

end OMA.Iter

namespace OMA.Iter
open OMA.Center Arxiv.«2607.27197» Filter Set
open scoped Topology

lemma configurations (m : ℕ) : ∃ (q : Fin (3+2*m) → ℝ) (a : Fin (3+2*m) → E) (A : ℝ),
    0 < A ∧ Jet (potential q a) A ∧ 0 ∉ range a ∧ Function.Injective a ∧
    (∀ i, 0 < q i) ∧ q ⟨0,by omega⟩ = 1 ∧
    ((4+20*m : ℕ) : ℕ∞) ≤ (nondegenerateEquilibria q a).encard := by
  induction m with
  | zero => exact ⟨unitQ,triangle,3/4,by norm_num,triangle_jet,tri_away,tri_inj,fun _ => by norm_num [unitQ],rfl,triangle_count⟩
  | succ m ih =>
    obtain ⟨q,a,A,hA,hjet,h0,hinj,hq,hfirst,hcount⟩ := ih
    have old : ((3+20*m+1 : ℕ) : ℕ∞) ≤ (nondegenerateEquilibria q a).encard := by convert hcount using 1 <;> push_cast <;> ring
    obtain ⟨G,hG,hgain⟩ := gain h0 hA hjet old
    have good := (hgain.and (places_good hinj h0)).and (positive_weights hq hA G)
    obtain ⟨δ,hδ,hall⟩ := Metric.eventually_nhds_iff.mp good
    let e := δ/2
    have he : 0 < e := half_pos hδ
    obtain ⟨⟨hc,hp⟩,hw⟩ := hall (y := e) (by rw [Real.dist_eq,sub_zero,abs_of_pos he]; exact half_lt_self hδ)
    refine ⟨charges q A G e,places a e,G*e^2,by positivity,?_,(hp he).2,(hp he).1,hw he,?_,?_⟩
    · rw [potential_add]; exact jet_added hjet G e he
    · change charges q A G e (⟨0,by omega⟩ : Fin (3+2*m)).castSucc.castSucc = 1
      simpa [charges] using hfirst
    · convert hc he using 1 <;> push_cast <;> ring

lemma regular_configuration {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) (a : Fin n → E)
    (ha : Function.Injective a) (hq : ∀ i, 0 < q i) (hu : q ⟨0,hn⟩ = 1) (k : ℕ)
    (hc : (k : ℕ∞) ≤ (nondegenerateEquilibria q a).encard) :
    ∃ b : Fin n → E, Function.Injective b ∧
      (∀ x ∈ equilibria q b, HasNondegenerateHessianAt (potential q b) x) ∧
      (equilibria q b).Finite ∧ (k : ℕ∞) ≤ (equilibria q b).encard := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hpos := Fin.cons_self_tail a
  have hchg : Fin.cons 1 (Fin.tail q) = q := hu ▸ Fin.cons_self_tail q
  obtain ⟨c,hi,hnd,hfin,hcard⟩ := OMA.Morse.perturb (Fin.tail q) (Fin.tail a) (k := k) (b := a 0)
    (by rwa [hpos]) (fun j => hq j.succ) (by rwa [hpos,hchg])
  rw [hchg] at hnd hfin hcard
  exact ⟨_,hi,hnd,hfin,hcard⟩

end OMA.Iter

open Arxiv.«2607.27197» OMA.Iter in
theorem OMA.solution : type_of% @Arxiv.«2607.27197».maxwell_conjecture.iterated := by
  intro m
  obtain ⟨q,a,_,_,_,_,ha,hq,hu,hc⟩ := configurations m
  obtain ⟨b,hi,hnd,hfin,hcard⟩ := regular_configuration (by omega) q a ha hq hu _ hc
  exact ⟨q,b,hi,hq,hnd,hfin,by simpa using hcard⟩
