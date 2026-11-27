import FormalConjectures.Arxiv.«2607.27197».MaxwellConjecture
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Twenty-four nondegenerate equilibria for five charges

This proves the five-charge construction of Arathoon, Ball and Kvalheim
(arXiv:2607.27197, Theorem 1). The quartic classification is the Lean proof
by @luciusacarr in project PR #836. The continuation and edge arguments are
from @PanPapag's PRs #1450 and #1378, assembled using reduction #1113.
The distance derivative in the edge argument follows @harshshah1618's
two-charge proof in PR #289.
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

section

/-!
# Persistence of the central Maxwell equilibria

Following the rescaling of Arathoon, Ball and Kvalheim (arXiv:2607.27197),
we extend the rescaled potential smoothly across ε = 0. A rationalized
remainder for each inverse distance makes the extension an exact identity.
The implicit function theorem then continues the zeros of the spatial
differential, and finite separation preserves their number.
-/

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
noncomputable def amp (e : ℝ) := 3/4 - 5/32*e^2
noncomputable def farTail (e a b : ℝ) := c4 a b + e^2*rem5 (e^2) a b

/-- The extension after scaling space by ε² and potential by ε⁶. -/
noncomputable def family (e : ℝ) (x : E) :=
  phiZero x + e^2*(farTail e (x.ofLp 0) (normSq x) +
    farTail e (dPlus x) (normSq x) + farTail e (dMinus x) (normSq x) -
    5/16*c4 (x.ofLp 2) (normSq x)) +
    e*amp e*(rem5 e (x.ofLp 2) (normSq x) + rem5 e (-x.ofLp 2) (normSq x))

lemma family_zero : family 0 = phiZero := by
  funext x
  simp [family]

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

lemma family_smooth (x : E) :
    ContDiffAt ℝ ⊤ (fun p : ℝ × E => family p.1 p.2) (0,x) := by
  have h (i : Fin 3) : ContDiffAt ℝ ⊤ (fun p : ℝ × E => p.2.ofLp i) (0,x) :=
    (proj i).contDiff.contDiffAt.comp _ contDiffAt_snd
  have hb : ContDiffAt ℝ ⊤ (fun p : ℝ × E => normSq p.2) (0,x) := by
    unfold normSq
    fun_prop
  have hp : ContDiffAt ℝ ⊤ (fun p : ℝ × E => dPlus p.2) (0,x) := by unfold dPlus; fun_prop
  have hm : ContDiffAt ℝ ⊤ (fun p : ℝ × E => dMinus p.2) (0,x) := by unfold dMinus; fun_prop
  have hr0 : ContDiffAt ℝ ⊤ (fun p : ℝ × E => rem5 (p.1^2) (p.2.ofLp 0) (normSq p.2)) (0,x) := by
    apply rem5_smooth <;> first | fun_prop | norm_num
  have hr1 : ContDiffAt ℝ ⊤ (fun p : ℝ × E => rem5 (p.1^2) (dPlus p.2) (normSq p.2)) (0,x) := by
    apply rem5_smooth <;> first | fun_prop | norm_num
  have hr2 : ContDiffAt ℝ ⊤ (fun p : ℝ × E => rem5 (p.1^2) (dMinus p.2) (normSq p.2)) (0,x) := by
    apply rem5_smooth <;> first | fun_prop | norm_num
  have hr3 : ContDiffAt ℝ ⊤ (fun p : ℝ × E => rem5 (p.1) (p.2.ofLp 2) (normSq p.2)) (0,x) := by
    apply rem5_smooth <;> first | fun_prop | norm_num
  have hr4 : ContDiffAt ℝ ⊤ (fun p : ℝ × E => rem5 (p.1) (-p.2.ofLp 2) (normSq p.2)) (0,x) := by
    apply rem5_smooth <;> first | fun_prop | norm_num
  unfold family phiZero farTail amp c4
  dsimp only
  fun_prop

def regular (e : ℝ) (x : E) : Prop :=
  0 < radicand (e^2) (x.ofLp 0) (normSq x) ∧
  0 < radicand (e^2) (dPlus x) (normSq x) ∧
  0 < radicand (e^2) (dMinus x) (normSq x) ∧
  0 < radicand e (x.ofLp 2) (normSq x) ∧
  0 < radicand e (-x.ofLp 2) (normSq x)

lemma regular_open : IsOpen {p : ℝ × E | regular p.1 p.2} := by
  have h (i : Fin 3) : Continuous (fun p : ℝ × E => p.2.ofLp i) :=
    (proj i).continuous.comp continuous_snd
  have posOpen (t a : ℝ × E → ℝ) (ht : Continuous t) (ha : Continuous a) :
      IsOpen {p : ℝ × E | 0 < radicand (t p) (a p) (normSq p.2)} := by
    apply isOpen_lt (f := fun _ => (0 : ℝ)) continuous_const
    unfold radicand normSq
    fun_prop
  unfold regular
  refine IsOpen.inter (posOpen _ _ ?_ ?_) (IsOpen.inter (posOpen _ _ ?_ ?_)
    (IsOpen.inter (posOpen _ _ ?_ ?_) (IsOpen.inter (posOpen _ _ ?_ ?_) (posOpen _ _ ?_ ?_))))
  all_goals first | fun_prop | unfold dPlus; fun_prop | unfold dMinus; fun_prop

lemma regular_zero (x : E) : regular 0 x := by simp [regular, radicand]

noncomputable def distList (e : ℝ) (x : E) : Fin 5 → ℝ :=
  ![Real.sqrt (radicand (e^2) (x.ofLp 0) (normSq x)),
    Real.sqrt (radicand (e^2) (dPlus x) (normSq x)),
    Real.sqrt (radicand (e^2) (dMinus x) (normSq x)),
    e * Real.sqrt (radicand e (x.ofLp 2) (normSq x)),
    e * Real.sqrt (radicand e (-x.ofLp 2) (normSq x))]

lemma distance_formula {e : ℝ} (he : 0 < e) (x : E) (j : Fin 5) :
    dist (e^2 • x) (counterexamplePositions e j) = distList e x j := by
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have pull (u : ℝ) : e * Real.sqrt u = Real.sqrt (e^2 * u) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq he.le]
  fin_cases j <;>
    simp [distList, counterexamplePositions, EuclideanSpace.dist_eq, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, Real.dist_eq, radicand, normSq, dPlus, dMinus, pull] <;>
    congr 1 <;> ring_nf <;> norm_num [hs] <;> ring

lemma away {e : ℝ} {x : E} (he : 0 < e) (h : regular e x) :
    e^2 • x ∉ Set.range (counterexamplePositions e) := by
  rintro ⟨j, hj⟩
  have hpos : 0 < distList e x j := by
    obtain ⟨h0,h1,h2,h3,h4⟩ := h
    fin_cases j <;> simp [distList, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] <;> positivity
  rw [← distance_formula he, hj, dist_self] at hpos
  exact lt_irrefl _ hpos

noncomputable def base (e : ℝ) := 3 + 2*e^2*amp e

set_option maxHeartbeats 1500000 in
lemma scaling {e : ℝ} {x : E} (he : 0 < e) (h : regular e x) :
    potential (counterexampleCharges e) (counterexamplePositions e) (e^2 • x) =
      base e + e^6 * family e x := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := h
  unfold potential
  simp only [distance_formula he]
  simp [counterexampleCharges, distList, Fin.sum_univ_succ, -one_div]
  have axial (u : ℝ) : (3/4*e^3-5/32*e^5)/(e*u) = (e^2*amp e)*(1/u) := by
    unfold amp
    rw [mul_comm e u, ← div_div, div_eq_mul_inv _ e]
    field_simp [he.ne']
  rw [axial, axial, expand_inv h0, expand_inv h1, expand_inv h2, expand_inv h3, expand_inv h4]
  unfold base family farTail phiZero amp c2 c3 c4
  dsimp only
  unfold dPlus dMinus normSq
  ring_nf
  norm_num [Real.sq_sqrt]
  ring

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

lemma original_critical {e : ℝ} {x : E} (he : 0 < e) (hr : regular e x)
    (hs : ContDiffAt ℝ 2 (family e) x) (hg : fderiv ℝ (family e) x = 0)
    (hn : HasNondegenerateHessianAt (family e) x) :
    e^2 • x ∈ nondegenerateEquilibria (counterexampleCharges e) (counterexamplePositions e) := by
  let A : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (G := ℝˣ) (Units.mk0 (e^2) (pow_ne_zero _ he.ne'))
  let V := potential (counterexampleCharges e) (counterexamplePositions e)
  have heq : V ∘ A =ᶠ[𝓝 x] fun y => base e + e^6 * family e y := by
    have ht : ContinuousAt (fun y : E => (e,y)) x := continuousAt_const.prodMk continuousAt_id
    filter_upwards [ht.tendsto (regular_open.mem_nhds hr)] with y hy
    exact scaling he hy
  obtain ⟨hg',hn'⟩ := transport A (pow_ne_zero 6 he.ne') heq hs hg hn
  exact ⟨⟨away he hr, grad_zero.mpr hg'⟩,hn'⟩

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

lemma center_branch {x : E} (hc : ∇ phiZero x = 0) (hn : HasNondegenerateHessianAt phiZero x)
    {r : ℝ} (hr : 0 < r) :
    ∃ g : ℝ → E, Tendsto g (𝓝 0) (𝓝 x) ∧ ∀ᶠ e in 𝓝 0, 0 < e →
      e^2 • g e ∈ nondegenerateEquilibria (counterexampleCharges e) (counterexamplePositions e) ∩
        Metric.ball 0 r := by
  have hs : ContDiffAt ℝ ⊤ (Function.uncurry family) (0,x) := family_smooth x
  obtain ⟨g,hg,hc'⟩ := branch hs (by rw [family_zero]; exact grad_zero.mp hc) (by rwa [family_zero])
  refine ⟨g,hg,?_⟩
  have hp : Tendsto (fun e => (e,g e)) (𝓝 0) (𝓝 (0,x)) := tendsto_id.prodMk_nhds hg
  have hreg := hp (regular_open.mem_nhds (regular_zero x))
  have h2 : ContDiffAt ℝ 2 (Function.uncurry family) (0,x) := hs.of_le (by simp)
  have hs' := hp (h2.eventually (by norm_num))
  have hball : Tendsto (fun e => e^2 • g e) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id (α := ℝ) (x := 𝓝 0)).pow 2 |>.smul hg
  filter_upwards [hc', hreg, hs', hball (Metric.ball_mem_nhds _ hr)] with e h he hdiff hb
  intro hepos
  change ContDiffAt ℝ 2 (Function.uncurry family) (e,g e) at hdiff
  have slice : ContDiffAt ℝ 2 (fun y : E => (e,y)) (g e) := by fun_prop
  exact ⟨original_critical hepos he (hdiff.comp (g e) slice)
    h.1 h.2, hb⟩

end OMA.Center

open Arxiv.«2607.27197» Filter OMA.Center
open scoped Topology Gradient

private theorem centralEquilibria :
    ∀ (s : Finset E), (∀ x ∈ s, ∇ phiZero x = 0 ∧ HasNondegenerateHessianAt phiZero x) →
    ∀ r > (0 : ℝ), ∃ δ > 0, ∀ ε ∈ Set.Ioo 0 δ,
      (s.card : ℕ∞) ≤ ((nondegenerateEquilibria (counterexampleCharges ε)
        (counterexamplePositions ε)) ∩ Metric.ball 0 r).encard := by
  classical
  intro s hs r hr
  choose g hg hmem using (fun i : s => center_branch (hs i i.property).1 (hs i i.property).2 hr)
  have hi := eventually_injective (a := fun i : s => (i : E)) Subtype.val_injective hg
  have h := hi.and (eventually_all.mpr hmem)
  obtain ⟨δ,hδ,hbound⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨δ,hδ,?_⟩
  intro e he
  obtain ⟨hinj,hinside⟩ := hbound (y := e) (by simpa [Real.dist_eq, abs_of_pos he.1] using he.2)
  have heinj : Function.Injective (fun i : s => e^2 • g i e) := by
    intro i j hij
    apply hinj
    exact (smul_right_injective _ (pow_ne_zero 2 he.1.ne')) hij
  have hle := heinj.encard_range.trans (Set.encard_le_encard (Set.range_subset_iff.mpr
    (fun i => hinside i he.1)))
  simpa using hle

end

section

/-!
# Three edge equilibria in the Maxwell counterexample

On the negative x-axis the gradient has just one possibly nonzero component.
For every axial separation parameter between 0 and 1/100 this component changes
sign on the interval from -1/3 to -1/4. Throughout the interval the Hessian is
diagonal with entries of signs -, +, -. Two symmetries of the five charges
carry the resulting equilibrium to distinct points at the same radius.

The distance derivative uses the squared-norm calculation from the project's
proof for the two-charge case.
-/

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

lemma force_root {e : ℝ} (he : e ∈ Set.Ioo 0 (1/100 : ℝ)) :
    ∃ t ∈ Set.Icc (-1/3 : ℝ) (-1/4), force e t = 0 := by
  have hw := weight_bounds he
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
    have h2 : 0 ≤ weight e / (poleDist e (-1/3))^3 := div_nonneg hw.1.le (pow_pos (hp _ (Set.left_mem_Icc.mpr hI)) 3).le
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

lemma diagonal_signs {e t : ℝ} (he : e ∈ Set.Ioo 0 (1/100 : ℝ))
    (ht : t ∈ Set.Icc (-1/3 : ℝ) (-1/4)) :
    diagX e t < 0 ∧ 0 < diagY e t ∧ diagZ e t < 0 := by
  obtain ⟨hw, hw'⟩ := weight_bounds he
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
  have e2 : e^2 ≤ (1/100 : ℝ)^2 := by gcongr <;> first | exact he.1.le | exact he.2.le
  have hA : 2 / (1-t)^3 < 6/5 := (div_lt_iff₀ ha3).2 (by linarith)
  have hXb : (4*(t+1/2)^2-3/2) / (baseDist t)^5 < -5/4 :=
    (div_lt_iff₀ (pow_pos B _)).2 (by linarith)
  have hXc : (4*t^2-2*e^2)*weight e / (poleDist e t)^5 < 1/100 :=
    (div_lt_iff₀ (pow_pos Z _)).2 (by
      have : (4*t^2-2*e^2)*weight e ≤ 1*weight e :=
        mul_le_mul_of_nonneg_right (by nlinarith only [t2, sq_nonneg e]) hw.le
      linarith)
  have hYa : -1 / (1-t)^3 > -1 := (lt_div_iff₀ ha3).2 (by linarith)
  have hYb : 2 < (3-2*(t+1/2)^2) / (baseDist t)^5 :=
    (lt_div_iff₀ (pow_pos B _)).2 (by linarith)
  have hYc : 2*weight e / (poleDist e t)^3 < 1/100 :=
    (div_lt_iff₀ (pow_pos Z _)).2 (by linarith)
  have hZc : (4*e^2-2*t^2)*weight e / (poleDist e t)^5 < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) hw) (pow_pos Z _)
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

lemma axis_equilibrium {e t : ℝ} (he : e ∈ Set.Ioo 0 (1/100 : ℝ))
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

open Arxiv.«2607.27197» in
private theorem edgeEquilibria :
    ∀ ε ∈ Set.Ioo (0 : ℝ) (1 / 100),
      3 ≤ ((nondegenerateEquilibria (counterexampleCharges ε) (counterexamplePositions ε)) \
        Metric.ball 0 (1 / 4)).encard := by
  intro e he
  obtain ⟨t, ht, hf⟩ := OMA.Edge.force_root he
  exact OMA.Edge.three_points ht (OMA.Edge.axis_equilibrium he ht hf)

end

open Arxiv.«2607.27197»
open scoped Gradient

theorem OMA.solution : type_of% @Arxiv.«2607.27197».maxwell_conjecture.counterexample := by
  obtain ⟨hcard, hn⟩ := quarticCriticalPoints
  have hfin := Set.finite_of_encard_eq_coe (k := 21) hcard
  have hs : ∀ x ∈ hfin.toFinset, ∇ phiZero x = 0 ∧ HasNondegenerateHessianAt phiZero x := by
    intro x hx
    have hc : ∇ phiZero x = 0 := hfin.mem_toFinset.mp hx
    exact ⟨hc, hn x hc⟩
  obtain ⟨δ, hδ, hcenter⟩ := centralEquilibria hfin.toFinset hs (1 / 4) (by norm_num)
  refine ⟨min δ (1 / 100), lt_min hδ (by norm_num), ?_⟩
  intro ε hε
  have inside := hcenter ε ⟨hε.1, lt_of_lt_of_le hε.2 (min_le_left _ _)⟩
  have outside := edgeEquilibria ε ⟨hε.1, lt_of_lt_of_le hε.2 (min_le_right _ _)⟩
  rw [← hfin.encard_eq_coe_toFinset_card, hcard] at inside
  rw [← Set.encard_sdiff_add_encard_inter _ (Metric.ball 0 (1 / 4))]
  exact add_le_add outside inside
