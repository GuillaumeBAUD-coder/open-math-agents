import OMAReductions.R_Arxiv_2607_27197_maxwell_conjecture_counterexample_R1

/-! The coordinates, derivative and Hessian computations are adapted from
@luciusacarr’s merged proof of phiZero_critical_points (project PR #836).
The witness consists of three axial, six planar and twelve off-plane points. -/

open Matrix
open Arxiv.«2607.27197»
open scoped Gradient

namespace MaxwellWitness

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
  simp (disch := fun_prop) only [fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul, fderiv_const_apply, _root_.zero_apply,
    fderiv_fun_pow, ContinuousLinearMap.fderiv, _root_.add_apply,
    _root_.sub_apply, _root_.smul_apply, smul_eq_mul]
  simp only [coord_apply]
  ring

private theorem critical_of_coordinates (p : E) :
      let x := p.ofLp 0
      let y := p.ofLp 1
      let z := p.ofLp 2
      let H := 5 + 36 * (x ^ 2 + y ^ 2) - 144 * z ^ 2
      x * H + 90 * (x ^ 2 - y ^ 2) = 0 ∧
      y * (H - 180 * x) = 0 ∧
      z * (-10 - 144 * (x ^ 2 + y ^ 2) + 96 * z ^ 2) = 0 → ∇ phiZero p = 0 := by
  have hgrad : ∇ phiZero p = 0 ↔ fderiv ℝ phiZero p = 0 := by
    rw [← toDual_gradient]
    exact (InnerProductSpace.toDual ℝ E).map_eq_zero_iff.symm
  rw [hgrad]
  dsimp only
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
    _root_.zero_apply,
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
  · simp only [hessianDet, hlin, add_zero, mul_zero,
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

private theorem direction_certificate {s x y z : ℝ} (hs : s ≠ 0) (hdir : direction s x y)
    (hz : (z = 0 ∧ 36 * s ^ 2 + 90 * s + 5 = 0) ∨
      (z ^ 2 = 5 / 48 + 3 / 2 * s ^ 2 ∧ (s = 1 / 6 ∨ s = 1 / 3))) :
    stationary x y z ∧ hessianDet x y z ≠ 0 := by
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

  constructor
  · unfold stationary
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

  · rw [hessianDet_radial hdir hrad]
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

private theorem planarRadii_root (b : Bool) :
    36 * planarRadii b ^ 2 + 90 * planarRadii b + 5 = 0 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7380)
  cases b <;> dsimp [planarRadii] <;> linear_combination h / 144

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

private theorem angular_direction (s : ℝ) (i : Fin 3) :
    direction s (angular s i).1 (angular s i).2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  fin_cases i
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, by change (Real.sqrt 3 * s / 2) ^ 2 = _; linear_combination s ^ 2 / 4 * hs⟩
  · exact Or.inr ⟨rfl, by change (-(Real.sqrt 3 * s / 2)) ^ 2 = _; linear_combination s ^ 2 / 4 * hs⟩

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

private theorem signedRoot_sq {r : ℝ} (hr : 0 ≤ r) (b : Bool) : signedRoot r b ^ 2 = r := by
  cases b <;> simp [signedRoot, Real.sq_sqrt hr]

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

private theorem nondegenerate_of_det (p : E)
    (hd : hessianDet (p.ofLp 0) (p.ofLp 1) (p.ofLp 2) ≠ 0) :
    HasNondegenerateHessianAt phiZero p := by
  have hdet : (hessianMatrix p).det ≠ 0 := by
    have hval : (hessianMatrix p).det = hessianDet (p.ofLp 0) (p.ofLp 1) (p.ofLp 2) := by
      simp only [hessianMatrix, Matrix.det_fin_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.of_apply, Matrix.head_cons, Matrix.tail_cons, hessianDet, radial]
      ring
    exact hval.symm ▸ hd
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

private theorem coordinate_certificate (i : CriticalIndex) :
    let p := criticalCoordinates i
    stationary p.1.1 p.1.2 p.2 ∧ hessianDet p.1.1 p.1.2 p.2 ≠ 0 := by
  rcases i with i | (⟨b, i⟩ | ⟨b, e, i⟩)
  · change stationary 0 0 (axialHeight i) ∧ hessianDet 0 0 (axialHeight i) ≠ 0
    have h : axialHeight i = 0 ∨ axialHeight i ^ 2 = 5 / 48 := by
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr (signedRoot_sq (by norm_num) false)
      · exact Or.inr (signedRoot_sq (by norm_num) true)
    rcases h with h | h
    · norm_num [h, stationary, radial, hessianDet]
    · simp [stationary, radial, hessianDet, h]
      norm_num
  · exact direction_certificate (planarRadii_neg b).ne (angular_direction _ i)
      (Or.inl ⟨rfl, planarRadii_root b⟩)
  · exact direction_certificate (offRadius_pos b).ne' (angular_direction _ i)
      (Or.inr ⟨signedRoot_sq (offHeightSq_pos _).le e, by cases b <;> norm_num [offRadius]⟩)

end MaxwellWitness

open MaxwellWitness in
theorem OMA.solution : OMA.R_Arxiv_2607_27197_maxwell_conjecture_counterexample_R1.H1 := by
  let points : CriticalIndex ↪ E := ⟨criticalPoint, criticalPoint_inj⟩
  refine ⟨Finset.univ.map points, ?_, ?_⟩
  · simp [CriticalIndex]
  · intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hp
    obtain ⟨hstat, hdet⟩ := coordinate_certificate i
    exact ⟨critical_of_coordinates _ hstat, nondegenerate_of_det _ hdet⟩
