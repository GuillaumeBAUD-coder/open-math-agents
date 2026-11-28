import FormalConjectures.OpenQuantumProblems.«23»
import Mathlib

/-! A finite pentagon reduction in dimension 69. The proof of the matrix conversion
and orbit construction adapts the local dimension-59 descent, itself based on the
dimension-68 reduction and its H2 proof by @marcusbuffett and on Yaoling Yang's
SICLean (Apache-2.0, e74571352233162adee70895903d82f8465fd054).

The nonsplit descent below uses Smith coordinates for the quadratic ideal quotient
in Radchenko and Wheeler, Real quadratic fields and finite quantum dilogarithms I,
equations (37) through (41), arXiv:2609.21892. Writing a numerator as Aε+B over
ε⁻³−1 gives coordinates (A mod 69, 67A+B mod 4554). In these coordinates the
69-torsion labels (i,j) are (-i+2j,66j). The group has exponent 4554, whereas
the split product of the torsion plane with a cyclic group of order 66 has
exponent 1518. The ghost-to-SIC construction is due to Appleby,
Flammia and Kopp. -/

namespace OMA.R_OpenQuantumProblem23_hasSICPOVM_69_R1

open Matrix OpenQuantumProblem23
open scoped BigOperators

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem rank_eq_trace_of_idem (A : Matrix (ι) (ι) ℂ) (hA : A * A = A) :
    ((A.rank : ℕ) : ℂ) = A.trace := by
  have he : IsIdempotentElem A.mulVecLin := by
    apply LinearMap.ext
    intro v
    simp only [Module.End.mul_apply, Matrix.mulVecLin_apply]
    rw [Matrix.mulVec_mulVec, hA]
  have htrL : A.trace = LinearMap.trace ℂ (ι → ℂ) A.mulVecLin := by
    rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (ι))]
    congr 1
    ext i j
    simp [Matrix.mulVecLin, LinearMap.toMatrix]
  have hr : A.rank = Module.finrank ℂ (LinearMap.range A.mulVecLin) := by
    rw [Matrix.rank_eq_finrank_range_toLin A (Pi.basisFun ℂ (ι)) (Pi.basisFun ℂ (ι))]
    rfl
  have hp : LinearMap.IsProj (LinearMap.range A.mulVecLin) A.mulVecLin :=
    LinearMap.IsIdempotentElem.isProj_range A.mulVecLin he
  rw [htrL, LinearMap.IsProj.trace hp, ← hr]


theorem exists_unit_of_rank_one (A : Matrix (ι) (ι) ℂ) (hH : A.IsHermitian)
    (hA : A * A = A) (h1 : A.rank = 1) :
    ∃ ψ : ι → ℂ, ∑ i, Complex.normSq (ψ i) = 1 ∧ ∀ i j, A i j = ψ i * star (ψ j) := by
  have hcj : ∀ k l, A l k = star (A k l) := fun k l => by
    have h1' : Matrix.conjTranspose A l k = A l k := by rw [show Matrix.conjTranspose A = A from hH]
    rw [Matrix.conjTranspose_apply] at h1'
    exact h1'.symm
  have htr : (1 : ℂ) = A.trace := by
    have h2 := rank_eq_trace_of_idem A hA
    rw [h1] at h2
    exact_mod_cast h2
  obtain ⟨k, hk⟩ : ∃ k, A k k ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hz : A.trace = (0:ℂ) := by
      show ∑ i, Matrix.diag A i = 0
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [Matrix.diag_apply]
      exact hcon i
    rw [hz] at htr
    exact absurd htr (by norm_num)
  set u : ι → ℂ := fun i => A i k with hu
  have hAu : A *ᵥ u = u := by
    funext i
    have h2 : (A * A) i k = A i k := congrFun (congrFun hA i) k
    rw [Matrix.mul_apply] at h2
    show ∑ l, A i l * u l = u i
    simpa [hu] using h2
  have hrk : Module.finrank ℂ (LinearMap.range A.mulVecLin) = 1 := by
    have h5 : A.rank = Module.finrank ℂ (LinearMap.range A.mulVecLin) := by
      rw [Matrix.rank_eq_finrank_range_toLin A (Pi.basisFun ℂ (ι)) (Pi.basisFun ℂ (ι))]
      rfl
    rw [← h5]
    exact h1
  have huMem : u ∈ LinearMap.range A.mulVecLin := by
    refine ⟨u, ?_⟩
    show A *ᵥ u = u
    exact hAu
  have hspan : LinearMap.range A.mulVecLin = Submodule.span ℂ {u} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hrk huMem (fun h => hk (congrFun h k))
  have hcol : ∀ j, (fun i => A i j) ∈ LinearMap.range A.mulVecLin := by
    intro j
    refine ⟨Pi.single j (1:ℂ), ?_⟩
    funext i
    show (A *ᵥ Pi.single j (1:ℂ)) i = A i j
    simp [Matrix.mulVec, Matrix.mulVec_single]
  have hdec : ∀ j, ∃ c : ℂ, ∀ i, A i j = c * u i := by
    intro j
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hcol j)
    exact ⟨c, fun i => by simpa using (congrFun hc i).symm⟩
  have hform : ∀ i j, A i j = A i k * A k j / A k k := by
    intro i j
    obtain ⟨c, hc⟩ := hdec j
    have hik : A i j = c * A i k := hc i
    have hkj : A k j = c * A k k := hc k
    rw [hik, hkj]
    field_simp [hk]
  -- A k k = ofReal (∑ normSq (A k l)), positive
  have hkksum : A k k = ∑ l, ((Complex.normSq (A k l) : ℝ) : ℂ) := by
    have h2 : (A * A) k k = A k k := congrFun (congrFun hA k) k
    rw [Matrix.mul_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hcj k l]
    simp only [Complex.star_def, Complex.mul_conj]
  have hsumnn : 0 ≤ ∑ l, Complex.normSq (A k l) :=
    Finset.sum_nonneg (fun l _ => Complex.normSq_nonneg _)
  have hrne : (∑ l, Complex.normSq (A k l)) ≠ 0 := by
    intro hz
    apply hk
    rw [hkksum, ← Complex.ofReal_sum, hz]
    simp
  obtain ⟨r, hr0, hrc⟩ : ∃ r : ℝ, 0 < r ∧ ((r : ℂ) = A k k) := by
    refine ⟨∑ l, Complex.normSq (A k l), lt_of_le_of_ne hsumnn (Ne.symm hrne), ?_⟩
    rw [hkksum]
    exact Complex.ofReal_sum _ _
  -- the column sum equals the row sum
  have hcolsum : ∑ i, Complex.normSq (A i k) = r := by
    have h7 : ((∑ i, Complex.normSq (A i k) : ℝ) : ℂ) = A k k := by
      rw [Complex.ofReal_sum, hkksum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hcj k i]
      simp only [Complex.star_def, Complex.normSq_conj]
    exact Complex.ofReal_inj.mp (h7.trans hrc.symm)
  refine ⟨fun i => A i k / ((Real.sqrt r : ℂ)), ?_, ?_⟩
  · have hdiv : ∀ i, Complex.normSq (A i k / ((Real.sqrt r : ℂ)))
        = Complex.normSq (A i k) / r := by
      intro i
      rw [Complex.normSq_div, Complex.normSq_ofReal, Real.mul_self_sqrt hr0.le]
    show ∑ i, Complex.normSq (A i k / ((Real.sqrt r : ℂ))) = 1
    rw [Finset.sum_congr rfl (fun i _ => hdiv i), ← Finset.sum_div, hcolsum, div_self hr0.ne']
  · intro i j
    rw [hform i j, hcj j k, ← hrc]
    show A i k * star (A j k) / ((r : ℝ) : ℂ)
      = A i k / ((Real.sqrt r : ℂ)) * star (A j k / ((Real.sqrt r : ℂ)))
    have hsd : star (A j k / ((Real.sqrt r : ℂ)))
        = star (A j k) / star ((Real.sqrt r : ℂ)) := star_div₀ _ _
    have hs : star ((Real.sqrt r : ℂ)) = ((Real.sqrt r : ℂ)) := by simp
    rw [hsd, hs, div_mul_div_comm]
    congr 1
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr0.le]


end

section

private theorem char_normSq {d : ℕ} [NeZero d] (x : ZMod d) :
    Complex.normSq (ZMod.stdAddChar x) = 1 := by
  exact Circle.normSq_coe (ZMod.toCircle x)

private theorem char_star {d : ℕ} [NeZero d] (x : ZMod d) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  rw [AddChar.map_neg_eq_inv]
  exact (Circle.coe_inv_eq_conj (ZMod.toCircle x)).symm

private theorem orbit_of_matrix {d : ℕ} [NeZero d]
    (A : Matrix (ZMod d) (ZMod d) ℂ) (hH : A.IsHermitian)
    (hA : A * A = A) (htr : A.trace = 1)
    (hflat : ∀ a b : ZMod d, (a,b) ≠ (0,0) →
      Complex.normSq (∑ t, A (t+a) t * ZMod.stdAddChar (b*t)) = sicOverlapSq d) :
    HasSICPOVM d := by
  classical
  have hrank : A.rank = 1 := by
    have h := (rank_eq_trace_of_idem A hA).trans htr
    exact_mod_cast h
  obtain ⟨v, hv, hAv⟩ := exists_unit_of_rank_one A hH hA hrank
  let coord : Fin d ≃ ZMod d := Fintype.equivOfCardEq (by simp)
  let label : Fin (d^2) ≃ ZMod d × ZMod d := Fintype.equivOfCardEq (by simp [pow_two])
  let w (p : ZMod d × ZMod d) (t : ZMod d) := ZMod.stdAddChar (p.2*t) * v (t+p.1)
  refine ⟨fun j => mkStateVector (fun i => w (label j) (coord i)), ?_, ?_⟩
  · intro j
    have unit : ∑ i : Fin d, Complex.normSq (w (label j) (coord i)) = 1 := by
      rw [coord.sum_comp (fun t => Complex.normSq (w (label j) t))]
      simp only [w, Complex.normSq_mul, char_normSq, one_mul]
      exact (Equiv.sum_comp (Equiv.addRight (label j).1) (fun t => Complex.normSq (v t))).trans hv
    have hn : ‖mkStateVector (fun i => w (label j) (coord i))‖ ^ 2 = 1 := by
      simpa only [PiLp.norm_sq_eq_of_L2, Complex.sq_norm] using unit
    unfold IsNormalized
    nlinarith [norm_nonneg (mkStateVector (fun i => w (label j) (coord i)))]
  · intro j k hjk
    let p := label j
    let q := label k
    let a := q.1-p.1
    let b := q.2-p.2
    have hab : (a,b) ≠ (0,0) := by
      intro h
      apply hjk
      apply label.injective
      change p = q
      exact Prod.ext (sub_eq_zero.mp (congrArg Prod.fst h)).symm
        (sub_eq_zero.mp (congrArg Prod.snd h)).symm
    let f := fun t => A (t+a) t * ZMod.stdAddChar (b*t)
    have he (t) : star (w p t) * w q t =
        ZMod.stdAddChar (-(b*p.1)) * f (t+p.1) := by
      have heq : -(p.2*t) + q.2*t = -(b*p.1) + b*(t+p.1) := by dsimp [b]; ring
      have hx : t+p.1+a = t+q.1 := by dsimp [a]; abel
      simp only [w, f, star_mul, char_star, hAv, hx]
      calc
        _ = (ZMod.stdAddChar (-(p.2*t)) * ZMod.stdAddChar (q.2*t)) *
            (v (t+q.1) * star (v (t+p.1))) := by ring
        _ = _ := by
          rw [← AddChar.map_add_eq_mul, heq, AddChar.map_add_eq_mul]
          ring
    change Complex.normSq (∑ i, star (w p (coord i)) * w q (coord i)) = sicOverlapSq d
    rw [show (∑ i, star (w p (coord i)) * w q (coord i)) =
      ∑ t, star (w p t) * w q t from coord.sum_comp (fun t => star (w p t) * w q t)]
    simp_rw [he]
    have htranslate : (∑ t, f (t+p.1)) = ∑ t, f t := Equiv.sum_comp (Equiv.addRight p.1) f
    rw [← Finset.mul_sum, htranslate, Complex.normSq_mul, char_normSq, one_mul]
    exact hflat a b hab

end


noncomputable section

private theorem scalar_origin :
    let x : ℂ := Real.sqrt ((68 + Real.sqrt 4620) / 2)
    (x^3)^2 - 1 = 69 * (Real.sqrt 66 : ℂ) * x^3 := by
  let u := (68 + Real.sqrt 4620) / 2
  let x := Real.sqrt u
  have hu : u ^ 2 - 68*u + 1 = 0 := by
    dsimp [u]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 4620)]
  have hu1 : 1 ≤ u := by dsimp [u]; linarith [Real.sqrt_nonneg 4620]
  have hx1 : 1 ≤ x := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by nlinarith)
  have hx : x ≠ 0 := by linarith
  have hx2 : x^2 = u := Real.sq_sqrt (by linarith)
  have hx4 : x^4 - 68*x^2 + 1 = 0 := by
    rw [show (4:ℕ) = 2*2 by decide, pow_mul, hx2]; exact hu
  have hw : 0 ≤ x-x⁻¹ := by
    have h := inv_le_one_of_one_le₀ hx1
    linarith
  have hd : Real.sqrt 66 = x-x⁻¹ := by
    apply (Real.sqrt_eq_iff_mul_self_eq (by norm_num) hw).2
    field_simp [hx]
    nlinarith [hx4]
  have he : (x^3)^2 - 1 = 69 * Real.sqrt 66 * x^3 := by
    rw [hd]
    field_simp [hx]
    linear_combination (x^2-1) * hx4
  change ((x : ℂ)^3)^2-1 = 69 * (Real.sqrt 66 : ℂ) * (x : ℂ)^3
  exact_mod_cast he

private theorem average_axis (f : ZMod 66 → ℂ) :
    (∑ t : ZMod 66, ∑ h : ZMod 66, f h * ZMod.stdAddChar (h*t)) = 66 * f 0 := by
  classical
  have orth (h : ZMod 66) : (∑ t : ZMod 66, ZMod.stdAddChar (h*t)) = if h = 0 then 66 else 0 := by
    split_ifs with hz
    · simp [hz, ZMod.card]
    · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar 66 hz)
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, orth]
  simp [mul_ite, mul_comm]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 25000000 in
private theorem matrixConversion :

  let e := fun (t : ZMod 69) => ZMod.stdAddChar t
  let q := fun (i j : ZMod 69) => e (i^2 - i*j + j^2)
  let u : ℝ := (68 + Real.sqrt 4620) / 2
  ∀ (F : ZMod 69 → ZMod 69 → ℂ) (τ : ℂ →+* ℂ),
  F 0 0 = ((Real.sqrt u : ℂ) ^ 3) →
  (∀ i j, (i, j) ≠ (0, 0) → F i j * F (-i) (-j) = (q i j)⁻¹) →
  (∀ r s, (69 : ℂ)⁻¹ * ∑ i, ∑ j, F i j * F (r-i) (s-j) * q i j * e (-i*r+j*(r-s)) =
      (Real.sqrt 66 : ℂ) * F r s + if (r,s) = (0,0) then 69 else 0) →
  (∀ i j, (i,j) ≠ (0,0) → ‖τ (F i j)‖ = 1) →
  ∃ A : Matrix (ZMod 69) (ZMod 69) ℂ, A.IsHermitian ∧ A * A = A ∧ A.trace = 1 ∧
    ∀ a b : ZMod 69, (a,b) ≠ (0,0) →
      Complex.normSq (∑ t, A (t+a) t * e (b*t)) = (70 : ℝ)⁻¹ := by
  classical
  intro char quadratic unit
  let omega (d : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / d)
  have omega_formula (d : ℕ) : omega d = Complex.exp (2 * Real.pi * Complex.I / d) := rfl
  let xi (d : ℕ) : ℂ := -Complex.exp (Real.pi * Complex.I / d)
  have xi_formula (d : ℕ) : xi d = -Complex.exp (Real.pi * Complex.I / d) := rfl
  let D (d : ℕ) (p : ℤ × ℤ) : Matrix (Fin d) (Fin d) ℂ :=
    fun i j =>
      if (((i : ℕ) : ℤ) : ZMod d) = (((j : ℕ) : ℤ) : ZMod d) + (p.1 : ZMod d) then
        xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((j : ℕ) : ℤ))
      else 0
  have displacement_entry (d : ℕ) (p : ℤ × ℤ) (i j : Fin d) :
      D d p i j = if (((i : ℕ) : ℤ) : ZMod d) = (((j : ℕ) : ℤ) : ZMod d) + (p.1 : ZMod d) then
        xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((j : ℕ) : ℤ)) else 0 := rfl
  let ov (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) (p : ℤ × ℤ) : ℂ :=
    (A * (D d p)ᴴ).trace
  have ov_formula (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) (p : ℤ × ℤ) : ov d A p =
    (A * (D d p)ᴴ).trace := rfl
  let IsZeroLabel (d : ℕ) (p : ℤ × ℤ) : Prop :=
    (d : ℤ) ∣ p.1 ∧ (d : ℤ) ∣ p.2
  let rsicConst (d r : ℕ) : ℝ :=
    ((r : ℝ) * ((d : ℝ) - r)) / ((d : ℝ) ^ 2 - 1)
  let IsGhost (d r : ℕ) (G : Matrix (Fin d) (Fin d) ℂ) : Prop :=
    G * G = G ∧ G.trace = r ∧ ∀ p : ℤ × ℤ, ¬ IsZeroLabel d p →
      ov d G p * ov d G (-p) = (rsicConst d r : ℂ)
  let UnimodularFlip (d r : ℕ) (G : Matrix (Fin d) (Fin d) ℂ) (σ : ℂ →+* ℂ) : Prop :=
    ∀ p : ℤ × ℤ, ¬ IsZeroLabel d p → Complex.normSq (σ (ov d G p)) = rsicConst d r
  let GhostGaloisInput (d r : ℕ) : Prop :=
    ∃ G : Matrix (Fin d) (Fin d) ℂ, IsGhost d r G ∧ ∃ σ : ℂ →+* ℂ, UnimodularFlip d r G σ
  have omega_eq_xi_sq (d : ℕ) : omega d = xi d ^ 2 := by
    simp only [omega, xi, pow_two, neg_mul_neg]
    rw [← Complex.exp_add]
    congr 1
    ring
  have xi_ne_zero (d : ℕ) : xi d ≠ 0 :=
    neg_ne_zero.mpr (Complex.exp_ne_zero _)
  have fin_ext_of_label {d : ℕ} [NeZero d] {i j : Fin d}
      (h : ((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d)) : i = j := by
    have hv : (ZMod.val ((i : ℕ) : ZMod d)) = (ZMod.val ((j : ℕ) : ZMod d)) := by
      rw [h]
    rw [ZMod.val_cast_of_lt i.isLt, ZMod.val_cast_of_lt j.isLt] at hv
    exact Fin.val_injective hv
  have exists_sub_of_label {d : ℕ} {i j : ℕ} {a : ℤ}
      (h : ((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + (a : ZMod d)) :
      ∃ t : ℤ, (i : ℤ) = (j : ℤ) + a + (d : ℤ) * t := by
    have h' : (((i : ℤ) - (j : ℤ) - a : ℤ) : ZMod d) = 0 := by
      push_cast
      rw [h]
      ring
    obtain ⟨t, ht⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h'
    exact ⟨t, by linear_combination ht⟩
  have omega_pow_d_of_ne_zero (d : ℕ) (hd : d ≠ 0) : omega d ^ (d : ℕ) = 1 := by
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
    simp only [omega]
    rw [← Complex.exp_nat_mul, mul_comm, div_mul_cancel₀ _ hd']
    exact Complex.exp_two_pi_mul_I
  have xi_zpow_two_mul_d (d : ℕ) : xi d ^ ((2 * d : ℕ) : ℤ) = 1 := by
    by_cases hd : d = 0
    · simp [hd]
    · rw [zpow_natCast, pow_mul, ← omega_eq_xi_sq]
      exact omega_pow_d_of_ne_zero d hd
  have omega_zpow (d : ℕ) (z : ℤ) : omega d ^ z = xi d ^ (2 * z) := by
    rw [omega_eq_xi_sq]
    exact (zpow_mul (xi d) 2 z).symm
  have xi_zpow_eq_of_dvd {d : ℕ} {e e' : ℤ} (h : ((2 * d : ℕ) : ℤ) ∣ (e - e')) :
      xi d ^ e = xi d ^ e' := by
    obtain ⟨n, hn⟩ := h
    have he : e = e' + ((2 * d : ℕ) : ℤ) * n := by linear_combination hn
    rw [he, zpow_add₀ (xi_ne_zero d), _root_.zpow_mul, xi_zpow_two_mul_d, _root_.one_zpow,
      mul_one]
  have star_xi (d : ℕ) : star (xi d) = (xi d)⁻¹ := by
    have hc : (starRingEnd ℂ) (Real.pi * Complex.I / (d : ℂ)) =
        -(Real.pi * Complex.I / (d : ℂ)) := by
      have hd : (starRingEnd ℂ) ((d : ℕ) : ℂ) = ((d : ℕ) : ℂ) := by simp
      rw [div_eq_mul_inv, (starRingEnd ℂ).map_mul, Complex.conj_inv, hd,
        (starRingEnd ℂ).map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    have hL : star (xi d) = -Complex.exp (-(Real.pi * Complex.I / (d : ℂ))) := by
      simp only [Complex.star_def, xi, map_neg, ← Complex.exp_conj, hc]
    have hR : (xi d)⁻¹ = -Complex.exp (-(Real.pi * Complex.I / (d : ℂ))) := by
      simp only [xi, ← neg_inv, ← Complex.exp_neg]
    rw [hL, hR]
  have star_omega (d : ℕ) : star (omega d) = (omega d)⁻¹ := by
    rw [omega_eq_xi_sq, star_pow, star_xi, ← inv_pow]
  let finIdx (d : ℕ) [NeZero d] (r : ZMod d) : Fin d :=
    ⟨ZMod.val r, ZMod.val_lt r⟩
  have label_finIdx (d : ℕ) [NeZero d] (r : ZMod d) : ((finIdx d r : ℕ) : ZMod d) = r := by
    have h1 : (finIdx d r : ℕ) < d := ZMod.val_lt r
    refine ZMod.val_injective d ?_
    rw [ZMod.val_cast_of_lt h1] <;> rfl
  have sum_label_single (d : ℕ) [NeZero d] (F : Fin d → ℂ) (r : ZMod d) :
      ∑ k : Fin d, (if ((k : ℕ) : ZMod d) = r then F k else 0) = F (finIdx d r) := by
    have h : ∑ k : Fin d, (if ((k : ℕ) : ZMod d) = r then F k else 0)
        = (if ((finIdx d r : ℕ) : ZMod d) = r then F (finIdx d r) else 0) :=
      Fintype.sum_eq_single
        (f := fun k : Fin d => if ((k : ℕ) : ZMod d) = r then F k else 0)
        (finIdx d r) (by
          intro k hk
          rw [if_neg]
          intro hcon
          exact hk (fin_ext_of_label (hcon.trans (label_finIdx d r).symm)))
    rwa [if_pos (label_finIdx d r)] at h
  have D_zero {d : ℕ} : D d (0, 0) = 1 := by
    ext i j
    by_cases hd : d = 0
    · exact absurd i.isLt (by omega)
    haveI : NeZero d := ⟨hd⟩
    have hD : (D d (0, 0)) i j = if ((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) then 1 else 0 := by
      simp only [displacement_entry]
      push_cast
      simp
    rw [hD, Matrix.one_apply]
    by_cases h : ((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d)
    · simp [fin_ext_of_label h]
    · rw [if_neg h, if_neg]
      intro hij
      exact h (by rw [hij])
  have star_zpow (x : ℂ) (z : ℤ) : star (x ^ z) = (star x) ^ z := by
    cases z with
    | ofNat n =>
        show star (x ^ ((n : ℕ) : ℤ)) = (star x) ^ ((n : ℕ) : ℤ)
        rw [zpow_natCast, star_pow, zpow_natCast]
    | negSucc n =>
        rw [zpow_negSucc, Complex.star_def, Complex.conj_inv, ← Complex.star_def, star_pow,
          ← zpow_negSucc]
  have conjTranspose_D {d : ℕ} (p : ℤ × ℤ) : (D d p)ᴴ = D d (-p) := by
    ext i j
    by_cases hd : d = 0
    · exact absurd i.isLt (by omega)
    haveI : NeZero d := ⟨hd⟩
    simp only [Matrix.conjTranspose_apply, displacement_entry]
    push_cast
    rw [show (-p).1 = -(p.1) from rfl, show (-p).2 = -(p.2) from rfl]
    have hnc : ∀ a : ℤ, ((-a : ℤ) : ZMod d) = (-(a : ZMod d)) := fun a => by push_cast; rfl
    rw [hnc]
    by_cases h : ((j : ℕ) : ZMod d) = ((i : ℕ) : ZMod d) + (p.1 : ZMod d)
    · rw [if_pos h, if_pos (show ((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + (-(p.1) : ZMod d) by
        linear_combination -h)]
      obtain ⟨t, ht⟩ := exists_sub_of_label h
      rw [star_mul, star_zpow, star_zpow, star_omega, star_xi, _root_.inv_zpow, _root_.inv_zpow,
        ← _root_.zpow_neg, ← _root_.zpow_neg, omega_zpow, omega_zpow,
        ← zpow_add₀ (xi_ne_zero d), ← zpow_add₀ (xi_ne_zero d)]
      refine xi_zpow_eq_of_dvd ⟨p.2 * t, ?_⟩
      push_cast
      linear_combination 2 * p.2 * ht
    · rw [if_neg h, star_zero, if_neg]
      intro hcon
      exact h (by linear_combination -hcon)
  have D_mul_D {d : ℕ} (p q : ℤ × ℤ) :
      D d p * D d q = xi d ^ (p.2 * q.1 - p.1 * q.2) • D d (p + q) := by
    ext i j
    by_cases hd : d = 0
    · exact absurd i.isLt (by omega)
    haveI : NeZero d := ⟨hd⟩
    simp only [Matrix.mul_apply, displacement_entry, Matrix.smul_apply, smul_eq_mul]
    push_cast
    rw [show (p + q).1 = p.1 + q.1 from rfl, show (p + q).2 = p.2 + q.2 from rfl]
    have h2 : ((p.1 + q.1 : ℤ) : ZMod d) = ((p.1 : ℤ) : ZMod d) + ((q.1 : ℤ) : ZMod d) := by
      rw [Int.cast_add]
    rw [h2]
    by_cases h : ((i : ℕ) : ZMod d) =
        ((j : ℕ) : ZMod d) + (((p.1 : ℤ) : ZMod d) + ((q.1 : ℤ) : ZMod d))
    · rw [if_pos h]
      have key : ∀ k : Fin d,
          (if ((i : ℕ) : ZMod d) = ((k : ℕ) : ZMod d) + (p.1 : ZMod d) then
                xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((k : ℕ) : ℤ)) else 0) *
            (if ((k : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + (q.1 : ZMod d) then
                xi d ^ (q.1 * q.2) * omega d ^ (q.2 * ((j : ℕ) : ℤ)) else 0)
            = (if ((k : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + (q.1 : ZMod d) then
                xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((k : ℕ) : ℤ)) *
                  (xi d ^ (q.1 * q.2) * omega d ^ (q.2 * ((j : ℕ) : ℤ))) else 0) := by
        intro k
        by_cases hk : ((k : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + (q.1 : ZMod d)
        · rw [if_pos hk, if_pos hk, if_pos (show ((i : ℕ) : ZMod d) =
              ((k : ℕ) : ZMod d) + (p.1 : ZMod d) by
              linear_combination h - hk), mul_assoc]
        · rw [if_neg hk, if_neg hk, mul_zero]
      rw [Finset.sum_congr rfl (fun k _ => key k),
        sum_label_single d (fun k => xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((k : ℕ) : ℤ)) *
          (xi d ^ (q.1 * q.2) * omega d ^ (q.2 * ((j : ℕ) : ℤ))))
          (((j : ℕ) : ZMod d) + (q.1 : ZMod d))]
      obtain ⟨t, ht⟩ := exists_sub_of_label (label_finIdx d (((j : ℕ) : ZMod d) + (q.1 : ZMod d)))
      rw [omega_zpow, omega_zpow, omega_zpow]
      simp only [mul_assoc]
      rw [← zpow_add₀ (xi_ne_zero d), ← zpow_add₀ (xi_ne_zero d), ← zpow_add₀ (xi_ne_zero d),
        ← zpow_add₀ (xi_ne_zero d), ← zpow_add₀ (xi_ne_zero d)]
      refine xi_zpow_eq_of_dvd ⟨p.2 * t, ?_⟩
      push_cast
      linear_combination 2 * p.2 * ht
    · rw [if_neg h, mul_zero]
      refine Finset.sum_eq_zero ?_
      intro k _
      by_cases hk : ((k : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + (q.1 : ZMod d)
      · rw [if_pos hk, if_neg (show ¬(((i : ℕ) : ZMod d) = ((k : ℕ) : ZMod d) + (p.1 : ZMod d)) by
          intro hc
          exact h (by linear_combination hc + hk)), zero_mul]
      · rw [if_neg hk, mul_zero]
  have D_mul_conjTranspose_D {d : ℕ} (p : ℤ × ℤ) : D d p * (D d p)ᴴ = 1 := by
    rw [conjTranspose_D, D_mul_D, show (-p).1 = -(p.1) from rfl, show (-p).2 = -(p.2) from rfl,
      show p.2 * (-(p.1)) - p.1 * (-(p.2)) = 0 from by ring,
      show p + -p = ((0 : ℤ), (0 : ℤ)) from (add_neg_cancel p).trans rfl,
      zpow_zero, one_smul, D_zero]
  have D_add_smul {d : ℕ} (p v : ℤ × ℤ) :
      D d (p + (d : ℤ) • v) =
        xi d ^ ((d : ℤ) * (p.1 * v.2 + v.1 * p.2) + (d : ℤ) ^ 2 * (v.1 * v.2)) • D d p := by
    by_cases hd : d = 0
    · subst hd
      ext i j
      exact absurd i.isLt (by omega)
    ext i j
    haveI : NeZero d := ⟨hd⟩
    simp only [displacement_entry, Matrix.smul_apply, smul_eq_mul]
    rw [show (p + (d : ℤ) • v).1 = p.1 + (d : ℤ) * v.1 from rfl,
      show (p + (d : ℤ) • v).2 = p.2 + (d : ℤ) * v.2 from rfl]
    push_cast
    simp only [ZMod.natCast_self, zero_mul, add_zero]
    by_cases h : ((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + (p.1 : ZMod d)
    · rw [if_pos h, if_pos h]
      rw [omega_zpow, omega_zpow, ← zpow_add₀ (xi_ne_zero d), ← zpow_add₀ (xi_ne_zero d),
        ← zpow_add₀ (xi_ne_zero d)]
      refine xi_zpow_eq_of_dvd ⟨v.2 * ((j : ℕ) : ℤ), ?_⟩
      push_cast
      linear_combination (d : ℤ) * v.2 * ((j : ℕ) : ℤ)
    · rw [if_neg h, if_neg h, mul_zero]
  have omega_zpow_dvd (d : ℕ) {z : ℤ} (h : (d : ℤ) ∣ z) : omega d ^ z = 1 := by
    by_cases hd : d = 0
    · subst hd
      have h1 : omega 0 = 1 := by
        rw [omega_formula]
        simp
      rw [h1, _root_.one_zpow]
    · obtain ⟨c, hc⟩ := h
      rw [hc, _root_.zpow_mul, zpow_natCast, omega_pow_d_of_ne_zero d hd, _root_.one_zpow]
  have omega_exp (d : ℕ) (z : ℤ) :
      omega d ^ z = Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (d : ℂ)) := by
    cases z with
    | ofNat n =>
        show omega d ^ ((n : ℕ) : ℤ) = Complex.exp (2 * ↑Real.pi * Complex.I * ((n : ℕ) : ℂ) / ↑d)
        rw [zpow_natCast]
        simp only [omega]
        rw [← Complex.exp_nat_mul]
        congr 1
        ring
    | negSucc n =>
        rw [zpow_negSucc]
        simp only [omega]
        rw [← Complex.exp_nat_mul, ← Complex.exp_neg]
        congr 1
        push_cast
        ring
  have omega_ne_one_of_not_dvd {d : ℕ} [NeZero d] {a : ℤ} (ha : ¬ (d : ℤ) ∣ a) : omega d ^ a ≠ 1 := by
    intro h
    apply ha
    have h1 : Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (d : ℂ)) = 1 := by
      rw [← omega_exp d a, h]
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h1
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
    have h2c : (2 : ℂ) ≠ 0 := by norm_num
    have hπ : ((Real.pi : ℂ)) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero h2c hπ) Complex.I_ne_zero
    have h2 : (2 * Real.pi * Complex.I : ℂ) * (a : ℂ)
        = (2 * Real.pi * Complex.I : ℂ) * ((k : ℂ) * (d : ℂ)) := by
      have h3 := (div_eq_iff hd0).mp hk
      linear_combination h3
    have h4 : (a : ℂ) = ((k * (d : ℕ) : ℤ) : ℂ) := by
      have := mul_left_cancel₀ hpi h2
      push_cast
      push_cast at this
      linear_combination this
    exact ⟨k, (Int.cast_injective h4).trans (mul_comm _ _)⟩
  have sum_omega_pow_eq_zero {d : ℕ} [NeZero d] {a : ℤ} (ha : ¬ (d : ℤ) ∣ a) :
      ∑ i : Fin d, omega d ^ (a * ((i : ℕ) : ℤ)) = 0 := by
    have h1 : omega d ^ a ≠ 1 := omega_ne_one_of_not_dvd ha
    rw [Fin.sum_univ_eq_sum_range (fun k => omega d ^ (a * ((k : ℕ) : ℤ))) d]
    have hterm : ∀ i ∈ Finset.range d, omega d ^ (a * ((i : ℕ) : ℤ)) = (omega d ^ a) ^ i := by
      intro i _
      rw [_root_.zpow_mul, zpow_natCast]
    have h5 : (omega d ^ a) ^ (d : ℕ) = omega d ^ (a * ((d : ℕ) : ℤ)) := by
      rw [← zpow_natCast, ← _root_.zpow_mul]
    rw [Finset.sum_congr rfl (fun i hi => hterm i hi), geom_sum_eq h1, h5, mul_comm,
      omega_zpow_dvd d ⟨a, rfl⟩]
    ring
  have trace_D {d : ℕ} [NeZero d] (p : ℤ × ℤ) :
      (D d p).trace = if IsZeroLabel d p then (d : ℂ) * xi d ^ (p.1 * p.2) else 0 := by
    have htr : (D d p).trace = ∑ i, (D d p) i i := by
      show ∑ i, Matrix.diag (D d p) i = ∑ i, (D d p) i i
      rw [Finset.sum_congr rfl (fun i _ => Matrix.diag_apply (D d p) i)]
    rw [htr]
    by_cases h1 : (d : ℤ) ∣ p.1
    · have hp1 : ((p.1 : ℤ) : ZMod d) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd p.1 d).mpr h1
      have entry : ∀ i : Fin d, (D d p) i i = xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((i : ℕ) : ℤ)) := by
        intro i
        show (if (((i : ℕ) : ℤ) : ZMod d) = (((i : ℕ) : ℤ) : ZMod d) + (p.1 : ZMod d) then
            xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((i : ℕ) : ℤ)) else 0)
          = xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((i : ℕ) : ℤ))
        rw [hp1, add_zero, if_pos rfl]
      rw [Finset.sum_congr rfl (fun i _ => entry i)]
      by_cases h2 : (d : ℤ) ∣ p.2
      · rw [if_pos ⟨h1, h2⟩]
        obtain ⟨c, hc⟩ := h2
        have homega : ∀ i : Fin d, omega d ^ (p.2 * ((i : ℕ) : ℤ)) = 1 := by
          intro i
          exact omega_zpow_dvd d ⟨c * (i : ℕ), by
            push_cast
            linear_combination ((i : ℕ) : ℤ) * hc⟩
        simp_rw [homega, mul_one]
        simp
      · have hmc : ∀ i : Fin d, xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((i : ℕ) : ℤ))
            = omega d ^ (p.2 * ((i : ℕ) : ℤ)) * xi d ^ (p.1 * p.2) := fun _ => mul_comm _ _
        rw [if_neg (fun hc => h2 hc.2), Finset.sum_congr rfl (fun i _ => hmc i),
          ← Finset.sum_mul, sum_omega_pow_eq_zero h2, zero_mul]
    · have hp1 : ¬ (((p.1 : ℤ) : ZMod d) = 0) := fun hc => h1 ((ZMod.intCast_zmod_eq_zero_iff_dvd p.1 d).mp hc)
      have entry : ∀ i : Fin d, (D d p) i i = 0 := by
        intro i
        show (if (((i : ℕ) : ℤ) : ZMod d) = (((i : ℕ) : ℤ) : ZMod d) + (p.1 : ZMod d) then
            xi d ^ (p.1 * p.2) * omega d ^ (p.2 * ((i : ℕ) : ℤ)) else 0) = 0
        rw [if_neg]
        intro h
        exact hp1 (show ((p.1 : ℤ) : ZMod d) = (0 : ZMod d) from by linear_combination -h)
      rw [Finset.sum_congr rfl (fun i _ => entry i), Finset.sum_const_zero, if_neg (fun hc => h1 hc.1)]
  have omega_ne_zero (d : ℕ) : omega d ≠ 0 := by
    show Complex.exp _ ≠ 0
    exact Complex.exp_ne_zero _
  have eq_sum_ov_smul_D {d : ℕ} [NeZero d] (A : Matrix (Fin d) (Fin d) ℂ) :
      A = (d : ℂ)⁻¹ • ∑ p : Fin d × Fin d,
        ov d A (((p.1 : ℕ) : ℤ), ((p.2 : ℕ) : ℤ)) • D d (((p.1 : ℕ) : ℤ), ((p.2 : ℕ) : ℤ)) := by
    ext i j
  
    have hDxy : ∀ x y : Fin d, (D d (((x : ℕ) : ℤ), ((y : ℕ) : ℤ))) i j
        = (if ((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + ((x : ℕ) : ZMod d) then
            xi d ^ (((x : ℕ) : ℤ) * ((y : ℕ) : ℤ)) * omega d ^ (((y : ℕ) : ℤ) * ((j : ℕ) : ℤ))
          else 0) := by
      intro x y
      show (if (((i : ℕ) : ℤ) : ZMod d) = (((j : ℕ) : ℤ) : ZMod d) + (((x : ℕ) : ℤ) : ZMod d) then
          xi d ^ (((x : ℕ) : ℤ) * ((y : ℕ) : ℤ))
            * omega d ^ (((y : ℕ) : ℤ) * ((j : ℕ) : ℤ)) else 0) = _
      push_cast
      rfl
  
    have hov : ∀ a b : Fin d, ov d A (((a : ℕ) : ℤ), ((b : ℕ) : ℤ))
        = xi d ^ (((a : ℕ) : ℤ) * ((b : ℕ) : ℤ))
          * ∑ s : Fin d, omega d ^ (-((b : ℕ) : ℤ) * ((s : ℕ) : ℤ))
            * A s (finIdx d (((s : ℕ) : ZMod d) + (-((a : ℕ) : ℤ) : ZMod d))) := by
      intro a b
      have hDt : (D d (((a : ℕ) : ℤ), ((b : ℕ) : ℤ)))ᴴ
          = D d (-((a : ℕ) : ℤ), -((b : ℕ) : ℤ)) := by
        rw [conjTranspose_D, show (-(((a : ℕ) : ℤ), ((b : ℕ) : ℤ)))
          = (-((a : ℕ) : ℤ), -((b : ℕ) : ℤ)) from rfl]
      show (A * (D d (((a : ℕ) : ℤ), ((b : ℕ) : ℤ)))ᴴ).trace = _
      rw [hDt]
      have h1 : ∀ s : Fin d, Matrix.diag (A * D d (-((a : ℕ) : ℤ), -((b : ℕ) : ℤ))) s
          = xi d ^ (((a : ℕ) : ℤ) * ((b : ℕ) : ℤ))
            * (omega d ^ (-((b : ℕ) : ℤ) * ((s : ℕ) : ℤ))
              * A s (finIdx d (((s : ℕ) : ZMod d) + (-((a : ℕ) : ℤ) : ZMod d)))) := by
        intro s
        rw [Matrix.diag_apply, Matrix.mul_apply]
        have hD : ∀ k : Fin d, (D d (-((a : ℕ) : ℤ), -((b : ℕ) : ℤ))) k s
            = xi d ^ (((a : ℕ) : ℤ) * ((b : ℕ) : ℤ))
              * (omega d ^ (-((b : ℕ) : ℤ) * ((s : ℕ) : ℤ))
                * (if ((k : ℕ) : ZMod d) = ((s : ℕ) : ZMod d) + (-((a : ℕ) : ℤ) : ZMod d) then
                  (1 : ℂ) else 0)) := by
          intro k
          simp only [displacement_entry]
          push_cast
          rw [neg_mul_neg]
          by_cases hc : ((k : ℕ) : ZMod d) = ((s : ℕ) : ZMod d) + (-((a : ℕ) : ZMod d))
          · rw [if_pos hc, if_pos hc, mul_one]
          · rw [if_neg hc, if_neg hc, mul_zero, mul_zero]
        have hpull : ∀ k : Fin d, A s k * (D d (-((a : ℕ) : ℤ), -((b : ℕ) : ℤ))) k s
            = xi d ^ (((a : ℕ) : ℤ) * ((b : ℕ) : ℤ))
              * (omega d ^ (-((b : ℕ) : ℤ) * ((s : ℕ) : ℤ))
                * (if ((k : ℕ) : ZMod d) = ((s : ℕ) : ZMod d) + (-((a : ℕ) : ℤ) : ZMod d) then
                  A s k else 0)) := by
          intro k
          rw [hD k]
          by_cases hc : ((k : ℕ) : ZMod d) = ((s : ℕ) : ZMod d) + (-((a : ℕ) : ℤ) : ZMod d)
          · rw [if_pos hc, if_pos hc, mul_one]
            ring
          · rw [if_neg hc, if_neg hc]
            ring
        rw [Finset.sum_congr rfl (fun k _ => hpull k), ← Finset.mul_sum,
          Finset.sum_congr rfl (fun k _ => by rw [mul_ite, mul_zero]),
          sum_label_single d (fun k => omega d ^ (-((b : ℕ) : ℤ) * ((s : ℕ) : ℤ)) * A s k)
            (((s : ℕ) : ZMod d) + (-((a : ℕ) : ℤ) : ZMod d))]
      show (∑ s, Matrix.diag (A * D d (-((a : ℕ) : ℤ), -((b : ℕ) : ℤ))) s) = _
      rw [Finset.sum_congr rfl (fun s _ => h1 s), ← Finset.mul_sum]
  
    set r : Fin d := finIdx d (((i : ℕ) : ZMod d) - ((j : ℕ) : ZMod d)) with hrdef
    have hr : ((r : ℕ) : ZMod d) = ((i : ℕ) : ZMod d) - ((j : ℕ) : ZMod d) := label_finIdx d _
    have hsum : ∑ p : Fin d × Fin d,
        ov d A (((p.1 : ℕ) : ℤ), ((p.2 : ℕ) : ℤ))
          * (D d (((p.1 : ℕ) : ℤ), ((p.2 : ℕ) : ℤ))) i j = (d : ℂ) * A i j := by
      rw [Fintype.sum_prod_type' (fun x y : Fin d =>
        ov d A (((x : ℕ) : ℤ), ((y : ℕ) : ℤ)) * (D d (((x : ℕ) : ℤ), ((y : ℕ) : ℤ))) i j)]
      have hzero : ∀ x : Fin d, x ≠ r → ∑ y : Fin d,
          (ov d A (((x : ℕ) : ℤ), ((y : ℕ) : ℤ))
            * (D d (((x : ℕ) : ℤ), ((y : ℕ) : ℤ))) i j) = 0 := by
        intro x hx
        refine Finset.sum_eq_zero ?_
        intro y _
        rw [hDxy x y, if_neg (show ¬(((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + ((x : ℕ) : ZMod d)) by
          intro hcon
          exact hx (fin_ext_of_label (show ((x : ℕ) : ZMod d) = ((r : ℕ) : ZMod d) by
            rw [hr]
            linear_combination -hcon))), mul_zero]
      rw [Fintype.sum_eq_single r hzero,
        Finset.sum_congr rfl (fun y _ => by
          rw [hDxy r y, if_pos (show ((i : ℕ) : ZMod d) = ((j : ℕ) : ZMod d) + ((r : ℕ) : ZMod d) by
            linear_combination -hr), hov r y])]
  
      have hph : ∀ y s : Fin d, xi d ^ (((r : ℕ) : ℤ) * ((y : ℕ) : ℤ))
            * (omega d ^ (-((y : ℕ) : ℤ) * ((s : ℕ) : ℤ))
              * (xi d ^ (((r : ℕ) : ℤ) * ((y : ℕ) : ℤ))
                * omega d ^ (((y : ℕ) : ℤ) * ((j : ℕ) : ℤ))))
          = omega d ^ ((((j : ℕ) : ℤ) - ((s : ℕ) : ℤ) + ((r : ℕ) : ℤ)) * ((y : ℕ) : ℤ)) := by
        intro y s
        rw [omega_zpow, omega_zpow, omega_zpow,
          ← zpow_add₀ (xi_ne_zero d), ← zpow_add₀ (xi_ne_zero d), ← zpow_add₀ (xi_ne_zero d)]
        refine xi_zpow_eq_of_dvd (⟨0, ?_⟩ : ((2 * d : ℕ) : ℤ) ∣ _)
        push_cast
        ring
      have htaux : ∀ y s : Fin d,
          (xi d ^ (((r : ℕ) : ℤ) * ((y : ℕ) : ℤ))
              * (omega d ^ (-((y : ℕ) : ℤ) * ((s : ℕ) : ℤ))
                * A s (finIdx d (((s : ℕ) : ZMod d) + (-((r : ℕ) : ℤ) : ZMod d)))))
            * (xi d ^ (((r : ℕ) : ℤ) * ((y : ℕ) : ℤ))
              * omega d ^ (((y : ℕ) : ℤ) * ((j : ℕ) : ℤ)))
          = omega d ^ ((((j : ℕ) : ℤ) - ((s : ℕ) : ℤ) + ((r : ℕ) : ℤ)) * ((y : ℕ) : ℤ))
            * A s (finIdx d (((s : ℕ) : ZMod d) + (-((r : ℕ) : ℤ) : ZMod d))) := by
        intro y s
        rw [mul_assoc,
          mul_right_comm (omega d ^ (-((y : ℕ) : ℤ) * ((s : ℕ) : ℤ)))
            (A s (finIdx d (((s : ℕ) : ZMod d) + (-((r : ℕ) : ℤ) : ZMod d))))
            (xi d ^ (((r : ℕ) : ℤ) * ((y : ℕ) : ℤ))
              * omega d ^ (((y : ℕ) : ℤ) * ((j : ℕ) : ℤ))),
          ← mul_assoc, hph y s]
      have hterm : ∀ y : Fin d,
          (xi d ^ (((r : ℕ) : ℤ) * ((y : ℕ) : ℤ))
              * ∑ s' : Fin d, omega d ^ (-((y : ℕ) : ℤ) * ((s' : ℕ) : ℤ))
                * A s' (finIdx d (((s' : ℕ) : ZMod d) + (-((r : ℕ) : ℤ) : ZMod d))))
            * (xi d ^ (((r : ℕ) : ℤ) * ((y : ℕ) : ℤ))
              * omega d ^ (((y : ℕ) : ℤ) * ((j : ℕ) : ℤ)))
          = ∑ s : Fin d, omega d ^ ((((j : ℕ) : ℤ) - ((s : ℕ) : ℤ) + ((r : ℕ) : ℤ)) * ((y : ℕ) : ℤ))
              * A s (finIdx d (((s : ℕ) : ZMod d) + (-((r : ℕ) : ℤ) : ZMod d))) := by
        intro y
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_congr rfl (fun s _ => htaux y s)]
      rw [Finset.sum_congr rfl (fun y _ => hterm y), Finset.sum_comm]
      have hpull2 : ∀ s : Fin d,
          ∑ y : Fin d, omega d ^ ((((j : ℕ) : ℤ) - ((s : ℕ) : ℤ) + ((r : ℕ) : ℤ)) * ((y : ℕ) : ℤ))
              * A s (finIdx d (((s : ℕ) : ZMod d) + (-((r : ℕ) : ℤ) : ZMod d)))
          = (∑ y : Fin d, omega d ^ ((((j : ℕ) : ℤ) - ((s : ℕ) : ℤ) + ((r : ℕ) : ℤ)) * ((y : ℕ) : ℤ)))
            * A s (finIdx d (((s : ℕ) : ZMod d) + (-((r : ℕ) : ℤ) : ZMod d))) :=
        fun s => (Finset.sum_mul _ _ _).symm
      rw [Finset.sum_congr rfl (fun s _ => hpull2 s)]
  
      have hinner : ∀ s : Fin d, ∑ y : Fin d,
          omega d ^ ((((j : ℕ) : ℤ) - ((s : ℕ) : ℤ) + ((r : ℕ) : ℤ)) * ((y : ℕ) : ℤ))
          = if s = i then (d : ℂ) else 0 := by
        intro s
        by_cases hs : s = i
        · rw [hs]
          have hdvd : (d : ℤ) ∣ (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) + ((r : ℕ) : ℤ)) := by
            rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
            push_cast
            rw [hr]
            ring
          rw [Finset.sum_congr rfl (fun y _ => omega_zpow_dvd d
            (dvd_mul_of_dvd_left hdvd _))]
          simp
        · have hnd : ¬((d : ℤ) ∣ (((j : ℕ) : ℤ) - ((s : ℕ) : ℤ) + ((r : ℕ) : ℤ))) := by
            intro hc
            have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc
            push_cast at h0
            rw [hr] at h0
            exact hs (fin_ext_of_label (show ((s : ℕ) : ZMod d) = ((i : ℕ) : ZMod d) by
              linear_combination -h0))
          rw [sum_omega_pow_eq_zero hnd, if_neg hs]
      rw [Finset.sum_congr rfl (fun s _ => by rw [hinner s, ite_mul, zero_mul])]
      rw [Fintype.sum_eq_single i (fun s hs => by rw [if_neg hs]),
        if_pos rfl]
      have hkj : finIdx d (((i : ℕ) : ZMod d) + (-((r : ℕ) : ℤ) : ZMod d)) = j :=
        fin_ext_of_label (show ((j : ℕ) : ZMod d)
            = ((finIdx d (((i : ℕ) : ZMod d) + (-((r : ℕ) : ℤ) : ZMod d)) : ℕ) : ZMod d) from by
          rw [label_finIdx]
          push_cast
          linear_combination hr).symm
      rw [hkj]
  
    simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    rw [hsum, inv_mul_cancel_left₀ (by exact_mod_cast (NeZero.ne d) : (d : ℂ) ≠ 0)]
  have exists_map_D {d : ℕ} [NeZero d] (σ : ℂ →+* ℂ) :
      ∃ k : ℤ, IsCoprime k (d : ℤ) ∧ ∀ p : ℤ × ℤ, (D d p).map σ = D d (p.1, k * p.2) := by
    have h2d : (2 * d : ℕ) ≠ 0 := fun h => NeZero.ne d (by simpa using h)
    have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / ((2 * d : ℕ) : ℂ))) (2 * d) :=
      Complex.isPrimitiveRoot_exp (2 * d) h2d
    have he : Complex.exp (2 * Real.pi * Complex.I / ((2 * d : ℕ) : ℂ))
        = Complex.exp (Real.pi * Complex.I / d) := by
      congr 1
      have hd : ((d : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
      field_simp [hd]
      push_cast
      ring
    have hinj : Function.Injective σ := RingHom.injective σ
    have hσprim : IsPrimitiveRoot (σ (Complex.exp (2 * Real.pi * Complex.I / ((2 * d : ℕ) : ℂ)))) (2 * d) :=
      (IsPrimitiveRoot.map_iff_of_injective (f := σ.toMonoidHom) hinj).mpr hprim
    obtain ⟨m, _, hm⟩ := IsPrimitiveRoot.eq_pow_of_pow_eq_one hprim hσprim.pow_eq_one
    have hcop : Nat.Coprime m (2 * d) := by
      refine (hprim.pow_iff_coprime (Nat.pos_of_ne_zero h2d) m).mp ?_
      rw [hm]
      exact hσprim
    have h2m : ¬ 2 ∣ m := by
      intro h2m
      have hg : 2 ∣ Nat.gcd m (2 * d) := Nat.dvd_gcd h2m ⟨d, by ring⟩
      rw [show Nat.gcd m (2 * d) = 1 from hcop] at hg
      norm_num at hg
    have hneg1 : (-1 : ℂ) ^ m = -1 := by
      rcases Nat.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
      · exact absurd (by rw [ht]; exact ⟨t, by ring⟩) h2m
      · exact Odd.neg_one_pow ⟨t, ht⟩
    refine ⟨(m : ℤ), (Nat.Coprime.coprime_mul_left_right hcop).cast, ?_⟩
    intro p
    ext i j
    simp only [Matrix.map_apply, displacement_entry]
    by_cases hc : (((i : ℕ) : ℤ) : ZMod d) = (((j : ℕ) : ℤ) : ZMod d) + (p.1 : ZMod d)
    · rw [if_pos hc, if_pos hc]
      have hw : Complex.exp (2 * Real.pi * Complex.I / d)
          = Complex.exp (2 * Real.pi * Complex.I / ((2 * d : ℕ) : ℂ)) ^ (2 : ℕ) := by
        rw [← Complex.exp_nat_mul]
        congr 1
        have hd : ((d : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
        field_simp [hd]
        push_cast
        ring
      have hx : σ (xi d) = xi d ^ ((m : ℕ) : ℤ) := by
        show σ (-Complex.exp (Real.pi * Complex.I / d))
          = (-Complex.exp (Real.pi * Complex.I / d)) ^ ((m : ℕ) : ℤ)
        rw [map_neg, ← he, ← hm]
        rw [show (-Complex.exp (2 * Real.pi * Complex.I / ((2 * d : ℕ) : ℂ))) ^ ((m : ℕ) : ℤ)
            = (-1 : ℂ) * Complex.exp (2 * Real.pi * Complex.I / ((2 * d : ℕ) : ℂ)) ^ m from by
          rw [neg_eq_neg_one_mul, mul_zpow, zpow_natCast, zpow_natCast, hneg1]]
        rw [neg_one_mul]
      have hw' : σ (omega d) = omega d ^ ((m : ℕ) : ℤ) := by
        show σ (Complex.exp (2 * Real.pi * Complex.I / d))
          = Complex.exp (2 * Real.pi * Complex.I / d) ^ ((m : ℕ) : ℤ)
        rw [hw, map_pow, ← hm, ← _root_.pow_mul, _root_.zpow_natCast, ← _root_.pow_mul,
          Nat.mul_comm m 2]
      rw [map_mul, map_zpow₀ σ (xi d) (p.1 * p.2), map_zpow₀ σ (omega d) (p.2 * ((j : ℕ) : ℤ)),
        hx, hw', ← _root_.zpow_mul, ← _root_.zpow_mul]
      congr 1
      · congr 1
        ring
      · congr 1
        ring
    · rw [if_neg hc, if_neg hc]
      exact map_zero σ
  have galois_xi_normSq (d : ℕ) (n : ℤ) :
      Complex.normSq (xi d ^ n) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_zpow]
    have h : ‖xi d‖ = 1 := by
      simp [xi, Complex.norm_exp]
    rw [h]
    simp
  have map_rsicConst (d r : ℕ) (σ : ℂ →+* ℂ) :
      σ (rsicConst d r : ℂ) = (rsicConst d r : ℂ) := by
    simp [rsicConst, map_div₀]
  have rsicConst_pos {d r : ℕ} (hd : 2 ≤ d) (hr : 1 ≤ r) (hrd : r < d) :
      0 < rsicConst d r := by
    have hd' : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
    have hr' : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have hrd' : (r : ℝ) < d := by exact_mod_cast hrd
    unfold rsicConst
    exact div_pos (mul_pos hr' (sub_pos.mpr hrd')) (by nlinarith)
  have galois_ov_adj {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
      (p : ℤ × ℤ) : ov d Aᴴ p = star (ov d A (-p)) := by
    simp only [ov, ← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
    rw [conjTranspose_D, trace_mul_comm]
  have map_ov_of_map_D {d : ℕ} (σ : ℂ →+* ℂ) (k : ℤ)
      (hD : ∀ p : ℤ × ℤ, (D d p).map σ = D d (p.1, k * p.2))
      (A : Matrix (Fin d) (Fin d) ℂ) (p : ℤ × ℤ) :
      σ (ov d A p) = ov d (A.map σ) (p.1, k * p.2) := by
    simp only [ov, conjTranspose_D, AddMonoidHom.map_trace, Matrix.map_mul]
    rw [hD]
    congr 2
    simp
  have galois_ov_phase {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
      {p q : ℤ × ℤ} {z : ℂ} (h : D d q = z • D d p) :
      ov d A q = star z * ov d A p := by
    simp only [ov, h, conjTranspose_smul, Matrix.mul_smul, trace_smul, smul_eq_mul]
  have galois_lift {d : ℕ} {k : ℤ} (hk : IsCoprime k (d : ℤ))
      (q : ℤ × ℤ) : ∃ p v : ℤ × ℤ,
        q = (p.1, k * p.2) + (d : ℤ) • v ∧
        (IsZeroLabel d p → IsZeroLabel d q) := by
    obtain ⟨a, b, hab⟩ := hk
    refine ⟨(q.1, a * q.2), (0, b * q.2), ?_, ?_⟩
    · apply Prod.ext
      · change q.1 = q.1 + (d : ℤ) * 0
        simp
      · change q.2 = k * (a * q.2) + (d : ℤ) * (b * q.2)
        calc
          q.2 = (a * k + b * (d : ℤ)) * q.2 := by rw [hab, one_mul]
          _ = k * (a * q.2) + (d : ℤ) * (b * q.2) := by ring
    · rintro ⟨h₁, h₂⟩
      refine ⟨h₁, ?_⟩
      have heq : q.2 = k * (a * q.2) + (d : ℤ) * (b * q.2) := by
        calc
          q.2 = (a * k + b * (d : ℤ)) * q.2 := by rw [hab, one_mul]
          _ = _ := by ring
      rw [heq]
      exact dvd_add (dvd_mul_of_dvd_right h₂ k) (dvd_mul_right _ _)
  have galois_eq_of_ov {d : ℕ} [NeZero d]
      {A B : Matrix (Fin d) (Fin d) ℂ}
      (h : ∀ p : Fin d × Fin d,
        ov d A (((p.1 : ℕ) : ℤ), ((p.2 : ℕ) : ℤ)) =
        ov d B (((p.1 : ℕ) : ℤ), ((p.2 : ℕ) : ℤ))) : A = B := by
    rw [eq_sum_ov_smul_D A, eq_sum_ov_smul_D B]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    rw [h p]
  have map_fiducial_of_ghost_flip {d r : ℕ} (hd : 2 ≤ d) (hr : 1 ≤ r)
      (hrd : r < d) {G : Matrix (Fin d) (Fin d) ℂ} (hG : IsGhost d r G)
      {σ : ℂ →+* ℂ} (hσ : UnimodularFlip d r G σ) :
      (G.map σ).IsHermitian ∧
      G.map σ * G.map σ = G.map σ ∧
      (G.map σ).trace = r ∧
      ∀ q : ℤ × ℤ, ¬ IsZeroLabel d q →
        Complex.normSq (ov d (G.map σ) q) = rsicConst d r := by
    have : NeZero d := ⟨by omega⟩
    obtain ⟨k, hk, hD⟩ := exists_map_D (d := d) σ
    let P := G.map σ
    have ht : P.trace = r := by
      change (G.map σ).trace = r
      rw [← AddMonoidHom.map_trace, hG.2.1, map_natCast]
    have hm (p : ℤ × ℤ) :
        σ (ov d G p) = ov d P (p.1, k * p.2) := map_ov_of_map_D σ k hD G p
    have hcpos := rsicConst_pos hd hr hrd
    have hconj (p : ℤ × ℤ) (hp : ¬ IsZeroLabel d p) :
        ov d P (-(p.1, k * p.2)) = star (ov d P (p.1, k * p.2)) := by
      have hnonzero : σ (ov d G p) ≠ 0 := by
        intro hz
        have hh := hσ p hp
        rw [hz, Complex.normSq_zero] at hh
        linarith
      have hprod : σ (ov d G p) * σ (ov d G (-p)) = (rsicConst d r : ℂ) := by
        rw [← map_mul, hG.2.2 p hp, map_rsicConst]
      have hnorm : σ (ov d G p) * star (σ (ov d G p)) = (rsicConst d r : ℂ) := by
        change σ (ov d G p) * starRingEnd ℂ (σ (ov d G p)) = _
        rw [Complex.mul_conj, hσ p hp]
      have hh := mul_left_cancel₀ hnonzero (hprod.trans hnorm.symm)
      rw [hm p, hm (-p)] at hh
      simpa using hh
    have hmod (q : ℤ × ℤ) (hq : ¬ IsZeroLabel d q) :
        Complex.normSq (ov d P q) = rsicConst d r := by
      obtain ⟨p, v, hqeq, hpq⟩ := galois_lift hk q
      have hp : ¬ IsZeroLabel d p := fun hp => hq (hpq hp)
      have hphase : D d q =
          xi d ^ ((d : ℤ) * (p.1 * v.2 + v.1 * (k * p.2)) +
            (d : ℤ) ^ 2 * (v.1 * v.2)) • D d (p.1, k * p.2) := by
        rw [hqeq, D_add_smul]
      rw [galois_ov_phase P hphase, Complex.normSq_mul, Complex.star_def, Complex.normSq_conj,
        galois_xi_normSq, one_mul, ← hm p]
      exact hσ p hp
    have hH : P.IsHermitian := by
      apply galois_eq_of_ov
      intro s
      let q : ℤ × ℤ := (((s.1 : ℕ) : ℤ), ((s.2 : ℕ) : ℤ))
      change ov d Pᴴ q = ov d P q
      by_cases hq : IsZeroLabel d q
      · have hqzero : q = (0, 0) := by
          have h₁ : (s.1 : ℤ) = 0 := by
            have hlt : (s.1 : ℤ) < d := by exact_mod_cast s.1.isLt
            have hnn : (0 : ℤ) ≤ s.1 := by positivity
            exact Int.eq_zero_of_dvd_of_nonneg_of_lt hnn hlt hq.1
          have h₂ : (s.2 : ℤ) = 0 := by
            have hlt : (s.2 : ℤ) < d := by exact_mod_cast s.2.isLt
            have hnn : (0 : ℤ) ≤ s.2 := by positivity
            exact Int.eq_zero_of_dvd_of_nonneg_of_lt hnn hlt hq.2
          exact Prod.ext h₁ h₂
        simp [hqzero, ov, D_zero, trace_conjTranspose, ht]
      · obtain ⟨p, v, hqeq, hpq⟩ := galois_lift hk q
        have hp : ¬ IsZeroLabel d p := fun hp => hq (hpq hp)
        have hphase : D d q =
            xi d ^ ((d : ℤ) * (p.1 * v.2 + v.1 * (k * p.2)) +
              (d : ℤ) ^ 2 * (v.1 * v.2)) • D d (p.1, k * p.2) := by
          rw [hqeq, D_add_smul]
        rw [galois_ov_phase Pᴴ hphase, galois_ov_phase P hphase,
          galois_ov_adj, hconj p hp, star_star]
    refine ⟨hH, ?_, ht, hmod⟩
    rw [← Matrix.map_mul, hG.1]
  let valueAt {M : ℕ} (F : ((ZMod M × ZMod M) → ℂ)) (i j : ℤ) : ℂ := F (i, j)
  let epsilon (M : ℕ) : ℝ :=
    ((M : ℝ) - 1 + Real.sqrt (((M : ℝ) - 1) ^ 2 - 4)) / 2
  let sqrtEpsilon (M : ℕ) : ℂ := (Real.sqrt (epsilon M) : ℂ)
  let denominator (M : ℕ) : ℂ := sqrtEpsilon M + (sqrtEpsilon M)⁻¹
  have denominator_formula (M : ℕ) : denominator M = sqrtEpsilon M + (sqrtEpsilon M)⁻¹ := rfl
  let convolutionScalar (M : ℕ) : ℂ := (Real.sqrt ((M : ℝ) - 3) : ℂ)
  let e (M : ℕ) (n : ℤ) : ℂ :=
    Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) / (M : ℂ))
  have e_formula (M : ℕ) (n : ℤ) : e M n =
    Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) / (M : ℂ)) := rfl
  let quadraticForm (i j : ℤ) : ℤ := i ^ 2 - i * j + j ^ 2
  let gaussianLift (M : ℕ) (i j : ℤ) : ℂ := e M (quadraticForm i j)
  have gaussianLift_formula (M : ℕ) (i j : ℤ) : gaussianLift M i j = e M (quadraticForm i j) := rfl
  let gaussian (M : ℕ) (h : (ZMod M × ZMod M)) : ℂ :=
    gaussianLift M h.1.val h.2.val
  let theta (M : ℕ) (i j : ℤ) : ℂ :=
    (-1 : ℂ) ^ (i + j + i * j) *
      Complex.exp (Real.pi * Complex.I * (quadraticForm i j : ℂ) / (M : ℂ))
  have theta_formula (M : ℕ) (i j : ℤ) : theta M i j =
    (-1 : ℂ) ^ (i + j + i * j) *
      Complex.exp (Real.pi * Complex.I * (quadraticForm i j : ℂ) / (M : ℂ)) := rfl
  let toWH (i j : ℤ) : ℤ × ℤ := (-j, i)
  let fromWH (p : ℤ × ℤ) : ℤ × ℤ := (p.2, -p.1)
  let convolution (M : ℕ) (F : ((ZMod M × ZMod M) → ℂ)) (r s : ℤ) : ℂ :=
    (M : ℂ)⁻¹ * ∑ i : Fin M, ∑ j : Fin M,
      valueAt F i j * valueAt F (r - i) (s - j) * gaussianLift M i j *
        e M (-(i : ℤ) * r + (j : ℤ) * (r - s))
  have convolution_formula (M : ℕ) (F : ((ZMod M × ZMod M) → ℂ)) (r s : ℤ) : convolution M F r s =
    (M : ℂ)⁻¹ * ∑ i : Fin M, ∑ j : Fin M,
      valueAt F i j * valueAt F (r - i) (s - j) * gaussianLift M i j *
        e M (-(i : ℤ) * r + (j : ℤ) * (r - s)) := rfl
  let P (M : ℕ) (F : ((ZMod M × ZMod M) → ℂ)) : Matrix (Fin M) (Fin M) ℂ :=
    (M : ℂ)⁻¹ • ∑ i : Fin M, ∑ j : Fin M,
      (theta M i j * valueAt F i j) • D M (toWH i j)
  have P_formula (M : ℕ) (F : ((ZMod M × ZMod M) → ℂ)) : P M F =
    (M : ℂ)⁻¹ • ∑ i : Fin M, ∑ j : Fin M,
      (theta M i j * valueAt F i j) • D M (toWH i j) := rfl
  let ghostProjector (M : ℕ) (F : ((ZMod M × ZMod M) → ℂ)) : Matrix (Fin M) (Fin M) ℂ :=
    (denominator M)⁻¹ • (sqrtEpsilon M • (1 : Matrix (Fin M) (Fin M) ℂ) - P M F)
  let coefficient (M : ℕ) (F : ((ZMod M × ZMod M) → ℂ)) (i j : ℤ) : ℂ :=
    -(theta M i j * valueAt F i j) / denominator M
  have coefficient_formula (M : ℕ) (F : ((ZMod M × ZMod M) → ℂ)) (i j : ℤ) : coefficient M F i j =
    -(theta M i j * valueAt F i j) / denominator M := rfl
  let RWConvolutionInput (M : ℕ) (F : ((ZMod M × ZMod M) → ℂ)) : Prop :=
    F 0 = sqrtEpsilon M ^ 3 ∧ (∀ h : (ZMod M × ZMod M), h ≠ 0 → F h * F (-h) = (gaussian M h)⁻¹) ∧
    ∀ h : (ZMod M × ZMod M), convolution M F h.1.val h.2.val =
      convolutionScalar M * F h + if h = 0 then (M : ℂ) else 0
  let RWUnitCircleInput (M : ℕ) (F : ((ZMod M × ZMod M) → ℂ)) (τ : ℂ →+* ℂ) : Prop := ∀ h : (ZMod M × ZMod M), h ≠ 0 → ‖τ (F h)‖ = 1
  have epsilon_gt_one {M : ℕ} (hM : 4 ≤ M) : 1 < epsilon M := by
    have hM4 : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hs := Real.sqrt_nonneg (((M : ℝ) - 1) ^ 2 - 4)
    unfold epsilon
    rw [one_lt_div (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have epsilon_quadratic {M : ℕ} (hM : 4 ≤ M) :
      epsilon M ^ 2 - ((M : ℝ) - 1) * epsilon M + 1 = 0 := by
    have hM4 : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hnng : (0 : ℝ) ≤ ((M : ℝ) - 1) ^ 2 - 4 := by nlinarith
    have hs := Real.sq_sqrt hnng
    unfold epsilon
    field_simp
    nlinarith
  have sqrtEpsilon_ne_zero {M : ℕ} (hM : 4 ≤ M) : sqrtEpsilon M ≠ 0 := by
    have h1 : (0 : ℝ) < epsilon M := lt_trans (by norm_num) (epsilon_gt_one hM)
    intro h
    apply absurd (Real.sqrt_eq_zero'.mp (Complex.ofReal_eq_zero.mp h))
    exact (not_le.mpr h1)
  have sqrtEpsilon_sub_inv {M : ℕ} (hM : 4 ≤ M) :
      sqrtEpsilon M - (sqrtEpsilon M)⁻¹ = convolutionScalar M := by
    have hε : (1 : ℝ) < epsilon M := epsilon_gt_one hM
    have hε0 : (0 : ℝ) < epsilon M := by linarith
    have hw2 : Real.sqrt (epsilon M) ^ 2 = epsilon M := Real.sq_sqrt (le_of_lt hε0)
    have hw1 : (1 : ℝ) ≤ Real.sqrt (epsilon M) :=
      (Real.le_sqrt (by norm_num) (by linarith)).mpr (by nlinarith)
    have h4 : Real.sqrt (epsilon M) ^ 4 = (epsilon M) ^ 2 := by
      rw [show ((4 : ℕ)) = 2 * 2 from rfl, pow_mul, hw2]
    have hwq : Real.sqrt (epsilon M) ^ 4 - ((M : ℝ) - 1) * Real.sqrt (epsilon M) ^ 2 + 1 = 0 := by
      rw [h4, hw2]
      exact epsilon_quadratic hM
    have key : (Real.sqrt (epsilon M) - (Real.sqrt (epsilon M))⁻¹) ^ 2 = ((M : ℝ) - 3) := by
      have hwpos : (0 : ℝ) < Real.sqrt (epsilon M) := by linarith
      field_simp
      nlinarith
    have hnn : (0 : ℝ) ≤ Real.sqrt (epsilon M) - (Real.sqrt (epsilon M))⁻¹ := by
      have hwpos : (0 : ℝ) < Real.sqrt (epsilon M) := by linarith
      by_contra hc
      push_neg at hc
      have h8 := mul_lt_mul_of_pos_right hc hwpos
      simp only [zero_mul] at h8
      rw [mul_comm, mul_sub, mul_inv_cancel₀ (ne_of_gt hwpos)] at h8
      nlinarith
    have hfin : Real.sqrt (((M : ℝ) - 3)) = Real.sqrt (epsilon M) - (Real.sqrt (epsilon M))⁻¹ :=
      (Real.sqrt_eq_iff_mul_self_eq (by nlinarith) hnn).mpr (by rw [← pow_two]; exact key.symm)
    have h2 : (Real.sqrt ((M : ℝ) - 3) : ℂ)
        = (Real.sqrt (epsilon M) : ℂ) - ((Real.sqrt (epsilon M) : ℝ) : ℂ)⁻¹ := by
      rw [hfin, Complex.ofReal_sub, Complex.ofReal_inv]
    simp only [sqrtEpsilon, convolutionScalar]
    exact h2.symm
  have sqrtEpsilon_cube {M : ℕ} (hM : 4 ≤ M) :
      sqrtEpsilon M ^ 3 = ((M : ℂ) - 1) * sqrtEpsilon M - (sqrtEpsilon M)⁻¹ := by
    have hν : sqrtEpsilon M ≠ 0 := sqrtEpsilon_ne_zero hM
    have hε0 : (0 : ℝ) < epsilon M := lt_trans (by norm_num) (epsilon_gt_one hM)
    have h2 : sqrtEpsilon M * sqrtEpsilon M = (epsilon M : ℂ) := by
      simp only [sqrtEpsilon]
      exact_mod_cast Real.mul_self_sqrt (le_of_lt hε0)
    have hq : epsilon M * epsilon M - ((M : ℝ) - 1) * epsilon M + 1 = 0 := by
      have h := epsilon_quadratic hM
      linear_combination h
    have hq2 : (epsilon M : ℂ) * (epsilon M : ℂ) - ((M : ℂ) - 1) * (epsilon M : ℂ) + 1 = 0 := by
      exact_mod_cast hq
    apply mul_right_cancel₀ hν
    have hν3 : sqrtEpsilon M ^ 3 * sqrtEpsilon M = sqrtEpsilon M ^ 4 := by
      rw [pow_succ, show ((4 : ℕ)) = 2 + 2 from rfl, pow_add, pow_two]
      ring
    have hq3 : sqrtEpsilon M ^ 4 - ((M : ℂ) - 1) * sqrtEpsilon M ^ 2 + 1 = 0 := by
      rw [show ((4 : ℕ)) = 2 + 2 from rfl, pow_add, pow_two, h2]
      exact hq2
    rw [hν3, sub_mul, mul_assoc, inv_mul_cancel₀ hν]
    linear_combination hq3
  have denominator_eq_sqrt {M : ℕ} (hM : 4 ≤ M) :
      denominator M = (Real.sqrt ((M : ℝ) + 1) : ℂ) := by
    have hε : (1 : ℝ) < epsilon M := epsilon_gt_one hM
    have hε0 : (0 : ℝ) < epsilon M := by linarith
    have hw2 : Real.sqrt (epsilon M) ^ 2 = epsilon M := Real.sq_sqrt (le_of_lt hε0)
    have hw1 : (1 : ℝ) ≤ Real.sqrt (epsilon M) :=
      (Real.le_sqrt (by norm_num) (by linarith)).mpr (by nlinarith)
    have h4 : Real.sqrt (epsilon M) ^ 4 = (epsilon M) ^ 2 := by
      rw [show ((4 : ℕ)) = 2 * 2 from rfl, pow_mul, hw2]
    have hq : epsilon M * epsilon M - ((M : ℝ) - 1) * epsilon M + 1 = 0 := by
      have h := epsilon_quadratic hM
      linear_combination h
    have key : (Real.sqrt (epsilon M) + (Real.sqrt (epsilon M))⁻¹) ^ 2 = ((M : ℝ) + 1) := by
      have hwpos : (0 : ℝ) < Real.sqrt (epsilon M) := by linarith
      field_simp
      nlinarith [hw2]
    have hnn : (0 : ℝ) ≤ Real.sqrt (epsilon M) + (Real.sqrt (epsilon M))⁻¹ := by
      have hwpos : (0 : ℝ) < Real.sqrt (epsilon M) := by linarith
      have := inv_nonneg.mpr (le_of_lt hwpos)
      linarith
    have hfin : Real.sqrt (((M : ℝ) + 1)) = Real.sqrt (epsilon M) + (Real.sqrt (epsilon M))⁻¹ :=
      (Real.sqrt_eq_iff_mul_self_eq (by nlinarith) hnn).mpr (by rw [← pow_two]; exact key.symm)
    have h2 : (Real.sqrt ((M : ℝ) + 1) : ℂ)
        = (Real.sqrt (epsilon M) : ℂ) + ((Real.sqrt (epsilon M) : ℝ) : ℂ)⁻¹ := by
      rw [hfin, Complex.ofReal_add, Complex.ofReal_inv]
    simp only [denominator, sqrtEpsilon]
    exact h2.symm
  have denominator_ne_zero {M : ℕ} (hM : 4 ≤ M) : denominator M ≠ 0 := by
    rw [denominator_eq_sqrt hM]
    intro h
    have h1 : Real.sqrt ((M : ℝ) + 1) = 0 := Complex.ofReal_eq_zero.mp h
    have h2 : ((M : ℝ) + 1) ≤ 0 := Real.sqrt_eq_zero'.mp h1
    have hM4 : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have map_denominator_eq_or_neg {M : ℕ} (hM : 4 ≤ M) (τ : ℂ →+* ℂ) :
      τ (denominator M) = (Real.sqrt ((M : ℝ) + 1) : ℂ) ∨
        τ (denominator M) = -(Real.sqrt ((M : ℝ) + 1) : ℂ) := by
    refine sq_eq_sq_iff_eq_or_eq_neg.mp ?_
    have hn : (0 : ℝ) ≤ ((M : ℝ) + 1) := by
      have hM4 : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      linarith
    have hsq : denominator M ^ 2 = ((M : ℂ) + 1) := by
      rw [denominator_eq_sqrt hM]
      exact_mod_cast Real.sq_sqrt hn
    rw [← map_pow τ _ 2, hsq, map_add, map_natCast, map_one]
    exact_mod_cast (Real.sq_sqrt hn).symm
  have e_eq_omega_zpow (M : ℕ) (n : ℤ) : e M n = omega M ^ n := by
    rw [e_formula, omega_exp]
  have e_eq_of_dvd {M : ℕ} {n n' : ℤ} (h : ((M : ℕ) : ℤ) ∣ n - n') : e M n = e M n' := by
    by_cases hM : M = 0
    · subst hM
      have hn : n = n' := sub_eq_zero.mp (Int.zero_dvd.mp h)
      rw [hn]
    · rw [e_eq_omega_zpow, e_eq_omega_zpow]
      obtain ⟨q, hq⟩ := h
      have hn : n = n' + ((M : ℕ) : ℤ) * q := by linear_combination hq
      rw [hn, zpow_add₀ (omega_ne_zero M), _root_.zpow_mul, zpow_natCast,
        omega_pow_d_of_ne_zero M hM, _root_.one_zpow, mul_one]
  have gaussian_eq_lift {M : ℕ} (hM : 4 ≤ M) (i j : ℤ) :
      gaussian M ((i : ZMod M), (j : ZMod M)) = gaussianLift M i j := by
    have hne : M ≠ 0 := by omega
    haveI : NeZero M := ⟨hne⟩
    have hA : ((M : ℕ) : ℤ) ∣ (((i : ZMod M).val : ℕ) : ℤ) - i := by
      have hv : (((i : ZMod M).val : ℕ) : ℤ) = i % ((M : ℕ) : ℤ) := ZMod.val_intCast i
      refine ⟨-(i / ((M : ℕ) : ℤ)), ?_⟩
      rw [hv]
      linarith [Int.emod_add_mul_ediv i ((M : ℕ) : ℤ)]
    have hB : ((M : ℕ) : ℤ) ∣ (((j : ZMod M).val : ℕ) : ℤ) - j := by
      have hv : (((j : ZMod M).val : ℕ) : ℤ) = j % ((M : ℕ) : ℤ) := ZMod.val_intCast j
      refine ⟨-(j / ((M : ℕ) : ℤ)), ?_⟩
      rw [hv]
      linarith [Int.emod_add_mul_ediv j ((M : ℕ) : ℤ)]
    have hdvd : ((M : ℕ) : ℤ) ∣ quadraticForm (((i : ZMod M).val : ℕ) : ℤ)
        (((j : ZMod M).val : ℕ) : ℤ) - quadraticForm i j := by
      have h1 : quadraticForm (((i : ZMod M).val : ℕ) : ℤ) (((j : ZMod M).val : ℕ) : ℤ)
          - quadraticForm i j
          = ((((i : ZMod M).val : ℕ) : ℤ) - i) * ((((i : ZMod M).val : ℕ) : ℤ) + i)
            - ((((i : ZMod M).val : ℕ) : ℤ) - i) * j
            - (((i : ZMod M).val : ℕ) : ℤ) * ((((j : ZMod M).val : ℕ) : ℤ) - j)
            + ((((j : ZMod M).val : ℕ) : ℤ) - j) * ((((j : ZMod M).val : ℕ) : ℤ) + j) := by
        unfold quadraticForm; ring
      rw [h1]
      exact dvd_add (dvd_sub
        (dvd_sub (dvd_mul_of_dvd_left hA _) (dvd_mul_of_dvd_left hA _))
        (dvd_mul_of_dvd_right hB _))
        (dvd_mul_of_dvd_left hB _)
    unfold gaussian gaussianLift
    exact e_eq_of_dvd hdvd
  have negOne_zpow_eq_of_two_dvd {e e' : ℤ} (h : (2 : ℤ) ∣ e - e') :
      (-1 : ℂ) ^ e = (-1 : ℂ) ^ e' := by
    obtain ⟨n, hn⟩ := h
    have he : e = e' + 2 * n := by linear_combination hn
    have h2 : (-1 : ℂ) ^ (2 : ℤ) = 1 := by norm_num
    rw [he, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), _root_.zpow_mul, h2, _root_.one_zpow, mul_one]
  have xi_zpow_exp (M : ℕ) (z : ℤ) :
      xi M ^ z = (-1 : ℂ) ^ z *
        Complex.exp (Real.pi * Complex.I * (z : ℂ) / (M : ℂ)) := by
    have hx : xi M = (-1 : ℂ) * Complex.exp (Real.pi * Complex.I / (M : ℂ)) := by
      rw [xi_formula]
      ring
    have key : Complex.exp (Real.pi * Complex.I * (z : ℂ) / (M : ℂ))
        = Complex.exp (Real.pi * Complex.I / (M : ℂ)) ^ z := by
      rw [← Complex.exp_int_mul]
      congr 1
      ring
    rw [hx, mul_zpow, key]
  have theta_eq_xi_zpow (M : ℕ) (i j : ℤ) :
      theta M i j = xi M ^ quadraticForm i j := by
    have h1 : (2 : ℤ) ∣ i - i * i := by
      obtain ⟨q, hq⟩ := Int.two_dvd_mul_add_one i
      exact ⟨-q + i, by linear_combination -hq⟩
    have h2 : (2 : ℤ) ∣ j - j * j := by
      obtain ⟨q, hq⟩ := Int.two_dvd_mul_add_one j
      exact ⟨-q + j, by linear_combination -hq⟩
    have hexp : (i + j + i * j) - quadraticForm i j
        = (i - i * i) + (j - j * j) + 2 * (i * j) := by
      unfold quadraticForm; ring
    have hpar : (2 : ℤ) ∣ (i + j + i * j) - quadraticForm i j := by
      rw [hexp]
      exact dvd_add (dvd_add h1 h2) (dvd_mul_right (2 : ℤ) (i * j))
    rw [theta_formula, xi_zpow_exp, negOne_zpow_eq_of_two_dvd hpar]
  have theta_neg (M : ℕ) (i j : ℤ) : theta M (-i) (-j) = theta M i j := by
    rw [theta_eq_xi_zpow, theta_eq_xi_zpow]
    congr 1
    unfold quadraticForm
    ring
  have theta_sq (M : ℕ) (i j : ℤ) : theta M i j ^ 2 = gaussianLift M i j := by
    rw [theta_eq_xi_zpow, pow_two, ← zpow_add₀ (xi_ne_zero M)]
    rw [show quadraticForm i j + quadraticForm i j = 2 * quadraticForm i j from by ring]
    rw [← omega_zpow, ← e_eq_omega_zpow, gaussianLift_formula]
  have theta_pow_two_mul {M : ℕ} (hM : 4 ≤ M) (i j : ℤ) :
      theta M i j ^ (2 * M) = 1 := by
    rw [theta_eq_xi_zpow, ← zpow_natCast (xi M ^ quadraticForm i j) (2 * M),
      ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, xi_zpow_two_mul_d, _root_.one_zpow]
  have map_theta_norm {M : ℕ} (hM : 4 ≤ M) (τ : ℂ →+* ℂ) (i j : ℤ) :
      ‖τ (theta M i j)‖ = 1 := by
    have hx : τ (theta M i j) ^ (2 * M) = 1 := by
      rw [← map_pow τ, theta_pow_two_mul hM, map_one]
    have hn : ‖τ (theta M i j)‖ ^ (2 * M) = 1 := by
      rw [← Complex.norm_pow, hx]
      simp
    have hn0 : (2 * M : ℕ) ≠ 0 := by omega
    have key : ∀ a : ℝ, 0 ≤ a → a ^ (2 * M) = 1 → a = 1 := by
      intro a ha h
      rcases lt_trichotomy a 1 with h1 | h1 | h1
      · exfalso
        rcases lt_or_ge (0 : ℝ) a with h0 | h0
        · have hin : 1 < a⁻¹ := (one_lt_inv_iff₀).mpr ⟨h0, h1⟩
          have h2 := one_lt_pow₀ hin hn0
          rw [inv_pow, h] at h2
          norm_num at h2
        · have h0e : a = 0 := le_antisymm h0 ha
          rw [h0e, zero_pow hn0] at h
          norm_num at h
      · exact h1
      · have h2 := one_lt_pow₀ h1 hn0
        rw [h] at h2
        linarith
    exact key ‖τ (theta M i j)‖ (norm_nonneg _) hn
  have xi_pow_M {M : ℕ} (hM : 4 ≤ M) :
      xi M ^ ((M : ℕ) : ℤ) = (-1 : ℂ) ^ (((M : ℕ) + 1 : ℕ) : ℤ) := by
    have hMn : (M : ℂ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
    have hkey : (M : ℂ) * (Real.pi * Complex.I / (M : ℂ)) = Real.pi * Complex.I := by
      field_simp
    have hexp : Complex.exp (Real.pi * Complex.I / (M : ℂ)) ^ (M : ℕ) = -1 := by
      rw [← Complex.exp_nat_mul, hkey, Complex.exp_pi_mul_I]
    have hR : (-1 : ℂ) ^ (((M + 1 : ℕ) : ℤ)) = (-1 : ℂ) ^ ((M : ℕ) : ℤ) * (-1 : ℂ) := by
      have hc : ((M + 1 : ℕ) : ℤ) = ((M : ℕ) : ℤ) + 1 := by omega
      rw [hc, zpow_add_one₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    rw [zpow_natCast, xi_formula, neg_pow, hexp, hR, zpow_natCast]
  have xi_zpow_mul_M {M : ℕ} (hM : 4 ≤ M) (k : ℤ) :
      xi M ^ ((M : ℤ) * k) = (-1 : ℂ) ^ (((M : ℤ) + 1) * k) := by
    have hc : ((M + 1 : ℕ) : ℤ) = (M : ℤ) + 1 := by omega
    rw [_root_.zpow_mul, xi_pow_M hM, hc, ← _root_.zpow_mul]
  have theta_add_period {M : ℕ} (hM : 4 ≤ M) (i j a b : ℤ) :
      theta M (i + (M : ℤ) * a) (j + (M : ℤ) * b) =
        (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a)) * theta M i j := by
    have hQ : quadraticForm (i + (M : ℤ) * a) (j + (M : ℤ) * b)
        = quadraticForm i j + (M : ℤ) * (2 * (i * a) - i * b - j * a + 2 * (j * b)
          + (M : ℤ) * quadraticForm a b) := by
      unfold quadraticForm; ring
    have hE : (-1 : ℂ) ^ (((M : ℤ) + 1) * (2 * (i * a) - i * b - j * a + 2 * (j * b)
          + (M : ℤ) * quadraticForm a b))
        = (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a)) := by
      refine negOne_zpow_eq_of_two_dvd ?_
      obtain ⟨t, hts⟩ := Int.two_dvd_mul_add_one M
      push_cast at hts
      refine ⟨((M : ℤ) + 1) * (i * a + j * b - i * b - j * a) + t * quadraticForm a b, ?_⟩
      unfold quadraticForm
      linear_combination (a * a - a * b + b * b) * hts
    rw [theta_eq_xi_zpow, theta_eq_xi_zpow, hQ, zpow_add₀ (xi_ne_zero M),
      xi_zpow_mul_M hM, hE,
      mul_comm ((-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a)))]
  have phased_displacement_add_period {M : ℕ} (hM : 4 ≤ M) (i j a b : ℤ) :
      theta M (i + (M : ℤ) * a) (j + (M : ℤ) * b) •
          D M (toWH (i + (M : ℤ) * a) (j + (M : ℤ) * b)) =
        theta M i j • D M (toWH i j) := by
    have hto : toWH (i + (M : ℤ) * a) (j + (M : ℤ) * b)
        = toWH i j + (M : ℤ) • ((-b, a) : ℤ × ℤ) := by
      show (-(j + (M : ℤ) * b), i + (M : ℤ) * a)
          = ((-j + (M : ℤ) * (-b), i + (M : ℤ) * a) : ℤ × ℤ)
      rw [Prod.mk.injEq]
      exact ⟨by ring, by ring⟩
    have hE : xi M ^ ((M : ℤ) * ((toWH i j).1 * ((-b, a) : ℤ × ℤ).2
          + ((-b, a) : ℤ × ℤ).1 * (toWH i j).2)
          + (M : ℤ) ^ 2 * (((-b, a) : ℤ × ℤ).1 * ((-b, a) : ℤ × ℤ).2))
        = (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a)) := by
      show xi M ^ ((M : ℤ) * (-j * a + -b * i) + (M : ℤ) ^ 2 * (-b * a))
        = (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a))
      have hexp2 : (M : ℤ) * (-j * a + -b * i) + (M : ℤ) ^ 2 * (-b * a)
          = (M : ℤ) * (-j * a + -b * i + (M : ℤ) * (-b * a)) := by
        ring
      rw [hexp2, xi_zpow_mul_M hM]
      refine negOne_zpow_eq_of_two_dvd ?_
      obtain ⟨t, hts⟩ := Int.two_dvd_mul_add_one M
      push_cast at hts
      refine ⟨-((M : ℤ) + 1) * (j * a + i * b) - t * (b * a), ?_⟩
      linear_combination (-(b * a)) * hts
    have hone : (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a))
        * (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a)) = 1 := by
      have h2 : (-1 : ℂ) ^ (2 : ℤ) = 1 := by norm_num
      rw [← _root_.zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
        show ((M : ℤ) + 1) * (i * b + j * a) + ((M : ℤ) + 1) * (i * b + j * a)
          = 2 * (((M : ℤ) + 1) * (i * b + j * a)) from by ring,
        _root_.zpow_mul, h2, _root_.one_zpow]
    have hs : ((-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a)) * theta M i j)
        * (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a)) = theta M i j := by
      have hrw : ((-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a)) * theta M i j)
          * (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a))
          = ((-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a))
            * (-1 : ℂ) ^ (((M : ℤ) + 1) * (i * b + j * a))) * theta M i j := by
        ring
      rw [hrw, hone, one_mul]
    rw [hto, D_add_smul, smul_smul, theta_add_period hM, hE, hs]
  let phasedD (M : ℕ) (i j : ℤ) : Matrix (Fin M) (Fin M) ℂ :=
    theta M i j • D M (toWH i j)
  have phasedD_formula (M : ℕ) (i j : ℤ) : phasedD M i j =
    theta M i j • D M (toWH i j) := rfl
  let residueD (M : ℕ) (h : (ZMod M × ZMod M)) : Matrix (Fin M) (Fin M) ℂ :=
    phasedD M h.1.val h.2.val
  have residueD_formula (M : ℕ) (h : (ZMod M × ZMod M)) : residueD M h =
    phasedD M h.1.val h.2.val := rfl
  let indexEquiv (M : ℕ) [NeZero M] : (Fin M × Fin M) ≃ (ZMod M × ZMod M) := {
    toFun p := ((p.1 : ℕ), (p.2 : ℕ))
    invFun h := (finIdx M h.1, finIdx M h.2)
    left_inv p := by
      apply Prod.ext <;> apply fin_ext_of_label <;> apply label_finIdx
    right_inv h := by
      exact Prod.ext (label_finIdx M h.1) (label_finIdx M h.2) }
  have sum_fin_index {M : ℕ} [NeZero M] {A : Type} [AddCommMonoid A]
      (f : (ZMod M × ZMod M) → A) :
      (∑ i : Fin M, ∑ j : Fin M, f ((i : ℕ), (j : ℕ))) = ∑ h : (ZMod M × ZMod M), f h := by
    rw [← Fintype.sum_prod_type']
    exact (indexEquiv M).sum_comp f
  have phasedD_eq_of_cast_eq {M : ℕ} (hM : 4 ≤ M) (i j k l : ℤ)
      (hi : (i : ZMod M) = (k : ZMod M)) (hj : (j : ZMod M) = (l : ZMod M)) :
      phasedD M i j = phasedD M k l := by
    obtain ⟨a, ha⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub k i M).mp hi.symm
    obtain ⟨b, hb⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub l j M).mp hj.symm
    have hi' : i = k + (M : ℤ) * a := by linear_combination ha
    have hj' : j = l + (M : ℤ) * b := by linear_combination hb
    rw [hi', hj']
    exact phased_displacement_add_period hM k l a b
  have residueD_eq_phasedD {M : ℕ} (hM : 4 ≤ M) (i j : ℤ) :
      residueD M ((i : ZMod M), (j : ZMod M)) = phasedD M i j := by
    haveI : NeZero M := ⟨by omega⟩
    apply phasedD_eq_of_cast_eq hM <;> simp
  have phasedD_zero (M : ℕ) : phasedD M 0 0 = 1 := by
    simp [phasedD, theta_eq_xi_zpow, quadraticForm, toWH, D_zero]
  have residueD_zero (M : ℕ) : residueD M 0 = 1 := by
    simpa [residueD] using phasedD_zero M
  have phasedD_mul (M : ℕ) (i j r s : ℤ) :
      phasedD M i j * phasedD M (r - i) (s - j) =
        (gaussianLift M i j * e M (-i * r + j * (r - s))) • phasedD M r s := by
    simp only [phasedD, Matrix.smul_mul, Matrix.mul_smul, D_mul_D, smul_smul]
    have ht : toWH i j + toWH (r - i) (s - j) = toWH r s := by
      ext <;> simp [toWH] <;> ring
    rw [ht]
    congr 1
    simp only [theta_eq_xi_zpow, gaussianLift, e_eq_omega_zpow, omega_zpow,
      ← zpow_add₀ (xi_ne_zero M)]
    congr 1
    dsimp [quadraticForm, toWH]
    ring
  have P_eq_sum_residueD {M : ℕ} [NeZero M] (hM : 4 ≤ M) (F : ((ZMod M × ZMod M) → ℂ)) :
      P M F = (M : ℂ)⁻¹ • ∑ h : (ZMod M × ZMod M), F h • residueD M h := by
    rw [P_formula, ← sum_fin_index]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [residueD, ZMod.val_cast_of_lt i.isLt, ZMod.val_cast_of_lt j.isLt,
      phasedD, valueAt, smul_smul, Int.cast_natCast, mul_comm]
  have isZeroLabel_iff_cast {M : ℕ} (i j : ℤ) :
      IsZeroLabel M (i, j) ↔ ((i : ZMod M), (j : ZMod M)) = 0 := by
    change (_ ∧ _) ↔ ((i : ZMod M), (j : ZMod M)) = (0, 0)
    simp only [IsZeroLabel, Prod.mk.injEq, Prod.fst_zero, Prod.snd_zero,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
  have isZeroLabel_toWH {M : ℕ} (i j : ℤ) :
      IsZeroLabel M (toWH i j) ↔ IsZeroLabel M (i, j) := by
    simp only [IsZeroLabel, toWH, dvd_neg, and_comm]
  let convolutionKernel (M : ℕ) (u r : (ZMod M × ZMod M)) : ℂ :=
    gaussianLift M u.1.val u.2.val *
      e M (-(u.1.val : ℤ) * r.1.val + (u.2.val : ℤ) * (r.1.val - r.2.val))
  have residueD_mul_sub {M : ℕ} [NeZero M] (hM : 4 ≤ M) (u r : (ZMod M × ZMod M)) :
      residueD M u * residueD M (r - u) =
        convolutionKernel M u r • residueD M r := by
    have hr : r - u =
        ((((r.1.val : ℤ) - u.1.val : ℤ) : ZMod M),
          (((r.2.val : ℤ) - u.2.val : ℤ) : ZMod M)) := by
      ext <;> simp
    rw [hr, residueD_eq_phasedD hM]
    exact phasedD_mul M u.1.val u.2.val r.1.val r.2.val
  have convolution_eq_sum_index {M : ℕ} [NeZero M] (F : ((ZMod M × ZMod M) → ℂ)) (r : (ZMod M × ZMod M)) :
      convolution M F r.1.val r.2.val =
        (M : ℂ)⁻¹ * ∑ u : (ZMod M × ZMod M), F u * F (r - u) * convolutionKernel M u r := by
    rcases r with ⟨r, s⟩
    rw [convolution_formula, ← sum_fin_index]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp [valueAt, convolutionKernel, ZMod.val_cast_of_lt i.isLt,
      ZMod.val_cast_of_lt j.isLt, mul_assoc]
  have trace_residueD {M : ℕ} [NeZero M] (hM : 4 ≤ M) (h : (ZMod M × ZMod M)) :
      (residueD M h).trace = if h = 0 then (M : ℂ) else 0 := by
    classical
    by_cases hh : h = 0
    · simp [hh, residueD_zero, Matrix.trace_one]
    · have hz : ¬ IsZeroLabel M (toWH h.1.val h.2.val) := by
        rw [isZeroLabel_toWH, isZeroLabel_iff_cast]
        simpa using hh
      rw [residueD_formula, phasedD_formula, Matrix.trace_smul, trace_D, if_neg hz, if_neg hh]
      simp
  have ov_residueD {M : ℕ} [NeZero M] (hM : 4 ≤ M)
      (h : (ZMod M × ZMod M)) (i j : ℤ) :
      ov M (residueD M h) (toWH i j) =
        if h = ((i : ZMod M), (j : ZMod M)) then theta M i j * (M : ℂ) else 0 := by
    classical
    by_cases hh : h = ((i : ZMod M), (j : ZMod M))
    · rw [hh, residueD_eq_phasedD hM]
      simp [ov, phasedD, Matrix.smul_mul, D_mul_conjTranspose_D, Matrix.trace_smul,
        Matrix.trace_one]
    · have hz : ¬ IsZeroLabel M (toWH h.1.val h.2.val + -(toWH i j)) := by
        intro hz
        apply hh
        have hz' := (isZeroLabel_iff_cast _ _).mp hz
        have h₁ := congrArg Prod.fst hz'
        have h₂ := congrArg Prod.snd hz'
        simp [toWH] at h₁ h₂
        apply Prod.ext <;> dsimp
        · linear_combination h₂
        · linear_combination -h₁
      rw [residueD_formula, phasedD_formula, ov_formula, Matrix.smul_mul, conjTranspose_D, D_mul_D,
        Matrix.trace_smul, Matrix.trace_smul, trace_D, if_neg hz, if_neg hh]
      simp
  have ov_P_toWH {M : ℕ} (hM : 4 ≤ M) (F : ((ZMod M × ZMod M) → ℂ)) (i j : ℤ) :
      ov M (P M F) (toWH i j) = theta M i j * valueAt F i j := by
    classical
    haveI : NeZero M := ⟨by omega⟩
    have hn : (M : ℂ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
    rw [P_eq_sum_residueD hM]
    simp only [ov, Matrix.smul_mul, Matrix.sum_mul, Matrix.trace_smul, Matrix.trace_sum,
      smul_eq_mul]
    change (M : ℂ)⁻¹ * ∑ h : (ZMod M × ZMod M), F h * ov M (residueD M h) (toWH i j) = _
    simp_rw [ov_residueD hM]
    simp [mul_ite, Finset.sum_ite_eq', valueAt, hn, mul_comm, mul_left_comm, mul_assoc]
  have P_mul_P {M : ℕ} (hM : 4 ≤ M) {F : ((ZMod M × ZMod M) → ℂ)}
      (hA : RWConvolutionInput M F) :
      P M F * P M F = convolutionScalar M • P M F + 1 := by
    classical
    haveI : NeZero M := ⟨by omega⟩
    have hn : (M : ℂ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
    have hprod : P M F * P M F =
        (M : ℂ)⁻¹ • ∑ r : (ZMod M × ZMod M), (convolution M F r.1.val r.2.val) • residueD M r := by
      calc
        _ = (M : ℂ)⁻¹ • ((M : ℂ)⁻¹ • ∑ u : (ZMod M × ZMod M), ∑ v : (ZMod M × ZMod M),
            (F u * F v) • (residueD M u * residueD M v)) := by
          simp only [P_eq_sum_residueD hM, Matrix.smul_mul, Matrix.mul_smul,
            Matrix.sum_mul, Matrix.mul_sum, Finset.smul_sum, smul_smul, mul_assoc]
          rw [Finset.sum_comm]
          simp only [mul_assoc, mul_left_comm, mul_comm]
        _ = (M : ℂ)⁻¹ • ((M : ℂ)⁻¹ • ∑ u : (ZMod M × ZMod M), ∑ r : (ZMod M × ZMod M),
            (F u * F (r - u) * convolutionKernel M u r) • residueD M r) := by
          congr 1
          congr 1
          apply Finset.sum_congr rfl
          intro u _
          apply Fintype.sum_equiv (Equiv.addLeft u)
          intro v
          change (F u * F v) • (residueD M u * residueD M v) =
            (F u * F (u + v - u) * convolutionKernel M u (u + v)) • residueD M (u + v)
          have hm := residueD_mul_sub hM u (u + v)
          simp only [add_sub_cancel_left] at hm ⊢
          rw [hm, smul_smul]
        _ = (M : ℂ)⁻¹ • ∑ r : (ZMod M × ZMod M),
            ((M : ℂ)⁻¹ * ∑ u : (ZMod M × ZMod M), F u * F (r - u) * convolutionKernel M u r) •
              residueD M r := by
          rw [Finset.sum_comm]
          simp only [mul_smul, Finset.smul_sum, Finset.sum_smul]
        _ = _ := by simp_rw [convolution_eq_sum_index]
    rw [hprod]
    simp_rw [hA.2.2]
    rw [P_eq_sum_residueD hM]
    simp [add_smul, ite_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul,
      residueD_zero, hn, mul_comm, mul_left_comm, mul_assoc]
  have P_quadratic {M : ℕ} (hM : 4 ≤ M) {F : ((ZMod M × ZMod M) → ℂ)}
      (hA : RWConvolutionInput M F) :
      (P M F - sqrtEpsilon M • (1 : Matrix (Fin M) (Fin M) ℂ)) *
        (P M F + (sqrtEpsilon M)⁻¹ • (1 : Matrix (Fin M) (Fin M) ℂ)) = 0 := by
    have hν := sqrtEpsilon_ne_zero hM
    have hc := sqrtEpsilon_sub_inv hM
    have hprod := P_mul_P hM hA
    calc
      _ = (P M F * P M F - convolutionScalar M • P M F) - 1 := by
        simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.one_mul, Matrix.mul_one, smul_smul]
        rw [← hc]
        simp only [sub_smul, mul_inv_cancel₀ hν, one_smul]
        match_scalars <;> simp [hν] <;> ring
      _ = 0 := by rw [hprod]; abel
  have trace_P {M : ℕ} (hM : 4 ≤ M) {F : ((ZMod M × ZMod M) → ℂ)}
      (hA : RWConvolutionInput M F) : (P M F).trace = sqrtEpsilon M ^ 3 := by
    classical
    haveI : NeZero M := ⟨by omega⟩
    have hn : (M : ℂ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
    rw [P_eq_sum_residueD hM]
    simp only [Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul]
    simp_rw [trace_residueD hM]
    simp [mul_ite, hA.1, hn, mul_assoc, mul_comm, mul_left_comm]
  have denominator_sq {M : ℕ} (hM : 4 ≤ M) :
      denominator M ^ 2 = (M : ℂ) + 1 := by
    rw [denominator_eq_sqrt hM]
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (M : ℝ) + 1 by positivity)
    exact_mod_cast hs
  have rsicConst_one {M : ℕ} (hM : 4 ≤ M) :
      rsicConst M 1 = ((M : ℝ) + 1)⁻¹ := by
    have hm : (4 : ℝ) ≤ M := by exact_mod_cast hM
    have hn : (M : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    simp only [rsicConst, Nat.cast_one, one_mul]
    field_simp
    <;> ring
  have ghostProjector_idempotent {M : ℕ} (hM : 4 ≤ M) {F : ((ZMod M × ZMod M) → ℂ)}
      (hA : RWConvolutionInput M F) :
      ghostProjector M F * ghostProjector M F = ghostProjector M F := by
    have hs := denominator_ne_zero hM
    have hq :
        (sqrtEpsilon M • (1 : Matrix (Fin M) (Fin M) ℂ) - P M F) *
            (sqrtEpsilon M • (1 : Matrix (Fin M) (Fin M) ℂ) - P M F) =
          denominator M • (sqrtEpsilon M • (1 : Matrix (Fin M) (Fin M) ℂ) - P M F) := by
      have he :
          (P M F - sqrtEpsilon M • (1 : Matrix (Fin M) (Fin M) ℂ)) *
              (P M F + (sqrtEpsilon M)⁻¹ • (1 : Matrix (Fin M) (Fin M) ℂ)) =
            (sqrtEpsilon M • (1 : Matrix (Fin M) (Fin M) ℂ) - P M F) *
                (sqrtEpsilon M • (1 : Matrix (Fin M) (Fin M) ℂ) - P M F) -
              denominator M • (sqrtEpsilon M • (1 : Matrix (Fin M) (Fin M) ℂ) - P M F) := by
        simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.smul_mul,
          Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, denominator]
        module
      rw [P_quadratic hM hA] at he
      exact sub_eq_zero.mp he.symm
    simp only [ghostProjector, Matrix.smul_mul, Matrix.mul_smul, hq, smul_smul]
    simp [mul_assoc, hs]
  have trace_ghostProjector {M : ℕ} (hM : 4 ≤ M) {F : ((ZMod M × ZMod M) → ℂ)}
      (hA : RWConvolutionInput M F) : (ghostProjector M F).trace = 1 := by
    have hs := denominator_ne_zero hM
    have ht : sqrtEpsilon M * (M : ℂ) - sqrtEpsilon M ^ 3 = denominator M := by
      rw [sqrtEpsilon_cube hM, denominator_formula]
      ring
    simp only [ghostProjector, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_one,
      Fintype.card_fin, smul_eq_mul, trace_P hM hA]
    rw [ht, inv_mul_cancel₀ hs]
  have coefficient_mul_neg {M : ℕ} (hM : 4 ≤ M) {F : ((ZMod M × ZMod M) → ℂ)}
      (hA : RWConvolutionInput M F) (i j : ℤ) (hij : ¬ IsZeroLabel M (i, j)) :
      coefficient M F i j * coefficient M F (-i) (-j) = ((M : ℂ) + 1)⁻¹ := by
    have hh : ((i : ZMod M), (j : ZMod M)) ≠ 0 :=
      mt (isZeroLabel_iff_cast i j).mpr hij
    have hr := hA.2.1 ((i : ZMod M), (j : ZMod M)) hh
    have hr' : valueAt F i j * valueAt F (-i) (-j) = (gaussianLift M i j)⁻¹ := by
      simpa only [valueAt, Prod.neg_mk, Int.cast_neg, gaussian_eq_lift hM] using hr
    have hg : gaussianLift M i j ≠ 0 := Complex.exp_ne_zero _
    rw [coefficient_formula, coefficient_formula, theta_neg]
    calc
      _ = (theta M i j ^ 2 * (valueAt F i j * valueAt F (-i) (-j))) /
          denominator M ^ 2 := by ring
      _ = _ := by rw [theta_sq, hr', denominator_sq hM, mul_inv_cancel₀ hg, one_div]
  have ov_ghostProjector {M : ℕ} (hM : 4 ≤ M) {F : ((ZMod M × ZMod M) → ℂ)}
      (hA : RWConvolutionInput M F) (p : ℤ × ℤ) (hp : ¬ IsZeroLabel M p) :
      ov M (ghostProjector M F) p = coefficient M F (fromWH p).1 (fromWH p).2 := by
    haveI : NeZero M := ⟨by omega⟩
    have hpneg : ¬ IsZeroLabel M (-p) := by simpa [IsZeroLabel] using hp
    have hov := ov_P_toWH hM F (fromWH p).1 (fromWH p).2
    have hback : toWH (fromWH p).1 (fromWH p).2 = p := by simp [toWH, fromWH]
    rw [hback] at hov
    simp only [ghostProjector, ov, Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul,
      Matrix.trace_smul, Matrix.trace_sub, smul_eq_mul]
    rw [conjTranspose_D, trace_D, if_neg hpneg]
    rw [← conjTranspose_D p]
    change (denominator M)⁻¹ * (sqrtEpsilon M * 0 - ov M (P M F) p) = _
    rw [hov]
    simp [coefficient, div_eq_mul_inv, mul_comm]
  have ov_ghostProjector_mul_neg {M : ℕ} (hM : 4 ≤ M) {F : ((ZMod M × ZMod M) → ℂ)}
      (hA : RWConvolutionInput M F) (p : ℤ × ℤ) (hp : ¬ IsZeroLabel M p) :
      ov M (ghostProjector M F) p * ov M (ghostProjector M F) (-p) =
        (rsicConst M 1 : ℂ) := by
    have hpneg : ¬ IsZeroLabel M (-p) := by simpa [IsZeroLabel] using hp
    have hf : ¬ IsZeroLabel M ((fromWH p).1, (fromWH p).2) := by
      simpa [fromWH, IsZeroLabel, and_comm] using hp
    rw [ov_ghostProjector hM hA p hp, ov_ghostProjector hM hA (-p) hpneg]
    change coefficient M F (fromWH p).1 (fromWH p).2 *
        coefficient M F (-(fromWH p).1) (-(fromWH p).2) = _
    rw [coefficient_mul_neg hM hA _ _ hf, rsicConst_one hM]
    push_cast
    rfl
  have isGhost_of_RW {M : ℕ} (hM : 4 ≤ M) {F : ((ZMod M × ZMod M) → ℂ)}
      (hA : RWConvolutionInput M F) : IsGhost M 1 (ghostProjector M F) := by
    exact ⟨ghostProjector_idempotent hM hA, by simpa using trace_ghostProjector hM hA,
      ov_ghostProjector_mul_neg hM hA⟩
  have map_coefficient_normSq {M : ℕ} (hM : 4 ≤ M) {F : ((ZMod M × ZMod M) → ℂ)}
      {τ : ℂ →+* ℂ} (hB : RWUnitCircleInput M F τ)
      (i j : ℤ) (hij : ¬ IsZeroLabel M (i, j)) :
      Complex.normSq (τ (coefficient M F i j)) = rsicConst M 1 := by
    have hh : ((i : ZMod M), (j : ZMod M)) ≠ 0 :=
      mt (isZeroLabel_iff_cast i j).mpr hij
    have hF : ‖τ (valueAt F i j)‖ = 1 := hB _ hh
    have hd : Complex.normSq (τ (denominator M)) = (M : ℝ) + 1 := by
      have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (M : ℝ) + 1 by positivity)
      rcases map_denominator_eq_or_neg hM τ with h | h
      · rw [h, Complex.normSq_ofReal]
        nlinarith
      · rw [h, Complex.normSq_neg, Complex.normSq_ofReal]
        nlinarith
    rw [coefficient_formula, map_div₀, map_neg, map_mul, Complex.normSq_div,
      Complex.normSq_neg, Complex.normSq_mul, hd]
    simp only [Complex.normSq_eq_norm_sq, map_theta_norm hM τ, hF, one_pow, one_mul,
      rsicConst_one hM, one_div]
  have unimodularFlip_of_RW {M : ℕ} (hM : 4 ≤ M) {F : ((ZMod M × ZMod M) → ℂ)}
      (hA : RWConvolutionInput M F) {τ : ℂ →+* ℂ} (hB : RWUnitCircleInput M F τ) :
      UnimodularFlip M 1 (ghostProjector M F) τ := by
    intro p hp
    have hf : ¬ IsZeroLabel M ((fromWH p).1, (fromWH p).2) := by
      simpa [fromWH, IsZeroLabel, and_comm] using hp
    rw [ov_ghostProjector hM hA p hp]
    exact map_coefficient_normSq hM hB _ _ hf
  have ghostGaloisInput_of_RW {M : ℕ} (hM : 4 ≤ M) {F : ((ZMod M × ZMod M) → ℂ)}
      (hA : RWConvolutionInput M F) {τ : ℂ →+* ℂ} (hB : RWUnitCircleInput M F τ) :
      GhostGaloisInput M 1 := by
    exact ⟨ghostProjector M F, isGhost_of_RW hM hA, τ, unimodularFlip_of_RW hM hA hB⟩
  have e_eq_char (i : ℤ) :
      e 69 i = ZMod.stdAddChar (i : ZMod 69) := by
    rw [ZMod.stdAddChar_coe] <;> rfl
  have gauss_eq_char (i j : ℤ) :
      gaussianLift 69 i j =
      ZMod.stdAddChar ((i : ZMod 69)^2 - (i : ZMod 69)*(j : ZMod 69) + (j : ZMod 69)^2) := by
    rw [gaussianLift_formula, e_eq_char]
    simp [quadraticForm]
  let residueIndex : ZMod 69 ≃ Fin 69 := (ZMod.finEquiv 69).toEquiv.symm
  have residueIndex_val (i : ZMod 69) : (residueIndex i).val = i.val := rfl
  have liftVal (t : ZMod 69) : ((t.val : ℤ) : ZMod 69) = t := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have trace_residues (A : Matrix (Fin 69) (Fin 69) ℂ) :
      (A.submatrix residueIndex residueIndex).trace = A.trace :=
    residueIndex.sum_comp (fun i => A i i)
  have fourier_diagonal (A : Matrix (Fin 69) (Fin 69) ℂ) (a b : ZMod 69) :
      Complex.normSq (∑ t, (A.submatrix residueIndex residueIndex) (t+a) t * ZMod.stdAddChar (b*t)) =
      Complex.normSq (ov 69 A ((a.val : ℤ),-(b.val : ℤ))) := by
    let z := star (xi 69 ^ ((a.val : ℤ) * -(b.val : ℤ)))
    have hz : Complex.normSq z = 1 := by
      unfold z
      rw [Complex.star_def, Complex.normSq_conj, Complex.normSq_eq_norm_sq, norm_zpow]
      have hu : ‖xi 69‖ = 1 := by simp [xi, Complex.norm_exp]
      simp [hu]
    have chars (t : ZMod 69) :
        star (omega 69 ^ (-(b.val : ℤ) * (t.val : ℤ))) = ZMod.stdAddChar (b*t) := by
      rw [omega_exp]
      change star (e 69 (-(b.val : ℤ) * (t.val : ℤ))) = _
      rw [e_eq_char]
      simp only [Int.cast_mul, Int.cast_neg, liftVal]
      rw [neg_mul, AddChar.map_neg_eq_inv]
      change star ((ZMod.toCircle (b*t) : ℂ)⁻¹) = _
      rw [star_inv₀]
      change (starRingEnd ℂ (ZMod.toCircle (b*t) : ℂ))⁻¹ = _
      rw [← Circle.coe_inv_eq_conj, Circle.coe_inv, inv_inv]
      rfl
    have hsum : ov 69 A ((a.val : ℤ),-(b.val : ℤ)) =
        z * ∑ t, (A.submatrix residueIndex residueIndex) (t+a) t * ZMod.stdAddChar (b*t) := by
      unfold ov
      rw [← trace_residues, ← Matrix.submatrix_mul_equiv _ _ residueIndex residueIndex residueIndex]
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.submatrix_apply,
        Matrix.conjTranspose_apply]
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      change (∑ i : ZMod 69, A (residueIndex i) (residueIndex t) * star (D 69 ((a.val : ℤ),-(b.val : ℤ)) (residueIndex i) (residueIndex t))) = _
      rw [Finset.sum_eq_single (t+a)]
      · have hD : D 69 ((a.val : ℤ),-(b.val : ℤ)) (residueIndex (t+a)) (residueIndex t) =
              xi 69 ^ ((a.val : ℤ) * -(b.val : ℤ)) *
                omega 69 ^ (-(b.val : ℤ) * (t.val : ℤ)) := by
          simp only [displacement_entry, residueIndex_val, liftVal, if_true]
        rw [hD, star_mul, chars]
        dsimp [z]
        ring
      · intro i _ hi
        have hD : D 69 ((a.val : ℤ),-(b.val : ℤ)) (residueIndex i) (residueIndex t) = 0 := by
          simp only [displacement_entry, residueIndex_val, liftVal, if_neg hi]
        rw [hD, star_zero, mul_zero]
      · simp
    rw [hsum, Complex.normSq_mul, hz, one_mul]
  have convolution_residues (F : ZMod 69 → ZMod 69 → ℂ) (r s : ZMod 69) :
      convolution 69 (fun h => F h.1 h.2) r.val s.val =
        (69 : ℂ)⁻¹ * ∑ i : ZMod 69, ∑ j : ZMod 69, F i j * F (r-i) (s-j) *
          ZMod.stdAddChar (i^2-i*j+j^2) * ZMod.stdAddChar (-i*r+j*(r-s)) := by
    unfold convolution
    congr 1
    rw [← residueIndex.sum_comp]
    apply Finset.sum_congr rfl
    intro i _
    rw [← residueIndex.sum_comp]
    apply Finset.sum_congr rfl
    intro j _
    simp only [valueAt, Function.comp_apply, gauss_eq_char, e_eq_char, Int.cast_neg,
      Int.cast_mul, Int.cast_sub, Int.cast_add, residueIndex_val, liftVal]
  classical
  intro F τ hzero hreflect hconv hcircle
  let f : ((ZMod 69 × ZMod 69) → ℂ) := fun h => F h.1 h.2
  have hA : RWConvolutionInput 69 f := by
    refine ⟨?_, ?_, ?_⟩
    · convert hzero using 1 <;> norm_num [f, sqrtEpsilon, epsilon, unit]
    · rintro ⟨i,j⟩ hij
      simpa [f, gaussian, gauss_eq_char] using hreflect i j hij
    · rintro ⟨r,s⟩
      change convolution 69 f r.val s.val = _
      rw [show convolution 69 f r.val s.val = _ from convolution_residues F r s]
      by_cases h : (r,s) = ((0,0) : ZMod 69 × ZMod 69)
      · have hz : (r,s) = (0 : (ZMod 69 × ZMod 69)) := h
        simpa only [convolutionScalar, Nat.cast_ofNat, show (69:ℝ)-3=66 by norm_num, f,
          if_pos h, if_pos hz] using hconv r s
      · have hz : (r,s) ≠ (0 : (ZMod 69 × ZMod 69)) := h
        simpa only [convolutionScalar, Nat.cast_ofNat, show (69:ℝ)-3=66 by norm_num, f,
          if_neg h, if_neg hz] using hconv r s
  have hB : RWUnitCircleInput 69 f τ := fun h hh => hcircle h.1 h.2 hh
  obtain ⟨G, hG, θ, hθ⟩ := ghostGaloisInput_of_RW (by decide : 4 ≤ 69) hA hB
  obtain ⟨hH, hP, ht, hflat⟩ := map_fiducial_of_ghost_flip (by decide : 2 ≤ 69)
    (by decide : 1 ≤ 1) (by decide : 1 < 69) hG hθ
  refine ⟨(G.map θ).submatrix residueIndex residueIndex, hH.submatrix _, ?_, ?_, ?_⟩
  · rw [Matrix.submatrix_mul_equiv, hP]
  · rw [trace_residues, ht, Nat.cast_one]
  intro a b hab
  rw [fourier_diagonal (G.map θ) a b]
  have hn : ¬IsZeroLabel 69 ((a.val : ℤ), -(b.val : ℤ)) := by
    rintro ⟨ha,hb⟩
    apply hab
    have ha0 : a.val = 0 := by have := a.val_lt; omega
    have hb0 : b.val = 0 := by have := b.val_lt; omega
    exact Prod.ext (ZMod.val_injective 69 (by simpa using ha0))
      (ZMod.val_injective 69 (by simpa using hb0))
  convert hflat _ hn using 1 <;> norm_num [rsicConst]


private theorem enumeration_bijective : Function.Bijective (fun w : ZMod 66 × ZMod 69 × ZMod 69 =>
    ((-w.2.1+2*w.2.2 : ZMod 69), ((66*w.2.2.val+w.1.val : ℕ) : ZMod 4554))) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · rintro ⟨c,i,j⟩ ⟨d,k,l⟩ heq
    obtain ⟨h₁,h₂⟩ := Prod.mk.inj heq
    change -i+2*j = -k+2*l at h₁
    change ((66*j.val+c.val : ℕ) : ZMod 4554) = ((66*l.val+d.val : ℕ) : ZMod 4554) at h₂
    have c_lt := c.val_lt
    have d_lt := d.val_lt
    have j_lt := j.val_lt
    have l_lt := l.val_lt
    have e := congrArg ZMod.val h₂
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at e
    have hj : j = l := ZMod.val_injective 69 (by omega)
    have hc : c = d := ZMod.val_injective 66 (by omega)
    subst l d
    simp only [add_left_inj, neg_inj] at h₁
    simp [h₁]
  · simp [ZMod.card]

private theorem enumerate_sum (T : ℤ → ℤ → ℂ)
    (hperiod : ∀ x y m, T (x+69*m) y = T x y) :
    (∑ c : ZMod 66, ∑ i : ZMod 69, ∑ j : ZMod 69,
      T (-(i.val : ℤ)+2*j.val) (66*(j.val : ℤ)+c.val)) =
    ∑ u : ZMod 69 × ZMod 4554, T u.1.val u.2.val := by
  let e := Equiv.ofBijective _ enumeration_bijective
  rw [← e.sum_comp (fun u : ZMod 69 × ZMod 4554 => T u.1.val u.2.val),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  let x := -(i.val : ℤ)+2*j.val
  change T x _ = T (-i+2*j).val (((66*j.val+c.val : ℕ) : ZMod 4554).val)
  have ej := j.val_lt
  have ec := c.val_lt
  rw [ZMod.val_natCast_of_lt (by omega), Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  have eqcast : (x : ZMod 69) = (((-i+2*j).val : ℤ) : ZMod 69) := by simp [x]
  obtain ⟨m, hm⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp eqcast
  have h : ((-i+2*j).val : ℤ) = x+69*m := by omega
  rw [h, hperiod]

private theorem character_period (x y a b m : ℤ) :
    (ZMod.stdAddChar ((132*((x+69*m)^2+(x+69*m)*y)+67*y^2+4554*y : ℤ) : ZMod 9108) =
    ZMod.stdAddChar ((132*(x^2+x*y)+67*y^2+4554*y : ℤ) : ZMod 9108)) ∧
    (ZMod.stdAddChar ((132*(x+69*m)*a+66*((x+69*m)*b+y*a)+67*y*b : ℤ) : ZMod 4554) =
    ZMod.stdAddChar ((132*x*a+66*(x*b+y*a)+67*y*b : ℤ) : ZMod 4554)) := by
  constructor <;> congr 1 <;> push_cast <;> ring_nf <;> reduce_mod_char

private theorem scale66 (z : ℤ) :
    ZMod.stdAddChar ((69*z : ℤ) : ZMod 4554) = ZMod.stdAddChar (z : ZMod 66) := by
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  push_cast
  congr 1
  ring
private theorem scale69 (z : ℤ) :
    ZMod.stdAddChar ((66*z : ℤ) : ZMod 4554) = ZMod.stdAddChar (z : ZMod 69) := by
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  push_cast
  congr 1
  ring
private theorem scaleQuad (z : ℤ) :
    ZMod.stdAddChar ((132*z : ℤ) : ZMod 9108) = ZMod.stdAddChar (z : ZMod 69) := by
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  push_cast
  congr 1
  ring
private theorem gaussian_plane (i j : ℤ) :
    let x := -i+2*j
    let y := 66*j
    ZMod.stdAddChar ((132*(x^2+x*y)+67*y^2+4554*y : ℤ) : ZMod 9108) =
    ZMod.stdAddChar ((i^2-i*j+j^2 : ℤ) : ZMod 69) := by
  dsimp only
  rw [← scaleQuad]
  congr 1
  push_cast
  ring_nf
  reduce_mod_char
private theorem pairing_plane (i j r s : ℤ) :
    let x := -i+2*j
    let y := 66*j
    let a := r-s
    let b := 68*r-67*s
    ZMod.stdAddChar ((132*x*a+66*(x*b+y*a)+67*y*b : ℤ) : ZMod 4554) =
      ZMod.stdAddChar ((-i*r+j*(r-s) : ℤ) : ZMod 69) := by
  dsimp only
  rw [← scale69]
  congr 1
  push_cast
  ring_nf
  reduce_mod_char
private theorem pairing_shift (x j c a b t : ℤ) :
    let y := 66*j+c
    let k := b+69*t
    ZMod.stdAddChar ((132*x*a+66*(x*k+y*a)+67*y*k : ℤ) : ZMod 4554) =
      ZMod.stdAddChar ((132*x*a+66*(x*b+y*a)+67*y*b : ℤ) : ZMod 4554) *
      ZMod.stdAddChar ((c*t : ℤ) : ZMod 66) := by
  dsimp only
  rw [← scale66, ← AddChar.map_add_eq_mul]
  congr 1
  push_cast
  ring_nf
  reduce_mod_char

private theorem orbit_minimum (P : ZMod 69 × ZMod 69 → Prop)
    (hrot : ∀ i j, P (-i+j,-i) ↔ P (i,j))
    (href : ∀ i j, P (-i,-j) ↔ P (i,j)) :
    let code (v : ZMod 69 × ZMod 69) := 69*v.1.val+v.2.val
    let orbit (i j : ZMod 69) : Finset (ZMod 69 × ZMod 69) :=
      {(i,j),(-i+j,-i),(-j,i-j),(-i,-j),(i-j,i),(j,-i+j)}
    (∀ i j, (i,j) ≠ (0,0) → (∀ w ∈ orbit i j, code (i,j) ≤ code w) → P (i,j)) →
    ∀ i j, (i,j) ≠ (0,0) → P (i,j) := by
  classical
  intro code orbit hmin
  have transfer (i j : ZMod 69) (w) (hw : w ∈ orbit i j) : P w ↔ P (i,j) := by
    have h₂ : P (-j,i-j) ↔ P (i,j) := by
      convert (hrot (-i+j) (-i)).trans (hrot i j) using 2 <;> abel
    simp only [orbit, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl|rfl|rfl|rfl|rfl|rfl
    · rfl
    · exact hrot i j
    · exact h₂
    · exact href i j
    · convert (href (-i+j) (-i)).trans (hrot i j) using 2 <;> abel
    · convert (href (-j) (i-j)).trans h₂ using 2 <;> abel
  have nonzero (i j : ZMod 69) (hn : (i,j) ≠ (0,0)) (w) (hw : w ∈ orbit i j) :
      w ≠ (0,0) := by
    simp only [orbit, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl|rfl|rfl|rfl|rfl|rfl <;> intro h <;>
      obtain ⟨h₁,h₂⟩ := Prod.mk.inj h <;> apply hn <;> apply Prod.ext <;>
      change _ = (0 : ZMod 69) <;> first | linear_combination h₁ | linear_combination h₂ | linear_combination -h₁ | linear_combination -h₂ | linear_combination h₁-h₂ | linear_combination h₂-h₁
  suffices ∀ n i j, code (i,j) = n → (i,j) ≠ (0,0) → P (i,j) by
    exact fun i j hn => this _ i j rfl hn
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro i j hc hn
    by_cases hm : ∀ w ∈ orbit i j, code (i,j) ≤ code w
    · exact hmin i j hn hm
    · push Not at hm
      obtain ⟨w,hw,hlt⟩ := hm
      exact (transfer i j w hw).mp (ih (code w) (hc ▸ hlt) w.1 w.2 rfl (nonzero i j hn w hw))

/-- Extend the specified boundary values and prove the nonzero-input pentagon identity. -/
def H1 : Prop :=
  let ε : ℝ := (68 + Real.sqrt 4620) / 2
  let γ (t : ℂ) := (314296*t - 4623) / (4623*t - 68)
  let e (z : ℂ) := Complex.exp (2*Real.pi*Complex.I*z)
  let p (x q : ℂ) := ∏' n : ℕ, (1-x*q^n)
  let μ := ModularForm.eta (γ Complex.I) /
    (ModularForm.eta Complex.I * (4623*Complex.I-68)^(1/2 : ℂ))
  let F (r s : ZMod 69) : ℂ :=
    if (r,s) = (0,0) then (Real.sqrt ε : ℂ)^3 else
      let i : ℂ := r.val
      let j : ℂ := s.val
      let z := (i*ε+j)/69
      μ * Filter.limUnder Filter.atTop (fun n : ℕ =>
        let t : ℂ := ε + Complex.I/(n+1)
        p (e (z+(-i-67*j)*t)) (e t) / p (e (z/(4623*t-68))) (e (γ t)))
  let idx (x y : ℤ) : ZMod 69 × ZMod 4554 := (x,y)
  let Q (x y : ℤ) := ZMod.stdAddChar ((132*(x^2+x*y)+67*y^2+4554*y : ℤ) : ZMod 9108)
  let B (x y a b : ℤ) := ZMod.stdAddChar ((132*x*a+66*(x*b+y*a)+67*y*b : ℤ) : ZMod 4554)
  ∃ V : ZMod 69 × ZMod 4554 → ℂ,
    let E (x y : ℤ) := V (idx x y)
    (∀ i j : ℤ, E (-i+2*j) (66*j) = F i j) ∧
    (∀ x y, E (x+y) (66*x+67*y) = E x y) ∧
    (∀ x y, idx x y ≠ 0 → E x y * E (-x) (-y) * Q x y = 1) ∧
    ∀ a b k l : ℤ, idx a b ≠ 0 →
      (∑ u : ZMod 69 × ZMod 4554,
        let x : ℤ := u.1.val
        let y : ℤ := u.2.val
        E x y * E (a-x) (b-y) * Q x y * B x y k l) =
      69 * (Real.sqrt 66 : ℂ) * (Q (a+k) (b+l) * E (-(a+k)) (-(b+l)) * E k l) * E a b

/-- Find one embedding making the boundary value unimodular at the least label of each orbit. -/
def H2 : Prop :=
  let ε : ℝ := (68 + Real.sqrt 4620) / 2
  let γ (t : ℂ) := (314296*t - 4623) / (4623*t - 68)
  let e (z : ℂ) := Complex.exp (2*Real.pi*Complex.I*z)
  let p (x q : ℂ) := ∏' n : ℕ, (1-x*q^n)
  let μ := ModularForm.eta (γ Complex.I) /
    (ModularForm.eta Complex.I * (4623*Complex.I-68)^(1/2 : ℂ))
  let F (r s : ZMod 69) : ℂ :=
    if (r,s) = (0,0) then (Real.sqrt ε : ℂ)^3 else
      let i : ℂ := r.val
      let j : ℂ := s.val
      let z := (i*ε+j)/69
      μ * Filter.limUnder Filter.atTop (fun n : ℕ =>
        let t : ℂ := ε + Complex.I/(n+1)
        p (e (z+(-i-67*j)*t)) (e t) / p (e (z/(4623*t-68))) (e (γ t)))
  let code (v : ZMod 69 × ZMod 69) := 69*v.1.val+v.2.val
  let orbit (i j : ZMod 69) : Finset (ZMod 69 × ZMod 69) :=
    {(i,j),(-i+j,-i),(-j,i-j),(-i,-j),(i-j,i),(j,-i+j)}
  ∃ τ : ℂ →+* ℂ, ∀ i j : ZMod 69, (i,j) ≠ (0,0) → (∀ w ∈ orbit i j, code (i,j) ≤ code w) → ‖τ (F i j)‖ = 1

section

private theorem nonsplit_descent (F : ZMod 69 → ZMod 69 → ℂ)
    (hzero : F 0 0 = (Real.sqrt ((68 + Real.sqrt 4620) / 2) : ℂ)^3)
    (τ : ℂ →+* ℂ) (hunit :
  let code (v : ZMod 69 × ZMod 69) := 69*v.1.val+v.2.val
  let orbit (i j : ZMod 69) : Finset (ZMod 69 × ZMod 69) :=
    {(i,j),(-i+j,-i),(-j,i-j),(-i,-j),(i-j,i),(j,-i+j)}
  ∀ i j : ZMod 69, (i,j) ≠ (0,0) → (∀ w ∈ orbit i j, code (i,j) ≤ code w) → ‖τ (F i j)‖ = 1) :
  let idx (x y : ℤ) : ZMod 69 × ZMod 4554 := (x,y)
  let Q (x y : ℤ) := ZMod.stdAddChar ((132*(x^2+x*y)+67*y^2+4554*y : ℤ) : ZMod 9108)
  let B (x y a b : ℤ) := ZMod.stdAddChar ((132*x*a+66*(x*b+y*a)+67*y*b : ℤ) : ZMod 4554)
  (∃ V : ZMod 69 × ZMod 4554 → ℂ,
    let E (x y : ℤ) := V (idx x y)
    (∀ i j : ℤ, E (-i+2*j) (66*j) = F i j) ∧
    (∀ x y, E (x+y) (66*x+67*y) = E x y) ∧
    (∀ x y, idx x y ≠ 0 → E x y * E (-x) (-y) * Q x y = 1) ∧
    ∀ a b k l : ℤ, idx a b ≠ 0 →
      (∑ u : ZMod 69 × ZMod 4554,
        let x : ℤ := u.1.val
        let y : ℤ := u.2.val
        E x y * E (a-x) (b-y) * Q x y * B x y k l) =
      69 * (Real.sqrt 66 : ℂ) * (Q (a+k) (b+l) * E (-(a+k)) (-(b+l)) * E k l) * E a b) → OpenQuantumProblem23.HasSICPOVM 69 := by
  classical
  intro idx Q B h
  obtain ⟨V, hslice, hrot, href, hpent⟩ := h
  let E (x y : ℤ) := V (idx x y)
  let val (i : ZMod 69) : ℤ := i.val
  have val_cast (i : ZMod 69) : (val i : ZMod 69) = i := by simp [val]
  have plane_ne (i j : ℤ) (hn : ((i : ZMod 69), (j : ZMod 69)) ≠ (0,0)) :
      idx (-i+2*j) (66*j) ≠ 0 := by
    intro h
    have h₁ : ((-i+2*j : ℤ) : ZMod 69) = 0 := congrArg Prod.fst h
    have h₂ : ((66*j : ℤ) : ZMod 4554) = 0 := congrArg Prod.snd h
    apply hn
    apply Prod.ext <;> change ((_ : ℤ) : ZMod 69) = 0
    all_goals
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at *
      omega
  -- The 66 lifts of a plane label rotate to their respective translates by that label.
  have cancel (r s t : ℤ) (hn : ((r : ZMod 69),(s : ZMod 69)) ≠ (0,0)) :
      let a := -r+2*s
      let b := 66*s
      let k := r-s
      let l := 68*r-67*s+69*t
      Q (a+k) (b+l) * E (-(a+k)) (-(b+l)) * E k l = 1 := by
    intro a b k l
    have hrotate : idx (k+l) (66*k+67*l) = idx (a+k) (b+l) := by
      apply Prod.ext <;> dsimp [idx, a, b, k, l] <;> push_cast <;> ring_nf <;> reduce_mod_char <;> ring_nf <;> reduce_mod_char
    have heq : E k l = E (a+k) (b+l) := (hrot k l).symm.trans (congrArg V hrotate)
    have hn' : idx (a+k) (b+l) ≠ 0 := by
      intro h
      have h₁ : ((a+k : ℤ) : ZMod 69) = 0 := congrArg Prod.fst h
      have h₂ : ((b+l : ℤ) : ZMod 4554) = 0 := congrArg Prod.snd h
      dsimp [a,b,k,l] at h₁ h₂
      apply hn
      apply Prod.ext <;> change ((_ : ℤ) : ZMod 69) = 0
      all_goals
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at *
        omega
    rw [heq]
    convert href (a+k) (b+l) hn' using 1 <;> ring
  let gauss (i j : ZMod 69) := ZMod.stdAddChar (i^2-i*j+j^2)
  let phase (i j r s : ZMod 69) := ZMod.stdAddChar (-i*r+j*(r-s))
  have reflect_int (i j : ℤ) (hne : ((i : ZMod 69),(j : ZMod 69)) ≠ (0,0)) :
      F i j * F (-i) (-j) * gauss i j = 1 := by
    have e := href _ _ (plane_ne i j hne)
    change E (-i+2*j) (66*j) * E (-(-i+2*j)) (-(66*j)) * Q (-i+2*j) (66*j) = 1 at e
    rw [show -(-i+2*j) = -(-i)+2*(-j) by ring, show -(66*j) = 66*(-j) by ring,
      show Q (-i+2*j) (66*j) = _ from gaussian_plane i j] at e
    change ∀ a b : ℤ, E (-a+2*b) (66*b) = F a b at hslice
    rw [hslice, hslice] at e
    simpa [gauss] using e
  have hr (i j : ZMod 69) (hn : (i,j) ≠ (0,0)) : F i j * F (-i) (-j) = (gauss i j)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    have e := reflect_int (val i) (val j) (by simpa only [val_cast] using hn)
    simpa only [val_cast] using e
  have full_unit : ∀ i j : ZMod 69, (i,j) ≠ (0,0) → ‖τ (F i j)‖ = 1 := by
    apply orbit_minimum (fun v => ‖τ (F v.1 v.2)‖ = 1) _ _ hunit
    · intro i j
      let u := val i
      let v := val j
      have eqidx : idx (-(-u+v)+2*(-u)) (66*(-u)) =
          idx ((-u+2*v)+66*v) (66*(-u+2*v)+67*(66*v)) := by
        apply Prod.ext <;> dsimp only [idx,Prod.mk.injEq] <;> push_cast <;> ring_nf <;> reduce_mod_char <;> ring_nf <;> reduce_mod_char
      have hf : F ((-u+v : ℤ) : ZMod 69) ((-u : ℤ) : ZMod 69) = F u v :=
        (hslice (-u+v) (-u)).symm.trans ((congrArg V eqidx).trans
          ((hrot (-u+2*v) (66*v)).trans (hslice u v)))
      have hfj : F (-i+j) (-i) = F i j := by simpa [u,v,val_cast] using hf
      simp only [hfj]
    · intro i j
      change (‖τ (F (-i) (-j))‖ = 1) ↔ (‖τ (F i j)‖ = 1)
      by_cases hz : (i,j) = (0,0)
      · obtain ⟨rfl,rfl⟩ := Prod.mk.inj hz
        simp
      have root (z : ZMod 69) : ZMod.stdAddChar z ^ 69 = 1 := by
        rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self,
          zero_mul, AddChar.map_zero_eq_one]
      have hg : ‖τ (gauss i j)‖ = 1 := by
        apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : 69 ≠ 0)).mp
        rw [← norm_pow, ← map_pow, root, map_one, norm_one]
      have hprod := congrArg (fun z => ‖τ z‖) (hr i j hz)
      simp only [map_mul, norm_mul, map_inv₀, norm_inv, hg, inv_one] at hprod
      constructor <;> intro e <;> simpa [e] using hprod
  let total (r s : ZMod 69) := ∑ i, ∑ j, F i j * F (r-i) (s-j) * gauss i j * phase i j r s
  have nonzero (r s : ℤ) (hn : ((r : ZMod 69),(s : ZMod 69)) ≠ (0,0)) :
      total r s = 69 * (Real.sqrt 66 : ℂ) * F r s := by
    let a := -r+2*s
    let b := 66*s
    let k := r-s
    let l := 68*r-67*s
    let term (i j : ZMod 69) (c : ZMod 66) :=
      let x := -(val i)+2*val j
      let y : ℤ := 66*val j+c.val
      E x y * E (a-x) (b-y) * Q x y * B x y k l
    let slice (c : ZMod 66) := ∑ i, ∑ j, term i j c
    have fourier (t : ZMod 66) :
        (∑ c : ZMod 66, slice c * ZMod.stdAddChar (c*t)) =
        69 * (Real.sqrt 66 : ℂ) * F r s := by
      let m := l+69*(t.val : ℤ)
      let T (x y : ℤ) := E x y * E (a-x) (b-y) * Q x y * B x y k m
      have hperiod (x y n : ℤ) : T (x+69*n) y = T x y := by
        have ix : idx (x+69*n) y = idx x y := by
          apply Prod.ext <;> dsimp [idx] <;> push_cast <;> ring_nf <;> reduce_mod_char
        have iv : idx (a-(x+69*n)) (b-y) = idx (a-x) (b-y) := by
          apply Prod.ext <;> dsimp [idx] <;> push_cast <;> ring_nf <;> reduce_mod_char
        have hq : Q (x+69*n) y = Q x y := (character_period x y k m n).1
        have hb : B (x+69*n) y k m = B x y k m := (character_period x y k m n).2
        simp only [T,E,ix,iv,hq,hb]
      have hp := (enumerate_sum T hperiod).trans (hpent a b k m (plane_ne r s hn))
      rw [show Q (a+k) (b+(l+69*(t.val:ℤ))) * E (-(a+k)) (-(b+(l+69*(t.val:ℤ)))) *
        E k (l+69*(t.val:ℤ)) = 1 from cancel r s t.val hn, mul_one] at hp
      change ∀ i j : ℤ, E (-i+2*j) (66*j) = F i j at hslice
      rw [← hslice]
      refine Eq.trans ?_ hp
      apply Finset.sum_congr rfl
      intro c _
      simp only [slice, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      let x := -val i+2*val j
      let y : ℤ := 66*val j+c.val
      have hB : B x y k (l+69*(t.val:ℤ)) = B x y k l * ZMod.stdAddChar (c*t) := by
        simpa [B,y] using pairing_shift x (val j) c.val k l t.val
      change (E x y * E (a-x) (b-y) * Q x y * B x y k l) * _ =
        E x y * E (a-x) (b-y) * Q x y * B x y k (l+69*(t.val:ℤ))
      rw [hB, mul_assoc]
    -- Orthogonality retains exactly the plane where the second Smith coordinate is divisible by 66.
    have sum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun t _ => fourier t)
    rw [average_axis] at sum
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, Nat.cast_ofNat] at sum
    have h0 : total r s = slice 0 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      let u := val i
      let v := val j
      change F i j * F (_-i) (_-j) * gauss i j * phase i j r s =
        E (-u+2*v) (66*v+(0 : ZMod 66).val) * E (a-(-u+2*v)) (b-(66*v+(0 : ZMod 66).val)) *
        Q (-u+2*v) (66*v+(0 : ZMod 66).val) * B (-u+2*v) (66*v+(0 : ZMod 66).val) k l
      simp only [ZMod.val_zero, Nat.cast_zero, add_zero]
      change ∀ i j : ℤ, E (-i+2*j) (66*j) = F i j at hslice
      rw [show a-(-u+2*v) = -(r-u)+2*(s-v) by dsimp [a]; ring,
        show b-66*v = 66*(s-v) by dsimp [b]; ring, hslice, hslice,
        show Q (-u+2*v) (66*v) = _ from gaussian_plane u v,
        show B (-u+2*v) (66*v) k l = _ from pairing_plane u v r s]
      simp [u,v,val_cast,gauss,phase]
    rw [h0]
    linear_combination sum / 66
  have conv (r s : ZMod 69) : total r s =
      69 * ((Real.sqrt 66 : ℂ) * F r s + if (r,s) = (0,0) then 69 else 0) := by
    by_cases h : (r,s) = (0,0)
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
      have one_term (i j : ZMod 69) : F i j * F (0-i) (0-j) * gauss i j * phase i j 0 0 =
          1 + if (i,j) = (0,0) then (F 0 0)^2-1 else 0 := by
        by_cases hi : (i,j) = (0,0)
        · obtain ⟨rfl,rfl⟩ := Prod.mk.inj hi
          simp [phase, gauss, pow_two]
        · simp only [if_neg hi, add_zero, zero_sub]
          rw [hr i j hi]
          simp [phase, gauss, show ZMod.stdAddChar (i^2-i*j+j^2) ≠ 0 from
            Circle.coe_ne_zero _]
      have scalar : (F 0 0)^2-1 = 69 * (Real.sqrt 66 : ℂ) * F 0 0 := by
        rw [hzero]
        exact scalar_origin
      unfold total
      simp_rw [one_term]
      simp [Finset.sum_add_distrib, Prod.mk.injEq, ite_and, Finset.sum_ite_irrel, ZMod.card, scalar]
      <;> ring
    · have h' := nonzero (val r) (val s) (by simpa only [val_cast] using h)
      simpa only [val_cast, if_neg h, add_zero, mul_assoc] using h'
  obtain ⟨A, hH, hA, htr, hflat⟩ := matrixConversion F τ hzero hr (by
    intro r s
    apply (inv_mul_eq_iff_eq_mul₀ (by norm_num : (69:ℂ) ≠ 0)).2
    exact conv r s) full_unit
  apply orbit_of_matrix A hH hA htr
  intro a b hab
  convert hflat a b hab using 1 <;> norm_num [OpenQuantumProblem23.sicOverlapSq]

theorem main : H1 → H2 → type_of% @OpenQuantumProblem23.hasSICPOVM_69 := by
  classical
  let ε : ℝ := (68 + Real.sqrt 4620) / 2
  let γ (t : ℂ) := (314296*t - 4623) / (4623*t - 68)
  let e (z : ℂ) := Complex.exp (2*Real.pi*Complex.I*z)
  let p (x q : ℂ) := ∏' n : ℕ, (1-x*q^n)
  let μ := ModularForm.eta (γ Complex.I) /
    (ModularForm.eta Complex.I * (4623*Complex.I-68)^(1/2 : ℂ))
  let F (r s : ZMod 69) : ℂ :=
    if (r,s) = (0,0) then (Real.sqrt ε : ℂ)^3 else
      let i : ℂ := r.val
      let j : ℂ := s.val
      let z := (i*ε+j)/69
      μ * Filter.limUnder Filter.atTop (fun n : ℕ =>
        let t : ℂ := ε + Complex.I/(n+1)
        p (e (z+(-i-67*j)*t)) (e t) / p (e (z/(4623*t-68))) (e (γ t)))
  intro hanalytic harithmetic
  obtain ⟨τ, hτ⟩ := harithmetic
  exact nonsplit_descent F (by simp [F, ε]) τ hτ hanalytic

end
end
end OMA.R_OpenQuantumProblem23_hasSICPOVM_69_R1
