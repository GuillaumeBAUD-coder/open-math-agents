import OMAReductions.R_Erdos1066_erdos_1066_variants_swanepoel_R1

/-!
Proof of `Erdos1066.erdos_1066.variants.swanepoel.R1.H2`.

Using the isometric identification `v : EuclideanSpace ℝ (Fin 2) → ℂ`, the unit-distance
equilateral triangles `(p m, p (m + 1), q m)` and `(p (m + 1), p (m + 2), q (m + 1))`
combined with `dist (q m) (q (m + 1)) = 1` and `t m ∈ [0, π/3)` force `t m = 0` for all
`2 ≤ m ≤ 10`. Around each `q m` (`2 ≤ m ≤ 11`), the six unit-distance neighbors in `X`
in strictly increasing counterclockwise angle order have pairwise distance at least `1`,
so consecutive angle gaps are all `≥ π/3` and sum to `2π`, forcing a regular hexagon.
Opposite-vertex relations at `q m` and `q (m + 1)` then yield `s m = r (m + 1)` for all
`2 ≤ m ≤ 10`, discharging both implications in `H2`.
-/

namespace Erdos1066SwanepoelR1H2

open Finset Real
open scoped EuclideanGeometry Topology

private def v (x : EuclideanSpace ℝ (Fin 2)) : ℂ := ⟨x 0, x 1⟩

private noncomputable def A (x y z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  let u := Complex.arg ((v z - v y) / (v x - v y))
  if u < 0 then u + 2 * π else u

private lemma v_inj : Function.Injective v := by
  intro x y h
  ext i
  fin_cases i
  · exact congrArg Complex.re h
  · exact congrArg Complex.im h

private lemma norm_v_sub_eq_dist (x y : EuclideanSpace ℝ (Fin 2)) :
    ‖v x - v y‖ = dist x y := by
  have hsq : ‖v x - v y‖ ^ 2 = dist x y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, EuclideanSpace.dist_eq,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Fin.sum_univ_two]
    simp only [v, Complex.sub_re, Complex.sub_im, Real.dist_eq, sq_abs]
    ring
  nlinarith [norm_nonneg (v x - v y), dist_nonneg (x := x) (y := y)]

private lemma A_mem_Ico (x y z : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ A x y z ∧ A x y z < 2 * π := by
  dsimp only [A]
  set u := Complex.arg ((v z - v y) / (v x - v y))
  have h1 : -π < u := Complex.neg_pi_lt_arg _
  have h2 : u ≤ π := Complex.arg_le_pi _
  split_ifs with h
  · constructor <;> linarith [Real.pi_pos]
  · constructor <;> linarith [Real.pi_pos]

private lemma A_self {x y : EuclideanSpace ℝ (Fin 2)} (hxy : dist x y = 1) :
    A x y x = 0 := by
  have hne : v x - v y ≠ 0 := by
    intro h0
    have hnorm : ‖v x - v y‖ = 0 := by rw [h0, norm_zero]
    rw [norm_v_sub_eq_dist, hxy] at hnorm
    norm_num at hnorm
  dsimp only [A]
  rw [div_self hne, Complex.arg_one]
  simp

private lemma div_eq_exp_I_mul_A {x y z : EuclideanSpace ℝ (Fin 2)}
    (hxy : dist x y = 1) (hzy : dist z y = 1) :
    (v z - v y) / (v x - v y) = Complex.exp (Complex.I * (A x y z : ℂ)) := by
  set w : ℂ := (v z - v y) / (v x - v y)
  have hnorm : ‖w‖ = 1 := by
    dsimp [w]
    rw [norm_div, norm_v_sub_eq_dist, norm_v_sub_eq_dist, hzy, hxy, div_one]
  have hpolar : w = Complex.exp (Complex.I * (Complex.arg w : ℂ)) := by
    have h := Complex.norm_mul_exp_arg_mul_I w
    rw [hnorm, Complex.ofReal_one, one_mul, mul_comm] at h
    exact h.symm
  dsimp only [A]
  split_ifs with hlt
  · rw [hpolar, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat, mul_add,
      Complex.exp_add]
    have h2pi : Complex.exp (Complex.I * (2 * (π : ℂ))) = 1 := by
      rw [show Complex.I * (2 * (π : ℂ)) = 2 * (π : ℂ) * Complex.I by ring]
      exact Complex.exp_two_pi_mul_I
    rw [h2pi, mul_one]
  · exact hpolar

private lemma norm_exp_I_sub_exp_I_sq (θ φ : ℝ) :
    ‖Complex.exp (Complex.I * (θ : ℂ)) - Complex.exp (Complex.I * (φ : ℂ))‖ ^ 2 =
      2 - 2 * Real.cos (θ - φ) := by
  rw [mul_comm Complex.I (θ : ℂ), mul_comm Complex.I (φ : ℂ),
    Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.sq_norm, Complex.normSq_apply]
  have hre : (((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) -
      ((Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I)).re = Real.cos θ - Real.cos φ := by
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have him : (((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) -
      ((Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I)).im = Real.sin θ - Real.sin φ := by
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  rw [hre, him, Real.cos_sub]
  have h1 := Real.sin_sq_add_cos_sq θ
  have h2 := Real.sin_sq_add_cos_sq φ
  nlinarith

private lemma dist_sq_eq_two_sub_two_cos {x y z₁ z₂ : EuclideanSpace ℝ (Fin 2)}
    (hxy : dist x y = 1) (hz₁ : dist z₁ y = 1) (hz₂ : dist z₂ y = 1) :
    dist z₁ z₂ ^ 2 = 2 - 2 * Real.cos (A x y z₁ - A x y z₂) := by
  have hne : v x - v y ≠ 0 := by
    intro h0
    have := norm_v_sub_eq_dist x y
    rw [h0, norm_zero, hxy] at this
    norm_num at this
  have h1 : v z₁ - v y = Complex.exp (Complex.I * (A x y z₁ : ℂ)) * (v x - v y) :=
    (div_eq_iff hne).mp (div_eq_exp_I_mul_A hxy hz₁)
  have h2 : v z₂ - v y = Complex.exp (Complex.I * (A x y z₂ : ℂ)) * (v x - v y) :=
    (div_eq_iff hne).mp (div_eq_exp_I_mul_A hxy hz₂)
  have hdiff : v z₁ - v z₂ =
      (v x - v y) * (Complex.exp (Complex.I * (A x y z₁ : ℂ)) -
        Complex.exp (Complex.I * (A x y z₂ : ℂ))) := by
    linear_combination h1 - h2
  rw [← norm_v_sub_eq_dist, hdiff, norm_mul, norm_v_sub_eq_dist, hxy, one_mul]
  exact norm_exp_I_sub_exp_I_sq (A x y z₁) (A x y z₂)

private lemma pi_div_three_bounds_of_cos_le_half {δ : ℝ}
    (h0 : 0 ≤ δ) (h2pi : δ ≤ 2 * π) (hcos : Real.cos δ ≤ 1 / 2) :
    π / 3 ≤ δ ∧ δ ≤ 5 * π / 3 := by
  constructor
  · by_contra hlt
    push Not at hlt
    have hgt : Real.cos (π / 3) < Real.cos δ :=
      Real.strictAntiOn_cos ⟨h0, by linarith [Real.pi_pos]⟩
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ hlt
    rw [Real.cos_pi_div_three] at hgt
    linarith
  · by_contra hgt
    push Not at hgt
    have hcos' : Real.cos (2 * π - δ) ≤ 1 / 2 := by
      simpa [Real.cos_two_pi_sub] using hcos
    have hlt' : 2 * π - δ < π / 3 := by linarith
    have hgt' : Real.cos (π / 3) < Real.cos (2 * π - δ) :=
      Real.strictAntiOn_cos ⟨by linarith, by linarith [Real.pi_pos]⟩
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ hlt'
    rw [Real.cos_pi_div_three] at hgt'
    linarith

private lemma hexagon_angles {X : Finset (EuclideanSpace ℝ (Fin 2))}
    (hX : (X : Set (EuclideanSpace ℝ (Fin 2))).Pairwise (fun x y => 1 ≤ dist x y))
    {Q : EuclideanSpace ℝ (Fin 2)} {w : Fin 6 → EuclideanSpace ℝ (Fin 2)}
    (hwX : ∀ j : Fin 6, w j ∈ X)
    (hdist : ∀ j : Fin 6, dist Q (w j) = 1)
    (hmono : StrictMono (fun j : Fin 6 => A (w 0) Q (w j))) :
    ∀ j : Fin 6, A (w 0) Q (w j) = (j.val : ℝ) * (π / 3) := by
  let θ : Fin 6 → ℝ := fun j => A (w 0) Q (w j)
  have hdist' : ∀ j : Fin 6, dist (w j) Q = 1 := fun j => by rw [dist_comm]; exact hdist j
  have hθ0 : θ 0 = 0 := A_self (hdist' 0)
  have hpair : ∀ j₁ j₂ : Fin 6, j₁ < j₂ →
      π / 3 ≤ θ j₂ - θ j₁ ∧ θ j₂ - θ j₁ ≤ 5 * π / 3 := by
    intro j₁ j₂ hlt
    have hne : w j₁ ≠ w j₂ := fun heq =>
      ne_of_lt (hmono hlt) (by simp only [heq])
    have hd : 1 ≤ dist (w j₂) (w j₁) := hX (hwX j₂) (hwX j₁) hne.symm
    have hsq : 1 ≤ dist (w j₂) (w j₁) ^ 2 := by nlinarith
    rw [dist_sq_eq_two_sub_two_cos (hdist' 0) (hdist' j₂) (hdist' j₁)] at hsq
    have hcos : Real.cos (θ j₂ - θ j₁) ≤ 1 / 2 := by linarith
    have h0 : 0 ≤ θ j₂ - θ j₁ := sub_nonneg.mpr (hmono hlt).le
    have h2pi : θ j₂ - θ j₁ ≤ 2 * π := by
      have hm1 := A_mem_Ico (w 0) Q (w j₁)
      have hm2 := A_mem_Ico (w 0) Q (w j₂)
      linarith
    exact pi_div_three_bounds_of_cos_le_half h0 h2pi hcos
  have g01 := (hpair 0 1 (by decide)).1
  have g12 := (hpair 1 2 (by decide)).1
  have g23 := (hpair 2 3 (by decide)).1
  have g34 := (hpair 3 4 (by decide)).1
  have g45 := (hpair 4 5 (by decide)).1
  have g05 := (hpair 0 5 (by decide)).2
  intro j
  fin_cases j <;> dsimp [θ] at hθ0 g01 g12 g23 g34 g45 g05 ⊢ <;> linarith

private lemma exp_I_two_pi_div_three_eq :
    Complex.exp (Complex.I * ((2 * π / 3 : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((π / 3 : ℝ) : ℂ)) - 1 := by
  have h1 : Complex.exp (Complex.I * ((π / 3 : ℝ) : ℂ)) =
      (1 / 2 : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
    rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
    push_cast
    rfl
  have h2 : Complex.exp (Complex.I * ((2 * π / 3 : ℝ) : ℂ)) =
      (-1 / 2 : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * Complex.I := by
    rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hcos : Real.cos (2 * π / 3) = -1 / 2 := by
      rw [show (2 * π / 3 : ℝ) = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
      ring
    have hsin : Real.sin (2 * π / 3) = Real.sqrt 3 / 2 := by
      rw [show (2 * π / 3 : ℝ) = π - π / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
    rw [hcos, hsin]
    push_cast
    rfl
  rw [h1, h2]
  ring

end Erdos1066SwanepoelR1H2

open Finset Real Erdos1066SwanepoelR1H2
open scoped EuclideanGeometry Topology

theorem OMA.solution : OMA.R_Erdos1066_erdos_1066_variants_swanepoel_R1.H2 := by
  classical
  dsimp only [OMA.R_Erdos1066_erdos_1066_variants_swanepoel_R1.H2]
  intro X hX p q r s t hcfg ht_nonneg ht_sum
  rcases hcfg with ⟨hpX, hqX, hrsX, _hp_inj, htri, _hdeg4, hq_dist, hq_mono, ht_eq⟩
  have hzeta_eq :
      ∀ m < 13, v (q m) - v (p m) =
        Complex.exp (Complex.I * ((π / 3 : ℝ) : ℂ)) * (v (p (m + 1)) - v (p m)) := by
    intro m hm
    obtain ⟨h1, h2, _h3, hA⟩ := htri m hm
    have h1' : dist (p (m + 1)) (p m) = 1 := by rw [dist_comm]; exact h1
    have h2' : dist (q m) (p m) = 1 := by rw [dist_comm]; exact h2
    have hdiv := div_eq_exp_I_mul_A h1' h2'
    have hA' : A (p (m + 1)) (p m) (q m) = π / 3 := hA
    rw [hA'] at hdiv
    have hne : v (p (m + 1)) - v (p m) ≠ 0 := by
      intro h0
      have := norm_v_sub_eq_dist (p (m + 1)) (p m)
      rw [h0, norm_zero, h1'] at this
      norm_num at this
    exact (div_eq_iff hne).mp hdiv
  have hzeta2_eq :
      ∀ m < 13, v (q m) - v (p (m + 1)) =
        Complex.exp (Complex.I * ((2 * π / 3 : ℝ) : ℂ)) * (v (p (m + 1)) - v (p m)) := by
    intro m hm
    rw [exp_I_two_pi_div_three_eq, sub_mul, one_mul, ← hzeta_eq m hm]
    ring
  have hs_eq_r : ∀ m, 2 ≤ m → m ≤ 10 → s m = r (m + 1) := by
    intro m hm2 hm10
    set e₁ : ℂ := v (p (m + 1)) - v (p m)
    set e₂ : ℂ := v (p (m + 2)) - v (p (m + 1))
    have he₁_norm : ‖e₁‖ = 1 := by
      dsimp [e₁]; rw [norm_v_sub_eq_dist, dist_comm]; exact (htri m (by omega)).1
    have he₂_norm : ‖e₂‖ = 1 := by
      dsimp [e₂]; rw [norm_v_sub_eq_dist, dist_comm]; exact (htri (m + 1) (by omega)).1
    have he₂_ne : e₂ ≠ 0 := by
      intro h0; rw [h0, norm_zero] at he₂_norm; norm_num at he₂_norm
    have ht_lt : t m < π / 3 := by
      have hle : t m ≤ ∑ k ∈ range 13, t k :=
        Finset.single_le_sum (fun k hk => ht_nonneg k (Finset.mem_range.mp hk))
          (Finset.mem_range.mpr (by omega))
      linarith
    have ht_nonneg_m : 0 ≤ t m := ht_nonneg m (by omega)
    have hturn : e₁ = Complex.exp (Complex.I * (t m : ℂ)) * e₂ := by
      have hA_eq : A (p (m + 2)) (p (m + 1)) (p m) = π + t m := by
        have h := ht_eq (m + 1) (by omega) (by omega)
        have hsub : m + 1 - 1 = m := by omega
        rw [hsub] at h
        change t m = A (p (m + 2)) (p (m + 1)) (p m) - π at h
        linarith
      have hd1 : dist (p (m + 2)) (p (m + 1)) = 1 := by
        rw [dist_comm]; exact (htri (m + 1) (by omega)).1
      have hd2 : dist (p m) (p (m + 1)) = 1 := (htri m (by omega)).1
      have hdiv := div_eq_exp_I_mul_A hd1 hd2
      rw [hA_eq] at hdiv
      have hneg : v (p m) - v (p (m + 1)) = -e₁ := by dsimp [e₁]; ring
      change (v (p m) - v (p (m + 1))) / e₂ = Complex.exp (Complex.I * ((π + t m : ℝ) : ℂ)) at hdiv
      rw [hneg, Complex.ofReal_add, mul_add, Complex.exp_add,
        mul_comm Complex.I (π : ℂ), Complex.exp_pi_mul_I] at hdiv
      have hdiv' : -e₁ = -(Complex.exp (Complex.I * (t m : ℂ)) * e₂) := by
        have := (div_eq_iff he₂_ne).mp hdiv
        linear_combination this
      linear_combination -hdiv'
    have htm_zero : t m = 0 := by
      have hqm_dist : dist (q m) (q (m + 1)) = 1 := by
        simpa using hq_dist m hm2 (by omega) 5
      have hqdiff : v (q m) - v (q (m + 1)) =
          Complex.exp (Complex.I * ((π / 3 : ℝ) : ℂ)) * e₂ *
            (Complex.exp (Complex.I * ((π / 3 + t m : ℝ) : ℂ)) -
              Complex.exp (Complex.I * ((0 : ℝ) : ℂ))) := by
        have h1 : v (q m) - v (p (m + 1)) =
            Complex.exp (Complex.I * ((2 * π / 3 : ℝ) : ℂ)) * e₁ := hzeta2_eq m (by omega)
        have h2 : v (q (m + 1)) - v (p (m + 1)) =
            Complex.exp (Complex.I * ((π / 3 : ℝ) : ℂ)) * e₂ := hzeta_eq (m + 1) (by omega)
        have h3 : v (q m) - v (q (m + 1)) =
            (v (q m) - v (p (m + 1))) - (v (q (m + 1)) - v (p (m + 1))) := by ring
        rw [h3, h1, h2, hturn]
        have hexp_prod :
            Complex.exp (Complex.I * ((2 * π / 3 : ℝ) : ℂ)) *
              Complex.exp (Complex.I * (t m : ℂ)) =
            Complex.exp (Complex.I * ((π / 3 : ℝ) : ℂ)) *
              Complex.exp (Complex.I * ((π / 3 + t m : ℝ) : ℂ)) := by
          rw [← Complex.exp_add, ← Complex.exp_add]
          congr 1
          push_cast
          ring
        have hexp0 : Complex.exp (Complex.I * ((0 : ℝ) : ℂ)) = 1 := by simp
        rw [hexp0]
        linear_combination e₂ * hexp_prod
      have hnorm_sq : (1 : ℝ) = 2 - 2 * Real.cos (π / 3 + t m) := by
        have h1 : dist (q m) (q (m + 1)) ^ 2 = 1 := by rw [hqm_dist]; norm_num
        rw [← h1, ← norm_v_sub_eq_dist, hqdiff, norm_mul, norm_mul, he₂_norm, mul_one]
        have hexp_norm : ‖Complex.exp (Complex.I * ((π / 3 : ℝ) : ℂ))‖ = 1 := by
          rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
        rw [hexp_norm, one_mul, norm_exp_I_sub_exp_I_sq, sub_zero]
      have hcos_eq : Real.cos (π / 3 + t m) = Real.cos (π / 3) := by
        rw [Real.cos_pi_div_three]; linarith
      have hinj := Real.strictAntiOn_cos.injOn
        (show π / 3 + t m ∈ Set.Icc 0 π by constructor <;> linarith [Real.pi_pos])
        (show π / 3 ∈ Set.Icc 0 π by constructor <;> linarith [Real.pi_pos])
        hcos_eq
      linarith
    have he_eq : e₁ = e₂ := by
      rw [hturn, htm_zero]
      simp
    have hhex_m : ∀ j : Fin 6,
        A (s m) (q m) (![s m, r m, q (m - 1), p m, p (m + 1), q (m + 1)] j) =
          (j.val : ℝ) * (π / 3) := by
      refine hexagon_angles hX (fun j => ?_) (hq_dist m hm2 (by omega))
        (hq_mono m hm2 (by omega))
      fin_cases j
      · exact (hrsX m hm2 (by omega)).2
      · exact (hrsX m hm2 (by omega)).1
      · exact hqX (m - 1) (by omega)
      · exact hpX m (by omega)
      · exact hpX (m + 1) (by omega)
      · exact hqX (m + 1) (by omega)
    have hhex_m1 : ∀ j : Fin 6,
        A (s (m + 1)) (q (m + 1))
          (![s (m + 1), r (m + 1), q (m + 1 - 1), p (m + 1), p (m + 2), q (m + 2)] j) =
          (j.val : ℝ) * (π / 3) := by
      refine hexagon_angles hX (fun j => ?_) (hq_dist (m + 1) (by omega) (by omega))
        (hq_mono (m + 1) (by omega) (by omega))
      fin_cases j
      · exact (hrsX (m + 1) (by omega) (by omega)).2
      · exact (hrsX (m + 1) (by omega) (by omega)).1
      · exact hqX (m + 1 - 1) (by omega)
      · exact hpX (m + 1) (by omega)
      · exact hpX (m + 2) (by omega)
      · exact hqX (m + 2) (by omega)
    have hsm : v (s m) - v (q m) = Complex.exp (Complex.I * ((π / 3 : ℝ) : ℂ)) * e₁ := by
      have hd0 : dist (s m) (q m) = 1 := by
        rw [dist_comm]; simpa using hq_dist m hm2 (by omega) 0
      have hd3 : dist (p m) (q m) = 1 := by
        rw [dist_comm]; simpa using hq_dist m hm2 (by omega) 3
      have hdiv := div_eq_exp_I_mul_A hd0 hd3
      have hA3 : A (s m) (q m) (p m) = π := by
        have h := hhex_m 3
        change A (s m) (q m) (p m) = ((3 : ℕ) : ℝ) * (π / 3) at h
        push_cast at h
        linarith
      rw [hA3, mul_comm Complex.I (π : ℂ), Complex.exp_pi_mul_I] at hdiv
      have hne0 : v (s m) - v (q m) ≠ 0 := by
        intro h0; have := norm_v_sub_eq_dist (s m) (q m)
        rw [h0, norm_zero, hd0] at this; norm_num at this
      have hopp : v (p m) - v (q m) = -(v (s m) - v (q m)) := by
        have := (div_eq_iff hne0).mp hdiv
        linear_combination this
      have hqm : v (q m) - v (p m) = Complex.exp (Complex.I * ((π / 3 : ℝ) : ℂ)) * e₁ :=
        hzeta_eq m (by omega)
      linear_combination hopp + hqm
    have hrm1 : v (r (m + 1)) - v (q (m + 1)) =
        Complex.exp (Complex.I * ((2 * π / 3 : ℝ) : ℂ)) * e₂ := by
      have hd0 : dist (s (m + 1)) (q (m + 1)) = 1 := by
        rw [dist_comm]; simpa using hq_dist (m + 1) (by omega) (by omega) 0
      have hd1 : dist (r (m + 1)) (q (m + 1)) = 1 := by
        rw [dist_comm]; simpa using hq_dist (m + 1) (by omega) (by omega) 1
      have hd4 : dist (p (m + 2)) (q (m + 1)) = 1 := by
        rw [dist_comm]; simpa using hq_dist (m + 1) (by omega) (by omega) 4
      have hdiv1 := div_eq_exp_I_mul_A hd0 hd1
      have hdiv4 := div_eq_exp_I_mul_A hd0 hd4
      have hA1 : A (s (m + 1)) (q (m + 1)) (r (m + 1)) = π / 3 := by
        have h := hhex_m1 1
        simpa using h
      have hA4 : A (s (m + 1)) (q (m + 1)) (p (m + 2)) = 4 * π / 3 := by
        have h := hhex_m1 4
        change A (s (m + 1)) (q (m + 1)) (p (m + 2)) = ((4 : ℕ) : ℝ) * (π / 3) at h
        push_cast at h
        linarith
      rw [hA1] at hdiv1
      rw [hA4] at hdiv4
      have hne0 : v (s (m + 1)) - v (q (m + 1)) ≠ 0 := by
        intro h0; have := norm_v_sub_eq_dist (s (m + 1)) (q (m + 1))
        rw [h0, norm_zero, hd0] at this; norm_num at this
      have h1 := (div_eq_iff hne0).mp hdiv1
      have h4 := (div_eq_iff hne0).mp hdiv4
      have hexp_opp :
          Complex.exp (Complex.I * ((4 * π / 3 : ℝ) : ℂ)) =
            -Complex.exp (Complex.I * ((π / 3 : ℝ) : ℂ)) := by
        have hsplit : Complex.I * ((4 * π / 3 : ℝ) : ℂ) =
            (π : ℂ) * Complex.I + Complex.I * ((π / 3 : ℝ) : ℂ) := by
          push_cast; ring
        rw [hsplit, Complex.exp_add, Complex.exp_pi_mul_I]
        ring
      rw [hexp_opp] at h4
      have hopp : v (r (m + 1)) - v (q (m + 1)) = -(v (p (m + 2)) - v (q (m + 1))) := by
        linear_combination h1 + h4
      have hqm1 : v (q (m + 1)) - v (p (m + 2)) =
          Complex.exp (Complex.I * ((2 * π / 3 : ℝ) : ℂ)) * e₂ :=
        hzeta2_eq (m + 1) (by omega)
      linear_combination hopp + hqm1
    have hq_step : v (q (m + 1)) - v (q m) = e₂ := by
      have h1 : v (q (m + 1)) - v (p (m + 1)) =
          Complex.exp (Complex.I * ((π / 3 : ℝ) : ℂ)) * e₂ :=
        hzeta_eq (m + 1) (by omega)
      have h2 : v (q m) - v (p (m + 1)) =
          Complex.exp (Complex.I * ((2 * π / 3 : ℝ) : ℂ)) * e₁ :=
        hzeta2_eq m (by omega)
      rw [he_eq] at h2
      have hsub_exp :
          Complex.exp (Complex.I * ((π / 3 : ℝ) : ℂ)) -
            Complex.exp (Complex.I * ((2 * π / 3 : ℝ) : ℂ)) = 1 := by
        rw [exp_I_two_pi_div_three_eq]; ring
      linear_combination h1 - h2 + e₂ * hsub_exp
    have hv_eq : v (s m) = v (r (m + 1)) := by
      rw [he_eq] at hsm
      have hsub_exp :
          Complex.exp (Complex.I * ((2 * π / 3 : ℝ) : ℂ)) + 1 -
            Complex.exp (Complex.I * ((π / 3 : ℝ) : ℂ)) = 0 := by
        rw [exp_I_two_pi_div_three_eq]; ring
      linear_combination hsm - hrm1 - hq_step - e₂ * hsub_exp
    exact v_inj hv_eq
  refine ⟨?_, ?_⟩
  · intro i hi1 hi10 hne
    exact absurd (hs_eq_r (i + 1) (by omega) (by omega)) hne
  · intro i hi1 hi9 hne _
    exact absurd (hs_eq_r (i + 1) (by omega) (by omega)) hne
