import FormalConjectures.ErdosProblems.«1038»

/-!
Erdős 1038 (ii) : majorant de T. Tao, Sublevel sets of logarithmic potentials (2025), § 2.
Cas des deux points (cas 1 de Tao, seuil 7/4) et cas lointain (cas 2 et 3 de Tao), où la
fonction de rang `x ↦ c + |G ∩ [c, x]|` remplace le réarrangement de Tao.
Le minorant, la factorisation du polynôme et `exists_gap` suivent la réduction R1 fusionnée.
https://terrytao.wordpress.com/wp-content/uploads/2025/12/erdos-1038-1.pdf
-/

-- BEGIN h2-commun
/- ### Inégalité (2.4) de Tao : recopiée de la preuve fusionnée de la réduction R1
(proofs/Erdos1038.erdos_1038.parts.ii.R1.H1.lean, crédit : MrSeizy), jusqu’au lemme `boundary`. -/

namespace OMA.CentralPair

open Set Real

-- P/Q agrees with log(1+x) through degree thirteen at zero.
private noncomputable def P (x : ℝ) : ℝ :=
  120120 * x + 392700 * x ^ 2 + 492800 * x ^ 3 + 295820 * x ^ 4 + 85764 * x ^ 5 + 10507 * x ^ 6 + 353 * x ^ 7

private noncomputable def Q (x : ℝ) : ℝ :=
  120120 + 452760 * x + 679140 * x ^ 2 + 514500 * x ^ 3 + 205800 * x ^ 4 + 41160 * x ^ 5 + 3430 * x ^ 6 + 70 * x ^ 7

-- A, B and C encode the even sum, common denominator and product
-- of the rational bounds at z and -z, as verified below.
private noncomputable def A (x : ℝ) : ℝ :=
  14428814400 - 34620616800 * x + 28674584400 * x ^ 2 - 9569964600 * x ^ 3 + 1138315080 * x ^ 4 - 31012100 * x ^ 5 + 49420 * x ^ 6

private noncomputable def B (x : ℝ) : ℝ :=
  14428814400 - 41835024000 * x + 44782491600 * x ^ 2 - 21623406000 * x ^ 3 + 4595514000 * x ^ 4 - 354387600 * x ^ 5 + 6002500 * x ^ 6 - 4900 * x ^ 7

private noncomputable def C (x : ℝ) : ℝ :=
  14428814400 - 35823018000 * x + 31118755360 * x ^ 2 - 11147867080 * x ^ 3 + 1487019016 * x ^ 4 - 49847665 * x ^ 5 + 124609 * x ^ 6

private theorem qpos {x : ℝ} (hx : -1 < x) : 0 < Q x := by
  have h : 0 < 1 + x := by linarith
  rw [show Q x = 490 * (1 + x) + 8820 * (1 + x) ^ 2 + 36750 * (1 + x) ^ 3 + 49000 * (1 + x) ^ 4 + 22050 * (1 + x) ^ 5 + 2940 * (1 + x) ^ 6 + 70 * (1 + x) ^ 7 by unfold Q; ring]
  positivity

private noncomputable def err (x : ℝ) := log (1+x) - P x / Q x

private theorem err_deriv {x : ℝ} (hx : -1 < x) :
    HasDerivAt err (4900 * x ^ 13 / Q x ^ 2) x := by
  have hx' : 0 < 1+x := by linarith
  have hq := (qpos hx).ne'
  have hl := (Real.hasDerivAt_log hx'.ne').comp x ((hasDerivAt_const x (1:ℝ)).add (hasDerivAt_id x))
  have hp : HasDerivAt P (120120 + 785400 * x + 1478400 * x ^ 2 + 1183280 * x ^ 3 + 428820 * x ^ 4 + 63042 * x ^ 5 + 2471 * x ^ 6) x := by
    unfold P
    convert! ((((((((hasDerivAt_id x).const_mul (120120:ℝ)).add
      (((hasDerivAt_id x).pow 2).const_mul (392700:ℝ))).add
      (((hasDerivAt_id x).pow 3).const_mul (492800:ℝ))).add
      (((hasDerivAt_id x).pow 4).const_mul (295820:ℝ))).add
      (((hasDerivAt_id x).pow 5).const_mul (85764:ℝ))).add
      (((hasDerivAt_id x).pow 6).const_mul (10507:ℝ))).add
      (((hasDerivAt_id x).pow 7).const_mul (353:ℝ))) using 1
    dsimp
    ring
  have hd : HasDerivAt Q (452760 + 1358280 * x + 1543500 * x ^ 2 + 823200 * x ^ 3 + 205800 * x ^ 4 + 20580 * x ^ 5 + 490 * x ^ 6) x := by
    unfold Q
    convert! ((((((((hasDerivAt_const x (120120:ℝ)).add
      ((hasDerivAt_id x).const_mul (452760:ℝ))).add
      (((hasDerivAt_id x).pow 2).const_mul (679140:ℝ))).add
      (((hasDerivAt_id x).pow 3).const_mul (514500:ℝ))).add
      (((hasDerivAt_id x).pow 4).const_mul (205800:ℝ))).add
      (((hasDerivAt_id x).pow 5).const_mul (41160:ℝ))).add
      (((hasDerivAt_id x).pow 6).const_mul (3430:ℝ))).add
      (((hasDerivAt_id x).pow 7).const_mul (70:ℝ))) using 1
    dsimp
    ring
  convert! hl.sub (hp.div hd hq) using 1
  field_simp [hq, hx'.ne']
  unfold P Q
  ring

private theorem log_lower {x : ℝ} (hx : -1 < x) : P x / Q x ≤ log (1+x) := by
  have hz : err 0 = 0 := by norm_num [err, P, Q]
  suffices h : 0 ≤ err x by simpa [err] using h
  rcases le_total 0 x with h | h
  · have hm : MonotoneOn err (Icc 0 x) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc ..)
        (fun y hy => (err_deriv (by linarith [hy.1] : -1 < y)).continuousAt.continuousWithinAt)
        (fun y hy => (err_deriv (by linarith [(interior_subset hy).1] : -1 < y)).hasDerivWithinAt)
      intro y hy
      have : 0 ≤ y := (interior_subset hy).1
      positivity
    simpa [hz] using hm (left_mem_Icc.mpr h) (right_mem_Icc.mpr h) h
  · have hm : AntitoneOn err (Icc x 0) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc ..)
        (fun y hy => (err_deriv (hx.trans_le hy.1)).continuousAt.continuousWithinAt)
        (fun y hy => (err_deriv (hx.trans_le (interior_subset hy).1)).hasDerivWithinAt)
      intro y hy
      have h' : y ≤ 0 := (interior_subset hy).2
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (by simpa using (show Odd 13 by decide).pow_nonpos h')
    simpa [hz] using hm (left_mem_Icc.mpr h) (right_mem_Icc.mpr h) h

-- Substituting r/(1+t) covers (0,r]. The numerators of the transformed
-- inequalities have nonnegative coefficients after clearing denominators.
private theorem interval_nonneg {f : ℝ → ℝ} {r : ℝ} (h0 : 0 ≤ f 0)
    (h : ∀ t : ℝ, 0 ≤ t → 0 ≤ f (r / (1+t))) {x : ℝ} (hx : 0 ≤ x) (hr : x ≤ r) :
    0 ≤ f x := by
  rcases hx.eq_or_lt with he | hp
  · simpa only [← he] using h0
  have ht : 0 ≤ r/x - 1 := by
    have := (le_div_iff₀ hp).2 (by simpa using hr : 1*x ≤ r)
    linarith
  have he : r / (1 + (r/x-1)) = x := by
    rw [show 1 + (r/x-1) = r/x by ring]
    field_simp [hp.ne', (hp.trans_le hr).ne']
  simpa only [he] using h _ ht

private theorem A_nonneg {x : ℝ} (hx : 0 ≤ x) (hr : x ≤ 71/100) : 0 ≤ A x := by
  refine interval_nonneg (f := A) (by norm_num [A]) ?_ hx hr
  intro t ht
  have h : 0 < 1 + t := by positivity
  unfold A
  field_simp
  ring_nf
  positivity

private theorem small_poly {x : ℝ} (hx : 0 ≤ x) (hr : x ≤ 176651/250000) :
    0 ≤ C x - 0.881374 * A x - 0.05594 * B x := by
  refine interval_nonneg (f := fun x => C x - 0.881374*A x - 0.05594*B x)
    (by norm_num [A,B,C]) ?_ hx hr
  intro t ht
  have h : 0 < 1 + t := by positivity
  dsimp [A,B,C]
  field_simp
  ring_nf
  positivity

private theorem large_poly {x : ℝ} (hx : 0 ≤ x) (hr : x ≤ 21/1000) :
    0 ≤ 1.9 * B x - (C x + 0.881374 * A x) := by
  refine interval_nonneg (f := fun x => 1.9*B x - (C x + 0.881374*A x))
    (by norm_num [A,B,C]) ?_ hx hr
  intro t ht
  have h : 0 < 1 + t := by positivity
  dsimp [A,B,C]
  field_simp
  ring_nf
  positivity

private theorem even_den (z : ℝ) : Q (-z) * Q z = B (z^2) := by unfold Q B; ring
private theorem even_sum (z : ℝ) :
    P (-z) * Q z + P z * Q (-z) = -(z^2) * A (z^2) := by unfold P Q A; ring
private theorem even_prod (z : ℝ) :
    P (-z) * P z = -(z^2) * C (z^2) := by unfold P C; ring

private theorem paired (l z : ℝ) (hm : -1 < -z) (hp : -1 < z) :
    ((l + P (-z) / Q (-z)) * (l + P z / Q z)) * B (z^2) =
      l^2 * B (z^2) - z^2 * (l * A (z^2) + C (z^2)) := by
  calc
    _ = l^2 * B (z^2) + l * (P (-z) * Q z + P z * Q (-z)) + P (-z) * P z := by
      rw [← even_den]
      field_simp [(qpos hm).ne', (qpos hp).ne']
      ring
    _ = _ := by rw [even_sum, even_prod]; ring

private theorem scaled_lower {c z : ℝ} (hc : 0 < c) (hz : -1 < z) :
    log c + P z / Q z ≤ log (c * (1+z)) := by
  rw [Real.log_mul hc.ne' (by linarith)]
  exact add_le_add_right (log_lower hz) _

private theorem small_pair {c z l : ℝ} (hc : 0 < c) (hl : log c = -l)
    (hL : l ≤ 0.881374) (hz : 0 ≤ z) (hmax : z^2 ≤ 0.706604)
    (hc1 : c*(1+z) ≤ 1) :
    log (c*(1-z)) * log (c*(1+z)) ≤ l^2 - 0.05594*z^2 := by
  have hm : -1 < -z := by nlinarith
  have hp : -1 < z := by linarith
  have h0 : 0 < 1-z := by linarith
  have h1 : 0 < 1+z := by linarith
  have ha := scaled_lower hc hm
  rw [hl, ← sub_eq_add_neg] at ha
  have hb := scaled_lower hc hp
  rw [hl] at hb
  have hneg := Real.log_nonpos (mul_nonneg hc.le h1.le) hc1
  have hneg' := Real.log_nonpos (mul_nonneg hc.le h0.le)
    ((mul_le_mul_of_nonneg_left (by linarith : 1-z ≤ 1+z) hc.le).trans hc1)
  have hprod := mul_le_mul (neg_le_neg ha) (neg_le_neg hb) (neg_nonneg.mpr hneg)
    (neg_nonneg.mpr (ha.trans hneg'))
  rw [neg_mul_neg, neg_mul_neg] at hprod
  apply hprod.trans
  have hB : 0 < B (z^2) := even_den z ▸ mul_pos (qpos hm) (qpos hp)
  apply le_of_mul_le_mul_right (a := B (z^2)) _ hB
  rw [paired (-l) z hm hp]
  have hA := A_nonneg (sq_nonneg z) (by linarith : z^2 ≤ 71/100)
  have hcert := small_poly (sq_nonneg z) (by linarith : z^2 ≤ 176651/250000)
  nlinarith only [mul_nonneg (sq_nonneg z) (add_nonneg hcert (mul_nonneg (sub_nonneg.mpr hL) hA))]

private theorem large_pair {c z l : ℝ} (hc : 0 < c) (hl : log c = l)
    (hl0 : 0 ≤ l) (hL : l ≤ 0.881374) (hz : 0 ≤ z) (hmax : z^2 ≤ 0.021)
    (hc1 : 1 ≤ c*(1-z)) :
    l^2 - 1.9*z^2 ≤ log (c*(1-z)) * log (c*(1+z)) := by
  have hm : -1 < -z := by nlinarith
  have hp : -1 < z := by linarith
  have ha := scaled_lower hc hm
  rw [hl, ← sub_eq_add_neg] at ha
  have hb := scaled_lower hc hp
  rw [hl] at hb
  have hP : 0 ≤ P z := by unfold P; positivity
  have hprod := mul_le_mul ha hb (add_nonneg hl0 (div_nonneg hP (qpos hp).le))
    (Real.log_nonneg hc1)
  apply le_trans _ hprod
  have hB : 0 < B (z^2) := even_den z ▸ mul_pos (qpos hm) (qpos hp)
  apply le_of_mul_le_mul_right (a := B (z^2)) _ hB
  rw [paired l z hm hp]
  have hA := A_nonneg (sq_nonneg z) (by linarith : z^2 ≤ 71/100)
  have hcert := large_poly (sq_nonneg z) (by linarith : z^2 ≤ 21/1000)
  nlinarith only [mul_nonneg (sq_nonneg z) (add_nonneg hcert (mul_nonneg (sub_nonneg.mpr hL) hA))]

private theorem sqrt_bounds : 1.41421356 ≤ sqrt 2 ∧ sqrt 2 ≤ 1.41421357 := by
  constructor
  · exact (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  · exact Real.sqrt_le_iff.mpr (by norm_num)

private theorem boundary {d : ℝ} (hd : 0 ≤ d) (hmax : d ≤ 1.7624 - sqrt 2) :
    log (sqrt 2 - 1 - d) * log (sqrt 2 - 1 + d) ≤
      log (sqrt 2 + 1 - d) * log (sqrt 2 + 1 + d) := by
  let s := sqrt 2
  let l := log (s+1)
  let v := d / (s-1)
  let u := d / (s+1)
  obtain ⟨hs, hs'⟩ := sqrt_bounds
  change 1.41421356 ≤ s at hs
  change s ≤ 1.41421357 at hs'
  change d ≤ 1.7624 - s at hmax
  have hc : 0 < s-1 := by linarith
  have he : 0 < s+1 := by linarith
  have hlog : log (s-1) = -l := by
    have h : (s-1)*(s+1) = 1 := by nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    have := Real.log_mul hc.ne' he.ne'
    rw [h, log_one] at this
    dsimp [l]; linarith
  have hl : l ≤ 0.881374 := by
    have h := log_lower (x := -0.58578644) (by norm_num)
    have h' : -(0.881374:ℝ) ≤ P (-0.58578644) / Q (-0.58578644) := by norm_num [P, Q]
    have hh := Real.log_le_log (by norm_num : (0:ℝ) < 1 + -0.58578644)
      (by linarith : 1 + -0.58578644 ≤ s-1)
    linarith only [hlog, hh, h, h']
  have hv : 0 ≤ v := div_nonneg hd hc.le
  have hu : 0 ≤ u := div_nonneg hd he.le
  have hv' : v ≤ 0.840597 := (div_le_iff₀ hc).2 (by linarith)
  have hv2 : v^2 ≤ 0.706604 := by nlinarith only [sq_le_sq' (by linarith : -0.840597 ≤ v) hv']
  have hu2 : u^2 ≤ 0.021 := by
    have h : u ≤ 0.1443 := (div_le_iff₀ he).2 (by linarith)
    nlinarith only [sq_le_sq' (by linarith : -0.1443 ≤ u) h]
  have hmulv : v*(s-1) = d := div_mul_cancel₀ _ hc.ne'
  have hmulu : u*(s+1) = d := div_mul_cancel₀ _ he.ne'
  have hfac (w a : ℝ) (h : w*a = d) : a*(1-w) = a-d ∧ a*(1+w) = a+d := by
    constructor <;> linarith only [h]
  obtain ⟨hvm, hvp⟩ := hfac _ _ hmulv
  obtain ⟨hum, hup⟩ := hfac _ _ hmulu
  have hh := small_pair hc hlog hl hv hv2 (by rw [hvp]; linarith)
  have hh' := large_pair he (show log (s+1) = l from rfl)
    (Real.log_nonneg (by linarith)) hl hu hu2 (by rw [hum]; linarith)
  rw [hvm, hvp] at hh
  rw [hum, hup] at hh'
  have hratio : u ≤ 0.171573*v := by
    apply (div_le_iff₀ he).2
    rw [← hmulv]
    nlinarith only [mul_nonneg hv (show 0 ≤ 0.171573*(s+1) - (s-1) by linarith)]
  have hz := sq_le_sq' (by linarith : -(0.171573*v) ≤ u) hratio
  exact hh.trans ((by nlinarith only [hz, sq_nonneg v] : l^2 - 0.05594*v^2 ≤ l^2 - 1.9*u^2).trans hh')

/-- Majorant de Padé (chef-1038) : `log (1 + x) = - log (1 + y)` avec `y = -x / (1 + x)`. -/
theorem log_upper {x : ℝ} (hx : -1 < x) :
    log (1 + x) ≤ -(P (-x / (1 + x)) / Q (-x / (1 + x))) := by
  have h1 : 0 < 1 + x := by linarith
  have hy : -1 < -x / (1 + x) := by
    rw [lt_div_iff₀ h1]; linarith
  have h := log_lower hy
  have e : 1 + -x / (1 + x) = (1 + x)⁻¹ := by field_simp; ring
  rw [e, Real.log_inv] at h
  linarith

/-- Les deux bornes de Padé, sous la forme `log c` pour `c > 0`. -/
theorem log_bounds {c : ℝ} (hc : 0 < c) :
    P (c - 1) / Q (c - 1) ≤ log c ∧ log c ≤ -(P (-(c - 1) / c) / Q (-(c - 1) / c)) := by
  have hx : -1 < c - 1 := by linarith
  have h1 := log_lower hx
  have h2 := log_upper hx
  rw [show 1 + (c - 1) = c by ring] at h1 h2
  exact ⟨h1, h2⟩

end OMA.CentralPair

namespace OMA.H2common

open MeasureTheory Set

/-- Forme close du potentiel logarithmique de `1_[a, b]`. -/
theorem integral_log_abs_sub (a b s : ℝ) :
    ∫ u in a..b, Real.log |u - s| =
      (b - s) * Real.log (b - s) - (a - s) * Real.log (a - s) - (b - a) := by
  simp only [Real.log_abs]
  rw [intervalIntegral.integral_comp_sub_right (fun x => Real.log x) s, integral_log]
  ring

theorem K_continuous (a b : ℝ) :
    Continuous (fun s : ℝ => (b - s) * Real.log (b - s) - (a - s) * Real.log (a - s)) :=
  (Real.continuous_mul_log.comp (continuous_const.sub continuous_id)).sub
    (Real.continuous_mul_log.comp (continuous_const.sub continuous_id))

theorem K_hasDerivAt {a b s : ℝ} (ha : s ≠ a) (hb : s ≠ b) :
    HasDerivAt (fun s : ℝ => (b - s) * Real.log (b - s) - (a - s) * Real.log (a - s))
      (Real.log (a - s) - Real.log (b - s)) s := by
  have hb' : b - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  have ha' : a - s ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  have h1 := (Real.hasDerivAt_mul_log hb').comp s ((hasDerivAt_id s).const_sub b)
  have h2 := (Real.hasDerivAt_mul_log ha').comp s ((hasDerivAt_id s).const_sub a)
  have h := h1.sub h2
  simp only [Function.comp_def] at h
  exact h.congr_deriv (by ring)

/-- Le potentiel de `1_[a, b]` décroît à gauche du milieu de `[a, b]`. -/
theorem K_antitoneOn {a b : ℝ} (hab : a < b) :
    AntitoneOn (fun s : ℝ => (b - s) * Real.log (b - s) - (a - s) * Real.log (a - s))
      (Iic ((a + b) / 2)) := by
  have hcont := K_continuous a b
  have h1 : AntitoneOn (fun s : ℝ => (b - s) * Real.log (b - s) - (a - s) * Real.log (a - s))
      (Iic a) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iic a) hcont.continuousOn
      (f' := fun s => Real.log (a - s) - Real.log (b - s))
    · intro x hx
      rw [interior_Iic] at hx
      have hx' : x < a := hx
      exact (K_hasDerivAt (ne_of_lt hx') (by linarith)).hasDerivWithinAt
    · intro x hx
      rw [interior_Iic] at hx
      have hx' : x < a := hx
      have : Real.log (a - x) ≤ Real.log (b - x) := Real.log_le_log (by linarith) (by linarith)
      linarith
  have h2 : AntitoneOn (fun s : ℝ => (b - s) * Real.log (b - s) - (a - s) * Real.log (a - s))
      (Icc a ((a + b) / 2)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) hcont.continuousOn
      (f' := fun s => Real.log (a - s) - Real.log (b - s))
    · intro x hx
      rw [interior_Icc] at hx
      exact (K_hasDerivAt (ne_of_gt hx.1) (by linarith [hx.2])).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have e : Real.log (a - x) = Real.log (x - a) := by
        rw [show a - x = -(x - a) by ring, Real.log_neg_eq_log]
      have : Real.log (x - a) ≤ Real.log (b - x) := Real.log_le_log (by linarith) (by linarith)
      linarith
  intro x hx y hy hxy
  have hy' : y ≤ (a + b) / 2 := hy
  rcases le_total y a with hya | hya
  · exact h1 (show x ≤ a from le_trans hxy hya) hya hxy
  rcases le_total a x with hax | hax
  · exact h2 ⟨hax, hx⟩ ⟨hya, hy'⟩ hxy
  · exact (h2 ⟨le_rfl, by linarith⟩ ⟨hya, hy'⟩ hya).trans (h1 hax (le_refl a) hax)

/-- Le potentiel de `1_[a, b]` croît à droite du milieu de `[a, b]`. -/
theorem K_monotoneOn {a b : ℝ} (hab : a < b) :
    MonotoneOn (fun s : ℝ => (b - s) * Real.log (b - s) - (a - s) * Real.log (a - s))
      (Ici ((a + b) / 2)) := by
  have hcont := K_continuous a b
  have h1 : MonotoneOn (fun s : ℝ => (b - s) * Real.log (b - s) - (a - s) * Real.log (a - s))
      (Ici b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici b) hcont.continuousOn
      (f' := fun s => Real.log (a - s) - Real.log (b - s))
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : b < x := hx
      exact (K_hasDerivAt (by linarith) (ne_of_gt hx')).hasDerivWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx' : b < x := hx
      have e1 : Real.log (a - x) = Real.log (x - a) := by
        rw [show a - x = -(x - a) by ring, Real.log_neg_eq_log]
      have e2 : Real.log (b - x) = Real.log (x - b) := by
        rw [show b - x = -(x - b) by ring, Real.log_neg_eq_log]
      have : Real.log (x - b) ≤ Real.log (x - a) := Real.log_le_log (by linarith) (by linarith)
      linarith
  have h2 : MonotoneOn (fun s : ℝ => (b - s) * Real.log (b - s) - (a - s) * Real.log (a - s))
      (Icc ((a + b) / 2) b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) hcont.continuousOn
      (f' := fun s => Real.log (a - s) - Real.log (b - s))
    · intro x hx
      rw [interior_Icc] at hx
      exact (K_hasDerivAt (by linarith [hx.1]) (ne_of_lt hx.2)).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have e : Real.log (a - x) = Real.log (x - a) := by
        rw [show a - x = -(x - a) by ring, Real.log_neg_eq_log]
      have : Real.log (b - x) ≤ Real.log (x - a) := Real.log_le_log (by linarith) (by linarith)
      linarith
  intro x hx y hy hxy
  have hx' : (a + b) / 2 ≤ x := hx
  rcases le_total b x with hbx | hbx
  · exact h1 hbx (le_trans hbx hxy) hxy
  rcases le_total y b with hyb | hyb
  · exact h2 ⟨hx', hbx⟩ ⟨le_trans hx' hxy, hyb⟩ hxy
  · exact (h2 ⟨hx', hbx⟩ ⟨by linarith, le_refl b⟩ hbx).trans (h1 (le_refl b) hyb hyb)

theorem intervalIntegrable_log_abs_sub (a b s : ℝ) :
    IntervalIntegrable (fun u : ℝ => Real.log |u - s|) volume a b := by
  simp only [Real.log_abs]
  simpa only [sub_add_cancel] using
    (intervalIntegral.intervalIntegrable_log' (a := a - s) (b := b - s)).comp_sub_right s

/-- Minorant sans annulation à gauche d'un intervalle. -/
theorem integral_ge_left {a b s : ℝ} (hsa : s < a) (hab : a ≤ b) :
    (b - a) * Real.log (a - s) ≤ ∫ u in a..b, Real.log |u - s| := by
  have h := intervalIntegral.integral_mono_on hab intervalIntegrable_const
    (intervalIntegrable_log_abs_sub a b s)
    (fun u hu => show Real.log (a - s) ≤ Real.log |u - s| from by
      rw [abs_of_pos (by linarith [hu.1])]
      exact Real.log_le_log (by linarith) (by linarith [hu.1]))
  simpa [intervalIntegral.integral_const, smul_eq_mul] using h

/-- Minorant sans annulation à droite d'un intervalle. -/
theorem integral_ge_right {a b s : ℝ} (hbs : b < s) (hab : a ≤ b) :
    (b - a) * Real.log (s - b) ≤ ∫ u in a..b, Real.log |u - s| := by
  have h := intervalIntegral.integral_mono_on hab intervalIntegrable_const
    (intervalIntegrable_log_abs_sub a b s)
    (fun u hu => show Real.log (s - b) ≤ Real.log |u - s| from by
      rw [abs_of_neg (by linarith [hu.2]), neg_sub]
      exact Real.log_le_log (by linarith) (by linarith [hu.2]))
  simpa [intervalIntegral.integral_const, smul_eq_mul] using h

end OMA.H2common
-- END h2-commun

open scoped BigOperators Real ENNReal
open MeasureTheory Set Polynomial

namespace OMA.H2low

open Real

-- Borne de Padé de la preuve fusionnée de R1.H1 (MrSeizy).
private def P {K : Type*} [Field K] (x : K) : K :=
  120120 * x + 392700 * x ^ 2 + 492800 * x ^ 3 + 295820 * x ^ 4 + 85764 * x ^ 5 + 10507 * x ^ 6 + 353 * x ^ 7

private def Q {K : Type*} [Field K] (x : K) : K :=
  120120 + 452760 * x + 679140 * x ^ 2 + 514500 * x ^ 3 + 205800 * x ^ 4 + 41160 * x ^ 5 + 3430 * x ^ 6 + 70 * x ^ 7


private def lp {K : Type*} [Field K] (y : K) : K := P (y-1) / Q (y-1)

private theorem lp_le (y : ℝ) (hy : 0 < y) : lp y ≤ log y := by
  exact (CentralPair.log_bounds hy).1

private def fl {K : Type*} [Field K] [LinearOrder K] (l r : K) : K :=
  if 0 ≤ l then
    let y := (l+r)/2
    let m := lp y + 1
    min (l*m) (r*m) - y
  else
    let m := -lp ((-l)⁻¹)
    min (l*m) (r*m)

private theorem min_mul_le {l x r m : ℝ} (hl : l ≤ x) (hr : x ≤ r) :
    min (l*m) (r*m) ≤ x*m := by
  rcases le_total 0 m with h | h
  · exact (min_le_left ..).trans (mul_le_mul_of_nonneg_right hl h)
  · exact (min_le_right ..).trans (mul_le_mul_of_nonpos_right hr h)

private theorem tangent {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x * (lp y + 1) - y ≤ x * log x := by
  rcases eq_or_lt_of_le hx with h | h
  · subst x
    simp [hy.le]
  have hi := mul_le_mul_of_nonneg_left
    (Real.self_sub_one_le_mul_log (div_nonneg h.le hy.le : 0 ≤ x/y)) hy.le
  rw [Real.log_div h.ne' hy.ne'] at hi
  field_simp [hy.ne'] at hi
  nlinarith only [hi, mul_le_mul_of_nonneg_left (lp_le y hy) h.le]

private theorem fl_le {l x r : ℝ} (hlr : l < r) (hl : l ≤ x) (hr : x ≤ r)
    (hs : 0 ≤ l ∨ r ≤ 0) : fl l r ≤ x * log x := by
  unfold fl
  split_ifs with h
  · exact (sub_le_sub_right (min_mul_le hl hr) _).trans
      (tangent (h.trans hl) (by linarith))
  · have hneg := lt_of_not_ge h
    have hx : x ≤ 0 := hr.trans (hs.resolve_left h)
    have hh := min_mul_le (m := -lp ((-l)⁻¹)) hl hr
    apply hh.trans
    rcases hx.eq_or_lt with hz | hx'
    · simp [hz]
    apply mul_le_mul_of_nonpos_left _ hx
    rw [← Real.log_neg_eq_log x]
    have hlog := lp_le (-l)⁻¹ (inv_pos.mpr (neg_pos.mpr hneg))
    rw [Real.log_inv] at hlog
    exact (Real.log_le_log (by linarith) (neg_le_neg hl)).trans (by linarith)

private def box {K : Type*} [Field K] [LinearOrder K]
    (a b w c d p q : K) : K :=
  lp p + w * (fl (b-q) (b-p) + fl (p-a) (q-a) - (b-a)) + d * lp (c-q)

private noncomputable def pot (a b w c d s : ℝ) :=
  log s + w * ((b-s)*log (b-s) + (s-a)*log (s-a) - (b-a)) + d*log (c-s)

private theorem box_le {a b w c d p q s : ℝ}
    (hp : 0 < p) (hpq : p < q) (hqc : q < c)
    (hw : 0 ≤ w) (hd : 0 ≤ d)
    (hab : 0 ≤ b-q ∨ b-p ≤ 0) (haa : 0 ≤ p-a ∨ q-a ≤ 0)
    (hs : p ≤ s) (hs' : s ≤ q) : box a b w c d p q ≤ pot a b w c d s := by
  have h1 := (lp_le p hp).trans (Real.log_le_log hp hs)
  have h2 := (lp_le (c-q) (by linarith)).trans
    (Real.log_le_log (by linarith) (by linarith : c-q ≤ c-s))
  have h3 := fl_le (l := b-q) (r := b-p) (x := b-s) (by linarith) (by linarith) (by linarith) hab
  have h4 := fl_le (l := p-a) (r := q-a) (x := s-a) (by linarith) (by linarith) (by linarith) haa
  exact add_le_add (add_le_add h1 (mul_le_mul_of_nonneg_left
    (sub_le_sub_right (add_le_add h3 h4) _) hw)) (mul_le_mul_of_nonneg_left h2 hd)

private theorem lp_cast (x : ℚ) : ((lp x : ℚ) : ℝ) = lp (x : ℝ) := by
  simp [lp, P, Q]

private theorem fl_cast (l r : ℚ) : ((fl l r : ℚ) : ℝ) = fl (l : ℝ) (r : ℝ) := by
  unfold fl
  by_cases h : 0 ≤ l
  · have h' : (0:ℝ) ≤ l := by exact_mod_cast h
    simp [h, h', lp_cast]
  · have h' : ¬ (0:ℝ) ≤ l := by exact_mod_cast h
    simp [h, h', lp_cast]

private theorem box_cast (a b w c d p q : ℚ) :
    ((box a b w c d p q : ℚ) : ℝ) = box (a:ℝ) b w c d p q := by
  simp [box, fl_cast, lp_cast]

private def good (a b w c d p q : ℚ) : Bool :=
  decide (0 < p ∧ p < q ∧ q < c ∧ 0 ≤ w ∧ 0 ≤ d ∧
    (0 ≤ b-q ∨ b-p ≤ 0) ∧ (0 ≤ p-a ∨ q-a ≤ 0) ∧ 0 < box a b w c d p q)

private theorem good_sound {a b w c d p q : ℚ} {s : ℝ} (h : good a b w c d p q)
    (hl : (p:ℝ) ≤ s) (hr : s ≤ (q:ℝ)) : 0 < pot a b w c d s := by
  unfold good at h
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := of_decide_eq_true h
  have h8' : (0:ℝ) < ((box a b w c d p q : ℚ):ℝ) := by exact_mod_cast h8
  rw [box_cast] at h8'
  apply h8'.trans_le
  exact box_le (by exact_mod_cast h1) (by exact_mod_cast h2) (by exact_mod_cast h3)
    (by exact_mod_cast h4) (by exact_mod_cast h5) (by exact_mod_cast h6) (by exact_mod_cast h7) hl hr

private def cover (a b w c d p r : ℚ) : List ℚ → Bool
  | [] => good a b w c d p r
  | q :: qs => good a b w c d p q && cover a b w c d q r qs

private theorem cover_sound {a b w c d p r : ℚ} {s : ℝ} (qs : List ℚ)
    (h : cover a b w c d p r qs) (hl : (p:ℝ) ≤ s) (hr : s ≤ (r:ℝ)) : 0 < pot a b w c d s := by
  induction qs generalizing p with
  | nil => exact good_sound h hl hr
  | cons q qs ih =>
    obtain ⟨h1,h2⟩ := Bool.and_eq_true_iff.mp h
    by_cases hs : s ≤ q
    · exact good_sound h1 hl hs
    · exact ih h2 (le_of_not_ge hs)

private abbrev Witness (t0 : ℝ) :=
    ∃ (m : ℕ) (A a b : Fin m → ℝ), (∀ k, 0 ≤ A k) ∧ (∀ k, t0 - 1 ≤ a k) ∧
      (∀ k, a k ≤ b k) ∧ (∀ k, b k ≤ 2 * Real.sqrt 2) ∧
      ∀ s ∈ Icc (t0 - 1) (t0 + 1),
        0 < Real.log s + ∑ k, A k * ∫ u in (a k)..(b k), Real.log |u - s|

private theorem exhibit {t a b w c d e : ℝ}
    (hw : 0 ≤ w) (hd : 0 ≤ d) (hta : t-1 ≤ a) (htc : t-1 ≤ c)
    (hab : a ≤ b) (hce : c < e) (hb : b ≤ 2*sqrt 2) (he : e ≤ 2*sqrt 2)
    (ht : t+1 < c) (h : ∀ s ∈ Icc (t-1) (t+1), 0 < pot a b w c d s) : Witness t := by
  have hw' : 0 ≤ d / (e-c) := div_nonneg hd (sub_pos.mpr hce).le
  refine ⟨2, ![w, d/(e-c)], ![a,c], ![b,e], ?_, ?_, ?_, ?_, ?_⟩
  · intro k; fin_cases k <;> assumption
  · intro k; fin_cases k <;> assumption
  · intro k; fin_cases k
    · exact hab
    · exact hce.le
  · intro k; fin_cases k <;> assumption
  · intro s hs
    rw [Fin.sum_univ_two]
    change 0 < log s + (w * (∫ u in a..b, log |u-s|) +
      (d/(e-c)) * (∫ u in c..e, log |u-s|))
    have hR := mul_le_mul_of_nonneg_left
      (H2common.integral_ge_left (hs.2.trans_lt ht) hce.le) hw'
    rw [show d/(e-c) * ((e-c) * log (c-s)) = d * log (c-s) by
      field_simp [(sub_pos.mpr hce).ne']] at hR
    rw [H2common.integral_log_abs_sub, show log (a-s) = log (s-a) by
      rw [← Real.log_neg_eq_log (a-s), neg_sub]]
    have h0 := h s hs
    unfold pot at h0
    linarith only [h0, hR]

private def points_175_177 : List ℚ :=
  [784/1000, 858/1000, 1015/1000, 1300/1000, 1679/1000, 1890/1000, 2027/1000,
   2123/1000, 2198/1000, 2266/1000, 2330/1000, 2389/1000, 2447/1000,
   2507/1000, 2568/1000, 2627/1000, 2670/1000, 2727/1000, 2760/1000]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem calc_175_177 : cover (1890/1000) (2670/1000) (424/1000) (2828/1000) (247/1000) (750/1000) (2770/1000) points_175_177 := by
  decide +kernel

private def points_177_180 : List ℚ :=
  [801/1000, 868/1000, 1008/1000, 1275/1000, 1659/1000, 1960/1000, 2094/1000,
   2187/1000, 2261/1000, 2331/1000, 2405/1000, 2481/1000, 2559/1000,
   2637/1000, 2705/1000, 2753/1000, 2760/1000, 2788/1000, 2798/1000]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem calc_177_180 : cover (1960/1000) (2760/1000) (450/1000) (2828/1000) (176/1000) (770/1000) (2800/1000) points_177_180 := by
  decide +kernel


private theorem cert_175_177 (t : ℝ) (ht : 7/4 < t) (ht' : t ≤ 177/100) :
    Witness t := by
  apply exhibit (a := 1890/1000) (b := 2670/1000) (w := 424/1000)
    (c := 2828/1000) (d := 247/1000) (e := 28284/10000)
  · norm_num
  · norm_num
  · linarith
  · linarith
  · norm_num
  · norm_num
  · linarith [CentralPair.sqrt_bounds.1]
  · linarith [CentralPair.sqrt_bounds.1]
  · linarith
  · intro s hs
    have hp : ((((750/1000) : ℚ) : ℝ)) ≤ s := by
      push_cast; linarith [hs.1]
    have hq : s ≤ (((2770/1000) : ℚ) : ℝ) := by
      push_cast; linarith [hs.2]
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      cover_sound points_175_177 calc_175_177 hp hq

private theorem cert_177_180 (t : ℝ) (ht : 177/100 < t) (ht' : t ≤ 9/5) :
    Witness t := by
  apply exhibit (a := 1960/1000) (b := 2760/1000) (w := 450/1000)
    (c := 2828/1000) (d := 176/1000) (e := 28284/10000)
  · norm_num
  · norm_num
  · linarith
  · linarith
  · norm_num
  · norm_num
  · linarith [CentralPair.sqrt_bounds.1]
  · linarith [CentralPair.sqrt_bounds.1]
  · linarith
  · intro s hs
    have hp : ((((770/1000) : ℚ) : ℝ)) ≤ s := by
      push_cast; linarith [hs.1]
    have hq : s ≤ (((2800/1000) : ℚ) : ℝ) := by
      push_cast; linarith [hs.2]
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      cover_sound points_177_180 calc_177_180 hp hq

end OMA.H2low

namespace OMA.H2high

open Real

noncomputable def J (a b s : ℝ) : ℝ :=
  (b - s) * log (b - s) - (a - s) * log (a - s) - (b - a)

theorem integral_eq_J (a b s : ℝ) :
    (∫ u in a..b, Real.log |u - s|) = J a b s := by
  exact H2common.integral_log_abs_sub a b s

/- Le logarithme binaire entier de x^512 fournit deux bornes rationnelles
   pour log x / log 2, distantes d'exactement 1/512. -/
def lo (x : ℚ) : ℚ := (Int.log 2 (x ^ 512) : ℚ) / 512
def hi (x : ℚ) : ℚ := lo x + 1 / 512

theorem log_band {x : ℚ} (hx : 0 < x) :
    (lo x : ℝ) * log 2 ≤ log x ∧ log x ≤ (hi x : ℝ) * log 2 := by
  let k := Int.log 2 (x ^ 512)
  have hl : (2 : ℚ) ^ k ≤ x ^ 512 := Int.zpow_log_le_self (by decide : 1 < 2) (pow_pos hx _)
  have hu : x ^ 512 < (2 : ℚ) ^ (k + 1) := Int.lt_zpow_succ_log_self (by decide : 1 < 2) _
  have hl' : (2 : ℝ) ^ k ≤ (x : ℝ) ^ 512 := by simpa only [Rat.cast_zpow, Rat.cast_pow,
    Rat.cast_ofNat] using ((Rat.cast_le (K := ℝ)).mpr hl)
  have hu' : (x : ℝ) ^ 512 < (2 : ℝ) ^ (k + 1) := by simpa only [Rat.cast_zpow, Rat.cast_pow,
    Rat.cast_ofNat] using ((Rat.cast_lt (K := ℝ)).mpr hu)
  have hl'' := log_le_log (by positivity) hl'
  have hu'' := log_le_log (pow_pos (show 0 < (x : ℝ) by exact_mod_cast hx) _) hu'.le
  rw [log_zpow, log_pow] at hl''
  rw [log_zpow, log_pow] at hu''
  norm_num at hl'' hu''
  constructor
  · change (((k : ℚ) / 512 : ℚ) : ℝ) * log 2 ≤ _
    push_cast
    linarith only [hl'']
  · change _ ≤ (((k : ℚ) / 512 + 1 / 512 : ℚ) : ℝ) * log 2
    push_cast
    linarith only [hu'']

def flo (x : ℚ) : ℚ := if 0 ≤ x then x * lo x else x * hi (-x)
def fhi (x : ℚ) : ℚ := if 0 ≤ x then x * hi x else x * lo (-x)

theorem f_band (x : ℚ) : (flo x : ℝ) * log 2 ≤ (x : ℝ) * log x ∧
    (x : ℝ) * log x ≤ (fhi x : ℝ) * log 2 := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · obtain ⟨hl, hu⟩ := log_band (neg_pos.mpr hx)
    rw [Rat.cast_neg, log_neg_eq_log] at hl hu
    have hx' : (x : ℝ) ≤ 0 := by exact_mod_cast hx.le
    simp only [flo, fhi, if_neg (not_le.mpr hx), Rat.cast_mul, mul_assoc]
    exact ⟨mul_le_mul_of_nonpos_left hu hx', mul_le_mul_of_nonpos_left hl hx'⟩
  · simp [flo, fhi]
  · obtain ⟨hl, hu⟩ := log_band hx
    have hx' : 0 ≤ (x : ℝ) := by exact_mod_cast hx.le
    simp only [flo, fhi, if_pos hx.le, Rat.cast_mul, mul_assoc]
    exact ⟨mul_le_mul_of_nonneg_left hl hx', mul_le_mul_of_nonneg_left hu hx'⟩

def jlo (a b t : ℚ) : ℚ := flo (b - t) - fhi (a - t) - (b - a) * 1.443

theorem jlo_le {a b : ℚ} (hab : a ≤ b) (t : ℚ) :
    (jlo a b t : ℝ) * log 2 ≤ J a b t := by
  have h₁ := (f_band (b - t)).1
  have h₂ := (f_band (a - t)).2
  have h₃ : (1 : ℝ) ≤ 1.443 * log 2 := by linarith only [Real.log_two_gt_d9]
  have h₄ : 0 ≤ (b : ℝ) - a := by exact_mod_cast sub_nonneg.mpr hab
  unfold jlo J
  push_cast at *
  nlinarith only [h₁, h₂, mul_nonneg h₄ (sub_nonneg.mpr h₃)]


/- Sur une cellule [p,q], le minimum de J est atteint au point le plus
   proche du milieu du segment chargé. -/
def clip (a b p q : ℚ) : ℚ := max p (min q ((a + b) / 2))

theorem clip_le {a b p q : ℚ} (hab : a < b) {s : ℝ} (hs : s ∈ Icc (p : ℝ) q) :
    J a b (clip a b p q) ≤ J a b s := by
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  let m := ((a : ℝ) + b) / 2
  have he : (clip a b p q : ℝ) = max (p : ℝ) (min (q : ℝ) m) := by simp [clip, m]
  rw [he]
  apply sub_le_sub_right
  by_cases h : s ≤ m
  · exact H2common.K_antitoneOn hab' h (max_le (hs.1.trans h) (min_le_right ..))
      (le_max_of_le_right (le_min hs.2 h))
  · have h' := le_of_not_ge h
    exact H2common.K_monotoneOn hab' (le_max_of_le_right (le_min (h'.trans hs.2) le_rfl)) h'
      (max_le hs.1 ((min_le_right ..).trans h'))

/- Le second minorant évite la soustraction de deux valeurs voisines de
   x log |x| pour un intervalle chargé étroit vu de loin. -/
def jpoint (a b t : ℚ) : ℚ :=
  if t < a then max (jlo a b t) ((b - a) * lo (a - t))
  else if b < t then max (jlo a b t) ((b - a) * lo (t - b))
  else jlo a b t

theorem jpoint_le {a b : ℚ} (hab : a < b) (t : ℚ) : (jpoint a b t : ℝ) * log 2 ≤ J a b t := by
  have hz : 0 ≤ log 2 := log_nonneg (by norm_num)
  have hd : a ≤ b := hab.le
  have hd' : (a : ℝ) ≤ b := by exact_mod_cast hd
  have hh := jlo_le hd t
  by_cases h : t < a
  · have h' : (t : ℝ) < a := by exact_mod_cast h
    have g := (log_band (sub_pos.mpr h)).1
    rw [Rat.cast_sub] at g
    have w := H2common.integral_ge_left h' hd'
    rw [integral_eq_J] at w
    simp only [jpoint, if_pos h, Rat.cast_max, Rat.cast_mul, Rat.cast_sub, max_mul_of_nonneg _ _ hz,
      max_le_iff, mul_assoc]
    exact ⟨hh, (mul_le_mul_of_nonneg_left g (sub_nonneg.mpr hd')).trans w⟩
  by_cases h' : b < t
  · have h'' : (b : ℝ) < t := by exact_mod_cast h'
    have g := (log_band (sub_pos.mpr h')).1
    rw [Rat.cast_sub] at g
    have w := H2common.integral_ge_right h'' hd'
    rw [integral_eq_J] at w
    simp only [jpoint, if_neg h, if_pos h', Rat.cast_max, Rat.cast_mul, Rat.cast_sub,
      max_mul_of_nonneg _ _ hz, max_le_iff, mul_assoc]
    exact ⟨hh, (mul_le_mul_of_nonneg_left g (sub_nonneg.mpr hd')).trans w⟩
  simpa only [jpoint, if_neg h, if_neg h'] using hh

def rowLo (a b c d A B p q : ℚ) : ℚ := lo p +
  (A * jpoint a b (clip a b p q) + B * jpoint c d (clip c d p q))

theorem row_pos {a b c d A B p q : ℚ} (hab : a < b) (hcd : c < d) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hp : 0 < p) (hcheck : 0 < rowLo a b c d A B p q) {s : ℝ} (hs : s ∈ Icc (p : ℝ) q) :
    0 < log s + (A * J a b s + B * J c d s) := by
  have h₁ := ((log_band hp).1).trans (log_le_log (by exact_mod_cast hp) hs.1)
  have h₂ := (jpoint_le hab (clip a b p q)).trans (clip_le hab hs)
  have h₃ := (jpoint_le hcd (clip c d p q)).trans (clip_le hcd hs)
  have h₄ := mul_le_mul_of_nonneg_left h₂ (show (0 : ℝ) ≤ A by exact_mod_cast hA)
  have h₅ := mul_le_mul_of_nonneg_left h₃ (show (0 : ℝ) ≤ B by exact_mod_cast hB)
  have h₆ := mul_pos (show (0 : ℝ) < rowLo a b c d A B p q by exact_mod_cast hcheck)
    (show 0 < log 2 from log_pos (by norm_num))
  simp only [rowLo, Rat.cast_add, Rat.cast_mul, add_mul, mul_assoc] at h₆
  linarith only [h₁, h₄, h₅, h₆]

def checkGrid (a b c d A B : ℚ) : ℚ → List ℚ → ℚ → Bool
  | p, [], q => decide (0 < p ∧ 0 < rowLo a b c d A B p q)
  | p, m :: ms, q => decide (0 < p ∧ 0 < rowLo a b c d A B p m) && checkGrid a b c d A B m ms q

theorem grid_pos {a b c d A B : ℚ} (hab : a < b) (hcd : c < d) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ms : List ℚ) (p q : ℚ) (h : checkGrid a b c d A B p ms q = true) {s : ℝ}
    (hs : s ∈ Icc (p : ℝ) q) : 0 < log s + (A * J a b s + B * J c d s) := by
  induction ms generalizing p with
  | nil =>
    exact row_pos hab hcd hA hB (of_decide_eq_true h).1 (of_decide_eq_true h).2 hs
  | cons m ms ih =>
    obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp h
    by_cases hm : s ≤ m
    · exact row_pos hab hcd hA hB (of_decide_eq_true hl).1 (of_decide_eq_true hl).2 ⟨hs.1, hm⟩
    · exact ih m hr ⟨le_of_not_ge hm, hs.2⟩

def cuts : List ℚ := [0.875, 0.95, 1.1, 1.4, 1.73, 2.05, 2.14, 2.23, 2.275, 2.32,
  2.365, 2.41, 2.455, 2.5, 2.545, 2.59, 2.635, 2.68, 2.725, 2.7475, 2.7588,
  2.77, 2.7773, 2.7845, 2.799, 2.828]

set_option maxHeartbeats 2000000 in
theorem cert_180_200 (s : ℝ) (hs : s ∈ Icc 0.8 3) :
    0 < log s + (0.5 * J 2.05 2.77 s + 2.17 * J 2.77 2.828 s) := by
  have hg : checkGrid 2.05 2.77 2.77 2.828 0.5 2.17 0.8 cuts 3 = true := by decide +kernel
  have hm : s ∈ Icc ((0.8 : ℚ) : ℝ) ((3 : ℚ) : ℝ) := by norm_num at hs ⊢; exact hs
  have hp := grid_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) _ _ _ hg hm
  norm_num at hp ⊢
  exact hp

end OMA.H2high

namespace OMA.Erdos1038ii

/-- Inégalité (2.4) de Tao (cas 1), en la variable `a = t0 - 1`, pour `√2 < t0 ≤ 7/4`. -/
def H1 : Prop :=
  ∀ a : ℝ, Real.sqrt 2 - 1 ≤ a → a ≤ 3 / 4 →
    Real.log a * Real.log (2 * Real.sqrt 2 - 2 - a) ≤
      Real.log (2 + a) * Real.log (2 * Real.sqrt 2 - a)

/-- Certificats des cas 2 et 3 de Tao, (2.5) et (2.6) : la mesure `δ_0 + ∑ A_k 1_[a_k, b_k]`
a un potentiel strictement négatif sur `[t0 - 1, t0 + 1]`. -/
def H2 : Prop :=
  ∀ t0 : ℝ, 7 / 4 < t0 → t0 ≤ 2 →
    ∃ (m : ℕ) (A a b : Fin m → ℝ), (∀ k, 0 ≤ A k) ∧ (∀ k, t0 - 1 ≤ a k) ∧
      (∀ k, a k ≤ b k) ∧ (∀ k, b k ≤ 2 * Real.sqrt 2) ∧
      ∀ s ∈ Icc (t0 - 1) (t0 + 1),
        0 < Real.log s + ∑ k, A k * ∫ u in (a k)..(b k), Real.log |u - s|

/- ### Les deux inégalités numériques -/

theorem h1_holds : H1 := by
  intro a ha1 ha2
  have hb := CentralPair.boundary (d := a - (Real.sqrt 2 - 1)) (by linarith) (by linarith)
  have e1 : Real.sqrt 2 - 1 - (a - (Real.sqrt 2 - 1)) = 2 * Real.sqrt 2 - 2 - a := by ring
  have e2 : Real.sqrt 2 - 1 + (a - (Real.sqrt 2 - 1)) = a := by ring
  have e3 : Real.sqrt 2 + 1 - (a - (Real.sqrt 2 - 1)) = 2 * Real.sqrt 2 - a := by ring
  have e4 : Real.sqrt 2 + 1 + (a - (Real.sqrt 2 - 1)) = 2 + a := by ring
  rw [e1, e2, e3, e4] at hb
  linarith [mul_comm (Real.log a) (Real.log (2 * Real.sqrt 2 - 2 - a)),
    mul_comm (Real.log (2 + a)) (Real.log (2 * Real.sqrt 2 - a))]

/-- Certificats pour `t0 ∈ (7/4, 9/5]` (lemme 3, sous-agent l1038-l3). -/
theorem h2_low : ∀ t0 : ℝ, 7 / 4 < t0 → t0 ≤ 9 / 5 →
    ∃ (m : ℕ) (A a b : Fin m → ℝ), (∀ k, 0 ≤ A k) ∧ (∀ k, t0 - 1 ≤ a k) ∧
      (∀ k, a k ≤ b k) ∧ (∀ k, b k ≤ 2 * Real.sqrt 2) ∧
      ∀ s ∈ Icc (t0 - 1) (t0 + 1),
        0 < Real.log s + ∑ k, A k * ∫ u in (a k)..(b k), Real.log |u - s| := by
  intro t ht ht'
  by_cases hm : t ≤ 177/100
  · exact H2low.cert_175_177 t ht hm
  · exact H2low.cert_177_180 t (lt_of_not_ge hm) ht'

/-- Certificats pour `t0 ∈ [9/5, 2]` (lemme 4, sous-agent l1038-l4). -/
theorem h2_high : ∀ t0 : ℝ, 9 / 5 ≤ t0 → t0 ≤ 2 →
    ∃ (m : ℕ) (A a b : Fin m → ℝ), (∀ k, 0 ≤ A k) ∧ (∀ k, t0 - 1 ≤ a k) ∧
      (∀ k, a k ≤ b k) ∧ (∀ k, b k ≤ 2 * Real.sqrt 2) ∧
      ∀ s ∈ Icc (t0 - 1) (t0 + 1),
        0 < Real.log s + ∑ k, A k * ∫ u in (a k)..(b k), Real.log |u - s| := by
  intro t0 h₀ h₁
  refine ⟨2, ![0.5, 2.17], ![2.05, 2.77], ![2.77, 2.828], ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> norm_num
  · intro i; fin_cases i <;> norm_num <;> linarith
  · intro i; fin_cases i <;> norm_num
  · have hb : (1.414 : ℝ) ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
    intro i; fin_cases i <;> norm_num <;> linarith
  · intro s hs
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, H2high.integral_eq_J] using
      H2high.cert_180_200 s ⟨by linarith [hs.1], by linarith [hs.2]⟩

theorem h2_holds : H2 := by
  intro t0 h1 h2
  rcases le_or_gt t0 (9 / 5) with h | h
  · exact h2_low t0 h1 h
  · exact h2_high t0 h.le h2

/- ### Cas des deux points -/

/-- Conditions aux extrémités `t = ± 1` pour deux points de l'ensemble proches du centre. -/
theorem endpoint_ineq (h1 : H1) {x y : ℝ} (hxT : -(7 / 4 : ℝ) ≤ x) (hyT : y ≤ 7 / 4)
    (hxy : 2 * Real.sqrt 2 < y - x) :
    Real.log (-1 - x) * Real.log (y - 1) ≤ Real.log (y + 1) * Real.log (1 - x) := by
  have hs : (1.375 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = -1 - x := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = x + 2 * Real.sqrt 2 - 1 := ⟨_, rfl⟩
  have hapos : 0 < a := by linarith
  have hbpos : 0 < b := by linarith
  have hkey : Real.log a * Real.log b ≤ Real.log (2 + a) * Real.log (2 + b) := by
    rcases le_total (Real.sqrt 2 - 1) a with h | h
    · have h' := h1 a h (by linarith)
      have e1 : 2 * Real.sqrt 2 - 2 - a = b := by linarith
      have e2 : 2 * Real.sqrt 2 - a = 2 + b := by linarith
      rw [e1, e2] at h'
      exact h'
    · have h' := h1 b (by linarith) (by linarith)
      have e1 : 2 * Real.sqrt 2 - 2 - b = a := by linarith
      have e2 : 2 * Real.sqrt 2 - b = 2 + a := by linarith
      rw [e1, e2] at h'
      linarith [mul_comm (Real.log a) (Real.log b),
        mul_comm (Real.log (2 + a)) (Real.log (2 + b))]
  have hlogA : Real.log a ≤ 0 := Real.log_nonpos hapos.le (by linarith)
  have hlogy1 : Real.log b ≤ Real.log (y - 1) := Real.log_le_log hbpos (by linarith)
  have h2a : 0 ≤ Real.log (2 + a) := Real.log_nonneg (by linarith)
  have hlogy2 : Real.log (2 + b) ≤ Real.log (y + 1) := Real.log_le_log (by linarith) (by linarith)
  have e3 : -1 - x = a := by linarith
  have e4 : 1 - x = 2 + a := by linarith
  rw [e3, e4]
  calc Real.log a * Real.log (y - 1) ≤ Real.log a * Real.log b :=
        mul_le_mul_of_nonpos_left hlogy1 hlogA
    _ ≤ Real.log (2 + a) * Real.log (2 + b) := hkey
    _ ≤ Real.log (2 + a) * Real.log (y + 1) := mul_le_mul_of_nonneg_left hlogy2 h2a
    _ = Real.log (y + 1) * Real.log (2 + a) := mul_comm _ _

/-- Certificat à deux points : la mesure `log (y+1) δ_x - log (-1-x) δ_y` (lemme 2.1 de Tao),
par concavité du logarithme entre `t = -1` et `t = 1`. -/
theorem two_point_cert {x y : ℝ} (hx : x < -1) (hy : 1 < y) (hx2 : -2 < x)
    (hF : Real.log (-1 - x) * Real.log (y - 1) ≤ Real.log (y + 1) * Real.log (1 - x))
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    0 ≤ Real.log (y + 1) * Real.log |x - t| - Real.log (-1 - x) * Real.log |y - t| := by
  obtain ⟨ht1, ht2⟩ := ht
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = (1 + t) / 2 := ⟨_, rfl⟩
  have hl0 : 0 ≤ l := by linarith
  have hl1 : 0 ≤ 1 - l := by linarith
  have hc := strictConcaveOn_log_Ioi.concaveOn
  have h1 : (1 - l) * Real.log (-1 - x) + l * Real.log (1 - x) ≤ Real.log (t - x) := by
    have h' := hc.2 (show (-1 - x) ∈ Ioi (0:ℝ) from by simp only [mem_Ioi]; linarith)
      (show (1 - x) ∈ Ioi (0:ℝ) from by simp only [mem_Ioi]; linarith) hl1 hl0 (by ring)
    simp only [smul_eq_mul] at h'
    have e : (1 - l) * (-1 - x) + l * (1 - x) = t - x := by rw [hl]; ring
    rw [e] at h'
    exact h'
  have h2 : (1 - l) * Real.log (y + 1) + l * Real.log (y - 1) ≤ Real.log (y - t) := by
    have h' := hc.2 (show (y + 1) ∈ Ioi (0:ℝ) from by simp only [mem_Ioi]; linarith)
      (show (y - 1) ∈ Ioi (0:ℝ) from by simp only [mem_Ioi]; linarith) hl1 hl0 (by ring)
    simp only [smul_eq_mul] at h'
    have e : (1 - l) * (y + 1) + l * (y - 1) = y - t := by rw [hl]; ring
    rw [e] at h'
    exact h'
  have hax : |x - t| = t - x := by rw [abs_sub_comm]; exact abs_of_pos (by linarith)
  have hay : |y - t| = y - t := abs_of_pos (by linarith)
  rw [hax, hay]
  have hA : 0 < Real.log (y + 1) := Real.log_pos (by linarith)
  have hB : Real.log (-1 - x) < 0 := Real.log_neg (by linarith) (by linarith)
  have m1 := mul_le_mul_of_nonneg_left h1 hA.le
  have m2 := mul_le_mul_of_nonneg_left h2 (neg_nonneg.mpr hB.le)
  have m3 : 0 ≤ l * (Real.log (y + 1) * Real.log (1 - x) - Real.log (-1 - x) * Real.log (y - 1)) :=
    mul_nonneg hl0 (by linarith)
  nlinarith [m1, m2, m3]

theorem near_case (h1 : H1) {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, r i ∈ Icc (-1 : ℝ) 1)
    {x y : ℝ} (hx : (∏ i, |x - r i|) < 1) (hy : (∏ i, |y - r i|) < 1)
    (hxT : -(7 / 4 : ℝ) ≤ x) (hyT : y ≤ 7 / 4) (hxy : 2 * Real.sqrt 2 < y - x) : False := by
  have hs : (1.375 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hx1 : x < -1 := by linarith
  have hy1 : 1 < y := by linarith
  have hx2 : -2 < x := by linarith
  have hF := endpoint_ineq h1 hxT hyT hxy
  have hsum : 0 ≤ ∑ i, (Real.log (y + 1) * Real.log |x - r i| -
      Real.log (-1 - x) * Real.log |y - r i|) :=
    Finset.sum_nonneg fun i _ => two_point_cert hx1 hy1 hx2 hF (hr i)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hxne : ∀ i ∈ (Finset.univ : Finset (Fin n)), |x - r i| ≠ 0 := fun i _ => by
    have := (hr i).1
    exact abs_ne_zero.mpr (by linarith)
  have hyne : ∀ i ∈ (Finset.univ : Finset (Fin n)), |y - r i| ≠ 0 := fun i _ => by
    have := (hr i).2
    exact abs_ne_zero.mpr (by linarith)
  rw [← Real.log_prod hxne, ← Real.log_prod hyne] at hsum
  have hpx : 0 < ∏ i, |x - r i| :=
    Finset.prod_pos fun i hi => lt_of_le_of_ne (abs_nonneg _) (hxne i hi).symm
  have hpy : 0 < ∏ i, |y - r i| :=
    Finset.prod_pos fun i hi => lt_of_le_of_ne (abs_nonneg _) (hyne i hi).symm
  have hlx : Real.log (∏ i, |x - r i|) < 0 := Real.log_neg hpx hx
  have hly : Real.log (∏ i, |y - r i|) < 0 := Real.log_neg hpy hy
  have hA : 0 < Real.log (y + 1) := Real.log_pos (by linarith)
  have hB : Real.log (-1 - x) < 0 := Real.log_neg (by linarith) (by linarith)
  nlinarith [mul_neg_of_pos_of_neg hA hlx, mul_pos_of_neg_of_neg hB hly]

/- ### Fonction de rang -/

theorem rank_props {G : Set ℝ} {c : ℝ} {R : ℝ → ℝ}
    (hR : ∀ x, R x = c + (volume (G ∩ Icc c x)).toReal) :
    Monotone R ∧ (∀ x y, |R x - R y| ≤ |x - y|) ∧ (∀ x, c ≤ R x) ∧
      (∀ x, c ≤ x → R x ≤ x) := by
  have hfin (x : ℝ) : volume (G ∩ Icc c x) ≠ ⊤ :=
    measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne
  have hmono : Monotone R := by
    intro x y hxy
    rw [hR x, hR y]
    apply add_le_add le_rfl
    apply ENNReal.toReal_mono (hfin y) (measure_mono ?_)
    exact fun z hz => ⟨hz.1, hz.2.1, hz.2.2.trans hxy⟩
  have hinc (x y : ℝ) (hxy : x ≤ y) : R y - R x ≤ y - x := by
    have hsub : G ∩ Icc c y ⊆ (G ∩ Icc c x) ∪ Ioc x y := by
      intro z hz
      rcases le_or_gt z x with h | h
      · exact Or.inl ⟨hz.1, hz.2.1, h⟩
      · exact Or.inr ⟨h, hz.2.2⟩
    have hvol := (measure_mono (μ := volume) hsub).trans (measure_union_le _ _)
    rw [Real.volume_Ioc] at hvol
    have hle := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨hfin x, ENNReal.ofReal_ne_top⟩) hvol
    rw [ENNReal.toReal_add (hfin x) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hxy)] at hle
    rw [hR x, hR y]
    linarith
  refine ⟨hmono, ?_, ?_, ?_⟩
  · intro x y
    rcases le_total x y with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr (hmono h)), abs_of_nonpos (sub_nonpos.mpr h)]
      linarith [hinc x y h]
    · rw [abs_of_nonneg (sub_nonneg.mpr (hmono h)), abs_of_nonneg (sub_nonneg.mpr h)]
      exact hinc y x h
  · intro x
    rw [hR x]
    exact le_add_of_nonneg_right ENNReal.toReal_nonneg
  · intro x hcx
    have hle : volume (G ∩ Icc c x) ≤ volume (Icc c x) := measure_mono inter_subset_right
    rw [Real.volume_Icc] at hle
    have hle' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hcx)] at hle'
    rw [hR x]
    linarith

/-- La fonction de rang transporte la mesure de Lebesgue sur `G` en celle de
`[c, c + |G|]`. -/
theorem map_rank {G : Set ℝ} {c d : ℝ} {R : ℝ → ℝ}
    (hR : ∀ x, R x = c + (volume (G ∩ Icc c x)).toReal)
    (hGm : MeasurableSet G) (hG : G ⊆ Icc c d) :
    Measure.map R (volume.restrict G) = volume.restrict (Icc c (c + (volume G).toReal)) := by
  obtain ⟨hmono, hlip, hlower, hupper⟩ := rank_props hR
  have hcont : Continuous R := by
    apply LipschitzWith.continuous (K := 1)
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa [Real.dist_eq] using hlip x y
  have hfin : volume G ≠ ⊤ := measure_ne_top_of_subset hG measure_Icc_lt_top.ne
  have : IsFiniteMeasure (volume.restrict G) := isFiniteMeasure_restrict.2 hfin
  have hmax (x : ℝ) : R x ≤ c + (volume G).toReal := by
    rw [hR]
    exact add_le_add le_rfl (ENNReal.toReal_mono hfin (measure_mono inter_subset_left))
  have hsat (x : ℝ) (hdx : d ≤ x) : R x = c + (volume G).toReal := by
    rw [hR, inter_eq_left.mpr (show G ⊆ Icc c x from
      fun z hz => ⟨(hG hz).1, (hG hz).2.trans hdx⟩)]
  apply Measure.ext_of_Iic
  intro s
  rw [Measure.map_apply hcont.measurable measurableSet_Iic, Measure.restrict_apply' hGm,
    Measure.restrict_apply measurableSet_Iic]
  by_cases hlow : s < c
  · have hleft : (R ⁻¹' Iic s) ∩ G = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx =>
      hlow.not_ge ((hlower x).trans hx.1)
    have hright : Iic s ∩ Icc c (c + (volume G).toReal) = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun x hx => hlow.not_ge (hx.2.1.trans hx.1)
    rw [hleft, hright]
  by_cases hhigh : c + (volume G).toReal ≤ s
  · have hleft : (R ⁻¹' Iic s) ∩ G = G := inter_eq_right.mpr fun x _ => (hmax x).trans hhigh
    have hright : Iic s ∩ Icc c (c + (volume G).toReal) = Icc c (c + (volume G).toReal) :=
      inter_eq_right.mpr fun x hx => hx.2.trans hhigh
    rw [hleft, hright, Real.volume_Icc, add_sub_cancel_left, ENNReal.ofReal_toReal hfin]
  let S := R ⁻¹' Iic s
  have hne : S.Nonempty := ⟨c, (hupper c le_rfl).trans (le_of_not_gt hlow)⟩
  have hbd : BddAbove S := by
    refine ⟨d, ?_⟩
    intro x hx
    by_contra! hdx
    exact hhigh ((hsat x hdx.le).symm.trans_le hx)
  let u := sSup S
  have hu : R u ≤ s := (isClosed_Iic.preimage hcont).csSup_mem hne hbd
  have heq : R u = s := by
    let v := u + (s - R u)
    have hd : 0 ≤ v - u := by dsimp [v]; linarith
    have hdist := (le_abs_self (R v - R u)).trans (hlip v u)
    rw [abs_of_nonneg hd] at hdist
    have hv : v ∈ S := by
      change R v ≤ s
      dsimp [v] at hdist ⊢
      linarith
    have hvu : v ≤ u := le_csSup hbd hv
    dsimp [v] at hvu
    linarith
  have hleft : (R ⁻¹' Iic s) ∩ G = G ∩ Icc c u := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.2, (hG hx.2).1, le_csSup hbd hx.1⟩
    · intro hx
      exact ⟨(hmono hx.2.2).trans hu, hx.1⟩
  have hright : Iic s ∩ Icc c (c + (volume G).toReal) = Icc c s := by
    ext x
    constructor
    · exact fun hx => ⟨hx.2.1, hx.1⟩
    · exact fun hx => ⟨hx.2, hx.1, hx.2.trans (le_of_not_ge hhigh)⟩
  have hmass : (volume (G ∩ Icc c u)).toReal = s - c := by linarith [hR u]
  rw [hleft, hright, Real.volume_Icc, ← hmass,
    ENNReal.ofReal_toReal (measure_ne_top_of_subset inter_subset_left hfin)]

theorem integrableOn_log_abs_shift (a b t : ℝ) :
    IntegrableOn (fun x : ℝ => Real.log |x - t|) (Icc a b) := by
  have h : IntervalIntegrable (fun x : ℝ => Real.log (x - t)) volume a b := by
    simpa only [sub_add_cancel] using
      (intervalIntegral.intervalIntegrable_log' (a := a - t) (b := b - t)).comp_sub_right t
  simp only [Real.log_abs]
  exact (integrableOn_Icc_iff_integrableOn_Ioc (f := fun x : ℝ => Real.log (x - t))
    (a := a) (by finiteness)).mpr h.1

/-- Comparaison de Tao `|t - φ(s)| ≥ |s0 - s|`, intégrée. -/
theorem integral_rank_le {G : Set ℝ} {c d : ℝ} {R : ℝ → ℝ}
    (hR : ∀ x, R x = c + (volume (G ∩ Icc c x)).toReal)
    (hGm : MeasurableSet G) (hG : G ⊆ Icc c d)
    {α β : ℝ} (hcα : c ≤ α) (hαβ : α ≤ β) (hβ : β ≤ c + (volume G).toReal) (t : ℝ) :
    ∫ u in α..β, Real.log |u - R t| ≤ ∫ x in G ∩ R ⁻¹' Icc α β, Real.log |x - t| := by
  let F := G ∩ R ⁻¹' Icc α β
  let g := fun u : ℝ => Real.log |u - R t|
  have hdist := (rank_props hR).2.1
  have hLip : LipschitzWith 1 R := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa [Real.dist_eq] using hdist x y
  have hRm := hLip.continuous.measurable
  have hpre : MeasurableSet (R ⁻¹' Icc α β) := hRm measurableSet_Icc
  have hmap : (volume.restrict F).map R = volume.restrict (Icc α β) := by
    have he := congrArg (fun ν : Measure ℝ => ν.restrict (Icc α β)) (map_rank hR hGm hG)
    simpa only [Measure.restrict_map hRm measurableSet_Icc, Measure.restrict_restrict hpre,
      inter_comm (R ⁻¹' Icc α β) G, Measure.restrict_restrict_of_subset (Icc_subset_Icc hcα hβ),
      F] using he
  have hg : Integrable g ((volume.restrict F).map R) := by
    rw [hmap]
    exact integrableOn_log_abs_shift α β (R t)
  have hne : ∀ᵐ x ∂volume.restrict F, R x ≠ R t := by
    apply ae_of_ae_map (p := fun u => u ≠ R t) hRm.aemeasurable
    rw [hmap]
    exact (volume.restrict (Icc α β)).ae_ne (R t)
  calc
    (∫ u in α..β, Real.log |u - R t|) = ∫ u in Icc α β, g u := by
      simp only [g, intervalIntegral.integral_of_le hαβ, integral_Icc_eq_integral_Ioc]
    _ = ∫ x in F, g (R x) := by
      rw [← hmap]
      exact integral_map hRm.aemeasurable hg.aestronglyMeasurable
    _ ≤ _ := by
      apply integral_mono_ae (hg.comp_measurable hRm)
        ((integrableOn_log_abs_shift c d t).mono_set (inter_subset_left.trans hG))
      filter_upwards [hne] with x hx
      exact Real.log_le_log (abs_pos.mpr (sub_ne_zero.mpr hx)) (hdist x t)


theorem sublevel_subset {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, r i ∈ Icc (-1 : ℝ) 1) :
    {x : ℝ | (∏ i, |x - r i|) < 1} ⊆ Ioo (-2) 2 := by
  intro x hx
  change (∏ i, |x - r i|) < 1 at hx
  constructor
  · by_contra! h
    apply hx.not_ge
    apply Finset.one_le_prod
    intro i _
    have t := (hr i).1
    calc
      1 ≤ -(x - r i) := by linarith
      _ ≤ |x - r i| := neg_le_abs _
  · by_contra! h
    apply hx.not_ge
    apply Finset.one_le_prod
    intro i _
    exact le_trans (by linarith [(hr i).2] : 1 ≤ x - r i) (le_abs_self _)

/- ### Dualité (lemme 2.1 de Tao) et cas lointain -/

theorem dual_sum {n m : ℕ} (r : Fin n → ℝ) {μ : ℝ} (hμr : ∀ i, μ ≠ r i)
    (hμ : (∏ i, |μ - r i|) ≤ 1) (A : Fin m → ℝ) (hA : ∀ k, 0 ≤ A k)
    (F : Fin m → Set ℝ) (hFm : ∀ k, MeasurableSet (F k)) (hFb : ∀ k, F k ⊆ Icc (-2 : ℝ) 2)
    (hFE : ∀ k, ∀ x ∈ F k, (∏ i, |x - r i|) < 1) :
    ∑ i, (Real.log |μ - r i| + ∑ k, A k * ∫ x in F k, Real.log |x - r i|) ≤ 0 := by
  have hsum {x : ℝ} (hne : ∀ i, x ≠ r i) (hle : (∏ i, |x - r i|) ≤ 1) :
      (∑ i, Real.log |x - r i|) ≤ 0 := by
    rw [← Real.log_prod (s := Finset.univ) (f := fun i => |x - r i|)
      (fun i _ => abs_ne_zero.mpr (sub_ne_zero.mpr (hne i)))]
    exact Real.log_nonpos (Finset.prod_nonneg fun i _ => abs_nonneg _) hle
  rw [Finset.sum_add_distrib]
  apply add_nonpos (hsum hμr hμ)
  rw [Finset.sum_comm]
  apply Finset.sum_nonpos
  intro k _
  rw [← Finset.mul_sum]
  apply mul_nonpos_of_nonneg_of_nonpos (hA k)
  rw [← integral_finsetSum Finset.univ (f := fun i x => Real.log |x - r i|)
    (fun i _ => (integrableOn_log_abs_shift (-2) 2 (r i)).mono_set (hFb k))]
  apply integral_nonpos_of_ae
  have hne : ∀ᵐ x ∂volume.restrict (F k), ∀ i, x ≠ r i :=
    ae_all_iff.mpr fun i => (volume.restrict (F k)).ae_ne (r i)
  filter_upwards [hne, ae_restrict_mem (μ := volume) (hFm k)] with x hx hxF
  exact hsum hx (hFE k x hxF).le


theorem far_case_left (h2 : H2) {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, r i ∈ Icc (-1 : ℝ) 1)
    (hvol : ENNReal.ofReal (2 * Real.sqrt 2) < volume {x : ℝ | (∏ i, |x - r i|) < 1})
    {x : ℝ} (hx : (∏ i, |x - r i|) < 1) (hxT : x < -(7 / 4 : ℝ)) : False := by
  classical
  have hcont : Continuous fun z : ℝ => ∏ i, |z - r i| :=
    continuous_finsetProd _ fun i _ => (continuous_id.sub continuous_const).abs
  obtain ⟨E, hE⟩ : ∃ E : Set ℝ, E = {x : ℝ | (∏ i, |x - r i|) < 1} := ⟨_, rfl⟩
  rw [← hE] at hvol
  have hEopen : IsOpen E := by rw [hE]; exact isOpen_lt hcont continuous_const
  have hEm : MeasurableSet E := hEopen.measurableSet
  have hEbox : E ⊆ Ioo (-2) 2 := by rw [hE]; exact sublevel_subset r hr
  have hxE : x ∈ E := by rw [hE]; exact hx
  have hEne : E.Nonempty := ⟨x, hxE⟩
  have hEbdd : BddBelow E := ⟨-2, fun z hz => (hEbox hz).1.le⟩
  obtain ⟨μ, hμdef⟩ : ∃ μ : ℝ, μ = sInf E := ⟨_, rfl⟩
  have hμx : μ ≤ x := by rw [hμdef]; exact csInf_le hEbdd hxE
  have hμ2 : -2 ≤ μ := by rw [hμdef]; exact le_csInf hEne fun z hz => (hEbox hz).1.le
  have hμle : ∀ z ∈ E, μ ≤ z := fun z hz => by rw [hμdef]; exact csInf_le hEbdd hz
  have hμP : (∏ i, |μ - r i|) ≤ 1 := by
    have hcl : closure E ⊆ {z : ℝ | (∏ i, |z - r i|) ≤ 1} := by
      apply closure_minimal _ (isClosed_le hcont continuous_const)
      intro z hz
      rw [hE] at hz
      exact le_of_lt (show (∏ i, |z - r i|) < 1 from hz)
    exact hcl (by rw [hμdef]; exact csInf_mem_closure hEne hEbdd)
  have hμr : ∀ i, μ ≠ r i := fun i h => by have := (hr i).1; linarith
  have ht0lo : 7 / 4 < -μ := by linarith
  have ht0hi : -μ ≤ 2 := by linarith
  obtain ⟨m, A, a, b, hA, ha, hab, hb, hcert⟩ := h2 (-μ) ht0lo ht0hi
  obtain ⟨G, hG⟩ : ∃ G : Set ℝ, G = E ∩ Ici (-1 : ℝ) := ⟨_, rfl⟩
  have hGm : MeasurableSet G := by rw [hG]; exact hEm.inter measurableSet_Ici
  have hGsub : G ⊆ Icc (-1 : ℝ) 2 := by
    rw [hG]; exact fun z hz => ⟨hz.2, (hEbox hz.1).2.le⟩
  have hGfin : volume G ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono hGsub)
  have hGvol : 2 * Real.sqrt 2 + μ + 1 < (volume G).toReal := by
    have hsplit : E ⊆ Icc μ (-1) ∪ G := by
      intro z hz
      by_cases hz1 : -1 ≤ z
      · exact Or.inr (by rw [hG]; exact ⟨hz, hz1⟩)
      · exact Or.inl ⟨hμle z hz, le_of_lt (not_le.mp hz1)⟩
    have h1 : volume E ≤ ENNReal.ofReal (-1 - μ) + volume G := by
      calc volume E ≤ volume (Icc μ (-1) ∪ G) := measure_mono hsplit
        _ ≤ volume (Icc μ (-1)) + volume G := measure_union_le _ _
        _ = ENNReal.ofReal (-1 - μ) + volume G := by rw [Real.volume_Icc]
    have h3 : ENNReal.ofReal (2 * Real.sqrt 2) < ENNReal.ofReal (-1 - μ) + volume G :=
      lt_of_lt_of_le hvol h1
    rw [← ENNReal.ofReal_toReal hGfin,
      ← ENNReal.ofReal_add (by linarith) ENNReal.toReal_nonneg] at h3
    have h4 := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp h3
    linarith
  obtain ⟨R, hR⟩ : ∃ R : ℝ → ℝ, ∀ z, R z = -1 + (volume (G ∩ Icc (-1) z)).toReal :=
    ⟨_, fun z => rfl⟩
  obtain ⟨hRmono, hRlip, hRge, hRle⟩ := rank_props hR
  have hRmeas : Measurable R := hRmono.measurable
  obtain ⟨F, hF⟩ : ∃ F : Fin m → Set ℝ, ∀ k, F k = G ∩ R ⁻¹' Icc (a k + μ) (b k + μ) :=
    ⟨_, fun k => rfl⟩
  have hFm : ∀ k, MeasurableSet (F k) := fun k => by
    rw [hF k]; exact hGm.inter (hRmeas measurableSet_Icc)
  have hFb : ∀ k, F k ⊆ Icc (-2 : ℝ) 2 := fun k z hz => by
    rw [hF k] at hz
    exact ⟨by linarith [(hGsub hz.1).1], (hGsub hz.1).2⟩
  have hFE : ∀ k, ∀ z ∈ F k, (∏ i, |z - r i|) < 1 := fun k z hz => by
    rw [hF k, hG] at hz
    have hz1 := hz.1.1
    rw [hE] at hz1
    exact hz1
  have hdual := dual_sum r hμr hμP A hA F hFm hFb hFE
  have hpos : ∀ i, 0 < Real.log |μ - r i| + ∑ k, A k * ∫ z in F k, Real.log |z - r i| := by
    intro i
    have hri := hr i
    have hs0lo : -1 ≤ R (r i) := hRge _
    have hs0hi : R (r i) ≤ r i := hRle _ hri.1
    have hs : R (r i) - μ ∈ Icc (-μ - 1) (-μ + 1) := ⟨by linarith, by linarith [hri.2]⟩
    have hc := hcert (R (r i) - μ) hs
    have hlog : Real.log (R (r i) - μ) ≤ Real.log |μ - r i| := by
      rw [abs_sub_comm, abs_of_pos (by linarith)]
      exact Real.log_le_log (by linarith) (by linarith)
    have hint : ∀ k, ∫ u in (a k)..(b k), Real.log |u - (R (r i) - μ)| ≤
        ∫ z in F k, Real.log |z - r i| := by
      intro k
      have htrans : ∫ u in (a k)..(b k), Real.log |u - (R (r i) - μ)| =
          ∫ u in (a k + μ)..(b k + μ), Real.log |u - R (r i)| := by
        rw [← intervalIntegral.integral_comp_add_right (fun u => Real.log |u - R (r i)|) μ]
        congr 1
        ext u
        congr 2
        ring
      rw [htrans, hF k]
      exact integral_rank_le hR hGm hGsub (by linarith [ha k]) (by linarith [hab k])
        (by linarith [hb k]) (r i)
    have hsum : ∑ k, A k * ∫ u in (a k)..(b k), Real.log |u - (R (r i) - μ)| ≤
        ∑ k, A k * ∫ z in F k, Real.log |z - r i| :=
      Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hint k) (hA k)
    linarith
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    rw [hcon, Finset.prod_empty] at hx
    exact lt_irrefl _ hx
  have hgt : 0 < ∑ i, (Real.log |μ - r i| + ∑ k, A k * ∫ z in F k, Real.log |z - r i|) :=
    Finset.sum_pos (fun i _ => hpos i) hne
  linarith

theorem far_case (h2 : H2) {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, r i ∈ Icc (-1 : ℝ) 1)
    (hvol : ENNReal.ofReal (2 * Real.sqrt 2) < volume {x : ℝ | (∏ i, |x - r i|) < 1})
    {x : ℝ} (hx : (∏ i, |x - r i|) < 1) (hxT : 7 / 4 < |x|) : False := by
  rcases lt_abs.mp hxT with h | h
  · have hr' : ∀ i, (fun i => -r i) i ∈ Icc (-1 : ℝ) 1 := fun i =>
      ⟨by linarith [(hr i).2], by linarith [(hr i).1]⟩
    have habs : ∀ z : ℝ, ∀ i, |z - (fun i => -r i) i| = |-z - r i| := fun z i => by
      simp only
      rw [show z - -r i = -(-z - r i) by ring, abs_neg]
    have hset : {z : ℝ | (∏ i, |z - (fun i => -r i) i|) < 1} =
        -{z : ℝ | (∏ i, |z - r i|) < 1} := by
      ext z
      simp only [mem_setOf_eq, Set.mem_neg, habs]
    refine far_case_left h2 (fun i => -r i) hr' ?_ (x := -x) ?_ (by linarith)
    · rw [hset, Measure.measure_neg]
      exact hvol
    · rw [Finset.prod_congr rfl fun i _ => habs (-x) i, neg_neg]
      exact hx
  · exact far_case_left h2 r hr hvol hx (by linarith)

/- ### Assemblage (d'après la réduction R1 fusionnée) -/

theorem exists_gap {E : Set ℝ} {d : ℝ} (hE : E ⊆ Ioo (-2) 2)
    (hvol : ENNReal.ofReal d < volume E) : ∃ x ∈ E, ∃ y ∈ E, d < y - x := by
  have hn : E.Nonempty := by
    by_contra! h
    simp [h] at hvol
  have hb : BddBelow E := ⟨-2, fun x hx => (hE hx).1.le⟩
  have ha : BddAbove E := ⟨2, fun x hx => (hE hx).2.le⟩
  by_contra! h
  have hwidth : sSup E ≤ d + sInf E := by
    apply csSup_le hn
    intro y hy
    have hy' : y - d ≤ sInf E :=
      le_csInf hn fun x hx => by linarith [h x hx y hy]
    linarith
  have hbox : E ⊆ Icc (sInf E) (sSup E) :=
    fun x hx => ⟨csInf_le hb hx, le_csSup ha hx⟩
  apply hvol.not_ge
  calc
    volume E ≤ volume (Icc (sInf E) (sSup E)) := measure_mono hbox
    _ = ENNReal.ofReal (sSup E - sInf E) := Real.volume_Icc
    _ ≤ ENNReal.ofReal d := ENNReal.ofReal_le_ofReal (by linarith)

theorem prod_bound (h1 : H1) (h2 : H2) {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ i, r i ∈ Icc (-1 : ℝ) 1) :
    volume {x : ℝ | (∏ i, |x - r i|) < 1} ≤ ENNReal.ofReal (2 * Real.sqrt 2) := by
  by_contra! hvol
  by_cases hfar : ∃ x ∈ {x : ℝ | (∏ i, |x - r i|) < 1}, (7 / 4 : ℝ) < |x|
  · obtain ⟨x, hx, hxT⟩ := hfar
    exact far_case h2 r hr hvol hx hxT
  · obtain ⟨x, hx, y, hy, hxy⟩ := exists_gap (sublevel_subset r hr) hvol
    push Not at hfar
    exact near_case h1 r hr hx hy (abs_le.mp (hfar x hx)).1 (abs_le.mp (hfar y hy)).2 hxy

end OMA.Erdos1038ii

open OMA.Erdos1038ii in
theorem OMA.solution : type_of% @Erdos1038.erdos_1038.parts.ii := by
  classical
  refine le_antisymm Erdos1038.erdos_1038.variants.sup_lowerBound (iSup_le ?_)
  rintro ⟨f, hmonic, hf⟩
  have hle := f.card_roots'
  have hge := Multiset.card_le_card (Multiset.filter_le (fun x => x ∈ Icc (-1 : ℝ) 1) f.roots)
  have hcard : f.roots.card = f.natDegree := by omega
  have hfilter : f.roots.filter (fun x => x ∈ Icc (-1 : ℝ) 1) = f.roots :=
    Multiset.eq_of_le_of_card_le (Multiset.filter_le _ _) (by omega)
  let L := f.roots.toList
  let r : Fin L.length → ℝ := L.get
  have hr (i : Fin L.length) : r i ∈ Icc (-1 : ℝ) 1 := by
    have hmem : r i ∈ f.roots := Multiset.mem_toList.mp (List.get_mem L i)
    exact (Multiset.mem_filter.mp (hfilter.symm ▸ hmem)).2
  have he (x : ℝ) : |f.eval x| = ∏ i, |x - r i| := by
    rw [(Polynomial.splits_iff_card_roots.mpr hcard).eval_eq_prod_roots_of_monic hmonic]
    change |(f.roots.map fun t => x - t).prod| = _
    rw [← f.roots.coe_toList]
    simp only [Multiset.map_coe, Multiset.prod_coe]
    change |(L.map fun t => x - t).prod| = _
    calc
      _ = |((List.ofFn r).map fun t => x - t).prod| := by
        rw [show List.ofFn r = L from List.ofFn_get L]
      _ = _ := by
        rw [List.map_ofFn, List.prod_ofFn, Finset.abs_prod]
        rfl
  change volume {x : ℝ | |f.eval x| < 1} ≤ _
  simp_rw [he]
  calc
    _ ≤ ENNReal.ofReal (2 * Real.sqrt 2) := prod_bound h1_holds h2_holds r hr
    _ = 2 * 2 ^ (1 / 2 : ℝ) := by
      rw [ENNReal.ofReal_mul zero_le_two, Real.sqrt_eq_rpow,
        ← ENNReal.ofReal_rpow_of_nonneg zero_le_two (by norm_num)]
      norm_num
