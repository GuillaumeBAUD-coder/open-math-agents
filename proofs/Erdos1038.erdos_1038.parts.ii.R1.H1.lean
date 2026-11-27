import OMAReductions.R_Erdos1038_erdos_1038_parts_ii_R1

/-!
The logarithmic endpoint criterion follows the two-point argument of Tao
used in the parent reduction. The rational approximation and the polynomial
certificates below give explicit bounds throughout the central range.
-/

open Set Real
namespace CentralPair

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

private theorem ordered_det {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 1.7624)
    (hgap : 2 * sqrt 2 < a+b) :
    log (a-1) * log (b-1) < log (a+1) * log (b+1) := by
  have hs := sqrt_bounds.1
  let a₀ := 2 * sqrt 2 - b
  have ha₀ : 1 < a₀ := by dsimp [a₀]; linarith
  have hinc : a₀ < a := by dsimp [a₀]; linarith
  have hc := boundary (d := b - sqrt 2) (by linarith) (by linarith)
  have align (c : ℝ) :
      sqrt 2 + c - (b - sqrt 2) = a₀+c ∧ sqrt 2 + c + (b - sqrt 2) = b+c := by
    dsimp [a₀]; constructor <;> ring
  rw [show sqrt 2 - 1 = sqrt 2 + (-1) by ring,
    (align (-1)).1, (align (-1)).2, (align 1).1, (align 1).2] at hc
  simp only [sub_eq_add_neg] at ⊢
  exact (mul_le_mul_of_nonpos_right (Real.log_le_log (by linarith) (by linarith : a₀ + -1 ≤ a + -1))
    (Real.log_nonpos (by linarith) (by linarith : b + -1 ≤ 1))).trans_lt
    (hc.trans_lt (mul_lt_mul_of_pos_right
      (Real.log_lt_log (by linarith) (by linarith : a₀+1 < a+1))
      (Real.log_pos (by linarith))))

private theorem multiplicities {A B C D : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hdet : B*C < D*A) :
    ∃ p q : ℕ, B * (q+1 : ℝ) < (p+1 : ℝ) * A ∧
      (p+1 : ℝ) * C < D * (q+1 : ℝ) := by
  have h : B/A < D/C := (div_lt_div_iff₀ hA hC).2 hdet
  obtain ⟨n, hn⟩ := exists_nat_gt (D/C-B/A)⁻¹
  have hn' := (inv_pos.mpr (sub_pos.mpr h)).trans hn
  obtain ⟨m, hm, hm'⟩ := exists_div_btwn h hn
  have hmpos : 0 < (m:ℝ) := by
    have ht := (lt_div_iff₀ hn').1 ((div_pos hB hA).trans hm)
    simpa using ht
  have hmi : (0:ℤ) < m := by exact_mod_cast hmpos
  lift m to ℕ using hmi.le
  cases m with
  | zero => simp at hmpos
  | succ p =>
    cases n with
    | zero => simp at hn'
    | succ q =>
      refine ⟨p, q, ?_, ?_⟩
      · simpa using (div_lt_div_iff₀ hA hn').1 hm
      · simpa using (div_lt_div_iff₀ hn' hC).1 hm'

-- Interpolation between the gap endpoints also occurs in the sibling
-- inf_upperBound proof. Here we apply concavity directly to each logarithm.
private theorem interpolate {a b t m n : ℝ}
    (ha : 1 < a) (hb : 1 < b) (ht : t ∈ Icc (-1 : ℝ) 1)
    (hm : 0 ≤ m) (hn : 0 ≤ n)
    (hleft : 0 ≤ m*log (a-1) + n*log (b+1))
    (hright : 0 ≤ m*log (a+1) + n*log (b-1)) :
    0 ≤ m*log (a+t) + n*log (b-t) := by
  let u := (1-t)/2
  let v := (1+t)/2
  have hu : 0 ≤ u := by dsimp [u]; linarith [ht.2]
  have hv : 0 ≤ v := by dsimp [v]; linarith [ht.1]
  have huv : u+v=1 := by dsimp [u,v]; ring
  have hj (c d : ℝ) (hc : 0 < c) (hd : 0 < d) :
      u*log c + v*log d ≤ log (u*c + v*d) :=
    strictConcaveOn_log_Ioi.concaveOn.2 hc hd hu hv huv
  have h1 := hj (a-1) (a+1) (by linarith) (by linarith)
  have h2 := hj (b+1) (b-1) (by linarith) (by linarith)
  rw [show u*(a-1)+v*(a+1) = a+t by dsimp [u,v]; ring] at h1
  rw [show u*(b+1)+v*(b-1) = b-t by dsimp [u,v]; ring] at h2
  linarith only [mul_nonneg hu hleft, mul_nonneg hv hright,
    mul_le_mul_of_nonneg_left h1 hm, mul_le_mul_of_nonneg_left h2 hn]

end CentralPair

-- Credit: @MrSeizy
theorem OMA.solution : OMA.R_Erdos1038_erdos_1038_parts_ii_R1.H1 := by
  intro x y hx hy hgap
  let a := -x
  let b := y
  have hs := CentralPair.sqrt_bounds.1
  have ha' : a ≤ 1.7624 := by dsimp [a]; linarith
  have hsum : 2 * sqrt 2 < a + b := by dsimp [a,b]; linarith
  change b ≤ 1.7624 at hy
  have ha : 1 < a := by linarith
  have hb : 1 < b := by linarith
  have hdet : log (a-1) * log (b-1) < log (a+1) * log (b+1) := by
    rcases le_total a b with h | h
    · exact CentralPair.ordered_det h hy hsum
    · simpa only [mul_comm (log (b-1)), mul_comm (log (b+1))] using
        CentralPair.ordered_det h ha' (by linarith)
  obtain ⟨p,q,hp,hq⟩ := CentralPair.multiplicities
    (Real.log_pos (by linarith : 1 < a+1))
    (neg_pos.mpr (Real.log_neg (by linarith : 0 < b-1) (by linarith)))
    (neg_pos.mpr (Real.log_neg (by linarith : 0 < a-1) (by linarith)))
    (D := log (b+1)) (by linarith only [hdet])
  refine ⟨p,q,?_⟩
  intro t ht
  have haₜ : 0 < a+t := by linarith [ht.1]
  have hbₜ : 0 < b-t := by linarith [ht.2]
  rw [abs_of_nonpos (by dsimp [a] at haₜ; linarith : x-t ≤ 0),
    show -(x-t) = a+t by dsimp [a]; ring,
    abs_of_nonneg (show 0 ≤ y-t from hbₜ.le)]
  change 1 ≤ (a+t)^(p+1) * (b-t)^(q+1)
  apply (Real.log_le_log_iff (by norm_num) (by positivity)).1
  rw [log_one, Real.log_mul (by positivity) (by positivity), log_pow, log_pow]
  push_cast
  exact CentralPair.interpolate ha hb ht (by positivity) (by positivity)
    (by linarith only [hq]) (by linarith only [hp])
