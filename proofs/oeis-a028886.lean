import OMAStatements.S_oeis_a028886
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic

namespace OMA.OeisA028886

private abbrev Z2 := Zsqrtd 2

private lemma z2_norm_eq (z : Z2) : z.norm = z.re ^ 2 - 2 * z.im ^ 2 := by
  simp only [Zsqrtd.norm]
  ring

private lemma z2_mul_star (a : Z2) : a * star a = (a.norm : Z2) := by
  apply Zsqrtd.ext <;> simp [Zsqrtd.norm] <;> ring

private lemma z2_norm_intCast (c : ℤ) : ((c : Z2)).norm = c ^ 2 := by
  simp [Zsqrtd.norm, sq]

private lemma norm_eq_zero_iff (z : Z2) : z.norm = 0 ↔ z = 0 := by
  constructor
  · intro h
    have hnat : ∀ n : ℕ, ∀ a b : ℤ, b.natAbs ≤ n → a ^ 2 - 2 * b ^ 2 = 0 → a = 0 ∧ b = 0 := by
      intro n
      induction n with
      | zero =>
        intro a b hb hab
        have hb0 : b = 0 := by omega
        subst hb0
        have ha0 : a = 0 := by nlinarith
        exact ⟨ha0, rfl⟩
      | succ n ih =>
        intro a b hb hab
        by_cases hbn : b.natAbs ≤ n
        · exact ih a b hbn hab
        · have ha2 : 2 ∣ a := by
            have hev : Even (a ^ 2) := ⟨b ^ 2, by linarith⟩
            rcases Int.even_pow.mp hev with ⟨he, _⟩
            exact even_iff_two_dvd.mp he
          rcases ha2 with ⟨a', rfl⟩
          have hb2 : 2 ∣ b := by
            have hev : Even (b ^ 2) := ⟨a' ^ 2, by linarith⟩
            rcases Int.even_pow.mp hev with ⟨he, _⟩
            exact even_iff_two_dvd.mp he
          rcases hb2 with ⟨b', rfl⟩
          have hlt : b'.natAbs ≤ n := by omega
          have hsub : a' ^ 2 - 2 * b' ^ 2 = 0 := by linarith
          rcases ih a' b' hlt hsub with ⟨ha', hb'⟩
          exact ⟨by omega, by omega⟩
    rw [z2_norm_eq] at h
    rcases hnat z.im.natAbs z.re z.im le_rfl h with ⟨h1, h2⟩
    exact Zsqrtd.ext h1 h2
  · rintro rfl
    simp [Zsqrtd.norm]

private lemma z2_mul_right_cancel {a b c : Z2} (hc : c ≠ 0) (h : a * c = b * c) : a = b := by
  have hsub : (a - b) * c = 0 := by linear_combination h
  have hnorm : (a - b).norm * c.norm = 0 := by
    rw [← Zsqrtd.norm_mul, hsub, Zsqrtd.norm_zero]
  have hcn : c.norm ≠ 0 := fun h0 => hc ((norm_eq_zero_iff c).mp h0)
  have hab : (a - b).norm = 0 := (mul_eq_zero.mp hnorm).resolve_right hcn
  exact sub_eq_zero.mp ((norm_eq_zero_iff (a - b)).mp hab)

private lemma z2_mul_left_cancel {a b c : Z2} (hc : c ≠ 0) (h : c * a = c * b) : a = b :=
  z2_mul_right_cancel hc (by linear_combination h)

private lemma exists_round (u n : ℤ) (hn : n ≠ 0) :
    ∃ q : ℤ, 2 * |u - q * n| ≤ |n| := by
  by_cases hn0 : 0 < n
  · set q := (u + n / 2) / n
    refine ⟨q, ?_⟩
    rw [abs_of_pos hn0]
    have h1 : q * n ≤ u + n / 2 := by
      have := Int.ediv_mul_le (u + n / 2) (ne_of_gt hn0)
      linarith
    have h2 : u + n / 2 < (q + 1) * n := by
      have := Int.lt_ediv_add_one_mul_self (u + n / 2) hn0
      linarith
    have h2' : u + n / 2 < q * n + n := by linarith
    rcases abs_cases (u - q * n) with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  · have hnneg : 0 < -n := by omega
    set q' := (u + (-n) / 2) / (-n)
    refine ⟨-q', ?_⟩
    rw [abs_of_neg (by omega : n < 0)]
    have h1 : q' * (-n) ≤ u + (-n) / 2 := by
      have := Int.ediv_mul_le (u + (-n) / 2) (ne_of_gt hnneg)
      linarith
    have h2 : u + (-n) / 2 < (q' + 1) * (-n) := by
      have := Int.lt_ediv_add_one_mul_self (u + (-n) / 2) hnneg
      linarith
    have h2' : u + (-n) / 2 < q' * (-n) + (-n) := by linarith
    have heq : u - (-q') * n = u - q' * (-n) := by ring
    rw [heq]
    rcases abs_cases (u - q' * (-n)) with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

private lemma euclid_div (α β : Z2) (hβ : β ≠ 0) :
    ∃ q r : Z2, α = q * β + r ∧ r.norm.natAbs < β.norm.natAbs := by
  have hbn : β.norm ≠ 0 := fun h => hβ ((norm_eq_zero_iff β).mp h)
  set w := α * star β
  obtain ⟨q1, hq1⟩ := exists_round w.re β.norm hbn
  obtain ⟨q2, hq2⟩ := exists_round w.im β.norm hbn
  set q : Z2 := ⟨q1, q2⟩
  set r : Z2 := α - q * β
  refine ⟨q, r, by ring, ?_⟩
  have hrw : r * star β = ⟨w.re - q1 * β.norm, w.im - q2 * β.norm⟩ := by
    have hβmul : β * star β = (β.norm : Z2) := z2_mul_star β
    calc r * star β = α * star β - q * (β * star β) := by ring
      _ = w - q * (β.norm : Z2) := by rw [hβmul]
      _ = ⟨w.re - q1 * β.norm, w.im - q2 * β.norm⟩ := by
        apply Zsqrtd.ext <;> simp [q]
  have hnorm_prod : r.norm * β.norm = (w.re - q1 * β.norm) ^ 2 - 2 * (w.im - q2 * β.norm) ^ 2 := by
    have h1 : (r * star β).norm = r.norm * (star β).norm := Zsqrtd.norm_mul r (star β)
    have h2 : (star β).norm = β.norm := Zsqrtd.norm_conj β
    rw [h2] at h1
    rw [← h1, hrw, z2_norm_eq]
  set x := w.re - q1 * β.norm
  set y := w.im - q2 * β.norm
  have hx2 : 4 * x ^ 2 ≤ β.norm ^ 2 := by
    have h := mul_self_le_mul_self (by positivity) hq1
    nlinarith [sq_abs x, sq_abs β.norm]
  have hy2 : 4 * y ^ 2 ≤ β.norm ^ 2 := by
    have h := mul_self_le_mul_self (by positivity) hq2
    nlinarith [sq_abs y, sq_abs β.norm]
  have habs_lt : |r.norm * β.norm| < β.norm ^ 2 := by
    rw [hnorm_prod, abs_lt]
    have hbn2 : 0 < β.norm ^ 2 := sq_pos_of_ne_zero hbn
    constructor <;> nlinarith
  have habs_r : |r.norm| < |β.norm| := by
    rw [abs_mul] at habs_lt
    have hpos : 0 < |β.norm| := abs_pos.mpr hbn
    nlinarith [sq_abs β.norm]
  zify
  exact habs_r

private noncomputable def toR (z : Z2) : ℝ :=
  (z.re : ℝ) + (z.im : ℝ) * Real.sqrt 2

private lemma toR_add (a b : Z2) : toR (a + b) = toR a + toR b := by
  simp only [toR, Zsqrtd.re_add, Zsqrtd.im_add, Int.cast_add]
  ring

private lemma toR_neg (a : Z2) : toR (-a) = -toR a := by
  simp only [toR, Zsqrtd.re_neg, Zsqrtd.im_neg, Int.cast_neg]
  ring

private lemma toR_mul (a b : Z2) : toR (a * b) = toR a * toR b := by
  simp only [toR, Zsqrtd.re_mul, Zsqrtd.im_mul, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  linear_combination -(a.im : ℝ) * (b.im : ℝ) * hs

private lemma toR_one : toR 1 = 1 := by
  simp [toR]

private lemma toR_mul_star (a : Z2) : toR a * toR (star a) = (a.norm : ℝ) := by
  rw [← toR_mul, z2_mul_star]
  simp [toR]

private lemma toR_add_star (a : Z2) : toR a + toR (star a) = 2 * (a.re : ℝ) := by
  simp only [toR, Zsqrtd.re_star, Zsqrtd.im_star, Int.cast_neg]
  ring

private lemma toR_injective : Function.Injective toR := by
  intro a b h
  have hsub : toR (a - b) = 0 := by
    rw [sub_eq_add_neg, toR_add, toR_neg, h, add_neg_cancel]
  have hnorm : ((a - b).norm : ℝ) = 0 := by
    rw [← toR_mul_star, hsub, zero_mul]
  have hnormZ : (a - b).norm = 0 := by exact_mod_cast hnorm
  exact sub_eq_zero.mp ((norm_eq_zero_iff (a - b)).mp hnormZ)

private def etaU : Z2ˣ :=
  ⟨⟨1, 1⟩, ⟨-1, 1⟩, by ext <;> norm_num, by ext <;> norm_num⟩

private def epsU : Z2ˣ :=
  ⟨⟨3, 2⟩, ⟨3, -2⟩, by ext <;> norm_num, by ext <;> norm_num⟩

private lemma etaU_sq : etaU ^ 2 = epsU := by
  apply Units.ext
  ext <;> norm_num [etaU, epsU, sq]

private lemma norm_etaU : (etaU : Z2).norm = -1 := by
  norm_num [etaU, Zsqrtd.norm]

private lemma norm_epsU : (epsU : Z2).norm = 1 := by
  norm_num [epsU, Zsqrtd.norm]

private lemma epsU_zpow_mul (a b : ℤ) :
    ((epsU ^ a : Z2ˣ) : Z2) * ((epsU ^ b : Z2ˣ) : Z2) = ((epsU ^ (a + b) : Z2ˣ) : Z2) := by
  rw [← Units.val_mul, ← zpow_add]

private lemma epsU_zpow_mul_neg (a : ℤ) :
    ((epsU ^ a : Z2ˣ) : Z2) * ((epsU ^ (-a) : Z2ˣ) : Z2) = 1 := by
  rw [epsU_zpow_mul, add_neg_cancel, zpow_zero, Units.val_one]

private lemma norm_zpow_epsU (k : ℤ) : ((epsU ^ k : Z2ˣ) : Z2).norm = 1 := by
  induction k using Int.induction_on with
  | zero => simp [Zsqrtd.norm]
  | succ n ih =>
    have : ((epsU ^ ((n : ℤ) + 1) : Z2ˣ) : Z2) = ((epsU ^ (n : ℤ) : Z2ˣ) : Z2) * (epsU : Z2) := by
      rw [zpow_add_one]; rfl
    rw [this, Zsqrtd.norm_mul, ih, norm_epsU, mul_one]
  | pred n ih =>
    have hinv : ((epsU⁻¹ : Z2ˣ) : Z2).norm = 1 := by norm_num [epsU, Zsqrtd.norm]
    have : ((epsU ^ (-(n : ℤ) - 1) : Z2ˣ) : Z2) = ((epsU ^ (-(n : ℤ)) : Z2ˣ) : Z2) * ((epsU⁻¹ : Z2ˣ) : Z2) := by
      rw [sub_eq_add_neg, zpow_add, zpow_neg_one]; rfl
    rw [this, Zsqrtd.norm_mul, ih, hinv, mul_one]

private lemma star_zpow_epsU (k : ℤ) :
    star ((epsU ^ k : Z2ˣ) : Z2) = ((epsU ^ (-k) : Z2ˣ) : Z2) := by
  have h1 : star (epsU : Z2) = ((epsU⁻¹ : Z2ˣ) : Z2) := by ext <;> norm_num [epsU]
  have h2 : star ((epsU⁻¹ : Z2ˣ) : Z2) = (epsU : Z2) := by ext <;> norm_num [epsU]
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
    have hL : ((epsU ^ ((n : ℤ) + 1) : Z2ˣ) : Z2) = ((epsU ^ (n : ℤ) : Z2ˣ) : Z2) * (epsU : Z2) := by
      rw [zpow_add_one]; rfl
    have hR : ((epsU ^ (-((n : ℤ) + 1)) : Z2ˣ) : Z2) =
        ((epsU⁻¹ : Z2ˣ) : Z2) * ((epsU ^ (-(n : ℤ)) : Z2ˣ) : Z2) := by
      rw [neg_add, add_comm, zpow_add, zpow_neg_one]; rfl
    rw [hL, star_mul, h1, ih, hR]
  | pred n ih =>
    have hL : ((epsU ^ (-(n : ℤ) - 1) : Z2ˣ) : Z2) =
        ((epsU ^ (-(n : ℤ)) : Z2ˣ) : Z2) * ((epsU⁻¹ : Z2ˣ) : Z2) := by
      rw [sub_eq_add_neg, zpow_add, zpow_neg_one]; rfl
    have hR : ((epsU ^ (-(-(n : ℤ) - 1)) : Z2ˣ) : Z2) =
        (epsU : Z2) * ((epsU ^ (-(-(n : ℤ))) : Z2ˣ) : Z2) := by
      have : -(-(n : ℤ) - 1) = 1 + -(-(n : ℤ)) := by ring
      rw [this, zpow_add, zpow_one]; rfl
    rw [hL, star_mul, h2, ih, hR]

private lemma star_etaU : star (etaU : Z2) = -((etaU⁻¹ : Z2ˣ) : Z2) := by
  ext <;> norm_num [etaU]

private lemma toR_zpow_epsU (k : ℤ) :
    toR ((epsU ^ k : Z2ˣ) : Z2) = (toR (epsU : Z2)) ^ k := by
  have hpos : 0 < toR (epsU : Z2) := by
    simp only [toR, epsU]; positivity
  have hne : toR (epsU : Z2) ≠ 0 := ne_of_gt hpos
  have hinv : toR ((epsU⁻¹ : Z2ˣ) : Z2) = (toR (epsU : Z2))⁻¹ := by
    have hm : toR ((epsU⁻¹ : Z2ˣ) : Z2) * toR (epsU : Z2) = 1 := by
      rw [← toR_mul]
      have : ((epsU⁻¹ : Z2ˣ) : Z2) * (epsU : Z2) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [this, toR_one]
    exact eq_inv_of_mul_eq_one_left hm
  induction k using Int.induction_on with
  | zero => simp [toR_one]
  | succ n ih =>
    have hL : ((epsU ^ ((n : ℤ) + 1) : Z2ˣ) : Z2) = ((epsU ^ (n : ℤ) : Z2ˣ) : Z2) * (epsU : Z2) := by
      rw [zpow_add_one]; rfl
    rw [hL, toR_mul, ih, zpow_add_one₀ hne]
  | pred n ih =>
    have hL : ((epsU ^ (-(n : ℤ) - 1) : Z2ˣ) : Z2) =
        ((epsU ^ (-(n : ℤ)) : Z2ˣ) : Z2) * ((epsU⁻¹ : Z2ˣ) : Z2) := by
      rw [sub_eq_add_neg, zpow_add, zpow_neg_one]; rfl
    rw [hL, toR_mul, ih, hinv, zpow_sub_one₀ hne]

private lemma exists_pow_gt_real (e y : ℝ) (he : 1 < e) : ∃ n : ℕ, y < e ^ n := by
  have hbern : ∀ n : ℕ, 1 + (n : ℝ) * (e - 1) ≤ e ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Nat.cast_succ]
      have : 0 ≤ (k : ℝ) * (e - 1) ^ 2 := by positivity
      nlinarith
  obtain ⟨n, hn⟩ := exists_nat_gt (y / (e - 1))
  refine ⟨n, ?_⟩
  have h1 : y < (n : ℝ) * (e - 1) := by
    have := mul_lt_mul_of_pos_right hn (sub_pos.mpr he)
    rwa [div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr he))] at this
  linarith [hbern n]

private lemma exists_zpow_interval (a b e : ℝ) (ha : 0 < a) (hb : 0 < b) (he : 1 < e) :
    ∃ k : ℤ, a ≤ b * e ^ k ∧ b * e ^ k < a * e := by
  have he0 : 0 < e := by linarith
  have hne : e ≠ 0 := ne_of_gt he0
  obtain ⟨n, hn⟩ := exists_pow_gt_real e (b / a) he
  obtain ⟨m, hm⟩ := exists_pow_gt_real e (a / b) he
  have hlow : b * e ^ (-(n : ℤ)) < a := by
    have h1 : b < a * e ^ n := by
      have := mul_lt_mul_of_pos_left hn ha
      rwa [mul_div_cancel₀ _ (ne_of_gt ha)] at this
    rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv, div_lt_iff₀ (pow_pos he0 n)]
    linarith
  have hhigh : a ≤ b * e ^ (m : ℤ) := by
    have h1 : a < b * e ^ m := by
      have := mul_lt_mul_of_pos_left hm hb
      rwa [mul_div_cancel₀ _ (ne_of_gt hb)] at this
    rw [zpow_natCast]
    linarith
  have hex : ∃ r : ℕ, a ≤ b * e ^ ((r : ℤ) - (n : ℤ)) := by
    refine ⟨m + n, ?_⟩
    have : ((m + n : ℕ) : ℤ) - (n : ℤ) = (m : ℤ) := by omega
    rw [this]
    exact hhigh
  classical
  set r := Nat.find hex
  have hr : a ≤ b * e ^ ((r : ℤ) - (n : ℤ)) := Nat.find_spec hex
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0] at hr
    simp only [Nat.cast_zero, zero_sub] at hr
    linarith
  have hprev : ¬ (a ≤ b * e ^ (((r - 1 : ℕ) : ℤ) - (n : ℤ))) :=
    Nat.find_min hex (by omega)
  push_neg at hprev
  refine ⟨(r : ℤ) - (n : ℤ), hr, ?_⟩
  have hexp : (r : ℤ) - (n : ℤ) = (((r - 1 : ℕ) : ℤ) - (n : ℤ)) + 1 := by omega
  rw [hexp, zpow_add_one₀ hne]
  have := mul_lt_mul_of_pos_right hprev he0
  linarith

private lemma forward_int (m N x y : ℤ) (hm : 3 ≤ m) (hNprime : Prime N)
    (hN_eq : N = (2 * m + 1) ^ 2 - 8)
    (hx_lo : 2 * m + 1 < x) (hx_hi : x ≤ 6 * m - 7) (hy_pos : 0 < y)
    (hx_eq : x ^ 2 - 2 * y ^ 2 = N) : False := by
  have hN_pos : 0 < N := by nlinarith
  have hN_ne : N ≠ 0 := ne_of_gt hN_pos
  set a : ℤ := 2 * m + 1
  have ha_eq : a ^ 2 - 8 = N := by dsimp [a]; linarith
  have ha7 : 7 ≤ a := by dsimp [a]; omega
  have hdvd_prod : N ∣ (a * y - 2 * x) * (a * y + 2 * x) := by
    refine ⟨y ^ 2 - 4, ?_⟩
    linear_combination y ^ 2 * ha_eq - 4 * hx_eq
  rcases hNprime.dvd_or_dvd hdvd_prod with h1 | h2
  · rcases h1 with ⟨v, hv⟩
    have hsq_u : (x * a - 4 * y) ^ 2 = N ^ 2 * (1 + 2 * v ^ 2) := by
      have hid : (x * a - 4 * y) ^ 2 - 2 * (a * y - 2 * x) ^ 2 =
          (x ^ 2 - 2 * y ^ 2) * (a ^ 2 - 8) := by ring
      rw [ha_eq, hx_eq, hv] at hid
      linarith
    have hdvd_u2 : N ∣ (x * a - 4 * y) ^ 2 := ⟨N * (1 + 2 * v ^ 2), by linarith⟩
    have hdvd_u : N ∣ (x * a - 4 * y) := hNprime.dvd_of_dvd_pow hdvd_u2
    rcases hdvd_u with ⟨u, hu⟩
    have hpell : u ^ 2 - 2 * v ^ 2 = 1 := by
      rw [hu] at hsq_u
      have h0 : N ^ 2 * (u ^ 2 - 2 * v ^ 2 - 1) = 0 := by linear_combination hsq_u
      have h1' := (mul_eq_zero.mp h0).resolve_left (pow_ne_zero 2 hN_ne)
      linarith
    have hx_rec : x = u * a + 4 * v := by
      have h0 : N * x = N * (u * a + 4 * v) := by
        linear_combination a * hu + 4 * hv - x * ha_eq
      exact mul_left_cancel₀ hN_ne h0
    have hy_rec : y = 2 * u + v * a := by
      have h0 : N * y = N * (2 * u + v * a) := by
        linear_combination 2 * hu + a * hv - y * ha_eq
      exact mul_left_cancel₀ hN_ne h0
    have hv_ne0 : v ≠ 0 := by
      intro hv0; subst hv0
      have : u = 1 ∨ u = -1 := by
        have : (u - 1) * (u + 1) = 0 := by linarith
        rcases mul_eq_zero.mp this with h | h <;> [left; right] <;> linarith
      rcases this with rfl | rfl <;> linarith
    have hv_pos : 0 < v := by
      by_contra hvn
      have hvle : v ≤ -1 := by omega
      by_cases hu0 : u ≤ 0
      · nlinarith only [hx_rec, hx_lo, ha7, hu0, hvle]
      · have hu_pos : 0 < u := by omega
        have h7v : 7 * (-v) ≤ a * (-v) := by nlinarith only [ha7, hvle]
        have h4u2 : (2 * u) ^ 2 < (a * (-v)) ^ 2 := by nlinarith only [hpell, hvle, h7v]
        have h2u_lt : 2 * u < a * (-v) := by nlinarith only [h4u2, hu_pos, h7v, hvle]
        linarith [hy_rec, hy_pos]
    have hv_ge2 : 2 ≤ v := by
      by_contra hv1
      have hv_eq : v = 1 := by omega
      rw [hv_eq] at hpell
      have : u ≤ -2 ∨ u = -1 ∨ u = 0 ∨ u = 1 ∨ 2 ≤ u := by omega
      rcases this with h | h | h | h | h <;> nlinarith only [hpell, h]
    have hu_ge3 : 3 ≤ u := by
      by_contra hun
      have hu_le : u ≤ -3 := by
        have : u ≤ -3 ∨ u = -2 ∨ u = -1 ∨ u = 0 ∨ u = 1 ∨ u = 2 := by omega
        rcases this with h | h | h | h | h | h <;> nlinarith only [hpell, hv_ge2, h]
      have h7u : 7 * (-u) ≤ a * (-u) := by nlinarith only [ha7, hu_le]
      have h4v2 : (4 * v) ^ 2 < (a * (-u)) ^ 2 := by nlinarith only [hpell, hu_le, h7u]
      have h4v_lt : 4 * v < a * (-u) := by nlinarith only [h4v2, hv_pos, h7u, hu_le]
      linarith [hx_rec, hx_lo, ha7]
    nlinarith only [hx_rec, hx_hi, hu_ge3, hv_ge2, hm, (show a = 2 * m + 1 from rfl)]
  · rcases h2 with ⟨v, hv⟩
    have hsq_u : (x * a + 4 * y) ^ 2 = N ^ 2 * (1 + 2 * v ^ 2) := by
      have hid : (x * a + 4 * y) ^ 2 - 2 * (a * y + 2 * x) ^ 2 =
          (x ^ 2 - 2 * y ^ 2) * (a ^ 2 - 8) := by ring
      rw [ha_eq, hx_eq, hv] at hid
      linarith
    have hdvd_u2 : N ∣ (x * a + 4 * y) ^ 2 := ⟨N * (1 + 2 * v ^ 2), by linarith⟩
    have hdvd_u : N ∣ (x * a + 4 * y) := hNprime.dvd_of_dvd_pow hdvd_u2
    rcases hdvd_u with ⟨u, hu⟩
    have hpell : u ^ 2 - 2 * v ^ 2 = 1 := by
      rw [hu] at hsq_u
      have h0 : N ^ 2 * (u ^ 2 - 2 * v ^ 2 - 1) = 0 := by linear_combination hsq_u
      have h1' := (mul_eq_zero.mp h0).resolve_left (pow_ne_zero 2 hN_ne)
      linarith
    have hx_rec : x = u * a - 4 * v := by
      have h0 : N * x = N * (u * a - 4 * v) := by
        linear_combination a * hu - 4 * hv - x * ha_eq
      exact mul_left_cancel₀ hN_ne h0
    have hv_pos : 0 < v := by nlinarith only [hv, ha7, hy_pos, hx_lo, hN_pos]
    have hu_pos : 0 < u := by nlinarith only [hu, ha7, hy_pos, hx_lo, hN_pos]
    have hv_ge2 : 2 ≤ v := by
      by_contra hv1
      have hv_eq : v = 1 := by omega
      rw [hv_eq] at hpell
      have : u ≤ 1 ∨ 2 ≤ u := by omega
      rcases this with h | h <;> nlinarith only [hpell, hu_pos, h]
    have hu_ge3 : 3 ≤ u := by nlinarith only [hpell, hv_ge2, hu_pos]
    by_cases hu3 : u = 3
    · rw [hu3] at hpell hx_rec
      have hv2 : v = 2 := by nlinarith only [hpell, hv_pos]
      nlinarith only [hx_rec, hx_hi, hv2, (show a = 2 * m + 1 from rfl)]
    · have hu4 : 4 ≤ u := by omega
      have h4v_lt : 4 * v < 3 * u := by nlinarith only [hpell, hu_pos, hv_pos]
      nlinarith only [hx_rec, hx_hi, hu4, h4v_lt, hm, (show a = 2 * m + 1 from rfl)]

private lemma forward_dir (m : ℕ) (hm : 2 < m) (hprime : Nat.Prime ((2 * m + 1) ^ 2 - 8)) :
    ∀ q : ℕ, 1 ≤ q → q ≤ 2 * (m - 2) → ¬ IsSquare (q * (m + 1) + q.choose 2 + 1) := by
  intro q hq1 hq2 ⟨s, hs⟩
  have hch : 2 * q.choose 2 = q * (q - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (Nat.even_mul_pred_self q).two_dvd
  have hsub8 : 8 ≤ (2 * m + 1) ^ 2 := by nlinarith
  have hN_eq : (((2 * m + 1) ^ 2 - 8 : ℕ) : ℤ) = (2 * (m : ℤ) + 1) ^ 2 - 8 := by
    zify [hsub8]
  have hchZ : 2 * (q.choose 2 : ℤ) = (q : ℤ) * ((q : ℤ) - 1) := by
    zify [hq1] at hch
    exact hch
  have hsZ : (q : ℤ) * ((m : ℤ) + 1) + (q.choose 2 : ℤ) + 1 = (s : ℤ) * (s : ℤ) := by
    exact_mod_cast hs
  have hs0 : 0 < s := by
    have : 1 ≤ s * s := by omega
    nlinarith
  refine forward_int (m : ℤ) (((2 * m + 1) ^ 2 - 8 : ℕ) : ℤ)
    (2 * (q : ℤ) + 2 * (m : ℤ) + 1) (2 * (s : ℤ))
    (by omega) (Nat.prime_iff_prime_int.mp hprime) hN_eq
    (by omega) (by omega) (by omega) ?_
  nlinarith

private lemma dvd_norm_lincomb (α x y : Z2) (p : ℤ) (hpN : p ∣ α.norm) :
    p ∣ (x * α + y * (p : Z2)).norm := by
  set z := x * α + y * (p : Z2)
  have h1 : z * star z = (α.norm : Z2) * (x * star x) +
      (p : Z2) * (x * α * star y + y * star (x * α) + (p : Z2) * (y * star y)) := by
    dsimp [z]
    have hsp : star (p : Z2) = (p : Z2) := by apply Zsqrtd.ext <;> simp
    rw [star_add, star_mul, star_mul, hsp]
    have hα : α * star α = (α.norm : Z2) := z2_mul_star α
    linear_combination (x * star x) * hα
  have h2 : (z * star z).re = z.norm := by rw [z2_mul_star]; simp
  have hre_cast : ∀ (c : ℤ) (w : Z2), ((c : Z2) * w).re = c * w.re := by
    intro c w; simp
  rw [← h2, h1, Zsqrtd.re_add, hre_cast, hre_cast]
  rcases hpN with ⟨k, hk⟩
  refine ⟨k * (x * star x).re + (x * α * star y + y * star (x * α) + (p : Z2) * (y * star y)).re, ?_⟩
  rw [hk]; ring

private lemma exists_split_prime (m : ℕ) (p : ℕ) (hp : p.Prime)
    (hpN : (p : ℤ) ∣ (⟨2 * (m : ℤ) + 1, 2⟩ : Z2).norm) :
    ∃ π γ : Z2, π.norm = (p : ℤ) ∧ (⟨2 * (m : ℤ) + 1, 2⟩ : Z2) = π * γ := by
  set α : Z2 := ⟨2 * (m : ℤ) + 1, 2⟩
  have hNodd : Odd α.norm := by
    refine ⟨2 * (m : ℤ) ^ 2 + 2 * (m : ℤ) - 4, ?_⟩
    rw [z2_norm_eq]; simp only [α]; ring
  have hp_ne2 : p ≠ 2 := by
    intro h2; subst h2
    rcases hNodd with ⟨t, ht⟩; rcases hpN with ⟨k, hk⟩; omega
  set P : ℕ → Prop := fun k => 0 < k ∧ ∃ z : Z2, z.norm.natAbs = k ∧
    ∃ x y : Z2, z = x * α + y * ((p : ℤ) : Z2)
  have hex : ∃ k, P k := by
    refine ⟨p * p, Nat.mul_pos hp.pos hp.pos, ((p : ℤ) : Z2), ?_, 0, 1, by ring⟩
    rw [z2_norm_intCast, sq, Int.natAbs_mul]; simp
  classical
  set k0 := Nat.find hex
  have hk0 : P k0 := Nat.find_spec hex
  have hmin : ∀ k < k0, ¬ P k := fun k hk => Nat.find_min hex hk
  rcases hk0 with ⟨hk0_pos, π0, hπ0_norm, x0, y0, hπ0_eq⟩
  have hπ0_ne0 : π0 ≠ 0 := by
    intro h0; rw [h0, Zsqrtd.norm_zero] at hπ0_norm; omega
  have hdvd_ideal : ∀ w : Z2, (∃ x y : Z2, w = x * α + y * ((p : ℤ) : Z2)) → π0 ∣ w := by
    intro w ⟨xw, yw, hw⟩
    obtain ⟨q, r, hqr, hlt⟩ := euclid_div w π0 hπ0_ne0
    have hr_mem : ∃ x y : Z2, r = x * α + y * ((p : ℤ) : Z2) := by
      refine ⟨xw - q * x0, yw - q * y0, ?_⟩
      have : r = w - q * π0 := by linear_combination -hqr
      rw [this, hw, hπ0_eq]; ring
    by_cases hr0 : r = 0
    · exact ⟨q, by rw [hqr, hr0, add_zero, mul_comm]⟩
    · exfalso
      have hrpos : 0 < r.norm.natAbs :=
        Int.natAbs_pos.mpr (fun h => hr0 ((norm_eq_zero_iff r).mp h))
      rw [hπ0_norm] at hlt
      exact hmin r.norm.natAbs hlt ⟨hrpos, r, rfl, hr_mem⟩
  have hπ0_dvd_α : π0 ∣ α := hdvd_ideal α ⟨1, 0, by ring⟩
  have hπ0_dvd_p : π0 ∣ ((p : ℤ) : Z2) := hdvd_ideal ((p : ℤ) : Z2) ⟨0, 1, by ring⟩
  have hp_dvd_π0norm : (p : ℤ) ∣ π0.norm := by
    rw [hπ0_eq]; exact dvd_norm_lincomb α x0 y0 p hpN
  have hπ0norm_dvd_p2 : π0.norm ∣ (p : ℤ) ^ 2 := by
    rcases hπ0_dvd_p with ⟨c, hc⟩
    refine ⟨c.norm, ?_⟩
    have := congrArg Zsqrtd.norm hc
    rw [Zsqrtd.norm_mul, z2_norm_intCast] at this
    exact this
  have hk0_dvd_p2 : k0 ∣ p ^ 2 := by
    rw [← hπ0_norm]
    have : (π0.norm.natAbs : ℤ) ∣ ((p ^ 2 : ℕ) : ℤ) := by
      rw [Int.natAbs_dvd]; exact_mod_cast hπ0norm_dvd_p2
    exact_mod_cast this
  have hp_dvd_k0 : p ∣ k0 := by
    rw [← hπ0_norm]; exact Int.ofNat_dvd_left.mp hp_dvd_π0norm
  have hk0_ne_p2 : k0 ≠ p ^ 2 := by
    intro hEq
    rcases hπ0_dvd_p with ⟨u, hu⟩
    have hun : u.norm.natAbs = 1 := by
      have hmul := congrArg Zsqrtd.norm hu
      rw [Zsqrtd.norm_mul, z2_norm_intCast] at hmul
      have habs : π0.norm.natAbs * u.norm.natAbs = p ^ 2 := by
        have h1 := congrArg Int.natAbs hmul
        rw [Int.natAbs_mul, Int.natAbs_pow] at h1
        simpa using h1.symm
      rw [hπ0_norm, hEq] at habs
      have hp2pos : 0 < p ^ 2 := pow_pos hp.pos 2
      nlinarith
    have hu_unit : u * (if u.norm = 1 then star u else -star u) = 1 := by
      have hun' : u.norm = 1 ∨ u.norm = -1 := Int.natAbs_eq_iff.mp hun
      rcases hun' with h1 | h1
      · simp only [h1, ↓reduceIte]; rw [z2_mul_star, h1]; simp
      · simp only [h1, show (-1 : ℤ) ≠ 1 by norm_num, ↓reduceIte]
        have := z2_mul_star u
        rw [h1] at this
        linear_combination -this
    have hp_dvd_π0 : ((p : ℤ) : Z2) ∣ π0 := by
      refine ⟨if u.norm = 1 then star u else -star u, ?_⟩
      calc π0 = π0 * 1 := (mul_one π0).symm
        _ = π0 * (u * (if u.norm = 1 then star u else -star u)) := by rw [hu_unit]
        _ = (π0 * u) * (if u.norm = 1 then star u else -star u) := by ring
        _ = ((p : ℤ) : Z2) * (if u.norm = 1 then star u else -star u) := by rw [← hu]
    have hp_dvd_α : ((p : ℤ) : Z2) ∣ α := dvd_trans hp_dvd_π0 hπ0_dvd_α
    rcases hp_dvd_α with ⟨w, hw⟩
    have him : (2 : ℤ) = (p : ℤ) * w.im := by
      have := congrArg Zsqrtd.im hw; simpa [α] using this
    have hp_dvd2 : (p : ℤ) ∣ 2 := ⟨w.im, him⟩
    have hp_le2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) (by exact_mod_cast hp_dvd2)
    have := hp.two_le
    omega
  have hk0_eq_p : k0 = p := by
    rcases hp_dvd_k0 with ⟨t, ht⟩
    have ht_dvd : t ∣ p := by
      have : p * t ∣ p * p := by rw [← ht, ← sq]; exact hk0_dvd_p2
      exact (mul_dvd_mul_iff_left hp.ne_zero).mp this
    rcases (Nat.dvd_prime hp).mp ht_dvd with rfl | rfl
    · omega
    · exfalso; apply hk0_ne_p2; rw [ht, sq]
  have hπ0_abs : π0.norm.natAbs = p := by rw [hπ0_norm, hk0_eq_p]
  rcases hπ0_dvd_α with ⟨γ0, hγ0⟩
  rcases Int.natAbs_eq_iff.mp hπ0_abs with hpos | hneg
  · exact ⟨π0, γ0, hpos, hγ0⟩
  · refine ⟨π0 * (etaU : Z2), ((etaU⁻¹ : Z2ˣ) : Z2) * γ0, ?_, ?_⟩
    · rw [Zsqrtd.norm_mul, hneg, norm_etaU]; ring
    · have : (etaU : Z2) * ((etaU⁻¹ : Z2ˣ) : Z2) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      calc α = π0 * γ0 := hγ0
        _ = π0 * (1 * γ0) := by rw [one_mul]
        _ = π0 * (((etaU : Z2) * ((etaU⁻¹ : Z2ˣ) : Z2)) * γ0) := by rw [this]
        _ = (π0 * (etaU : Z2)) * (((etaU⁻¹ : Z2ˣ) : Z2) * γ0) := by ring

private lemma not_dvd_star_of_odd_prime_norm (π : Z2) (p : ℕ) (hp : p.Prime) (hp_ne2 : p ≠ 2)
    (hπ_norm : π.norm = (p : ℤ)) (hdvd : π ∣ star π) : False := by
  have hdvd_sum : π ∣ π + star π := dvd_add dvd_rfl hdvd
  have hdvd_diff : π ∣ π - star π := dvd_sub dvd_rfl hdvd
  have hsum_eq : π + star π = ⟨2 * π.re, 0⟩ := by apply Zsqrtd.ext <;> simp <;> ring
  have hdiff_eq : π - star π = ⟨0, 2 * π.im⟩ := by apply Zsqrtd.ext <;> simp <;> ring
  have hp_dvd_re2 : (p : ℤ) ∣ 4 * π.re ^ 2 := by
    rcases hdvd_sum with ⟨c, hc⟩
    have := congrArg Zsqrtd.norm hc
    rw [hsum_eq, Zsqrtd.norm_mul, hπ_norm, z2_norm_eq] at this
    exact ⟨c.norm, by linarith⟩
  have hp_dvd_im2 : (p : ℤ) ∣ 8 * π.im ^ 2 := by
    rcases hdvd_diff with ⟨c, hc⟩
    have := congrArg Zsqrtd.norm hc
    rw [hdiff_eq, Zsqrtd.norm_mul, hπ_norm, z2_norm_eq] at this
    exact ⟨-c.norm, by linarith⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp_ndvd2 : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have : p ∣ 2 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) this
    have := hp.two_le
    omega
  have hp_dvd_re : (p : ℤ) ∣ π.re := by
    have h4 : (p : ℤ) ∣ (2 * π.re) ^ 2 := by
      simpa [show (2 * π.re) ^ 2 = 4 * π.re ^ 2 by ring] using hp_dvd_re2
    exact (hpZ.dvd_or_dvd (hpZ.dvd_of_dvd_pow h4)).resolve_left hp_ndvd2
  have hp_dvd_im : (p : ℤ) ∣ π.im := by
    have h8 : (p : ℤ) ∣ 2 * (2 * π.im) ^ 2 := by
      simpa [show 2 * (2 * π.im) ^ 2 = 8 * π.im ^ 2 by ring] using hp_dvd_im2
    have h4i := (hpZ.dvd_or_dvd h8).resolve_left hp_ndvd2
    exact (hpZ.dvd_or_dvd (hpZ.dvd_of_dvd_pow h4i)).resolve_left hp_ndvd2
  rcases hp_dvd_re with ⟨r1, hr1⟩
  rcases hp_dvd_im with ⟨r2, hr2⟩
  have hp2_dvd : (p : ℤ) ^ 2 ∣ (p : ℤ) := by
    refine ⟨r1 ^ 2 - 2 * r2 ^ 2, ?_⟩
    have hnorm_def := z2_norm_eq π
    rw [hπ_norm, hr1, hr2] at hnorm_def
    linarith
  rcases hp2_dvd with ⟨t, ht⟩
  have hp_pos : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  have hp_ge2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp.two_le
  have ht1 : (p : ℤ) * t = 1 := by
    have : (p : ℤ) * ((p : ℤ) * t) = (p : ℤ) * 1 := by linarith
    exact mul_left_cancel₀ (ne_of_gt hp_pos) this
  have h2 : (p : ℤ) = 1 ∨ (p : ℤ) = -1 := Int.eq_one_or_neg_one_of_mul_eq_one ht1
  omega

private lemma no_self_conj_factor (m : ℕ) (γ : Z2) (sgn : ℤ) (k : ℤ)
    (hsgn : sgn = 1 ∨ sgn = -1)
    (hγ_gt1 : 1 < γ.norm) (hγ_odd : Odd γ.norm)
    (hγ_dvd_α : γ ∣ (⟨2 * (m : ℤ) + 1, 2⟩ : Z2))
    (hcancel : (sgn : Z2) * γ * ((epsU ^ k : Z2ˣ) : Z2) = star γ) : False := by
  have kill_re0 : ∀ δ : Z2, (δ.norm = γ.norm ∨ δ.norm = -γ.norm) → star δ = -δ → False := by
    intro δ hdn hst
    have hre : δ.re = 0 := by
      have := congrArg Zsqrtd.re hst
      simp at this; omega
    have hev : Even δ.norm := by
      refine ⟨-(δ.im ^ 2), ?_⟩
      rw [z2_norm_eq, hre]; ring
    rcases hγ_odd with ⟨r, hr⟩
    rcases hev with ⟨t, ht⟩
    rcases hdn with h | h <;> omega
  have kill_im0 : ∀ δ : Z2, (δ.norm = γ.norm ∨ δ.norm = -γ.norm) →
      δ ∣ γ → star δ = δ → False := by
    intro δ hdn hdvd hst
    have him : δ.im = 0 := by
      have := congrArg Zsqrtd.im hst
      simp at this; omega
    have hδ_eq : δ = ((δ.re : ℤ) : Z2) := by apply Zsqrtd.ext <;> simp [him]
    have hdvd_α : ((δ.re : ℤ) : Z2) ∣ (⟨2 * (m : ℤ) + 1, 2⟩ : Z2) := by
      rw [← hδ_eq]; exact dvd_trans hdvd hγ_dvd_α
    rcases hdvd_α with ⟨w, hw⟩
    have h1 : δ.re ∣ 2 * (m : ℤ) + 1 := ⟨w.re, by have := congrArg Zsqrtd.re hw; simpa using this⟩
    have h2 : δ.re ∣ 2 := ⟨w.im, by have := congrArg Zsqrtd.im hw; simpa using this⟩
    have h1' : δ.re ∣ 1 := by
      rcases h1 with ⟨c1, hc1⟩; rcases h2 with ⟨c2, hc2⟩
      exact ⟨c1 - (m : ℤ) * c2, by linear_combination hc1 - (m : ℤ) * hc2⟩
    have hsq : δ.re ^ 2 = 1 := by
      rcases h1' with ⟨t, ht⟩
      have : δ.re = 1 ∨ δ.re = -1 := Int.eq_one_or_neg_one_of_mul_eq_one ht.symm
      rcases this with h | h <;> simp [h]
    have hdn1 : δ.norm = 1 := by rw [z2_norm_eq, him, hsq]; ring
    rcases hdn with h | h <;> omega
  rcases Int.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · set δ : Z2 := γ * ((epsU ^ j : Z2ˣ) : Z2)
    have hstar_δ : star δ = (sgn : Z2) * δ := by
      have hst : star ((epsU ^ j : Z2ˣ) : Z2) = ((epsU ^ (-j) : Z2ˣ) : Z2) := star_zpow_epsU j
      have hpow : ((epsU ^ (j + j) : Z2ˣ) : Z2) * ((epsU ^ (-j) : Z2ˣ) : Z2) =
          ((epsU ^ j : Z2ˣ) : Z2) := by
        rw [epsU_zpow_mul]; congr 2; ring
      dsimp [δ]
      rw [star_mul, hst, ← hcancel]
      calc ((epsU ^ (-j) : Z2ˣ) : Z2) * ((sgn : Z2) * γ * ((epsU ^ (j + j) : Z2ˣ) : Z2))
          = (sgn : Z2) * γ * (((epsU ^ (j + j) : Z2ˣ) : Z2) * ((epsU ^ (-j) : Z2ˣ) : Z2)) := by ring
        _ = (sgn : Z2) * (γ * ((epsU ^ j : Z2ˣ) : Z2)) := by rw [hpow]; ring
    have hδ_norm : δ.norm = γ.norm := by
      dsimp [δ]; rw [Zsqrtd.norm_mul, norm_zpow_epsU, mul_one]
    have hδ_dvd : δ ∣ γ := by
      refine ⟨((epsU ^ (-j) : Z2ˣ) : Z2), ?_⟩
      dsimp [δ]; rw [mul_assoc, epsU_zpow_mul_neg, mul_one]
    rcases hsgn with rfl | rfl
    · exact kill_im0 δ (Or.inl hδ_norm) hδ_dvd (by simpa using hstar_δ)
    · exact kill_re0 δ (Or.inl hδ_norm) (by simpa using hstar_δ)
  · set δ : Z2 := γ * ((epsU ^ j : Z2ˣ) : Z2) * (etaU : Z2)
    have hstar_δ : star δ = (-sgn : Z2) * δ := by
      have hst1 : star ((epsU ^ j : Z2ˣ) : Z2) = ((epsU ^ (-j) : Z2ˣ) : Z2) := star_zpow_epsU j
      have hst2 : star (etaU : Z2) = -((etaU⁻¹ : Z2ˣ) : Z2) := star_etaU
      have hpow : ((epsU ^ (2 * j + 1) : Z2ˣ) : Z2) * ((epsU ^ (-j) : Z2ˣ) : Z2) =
          ((epsU ^ j : Z2ˣ) : Z2) * (epsU : Z2) := by
        rw [epsU_zpow_mul, ← Units.val_mul, ← zpow_add_one]
        congr 2; ring
      have heta2 : (epsU : Z2) * ((etaU⁻¹ : Z2ˣ) : Z2) = (etaU : Z2) := by
        rw [← Units.val_mul, ← etaU_sq, sq, mul_assoc, mul_inv_cancel, mul_one]
      dsimp [δ]
      rw [star_mul, star_mul, hst1, hst2, ← hcancel]
      have hneg : ((-sgn : ℤ) : Z2) = -((sgn : ℤ) : Z2) := by simp
      calc -((etaU⁻¹ : Z2ˣ) : Z2) * (((epsU ^ (-j) : Z2ˣ) : Z2) *
            ((sgn : Z2) * γ * ((epsU ^ (2 * j + 1) : Z2ˣ) : Z2)))
          = (-((sgn : ℤ) : Z2)) * γ * ((((epsU ^ (2 * j + 1) : Z2ˣ) : Z2) *
              ((epsU ^ (-j) : Z2ˣ) : Z2)) * ((etaU⁻¹ : Z2ˣ) : Z2)) := by ring
        _ = ((-sgn : ℤ) : Z2) * γ * (((epsU ^ j : Z2ˣ) : Z2) * ((epsU : Z2) * ((etaU⁻¹ : Z2ˣ) : Z2))) := by
            rw [hneg, hpow]; ring
        _ = ((-sgn : ℤ) : Z2) * (γ * ((epsU ^ j : Z2ˣ) : Z2) * (etaU : Z2)) := by
            rw [heta2]; ring
    have hδ_norm : δ.norm = -γ.norm := by
      dsimp [δ]; rw [Zsqrtd.norm_mul, Zsqrtd.norm_mul, norm_zpow_epsU, norm_etaU]; ring
    have hδ_dvd : δ ∣ γ := by
      refine ⟨((etaU⁻¹ : Z2ˣ) : Z2) * ((epsU ^ (-j) : Z2ˣ) : Z2), ?_⟩
      have hinv1 : (etaU : Z2) * ((etaU⁻¹ : Z2ˣ) : Z2) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      dsimp [δ]
      calc γ = γ * (((epsU ^ j : Z2ˣ) : Z2) * ((epsU ^ (-j) : Z2ˣ) : Z2)) := by
            rw [epsU_zpow_mul_neg, mul_one]
        _ = γ * ((epsU ^ j : Z2ˣ) : Z2) * ((etaU : Z2) * ((etaU⁻¹ : Z2ˣ) : Z2)) *
            ((epsU ^ (-j) : Z2ˣ) : Z2) := by rw [hinv1]; ring
        _ = γ * ((epsU ^ j : Z2ˣ) : Z2) * (etaU : Z2) *
            (((etaU⁻¹ : Z2ˣ) : Z2) * ((epsU ^ (-j) : Z2ˣ) : Z2)) := by ring
    rcases hsgn with rfl | rfl
    · exact kill_re0 δ (Or.inr hδ_norm) (by simpa using hstar_δ)
    · exact kill_im0 δ (Or.inr hδ_norm) hδ_dvd (by simpa using hstar_δ)

private lemma re_bounds_and_square (m : ℕ) (hm : 2 < m) (β : Z2)
    (hβ_norm : β.norm = (2 * (m : ℤ) + 1) ^ 2 - 8)
    (hlo : toR (star (⟨2 * (m : ℤ) + 1, 2⟩ : Z2)) < toR β)
    (hhi : toR β < toR (star (⟨2 * (m : ℤ) + 1, 2⟩ : Z2) * (epsU : Z2)))
    (hne : β ≠ (⟨2 * (m : ℤ) + 1, 2⟩ : Z2)) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ 2 * (m - 2) ∧ IsSquare (q * (m + 1) + q.choose 2 + 1) := by
  set α : Z2 := ⟨2 * (m : ℤ) + 1, 2⟩
  set N : ℝ := (2 * (m : ℝ) + 1) ^ 2 - 8
  have hm3 : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hN_pos : 0 < N := by dsimp [N]; nlinarith
  have hsq2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq2_lt : Real.sqrt 2 < 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by norm_num]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hsα_pos : 0 < toR (star α) := by
    have : toR (star α) = (2 * (m : ℝ) + 1) - 2 * Real.sqrt 2 := by
      simp only [toR, α, Zsqrtd.re_star, Zsqrtd.im_star]; push_cast; ring
    nlinarith
  have hα_pos : 0 < toR α := by
    have : toR α = (2 * (m : ℝ) + 1) + 2 * Real.sqrt 2 := by
      simp only [toR, α]; push_cast; ring
    nlinarith
  have hsα_lt_α : toR (star α) < toR α := by
    have h1 : toR (star α) = (2 * (m : ℝ) + 1) - 2 * Real.sqrt 2 := by
      simp only [toR, α, Zsqrtd.re_star, Zsqrtd.im_star]; push_cast; ring
    have h2 : toR α = (2 * (m : ℝ) + 1) + 2 * Real.sqrt 2 := by
      simp only [toR, α]; push_cast; ring
    nlinarith
  have hβ_pos : 0 < toR β := lt_trans hsα_pos hlo
  have hα_norm : α.norm = (2 * (m : ℤ) + 1) ^ 2 - 8 := by rw [z2_norm_eq]; simp only [α]; ring
  have hβ_prod : toR β * toR (star β) = N := by
    rw [toR_mul_star, hβ_norm]; dsimp [N]; push_cast; ring
  have hα_prod : toR α * toR (star α) = N := by
    rw [toR_mul_star, hα_norm]; dsimp [N]; push_cast; ring
  have hsum_α : toR α + toR (star α) = 2 * (2 * (m : ℝ) + 1) := by
    have := toR_add_star α
    simp only [α] at this
    push_cast at this ⊢; linarith
  have hsum_β : toR β + toR (star β) = 2 * (β.re : ℝ) := toR_add_star β
  have hβ_gt_α : toR α < toR β := by
    by_contra hle
    have hlt : toR β < toR α := lt_of_le_of_ne (le_of_not_gt hle) (fun h => hne (toR_injective h))
    have hpos_p : 0 < (toR β - toR (star α)) * (toR α - toR β) :=
      mul_pos (sub_pos.mpr hlo) (sub_pos.mpr hlt)
    have hre_lt : (β.re : ℝ) < 2 * (m : ℝ) + 1 := by
      nlinarith [hpos_p, hβ_prod, hα_prod, hsum_α, hsum_β, hβ_pos]
    have hre_pos : (0 : ℝ) < (β.re : ℝ) := by
      have hsβ_pos : 0 < toR (star β) := by nlinarith [hβ_prod, hβ_pos, hN_pos]
      linarith [hsum_β]
    have hre_ltZ : β.re < 2 * (m : ℤ) + 1 := by exact_mod_cast hre_lt
    have hre_posZ : 0 < β.re := by exact_mod_cast hre_pos
    have hre_le : β.re ≤ 2 * (m : ℤ) := by omega
    have hnd := z2_norm_eq β
    rw [hβ_norm] at hnd
    have hmZ : (3 : ℤ) ≤ (m : ℤ) := by omega
    nlinarith
  have hx_gt : 2 * (m : ℤ) + 1 < β.re := by
    have hpos_p : 0 < (toR β - toR α) * (toR β - toR (star α)) :=
      mul_pos (sub_pos.mpr hβ_gt_α) (sub_pos.mpr (lt_trans hsα_lt_α hβ_gt_α))
    have : 2 * (m : ℝ) + 1 < (β.re : ℝ) := by
      nlinarith [hpos_p, hβ_prod, hα_prod, hsum_α, hsum_β, hβ_pos]
    exact_mod_cast this
  have hx_lt : β.re < 6 * (m : ℤ) - 5 := by
    set w : Z2 := star α * (epsU : Z2)
    have hw_re : w.re = 6 * (m : ℤ) - 5 := by
      simp only [w, α, epsU, Zsqrtd.re_mul, Zsqrtd.re_star, Zsqrtd.im_star]
      ring
    have hw_norm : w.norm = (2 * (m : ℤ) + 1) ^ 2 - 8 := by
      dsimp [w]
      rw [Zsqrtd.norm_mul, Zsqrtd.norm_conj, hα_norm, norm_epsU, mul_one]
    have hw_prod : toR w * toR (star w) = N := by
      rw [toR_mul_star, hw_norm]; dsimp [N]; push_cast; ring
    have hsw_lt_β : toR (star w) < toR β := by
      have hw_gt_α : toR α < toR w := lt_trans hβ_gt_α hhi
      have hsw_lt_sα : toR (star w) < toR (star α) := by
        nlinarith [hw_prod, hα_prod, hw_gt_α, hα_pos, hN_pos]
      exact lt_trans hsw_lt_sα hlo
    have hpos_p : 0 < (toR w - toR β) * (toR β - toR (star w)) :=
      mul_pos (sub_pos.mpr hhi) (sub_pos.mpr hsw_lt_β)
    have hsum_w : toR w + toR (star w) = 2 * (6 * (m : ℝ) - 5) := by
      have := toR_add_star w
      rw [hw_re] at this
      push_cast at this ⊢; linarith
    have : (β.re : ℝ) < 6 * (m : ℝ) - 5 := by
      nlinarith [hpos_p, hβ_prod, hw_prod, hsum_w, hsum_β, hβ_pos]
    exact_mod_cast this
  have hnorm_def : β.re ^ 2 - 2 * β.im ^ 2 = (2 * (m : ℤ) + 1) ^ 2 - 8 := by
    rw [← z2_norm_eq, hβ_norm]
  have hx_odd : β.re % 2 = 1 := by
    have hmod : (β.re ^ 2) % 2 = 1 := by
      have : β.re ^ 2 = 2 * (β.im ^ 2 + 2 * (m : ℤ) ^ 2 + 2 * (m : ℤ) - 4) + 1 := by linarith
      omega
    rcases Int.emod_two_eq_zero_or_one β.re with h0 | h1
    · exfalso
      have : (β.re ^ 2) % 2 = 0 := by rw [sq, Int.mul_emod, h0]; norm_num
      omega
    · exact h1
  have hy_even : 2 ∣ β.im := by
    rcases Int.odd_iff.mpr hx_odd with ⟨t, ht⟩
    have h2y2 : 2 * β.im ^ 2 = 4 * t * (t + 1) - 4 * (m : ℤ) * ((m : ℤ) + 1) + 8 := by
      rw [ht] at hnorm_def; linarith
    have ht_ev : 2 ∣ t * (t + 1) := by
      rcases Int.even_or_odd t with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · exact ⟨k * (2 * k + 1), by ring⟩
      · exact ⟨(2 * k + 1) * (k + 1), by ring⟩
    have hm_ev : 2 ∣ (m : ℤ) * ((m : ℤ) + 1) := by
      rcases Int.even_or_odd (m : ℤ) with ⟨k, hk⟩ | ⟨k, hk⟩
      · exact ⟨k * (2 * k + 1), by rw [hk]; ring⟩
      · exact ⟨(2 * k + 1) * (k + 1), by rw [hk]; ring⟩
    rcases ht_ev with ⟨c1, hc1⟩
    rcases hm_ev with ⟨c2, hc2⟩
    have hy2_ev : Even (β.im ^ 2) := ⟨2 * c1 - 2 * c2 + 2, by linarith⟩
    exact even_iff_two_dvd.mp (Int.even_pow.mp hy2_ev).1
  set q : ℕ := ((β.re - (2 * (m : ℤ) + 1)) / 2).toNat
  have hq_eq : 2 * (q : ℤ) + 2 * (m : ℤ) + 1 = β.re := by omega
  have hq1 : 1 ≤ q := by omega
  have hq2 : q ≤ 2 * (m - 2) := by omega
  set s : ℕ := β.im.natAbs / 2
  have hs_eq : (2 * (s : ℤ)) ^ 2 = β.im ^ 2 := by
    rcases hy_even with ⟨y', hy'⟩
    have habs : β.im.natAbs = 2 * y'.natAbs := by
      rw [hy', Int.natAbs_mul]; norm_num
    have hs_val : s = y'.natAbs := by dsimp [s]; omega
    have hsq : (y'.natAbs : ℤ) ^ 2 = y' ^ 2 := Int.natAbs_sq y'
    rw [hs_val, hy']
    nlinarith
  have hch : 2 * q.choose 2 = q * (q - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (Nat.even_mul_pred_self q).two_dvd
  refine ⟨q, hq1, hq2, s, ?_⟩
  have hchZ : 2 * (q.choose 2 : ℤ) = (q : ℤ) * ((q : ℤ) - 1) := by
    zify [hq1] at hch
    exact hch
  have hgoalZ : (q : ℤ) * ((m : ℤ) + 1) + (q.choose 2 : ℤ) + 1 = (s : ℤ) * (s : ℤ) := by
    nlinarith [hnorm_def, hq_eq, hs_eq, hchZ]
  exact_mod_cast hgoalZ

private lemma backward_dir (m : ℕ) (hm : 2 < m)
    (hcomp : ¬ Nat.Prime ((2 * m + 1) ^ 2 - 8)) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ 2 * (m - 2) ∧ IsSquare (q * (m + 1) + q.choose 2 + 1) := by
  have h49 : 49 ≤ (2 * m + 1) ^ 2 := by nlinarith
  have hsub8 : 8 ≤ (2 * m + 1) ^ 2 := by omega
  set Nnat : ℕ := (2 * m + 1) ^ 2 - 8
  have hN_ge : 41 ≤ Nnat := by dsimp [Nnat]; omega
  have hN_ne1 : Nnat ≠ 1 := by omega
  set p := Nnat.minFac
  have hp : p.Prime := Nat.minFac_prime hN_ne1
  have hp_dvd_Nnat : p ∣ Nnat := Nat.minFac_dvd Nnat
  have hp_lt_Nnat : p < Nnat := by
    have hle : p ≤ Nnat := Nat.le_of_dvd (by omega) hp_dvd_Nnat
    have hne : p ≠ Nnat := fun h => hcomp (h ▸ hp)
    omega
  set α : Z2 := ⟨2 * (m : ℤ) + 1, 2⟩
  have hα_norm_eq : α.norm = (2 * (m : ℤ) + 1) ^ 2 - 8 := by rw [z2_norm_eq]; simp only [α]; ring
  have hα_norm : α.norm = (Nnat : ℤ) := by
    rw [hα_norm_eq]; dsimp [Nnat]; zify [hsub8]
  have hpN : (p : ℤ) ∣ α.norm := by rw [hα_norm]; exact_mod_cast hp_dvd_Nnat
  obtain ⟨π, γ, hπ_norm, hα_fac_raw⟩ := exists_split_prime m p hp hpN
  have hα_fac : α = π * γ := hα_fac_raw
  have hN_pos : (0 : ℤ) < (Nnat : ℤ) := by omega
  have hγ_norm_mul : (p : ℤ) * γ.norm = (Nnat : ℤ) := by
    have := congrArg Zsqrtd.norm hα_fac
    rw [Zsqrtd.norm_mul, hπ_norm, hα_norm] at this
    linarith
  have hγ_norm_gt1 : 1 < γ.norm := by nlinarith
  have hγ_ne0 : γ ≠ 0 := fun h => by rw [h, Zsqrtd.norm_zero] at hγ_norm_gt1; omega
  have hsπ_ne0 : star π ≠ 0 := by
    intro h0
    have : (star π).norm = 0 := by rw [h0, Zsqrtd.norm_zero]
    rw [Zsqrtd.norm_conj, hπ_norm] at this
    have := hp.pos; omega
  have hNodd : Odd (Nnat : ℤ) := by
    refine ⟨2 * (m : ℤ) ^ 2 + 2 * (m : ℤ) - 4, ?_⟩
    rw [← hα_norm, hα_norm_eq]; ring
  have hp_ne2 : p ≠ 2 := by
    intro h2
    rcases hp_dvd_Nnat with ⟨t, ht⟩
    rw [h2] at ht
    rcases hNodd with ⟨r, hr⟩
    have : (Nnat : ℤ) = 2 * (t : ℤ) := by exact_mod_cast ht
    omega
  have hγ_odd : Odd γ.norm := by
    by_contra hev
    rw [Int.not_odd_iff_even] at hev
    rcases hev with ⟨t, ht⟩; rcases hNodd with ⟨r, hr⟩
    have hmul2 : (Nnat : ℤ) = 2 * ((p : ℤ) * t) := by
      rw [← hγ_norm_mul, ht]; ring
    omega
  set β0_raw : Z2 := star π * γ
  have hβ0_raw_norm : β0_raw.norm = (Nnat : ℤ) := by
    dsimp [β0_raw]; rw [Zsqrtd.norm_mul, Zsqrtd.norm_conj, hπ_norm, hγ_norm_mul]
  have hβ0_raw_ne : toR β0_raw ≠ 0 := by
    intro h0
    have hmul0 := toR_mul_star β0_raw
    rw [h0, zero_mul, hβ0_raw_norm] at hmul0
    have hposR : (0 : ℝ) < ((Nnat : ℤ) : ℝ) := by exact_mod_cast hN_pos
    linarith
  set sgn : ℤ := if 0 < toR β0_raw then 1 else -1
  have hsgn_cases : sgn = 1 ∨ sgn = -1 := by dsimp [sgn]; split_ifs <;> simp
  have hsgn_sq : sgn ^ 2 = 1 := by rcases hsgn_cases with h | h <;> simp [h]
  set β0 : Z2 := (sgn : Z2) * β0_raw
  have hβ0_norm : β0.norm = (Nnat : ℤ) := by
    dsimp [β0]; rw [Zsqrtd.norm_mul, z2_norm_intCast, hβ0_raw_norm, hsgn_sq, one_mul]
  have hβ0_pos : 0 < toR β0 := by
    dsimp [β0, sgn]
    split_ifs with h
    · simpa using h
    · have hlt : toR β0_raw < 0 := lt_of_le_of_ne (le_of_not_gt h) hβ0_raw_ne
      rw [show ((-1 : ℤ) : Z2) * β0_raw = -β0_raw by ring, toR_neg]
      linarith
  have hsα_pos : 0 < toR (star α) := by
    have h1 : toR (star α) = (2 * (m : ℝ) + 1) - 2 * Real.sqrt 2 := by
      simp only [toR, α, Zsqrtd.re_star, Zsqrtd.im_star]; push_cast; ring
    have h2 : Real.sqrt 2 < 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by norm_num]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have hm3 : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith
  have heps_gt1 : 1 < toR (epsU : Z2) := by
    have h1 : toR (epsU : Z2) = 3 + 2 * Real.sqrt 2 := by simp only [toR, epsU]; push_cast; ring
    have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    linarith
  obtain ⟨k, hk1, hk2⟩ := exists_zpow_interval (toR (star α)) (toR β0) (toR (epsU : Z2))
    hsα_pos hβ0_pos heps_gt1
  set β : Z2 := β0 * ((epsU ^ k : Z2ˣ) : Z2)
  have hβ_norm : β.norm = (2 * (m : ℤ) + 1) ^ 2 - 8 := by
    dsimp [β]; rw [Zsqrtd.norm_mul, hβ0_norm, norm_zpow_epsU, mul_one, ← hα_norm, hα_norm_eq]
  have hβ_toR : toR β = toR β0 * (toR (epsU : Z2)) ^ k := by
    dsimp [β]; rw [toR_mul, toR_zpow_epsU]
  have hβ_ne_α : β ≠ α := by
    intro hEq
    have hmul_eq : ((sgn : Z2) * star π * ((epsU ^ k : Z2ˣ) : Z2)) * γ = π * γ := by
      calc ((sgn : Z2) * star π * ((epsU ^ k : Z2ˣ) : Z2)) * γ
          = β := by dsimp [β, β0, β0_raw]; ring
        _ = α := hEq
        _ = π * γ := hα_fac
    have hcancel : (sgn : Z2) * star π * ((epsU ^ k : Z2ˣ) : Z2) = π :=
      z2_mul_right_cancel hγ_ne0 hmul_eq
    have hπ_dvd_sπ : π ∣ star π := by
      refine ⟨(sgn : Z2) * ((epsU ^ (-k) : Z2ˣ) : Z2), ?_⟩
      have hsgn2 : (sgn : Z2) * (sgn : Z2) = 1 := by
        rcases hsgn_cases with h | h <;> simp [h]
      calc star π = ((sgn : Z2) * (sgn : Z2)) * star π *
              (((epsU ^ k : Z2ˣ) : Z2) * ((epsU ^ (-k) : Z2ˣ) : Z2)) := by
            rw [hsgn2, epsU_zpow_mul_neg, one_mul, mul_one]
        _ = ((sgn : Z2) * star π * ((epsU ^ k : Z2ˣ) : Z2)) *
              ((sgn : Z2) * ((epsU ^ (-k) : Z2ˣ) : Z2)) := by ring
        _ = π * ((sgn : Z2) * ((epsU ^ (-k) : Z2ˣ) : Z2)) := by rw [hcancel]
    exact not_dvd_star_of_odd_prime_norm π p hp hp_ne2 hπ_norm hπ_dvd_sπ
  have hβ_ne_sα : β ≠ star α := by
    intro hEq
    have hsα_fac : star α = star π * star γ := by rw [hα_fac, star_mul, mul_comm]
    have hmul_eq : star π * ((sgn : Z2) * γ * ((epsU ^ k : Z2ˣ) : Z2)) = star π * star γ := by
      calc star π * ((sgn : Z2) * γ * ((epsU ^ k : Z2ˣ) : Z2))
          = β := by dsimp [β, β0, β0_raw]; ring
        _ = star α := hEq
        _ = star π * star γ := hsα_fac
    have hcancel : (sgn : Z2) * γ * ((epsU ^ k : Z2ˣ) : Z2) = star γ :=
      z2_mul_left_cancel hsπ_ne0 hmul_eq
    exact no_self_conj_factor m γ sgn k hsgn_cases hγ_norm_gt1 hγ_odd ⟨π, by rw [hα_fac_raw, mul_comm]⟩ hcancel
  have hlo : toR (star α) < toR β :=
    lt_of_le_of_ne (by rwa [hβ_toR]) (fun h => hβ_ne_sα (toR_injective h.symm))
  have hhi : toR β < toR (star α * (epsU : Z2)) := by
    rw [hβ_toR, toR_mul (star α) (epsU : Z2)]; exact hk2
  exact re_bounds_and_square m hm β hβ_norm hlo hhi hβ_ne_α

end OMA.OeisA028886

theorem OMA.solution : type_of% @OMA.S_oeis_a028886.main := by
  intro m hm
  constructor
  · exact OMA.OeisA028886.forward_dir m hm
  · intro h
    by_contra hnp
    obtain ⟨q, hq1, hq2, hsq⟩ := OMA.OeisA028886.backward_dir m hm hnp
    exact h q hq1 hq2 hsq
