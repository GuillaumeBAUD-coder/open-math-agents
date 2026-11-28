import OMAStatements.S_mo_451543

open OMA.S_mo_451543 MeasureTheory Finset

namespace MartingaleJensenGap

lemma finiteGap_quadratic {a b c : ℝ} (ha : 0 ≤ a) : FiniteGap (quadratic a b c) := by
  intro n m w x y z hw _ hrow hcol
  have hrow' : ∀ i, ∑ j, w i j * y j = x i * ∑ j, w i j := fun i ↦ by
    have h := hrow i
    simp only [mul_sub, sum_sub_distrib, ← sum_mul] at h
    linarith
  have hcol' : ∀ j, ∑ i, w i j * x i = z j * ∑ i, w i j := fun j ↦ by
    have h := hcol j
    simp only [mul_sub, sum_sub_distrib, ← sum_mul] at h
    linarith
  have hxy_x2 : ∑ i, ∑ j, w i j * (x i * y j) = ∑ i, ∑ j, w i j * x i ^ 2 := by
    refine sum_congr rfl fun i _ ↦ ?_
    calc
      ∑ j, w i j * (x i * y j) = x i * ∑ j, w i j * y j := by
        rw [mul_sum]; refine sum_congr rfl fun j _ ↦ by ring
      _ = x i * (x i * ∑ j, w i j) := by rw [hrow' i]
      _ = ∑ j, w i j * x i ^ 2 := by rw [mul_sum, mul_sum]; refine sum_congr rfl fun j _ ↦ by ring
  have hxy_yz : ∑ i, ∑ j, w i j * (x i * y j) = ∑ i, ∑ j, w i j * (y j * z j) := by
    rw [sum_comm, sum_comm (s := univ) (t := univ) (f := fun i j ↦ w i j * (y j * z j))]
    refine sum_congr rfl fun j _ ↦ ?_
    calc
      ∑ i, w i j * (x i * y j) = y j * ∑ i, w i j * x i := by
        rw [mul_sum]; refine sum_congr rfl fun i _ ↦ by ring
      _ = y j * (z j * ∑ i, w i j) := by rw [hcol' j]
      _ = ∑ i, w i j * (y j * z j) := by
        rw [mul_sum, mul_sum]; refine sum_congr rfl fun i _ ↦ by ring
  have hlin1 : ∑ i, ∑ j, w i j * (y j - x i) = 0 := by
    rw [sum_eq_zero]; intro i _; exact hrow i
  have hlin2 : ∑ i, ∑ j, w i j * (z j - x i) = 0 := by
    rw [sum_comm, sum_eq_zero]; intro j _
    have h := hcol j
    have hneg : ∑ i, w i j * (z j - x i) = -(∑ i, w i j * (x i - z j)) := by
      rw [← sum_neg_distrib]; refine sum_congr rfl fun i _ ↦ by ring
    linarith
  have hquad :
      ∑ i, ∑ j, w i j * (quadratic a b c (y j) + quadratic a b c (z j) - 2 * quadratic a b c (x i)) =
        a * ∑ i, ∑ j, w i j * (y j - z j) ^ 2 := by
    have hsplit :
        ∑ i, ∑ j, w i j * (quadratic a b c (y j) + quadratic a b c (z j) - 2 * quadratic a b c (x i)) =
          a * (∑ i, ∑ j, w i j * (y j - z j) ^ 2 + 2 * (∑ i, ∑ j, w i j * (y j * z j) -
            ∑ i, ∑ j, w i j * x i ^ 2)) +
          b * (∑ i, ∑ j, w i j * (y j - x i) + ∑ i, ∑ j, w i j * (z j - x i)) := by
      simp only [quadratic, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
    rw [hsplit, ← hxy_yz, hxy_x2, sub_self, mul_zero, add_zero, hlin1, hlin2, add_zero, mul_zero,
      add_zero]
  rw [hquad]
  exact mul_nonneg ha (sum_nonneg fun i _ ↦ sum_nonneg fun j _ ↦ mul_nonneg (hw i j) (sq_nonneg _))

lemma finiteGap_convex {f : ℝ → ℝ} (hf : FiniteGap f) : ConvexOn ℝ Set.univ f := by
  refine ⟨convex_univ, fun a _ b _ p q hp hq hpq ↦ ?_⟩
  by_cases hab : a = b
  · subst hab
    have h1 : p • a + q • a = a := by
      simp only [smul_eq_mul]
      calc p * a + q * a = (p + q) * a := by ring
        _ = a := by rw [hpq, one_mul]
    rw [h1]
    simp only [smul_eq_mul]
    have h2 : p * f a + q * f a = (p + q) * f a := by ring
    rw [h2, hpq, one_mul]
  · let w : Fin 1 → Fin 2 → ℝ := fun _ ↦ ![p, q]
    let x : Fin 1 → ℝ := fun _ ↦ p * a + q * b
    let y : Fin 2 → ℝ := ![a, b]
    let z : Fin 2 → ℝ := fun _ ↦ p * a + q * b
    have hinj : Function.Injective y := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [y] at hij ⊢
      · exact (hab hij).elim
      · exact (hab hij.symm).elim
    have hgap := hf 1 2 w x y z
      (fun i j ↦ by fin_cases i; fin_cases j <;> simp [w, hp, hq])
      hinj
      (fun i ↦ by
        fin_cases i
        simp only [Fin.sum_univ_two, w, x, y, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one]
        calc p * (a - (p * a + q * b)) + q * (b - (p * a + q * b)) =
            (1 - (p + q)) * (p * a + q * b) := by ring
          _ = 0 := by rw [hpq]; ring)
      (fun j ↦ by
        fin_cases j <;> simp [w, x, z])
    simp only [Fin.sum_univ_one, Fin.sum_univ_two, w, x, y, z, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul] at hgap ⊢
    have hrew :
        p * (f a + f (p * a + q * b) - 2 * f (p * a + q * b)) +
          q * (f b + f (p * a + q * b) - 2 * f (p * a + q * b)) =
        p * f a + q * f b - (p + q) * f (p * a + q * b) := by ring
    rw [hrew, hpq, one_mul] at hgap
    linarith

lemma finiteGap_comp_neg {f : ℝ → ℝ} (hf : FiniteGap f) : FiniteGap (fun t ↦ f (-t)) := by
  intro n m w x y z hw hinj hrow hcol
  have hinj' : Function.Injective (fun j ↦ -y j) := fun j₁ j₂ h ↦ hinj (neg_inj.mp h)
  have hgap := hf n m w (fun i ↦ -x i) (fun j ↦ -y j) (fun j ↦ -z j) hw hinj'
    (fun i ↦ by
      have h := hrow i
      have heq : ∑ j, w i j * (-y j - -x i) = -(∑ j, w i j * (y j - x i)) := by
        rw [← sum_neg_distrib]; refine sum_congr rfl fun j _ ↦ by ring
      linarith)
    (fun j ↦ by
      have h := hcol j
      have heq : ∑ i, w i j * (-x i - -z j) = -(∑ i, w i j * (x i - z j)) := by
        rw [← sum_neg_distrib]; refine sum_congr rfl fun i _ ↦ by ring
      linarith)
  exact hgap

noncomputable def rDeriv (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  sInf ((fun h : ℝ ↦ (f (u + h) - f u) / h) '' Set.Ioi 0)

noncomputable def lDeriv (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  sSup ((fun h : ℝ ↦ (f u - f (u - h)) / h) '' Set.Ioi 0)

lemma secant_left_le_right {f : ℝ → ℝ} (hc : ConvexOn ℝ Set.univ f) (u : ℝ)
    {h₁ h₂ : ℝ} (h1 : 0 < h₁) (h2 : 0 < h₂) :
    (f u - f (u - h₁)) / h₁ ≤ (f (u + h₂) - f u) / h₂ := by
  have h := hc.secant_mono (Set.mem_univ u) (Set.mem_univ (u - h₁)) (Set.mem_univ (u + h₂))
    (by linarith) (by linarith) (by linarith)
  have hL : (f (u - h₁) - f u) / (u - h₁ - u) = (f u - f (u - h₁)) / h₁ := by
    have : u - h₁ - u = -h₁ := by ring
    rw [this, div_neg, ← neg_div, neg_sub]
  have hR : (f (u + h₂) - f u) / (u + h₂ - u) = (f (u + h₂) - f u) / h₂ := by
    have : u + h₂ - u = h₂ := by ring
    rw [this]
  linarith

lemma secant_right_mono {f : ℝ → ℝ} (hc : ConvexOn ℝ Set.univ f) (u : ℝ)
    {h₁ h₂ : ℝ} (h1 : 0 < h₁) (hle : h₁ ≤ h₂) :
    (f (u + h₁) - f u) / h₁ ≤ (f (u + h₂) - f u) / h₂ := by
  have h := hc.secant_mono (Set.mem_univ u) (Set.mem_univ (u + h₁)) (Set.mem_univ (u + h₂))
    (by linarith) (by linarith) (by linarith)
  simpa [add_sub_cancel_left] using h

lemma secant_left_anti {f : ℝ → ℝ} (hc : ConvexOn ℝ Set.univ f) (u : ℝ)
    {h₁ h₂ : ℝ} (h1 : 0 < h₁) (hle : h₁ ≤ h₂) :
    (f u - f (u - h₂)) / h₂ ≤ (f u - f (u - h₁)) / h₁ := by
  have h := hc.secant_mono (Set.mem_univ u) (Set.mem_univ (u - h₂)) (Set.mem_univ (u - h₁))
    (by linarith) (by linarith) (by linarith)
  have h1' : (f (u - h₁) - f u) / (u - h₁ - u) = (f u - f (u - h₁)) / h₁ := by
    have : u - h₁ - u = -h₁ := by ring
    rw [this, div_neg, ← neg_div, neg_sub]
  have h2' : (f (u - h₂) - f u) / (u - h₂ - u) = (f u - f (u - h₂)) / h₂ := by
    have : u - h₂ - u = -h₂ := by ring
    rw [this, div_neg, ← neg_div, neg_sub]
  linarith

lemma rDeriv_bddBelow {f : ℝ → ℝ} (hc : ConvexOn ℝ Set.univ f) (u : ℝ) :
    BddBelow ((fun h : ℝ ↦ (f (u + h) - f u) / h) '' Set.Ioi 0) :=
  ⟨(f u - f (u - 1)) / 1, by rintro _ ⟨h, hh, rfl⟩; exact secant_left_le_right hc u one_pos hh⟩

lemma lDeriv_bddAbove {f : ℝ → ℝ} (hc : ConvexOn ℝ Set.univ f) (u : ℝ) :
    BddAbove ((fun h : ℝ ↦ (f u - f (u - h)) / h) '' Set.Ioi 0) :=
  ⟨(f (u + 1) - f u) / 1, by rintro _ ⟨h, hh, rfl⟩; exact secant_left_le_right hc u hh one_pos⟩

lemma rDeriv_le_secant {f : ℝ → ℝ} (hc : ConvexOn ℝ Set.univ f) (u : ℝ) {h : ℝ} (hh : 0 < h) :
    rDeriv f u ≤ (f (u + h) - f u) / h :=
  csInf_le (rDeriv_bddBelow hc u) ⟨h, hh, rfl⟩

lemma secant_le_lDeriv {f : ℝ → ℝ} (hc : ConvexOn ℝ Set.univ f) (u : ℝ) {h : ℝ} (hh : 0 < h) :
    (f u - f (u - h)) / h ≤ lDeriv f u :=
  le_csSup (lDeriv_bddAbove hc u) ⟨h, hh, rfl⟩

lemma lDeriv_le_rDeriv {f : ℝ → ℝ} (hc : ConvexOn ℝ Set.univ f) (u : ℝ) :
    lDeriv f u ≤ rDeriv f u := by
  refine csSup_le ⟨_, ⟨1, Set.mem_Ioi.mpr one_pos, rfl⟩⟩ ?_
  rintro _ ⟨h₁, hh₁, rfl⟩
  refine le_csInf ⟨_, ⟨1, Set.mem_Ioi.mpr one_pos, rfl⟩⟩ ?_
  rintro _ ⟨h₂, hh₂, rfl⟩
  exact secant_left_le_right hc u hh₁ hh₂

lemma rDeriv_le_lDeriv_of_lt {f : ℝ → ℝ} (hc : ConvexOn ℝ Set.univ f) {u v : ℝ} (huv : u < v) :
    rDeriv f u ≤ lDeriv f v := by
  have h1 : rDeriv f u ≤ (f (u + (v - u)) - f u) / (v - u) :=
    rDeriv_le_secant hc u (sub_pos.mpr huv)
  have h2 : (f v - f (v - (v - u))) / (v - u) ≤ lDeriv f v :=
    secant_le_lDeriv hc v (sub_pos.mpr huv)
  rw [add_sub_cancel] at h1
  rw [sub_sub_cancel] at h2
  exact h1.trans h2

lemma rDeriv_comp_neg {f : ℝ → ℝ} (u : ℝ) :
    rDeriv (fun t ↦ f (-t)) (-u) = -lDeriv f u := by
  unfold rDeriv lDeriv
  have hset : (fun h : ℝ ↦ (f (-(-u + h)) - f (- -u)) / h) '' Set.Ioi 0 =
      Neg.neg '' ((fun h : ℝ ↦ (f u - f (u - h)) / h) '' Set.Ioi 0) := by
    ext y; simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨(f u - f (u - h)) / h, ⟨h, hh, rfl⟩, ?_⟩
      have : -(-u + h) = u - h := by ring
      rw [this, neg_neg, ← neg_div, neg_sub]
    · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
      refine ⟨h, hh, ?_⟩
      have : -(-u + h) = u - h := by ring
      rw [this, neg_neg, ← neg_div, neg_sub]
  rw [hset, Set.image_neg_eq_neg, Real.sInf_neg]

lemma lDeriv_comp_neg {f : ℝ → ℝ} (u : ℝ) :
    lDeriv (fun t ↦ f (-t)) (-u) = -rDeriv f u := by
  have h := rDeriv_comp_neg (f := fun t ↦ f (-t)) (-u)
  simp only [neg_neg] at h
  linarith

lemma trapezoid_ge {f : ℝ → ℝ} (hf : FiniteGap f) {u v : ℝ} (huv : u < v) :
    2 * (f v - f u) ≤ (v - u) * (rDeriv f u + lDeriv f v) := by
  have hc := finiteGap_convex hf
  have hstep1 : ∀ q : ℝ, 0 < q → q < 1 →
      0 ≤ q * (1 - q) * (v - u) * rDeriv f u + 2 * (1 - q) * f u + q * f v -
        (2 - q) * f (u + q * (v - u)) := fun q hq0 hq1 ↦ by
    have hcoeff : 0 < q * (1 - q) * (v - u) :=
      mul_pos (mul_pos hq0 (by linarith)) (sub_pos.mpr huv)
    have hK : ∀ h : ℝ, 0 < h → h < q * (v - u) →
        -(2 * (1 - q) * f u + q * f v - (2 - q) * f (u + q * (v - u))) /
          (q * (1 - q) * (v - u)) ≤ (f (u + h) - f u) / h := fun h hh0 hhq ↦ by
      let β : ℝ := h / ((1 - q) * (q * (v - u) - h))
      have hden : 0 < (1 - q) * (q * (v - u) - h) := mul_pos (by linarith) (by linarith)
      have hβ : 0 < β := div_pos hh0 hden
      have h1β : 1 + β * (1 - q) = q * (v - u) / (q * (v - u) - h) := by
        dsimp [β]; field_simp [(by linarith : (1 - q) ≠ 0), (by linarith : q * (v - u) - h ≠ 0)]; ring
      let w : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![β * (1 - q), β * q]]
      let x : Fin 2 → ℝ := ![u, u + q * (v - u)]
      let y : Fin 2 → ℝ := ![u, v]
      let z : Fin 2 → ℝ := ![u + h, u + q * (v - u)]
      have hinj : Function.Injective y := fun i j hij ↦ by
        fin_cases i <;> fin_cases j <;> simp [y] at hij ⊢ <;> linarith
      have hgap := hf 2 2 w x y z
        (fun i j ↦ by
          fin_cases i <;> fin_cases j <;> simp [w] <;> nlinarith)
        hinj
        (fun i ↦ by
          fin_cases i
          · simp [w, x, y]
          · simp [Fin.sum_univ_two, w, x, y]; ring)
        (fun j ↦ by
          fin_cases j
          · simp only [Fin.sum_univ_two, w, x, z, Matrix.cons_val_zero, Matrix.cons_val_one,
              Matrix.cons_val_fin_one]
            dsimp [β]
            field_simp [(by linarith : (1 - q) ≠ 0), (by linarith : q * (v - u) - h ≠ 0)]
            ring
          · simp [w, x, z])
      simp only [Fin.sum_univ_two, w, x, y, z, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at hgap
      have hsimp :
          (1 + β * (1 - q)) * (f (u + h) - f u) +
            β * (2 * (1 - q) * f u + q * f v - (2 - q) * f (u + q * (v - u))) ≥ 0 := by linarith
      have hratio : (1 + β * (1 - q)) / β = q * (1 - q) * (v - u) / h := by
        rw [h1β]; dsimp [β]
        field_simp [(by linarith : (1 - q) ≠ 0), (by linarith : q * (v - u) - h ≠ 0), hh0.ne']
      have hdiv : 0 ≤ q * (1 - q) * (v - u) * ((f (u + h) - f u) / h) +
          (2 * (1 - q) * f u + q * f v - (2 - q) * f (u + q * (v - u))) := by
        have h2 := div_nonneg hsimp hβ.le
        rw [add_div, mul_div_right_comm, hratio, mul_div_cancel_left₀ _ hβ.ne'] at h2
        have h3 : q * (1 - q) * (v - u) / h * (f (u + h) - f u) =
            q * (1 - q) * (v - u) * ((f (u + h) - f u) / h) := by ring
        linarith
      rw [div_le_iff₀ hcoeff]
      linarith
    have hinf : -(2 * (1 - q) * f u + q * f v - (2 - q) * f (u + q * (v - u))) /
        (q * (1 - q) * (v - u)) ≤ rDeriv f u := by
      refine le_csInf ⟨_, ⟨1, Set.mem_Ioi.mpr one_pos, rfl⟩⟩ ?_
      rintro _ ⟨h, hh, rfl⟩
      by_cases hlt : h < q * (v - u)
      · exact hK h hh hlt
      · push Not at hlt
        have hh2 : 0 < q * (v - u) / 2 := by nlinarith
        have hlt2 : q * (v - u) / 2 < q * (v - u) := by nlinarith
        exact (hK _ hh2 hlt2).trans (secant_right_mono hc u hh2 (by linarith))
    rw [div_le_iff₀ hcoeff] at hinf
    linarith
  have hstep2 : ∀ ε : ℝ, 0 < ε → ε < 1 →
      0 ≤ ((v - u) * (rDeriv f u + lDeriv f v) - 2 * (f v - f u)) +
        ε * ((v - u) * (lDeriv f v - rDeriv f u)) := fun ε hε0 hε1 ↦ by
    have h1 := hstep1 (1 - ε) (by linarith) (by linarith)
    have hsec : (f v - f (v - ε * (v - u))) / (ε * (v - u)) ≤ lDeriv f v :=
      secant_le_lDeriv hc v (mul_pos hε0 (sub_pos.mpr huv))
    have hpt : u + (1 - ε) * (v - u) = v - ε * (v - u) := by ring
    rw [hpt] at h1
    have hmul : f v - f (v - ε * (v - u)) ≤ ε * (v - u) * lDeriv f v := by
      have := mul_le_mul_of_nonneg_left hsec (mul_pos hε0 (sub_pos.mpr huv)).le
      rwa [mul_div_cancel₀ _ (mul_pos hε0 (sub_pos.mpr huv)).ne'] at this
    have h1' : 0 ≤ (1 - ε) * ε * (v - u) * rDeriv f u + 2 * ε * (f u - f v) +
        (1 + ε) * (f v - f (v - ε * (v - u))) := by linarith
    have h2 : 0 ≤ (1 - ε) * ε * (v - u) * rDeriv f u + 2 * ε * (f u - f v) +
        (1 + ε) * (ε * (v - u) * lDeriv f v) := by nlinarith
    have hfac :
        (1 - ε) * ε * (v - u) * rDeriv f u + 2 * ε * (f u - f v) +
          (1 + ε) * (ε * (v - u) * lDeriv f v) =
        ε * (((v - u) * (rDeriv f u + lDeriv f v) - 2 * (f v - f u)) +
          ε * ((v - u) * (lDeriv f v - rDeriv f u))) := by ring
    rw [hfac] at h2
    exact nonneg_of_mul_nonneg_right h2 hε0
  by_contra hneg
  push Not at hneg
  set A : ℝ := (v - u) * (rDeriv f u + lDeriv f v) - 2 * (f v - f u)
  set B : ℝ := (v - u) * (lDeriv f v - rDeriv f u)
  have hA : A < 0 := by dsimp [A]; linarith
  have hB : 0 ≤ B := mul_nonneg (sub_pos.mpr huv).le (sub_nonneg.mpr (rDeriv_le_lDeriv_of_lt hc huv))
  let ε : ℝ := min (1 / 2) (-A / (2 * (B + 1)))
  have hε0 : 0 < ε := lt_min (by norm_num) (div_pos (by linarith) (by linarith))
  have hε1 : ε < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hεB : ε * B ≤ -A / 2 := by
    have hle : ε ≤ -A / (2 * (B + 1)) := min_le_right _ _
    have h1 : ε * B ≤ (-A / (2 * (B + 1))) * B := mul_le_mul_of_nonneg_right hle hB
    have h2 : (-A / (2 * (B + 1))) * B ≤ -A / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    exact h1.trans h2
  linarith [hstep2 ε hε0 hε1]

lemma trapezoid_eq {f : ℝ → ℝ} (hf : FiniteGap f) {u v : ℝ} (huv : u < v) :
    2 * (f v - f u) = (v - u) * (rDeriv f u + lDeriv f v) := by
  refine le_antisymm (trapezoid_ge hf huv) ?_
  have hrev := trapezoid_ge (finiteGap_comp_neg hf) (neg_lt_neg huv)
  rw [rDeriv_comp_neg, lDeriv_comp_neg] at hrev
  simp only [neg_neg] at hrev
  linarith

lemma rDeriv_eq_lDeriv {f : ℝ → ℝ} (hf : FiniteGap f) (v : ℝ) : rDeriv f v = lDeriv f v := by
  have hc := finiteGap_convex hf
  refine le_antisymm ?_ (lDeriv_le_rDeriv hc v)
  by_contra hlt
  push Not at hlt
  set δ : ℝ := rDeriv f v - lDeriv f v
  have hδ : 0 < δ := sub_pos.mpr hlt
  have hex : ∃ t : ℝ, 0 < t ∧ (f (v + t) - f v) / t < rDeriv f v + δ / 2 := by
    have hne : ((fun h : ℝ ↦ (f (v + h) - f v) / h) '' Set.Ioi 0).Nonempty :=
      ⟨_, ⟨1, Set.mem_Ioi.mpr one_pos, rfl⟩⟩
    obtain ⟨_, ⟨t, ht, rfl⟩, hlt'⟩ :=
      exists_lt_of_csInf_lt hne (show rDeriv f v < rDeriv f v + δ / 2 by linarith)
    exact ⟨t, ht, hlt'⟩
  rcases hex with ⟨t, ht, hsec⟩
  have ht_eq := trapezoid_eq hf (show v < v + t by linarith)
  have hLt : lDeriv f (v + t) - rDeriv f v < δ := by
    have : t * (rDeriv f v + lDeriv f (v + t)) = 2 * (f (v + t) - f v) := by
      have : v + t - v = t := by ring
      linarith
    have hdiv : rDeriv f v + lDeriv f (v + t) = 2 * ((f (v + t) - f v) / t) := by
      field_simp [ht.ne']; linarith
    linarith
  let h : ℝ := t / 2
  have hh : 0 < h := by positivity
  have e1 := trapezoid_eq hf (show v - h < v by linarith)
  have e2 := trapezoid_eq hf (show v < v + 2 * h by linarith)
  have e3 := trapezoid_eq hf (show v - h < v + 2 * h by linarith)
  have hcomb : h * (rDeriv f v - lDeriv f v) =
      2 * h * (rDeriv f (v - h) - lDeriv f v) + h * (lDeriv f (v + 2 * h) - rDeriv f v) := by
    have h1 : v - (v - h) = h := by ring
    have h2 : v + 2 * h - v = 2 * h := by ring
    have h3 : v + 2 * h - (v - h) = 3 * h := by ring
    rw [h1] at e1; rw [h2] at e2; rw [h3] at e3
    linarith
  have hRle : rDeriv f (v - h) ≤ lDeriv f v := rDeriv_le_lDeriv_of_lt hc (by linarith)
  have h2h : v + 2 * h = v + t := by dsimp [h]; ring
  rw [h2h] at hcomb
  nlinarith

lemma finiteGap_imp_quadratic {f : ℝ → ℝ} (hf : FiniteGap f) :
    ∃ a b c : ℝ, 0 ≤ a ∧ ∀ x, f x = quadratic a b c x := by
  have hc := finiteGap_convex hf
  let d : ℝ → ℝ := rDeriv f
  have htrap : ∀ u v : ℝ, u < v → 2 * (f v - f u) = (v - u) * (d u + d v) := fun u v huv ↦ by
    dsimp [d]; rw [rDeriv_eq_lDeriv hf v]; exact trapezoid_eq hf huv
  have hcol : ∀ u v w : ℝ, u < v → v < w → (w - u) * d v = (w - v) * d u + (v - u) * d w :=
    fun u v w huv hvw ↦ by
      have e1 := htrap u v huv
      have e2 := htrap v w hvw
      have e3 := htrap u w (huv.trans hvw)
      linarith
  let a : ℝ := (d 1 - d 0) / 2
  let b : ℝ := d 0
  let c : ℝ := f 0
  have ha : 0 ≤ a := by
    dsimp [a, d]
    have := rDeriv_le_lDeriv_of_lt hc (by norm_num : (0 : ℝ) < 1)
    rw [← rDeriv_eq_lDeriv hf 1] at this
    linarith
  have hd_aff : ∀ x : ℝ, d x = 2 * a * x + b := fun x ↦ by
    by_cases h0 : x = 0
    · subst h0; dsimp [a, b]; ring
    · by_cases h1 : x = 1
      · subst h1; dsimp [a, b]; ring
      · rcases lt_or_gt_of_ne h0 with hx0 | hx0
        · have h := hcol x 0 1 hx0 (by norm_num)
          dsimp [a, b]; linarith
        · rcases lt_or_gt_of_ne h1 with hx1 | hx1
          · have h := hcol 0 x 1 hx0 hx1
            dsimp [a, b]; linarith
          · have h := hcol 0 1 x (by norm_num) hx1
            dsimp [a, b]; linarith
  refine ⟨a, b, c, ha, fun x ↦ ?_⟩
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have h := htrap x 0 hx
    rw [hd_aff x, hd_aff 0] at h
    dsimp [quadratic, c]; linarith
  · dsimp [quadratic, c]; ring
  · have h := htrap 0 x hx
    rw [hd_aff 0, hd_aff x] at h
    dsimp [quadratic, c]; linarith

lemma quartic_counterexample :
    let f := fun x : ℝ => (x - 3 / 8) ^ 4
    ConvexOn ℝ Set.univ f ∧ ConvexOn ℝ Set.univ (deriv (deriv f)) ∧ ¬ FiniteGap f := by
  intro f
  have hd1 : deriv f = fun x : ℝ ↦ 4 * (x - 3 / 8) ^ 3 := by
    ext x
    have h1 : HasDerivAt (fun t : ℝ ↦ t - 3 / 8) 1 x := (hasDerivAt_id x).sub_const _
    have h : HasDerivAt f (4 * (x - 3 / 8) ^ 3) x := by
      have hp := (hasDerivAt_pow 4 (x - 3 / 8)).comp x h1
      simpa [f, Function.comp_def, mul_one] using hp
    exact h.deriv
  have hd2 : deriv (deriv f) = fun x : ℝ ↦ 12 * (x - 3 / 8) ^ 2 := by
    rw [hd1]; ext x
    have h1 : HasDerivAt (fun t : ℝ ↦ t - 3 / 8) 1 x := (hasDerivAt_id x).sub_const _
    have h : HasDerivAt (fun t : ℝ ↦ 4 * (t - 3 / 8) ^ 3) (12 * (x - 3 / 8) ^ 2) x := by
      have hp := ((hasDerivAt_pow 3 (x - 3 / 8)).comp x h1).const_mul 4
      have heq : (4 : ℝ) * (3 * (x - 3 / 8) ^ 2) = 12 * (x - 3 / 8) ^ 2 := by ring
      simpa [Function.comp_def, mul_one, heq] using hp
    exact h.deriv
  have hd3 : deriv (deriv (deriv f)) = fun x : ℝ ↦ 24 * (x - 3 / 8) := by
    rw [hd2]; ext x
    have h1 : HasDerivAt (fun t : ℝ ↦ t - 3 / 8) 1 x := (hasDerivAt_id x).sub_const _
    have h : HasDerivAt (fun t : ℝ ↦ 12 * (t - 3 / 8) ^ 2) (24 * (x - 3 / 8)) x := by
      have hp := ((hasDerivAt_pow 2 (x - 3 / 8)).comp x h1).const_mul 12
      have heq : (12 : ℝ) * (2 * (x - 3 / 8)) = 24 * (x - 3 / 8) := by ring
      simpa [Function.comp_def, mul_one, pow_one, heq] using hp
    exact h.deriv
  have hd4 : deriv (deriv (deriv (deriv f))) = fun _ : ℝ ↦ 24 := by
    rw [hd3]; ext x
    have h1 : HasDerivAt (fun t : ℝ ↦ t - 3 / 8) 1 x := (hasDerivAt_id x).sub_const _
    have h : HasDerivAt (fun t : ℝ ↦ 24 * (t - 3 / 8)) 24 x := by
      simpa using h1.const_mul 24
    exact h.deriv
  refine ⟨?_, ?_, ?_⟩
  · refine convexOn_of_deriv2_nonneg convex_univ (by fun_prop) (by fun_prop)
      (by rw [hd1]; fun_prop) (fun x _ ↦ ?_)
    change 0 ≤ deriv (deriv f) x
    rw [hd2]; positivity
  · refine convexOn_of_deriv2_nonneg convex_univ (by rw [hd2]; fun_prop) (by rw [hd2]; fun_prop)
      (by rw [hd3]; fun_prop) (fun x _ ↦ ?_)
    change 0 ≤ deriv (deriv (deriv (deriv f))) x
    rw [hd4]; norm_num
  · intro hfg
    obtain ⟨a, b, c, _, hq⟩ := finiteGap_imp_quadratic hfg
    have h0 := hq 0; have h1 := hq 1; have h2 := hq 2; have h3 := hq 3
    dsimp [f, quadratic] at h0 h1 h2 h3
    linarith

lemma stochastic_quadratic_gap {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X Y : Ω → ℝ) (a b c : ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (hX2 : MemLp X 2 P) (hY2 : MemLp Y 2 P)
    (hmart : P[Y | MeasurableSpace.comap X (borel ℝ)] =ᵐ[P] X) :
    let z := P[X | MeasurableSpace.comap Y (borel ℝ)]
    (∫ ω, (quadratic a b c (Y ω) + quadratic a b c (z ω) - 2 * quadratic a b c (X ω)) ∂P) =
      a * ∫ ω, (Y ω - z ω) ^ 2 ∂P := by
  intro z
  have hmX : MeasurableSpace.comap X (borel ℝ) ≤ mΩ := by
    rw [← BorelSpace.measurable_eq (α := ℝ)]; exact hX.comap_le
  have hmY : MeasurableSpace.comap Y (borel ℝ) ≤ mΩ := by
    rw [← BorelSpace.measurable_eq (α := ℝ)]; exact hY.comap_le
  have hsfX : SigmaFinite (P.trim hmX) := (isFiniteMeasure_trim hmX).toSigmaFinite
  have hsfY : SigmaFinite (P.trim hmY) := (isFiniteMeasure_trim hmY).toSigmaFinite
  have hz2 : MemLp z 2 P := hX2.condExp (by norm_num)
  have hX1 : Integrable X P := hX2.integrable (by norm_num)
  have hY1 : Integrable Y P := hY2.integrable (by norm_num)
  have hz1 : Integrable z P := hz2.integrable (by norm_num)
  have hXsq : Integrable (fun ω ↦ X ω ^ 2) P :=
    (hX2.integrable_mul hX2).congr (Filter.Eventually.of_forall fun ω ↦ by simp [sq])
  have hYsq : Integrable (fun ω ↦ Y ω ^ 2) P :=
    (hY2.integrable_mul hY2).congr (Filter.Eventually.of_forall fun ω ↦ by simp [sq])
  have hzsq : Integrable (fun ω ↦ z ω ^ 2) P :=
    (hz2.integrable_mul hz2).congr (Filter.Eventually.of_forall fun ω ↦ by simp [sq])
  have hXY : Integrable (fun ω ↦ X ω * Y ω) P := hX2.integrable_mul hY2
  have hYz : Integrable (fun ω ↦ Y ω * z ω) P := hY2.integrable_mul hz2
  have hX_sm : StronglyMeasurable[MeasurableSpace.comap X (borel ℝ)] X := by
    have hmeas : @Measurable Ω ℝ (MeasurableSpace.comap X (borel ℝ)) inferInstance X := by
      rw [BorelSpace.measurable_eq (α := ℝ)]
      exact fun s hs ↦ ⟨s, hs, rfl⟩
    exact hmeas.stronglyMeasurable
  have hY_sm : StronglyMeasurable[MeasurableSpace.comap Y (borel ℝ)] Y := by
    have hmeas : @Measurable Ω ℝ (MeasurableSpace.comap Y (borel ℝ)) inferInstance Y := by
      rw [BorelSpace.measurable_eq (α := ℝ)]
      exact fun s hs ↦ ⟨s, hs, rfl⟩
    exact hmeas.stronglyMeasurable
  have hintY : ∫ ω, Y ω ∂P = ∫ ω, X ω ∂P := by
    rw [← integral_condExp hmX]; exact integral_congr_ae hmart
  have hintz : ∫ ω, z ω ∂P = ∫ ω, X ω ∂P := integral_condExp hmY
  have hintXY : ∫ ω, X ω * Y ω ∂P = ∫ ω, X ω ^ 2 ∂P := by
    have h1 : P[fun ω ↦ X ω * Y ω | MeasurableSpace.comap X (borel ℝ)] =ᵐ[P]
        fun ω ↦ X ω * P[Y | MeasurableSpace.comap X (borel ℝ)] ω :=
      condExp_mul_of_stronglyMeasurable_left hX_sm hXY hY1
    have h2 : (fun ω ↦ X ω * P[Y | MeasurableSpace.comap X (borel ℝ)] ω) =ᵐ[P] fun ω ↦ X ω ^ 2 :=
      hmart.mono fun ω hω ↦ by simp [hω, sq]
    rw [← integral_condExp hmX]
    exact integral_congr_ae (h1.trans h2)
  have hintYz : ∫ ω, Y ω * z ω ∂P = ∫ ω, X ω ^ 2 ∂P := by
    have hYX : Integrable (fun ω ↦ Y ω * X ω) P := hY2.integrable_mul hX2
    have h1 : P[fun ω ↦ Y ω * X ω | MeasurableSpace.comap Y (borel ℝ)] =ᵐ[P] fun ω ↦ Y ω * z ω :=
      condExp_mul_of_stronglyMeasurable_left hY_sm hYX hX1
    calc
      ∫ ω, Y ω * z ω ∂P = ∫ ω, P[fun ω ↦ Y ω * X ω | MeasurableSpace.comap Y (borel ℝ)] ω ∂P :=
        (integral_congr_ae h1).symm
      _ = ∫ ω, Y ω * X ω ∂P := integral_condExp hmY
      _ = ∫ ω, X ω * Y ω ∂P := integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ mul_comm _ _)
      _ = ∫ ω, X ω ^ 2 ∂P := hintXY
  have hLHS :
      (∫ ω, (quadratic a b c (Y ω) + quadratic a b c (z ω) - 2 * quadratic a b c (X ω)) ∂P) =
        a * (∫ ω, Y ω ^ 2 ∂P + ∫ ω, z ω ^ 2 ∂P - 2 * ∫ ω, X ω ^ 2 ∂P) +
          b * (∫ ω, Y ω ∂P + ∫ ω, z ω ∂P - 2 * ∫ ω, X ω ∂P) := by
    have hrewrite :
        (fun ω ↦ quadratic a b c (Y ω) + quadratic a b c (z ω) - 2 * quadratic a b c (X ω)) =
          fun ω ↦ (a * Y ω ^ 2 + a * z ω ^ 2 - (2 * a) * X ω ^ 2) +
            (b * Y ω + b * z ω - (2 * b) * X ω) := by
      ext ω; dsimp [quadratic]; ring
    have haY : Integrable (fun ω ↦ a * Y ω ^ 2) P := hYsq.const_mul a
    have haz : Integrable (fun ω ↦ a * z ω ^ 2) P := hzsq.const_mul a
    have haX : Integrable (fun ω ↦ (2 * a) * X ω ^ 2) P := hXsq.const_mul (2 * a)
    have haYz : Integrable (fun ω ↦ a * Y ω ^ 2 + a * z ω ^ 2) P := haY.add haz
    have haAll : Integrable (fun ω ↦ a * Y ω ^ 2 + a * z ω ^ 2 - (2 * a) * X ω ^ 2) P :=
      haYz.sub haX
    have hbY : Integrable (fun ω ↦ b * Y ω) P := hY1.const_mul b
    have hbz : Integrable (fun ω ↦ b * z ω) P := hz1.const_mul b
    have hbX : Integrable (fun ω ↦ (2 * b) * X ω) P := hX1.const_mul (2 * b)
    have hbYz : Integrable (fun ω ↦ b * Y ω + b * z ω) P := hbY.add hbz
    have hbAll : Integrable (fun ω ↦ b * Y ω + b * z ω - (2 * b) * X ω) P := hbYz.sub hbX
    rw [hrewrite, integral_add haAll hbAll, integral_sub haYz haX, integral_add haY haz,
      integral_sub hbYz hbX, integral_add hbY hbz,
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_const_mul, integral_const_mul]
    ring
  have hRHS :
      a * ∫ ω, (Y ω - z ω) ^ 2 ∂P =
        a * (∫ ω, Y ω ^ 2 ∂P + ∫ ω, z ω ^ 2 ∂P - 2 * ∫ ω, Y ω * z ω ∂P) := by
    have hrewrite : (fun ω ↦ (Y ω - z ω) ^ 2) = fun ω ↦ Y ω ^ 2 + z ω ^ 2 - 2 * (Y ω * z ω) := by
      ext ω; ring
    have hYz2 : Integrable (fun ω ↦ Y ω ^ 2 + z ω ^ 2) P := hYsq.add hzsq
    have h2Yz : Integrable (fun ω ↦ 2 * (Y ω * z ω)) P := hYz.const_mul 2
    rw [hrewrite, integral_sub hYz2 h2Yz, integral_add hYsq hzsq, integral_const_mul]
  rw [hLHS, hRHS, hintY, hintz, hintYz]
  ring

end MartingaleJensenGap

theorem OMA.solution : type_of% @OMA.S_mo_451543.main := by
  open MartingaleJensenGap in
  refine ⟨fun f _ ↦ ⟨finiteGap_imp_quadratic, fun ⟨a, b, c, ha, hq⟩ ↦ ?_⟩,
    quartic_counterexample, fun {Ω} _ P _ X Y a b c hX hY hX2 hY2 hmart ↦
      stochastic_quadratic_gap P X Y a b c hX hY hX2 hY2 hmart⟩
  have hf : f = quadratic a b c := funext hq
  rw [hf]
  exact finiteGap_quadratic ha
