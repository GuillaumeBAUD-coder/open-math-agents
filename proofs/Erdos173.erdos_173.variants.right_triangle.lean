import FormalConjectures.ErdosProblems.«173»
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle

/-!
Shader's theorem on monochromatic right triangles. The odd-scale obstruction
follows Shader (1976), and the triangle configuration and ladder follow
Erdős et al., "Euclidean Ramsey Theorems III".
-/

open scoped Congruent EuclideanGeometry
open Affine

private def sameColor (a b d : Fin 2) : Prop := a = b ∧ a = d

private theorem equal_off_color {a b d : Fin 2} (hb : b ≠ a) (hd : d ≠ a) : b = d := by
  fin_cases a <;> fin_cases b <;> fin_cases d <;>
    first | rfl | exact (hb rfl).elim | exact (hd rfl).elim

private theorem transferColors (h b a c d e f g : Fin 2) :
    (sameColor h b a →
      sameColor h b c ∨ sameColor a b d ∨ sameColor e d c ∨
      sameColor e f h ∨ sameColor d f g ∨ sameColor a h g) ∧
    (sameColor h b c →
      sameColor h b a ∨ sameColor b c d ∨ sameColor h c e ∨
      sameColor d e f ∨ sameColor a d g ∨ sameColor f g h) := by
  constructor
  · intro hs
    by_contra hno
    push Not at hno
    obtain ⟨n₁, n₂, n₃, n₄, n₅, n₆⟩ := hno
    have hc : c ≠ h := fun he => n₁ ⟨hs.1, he.symm⟩
    have hd : d ≠ h := fun he => n₂ ⟨hs.2.symm.trans hs.1, hs.2.symm.trans he.symm⟩
    have hg : g ≠ h := fun he => n₆ ⟨hs.2.symm, hs.2.symm.trans he.symm⟩
    have he : e = h := by
      by_contra he
      exact n₃ ⟨equal_off_color he hd, equal_off_color he hc⟩
    have hf : f = h := by
      by_contra hf
      exact n₅ ⟨equal_off_color hd hf, equal_off_color hd hg⟩
    exact n₄ ⟨he.trans hf.symm, he⟩
  · intro hs
    by_contra hno
    push Not at hno
    obtain ⟨n₁, n₂, n₃, n₄, n₅, n₆⟩ := hno
    have ha : a ≠ h := fun he => n₁ ⟨hs.1, he.symm⟩
    have hd : d ≠ h := fun he => n₂ ⟨hs.1.symm.trans hs.2, hs.1.symm.trans he.symm⟩
    have he : e ≠ h := fun he => n₃ ⟨hs.2, he.symm⟩
    have hf : f = h := by
      by_contra hf
      exact n₄ ⟨equal_off_color hd he, equal_off_color hd hf⟩
    have hg : g = h := by
      by_contra hg
      exact n₅ ⟨equal_off_color ha hd, equal_off_color ha hg⟩
    exact n₆ ⟨hf.trans hg.symm, hf⟩

private def monoShape (col : ℂ → Fin 2) (a b d : ℝ) : Prop :=
  ∃ x y z : ℂ, ‖y - x‖ = a ∧ ‖z - y‖ = b ∧ ‖z - x‖ = d ∧
    sameColor (col x) (col y) (col z)

private theorem transferConfiguration (col : ℂ → Fin 2) (p u v q : ℂ)
    (hq : ‖q‖ = 1) (hr : ‖1 - q‖ = 1) :
    (sameColor (col p) (col (p + u)) (col (p + q * u)) →
      monoShape col ‖u‖ ‖v - u‖ ‖v‖) ∧
    (sameColor (col p) (col (p + u)) (col (p + v)) →
      monoShape col ‖u‖ ‖u‖ ‖u‖ ∨
      monoShape col ‖v - u‖ ‖v - u‖ ‖v - u‖ ∨ monoShape col ‖v‖ ‖v‖ ‖v‖) := by
  -- The eight points are the configuration from Euclidean Ramsey Theorems III, Figure 1.
  let a := p + q * u
  let b := p + u
  let c := p + v
  let d := p + q * u + (1 - q) * v
  let e := p + (1 - q) * v
  let f := p + (1 - q) * (v - u)
  let g := p + q * (u - v)
  have hpb : ‖b - p‖ = ‖u‖ := by simp [b]
  have hpc : ‖c - p‖ = ‖v‖ := by simp [c]
  have hbc : ‖c - b‖ = ‖v - u‖ := by rw [show c - b = v - u by dsimp [c, b]; ring]
  have hab : ‖b - a‖ = ‖u‖ := by
    rw [show b - a = (1 - q) * u by dsimp [a, b]; ring, norm_mul, hr, one_mul]
  have hbd : ‖d - b‖ = ‖v - u‖ := by
    rw [show d - b = (1 - q) * (v - u) by dsimp [b, d]; ring, norm_mul, hr, one_mul]
  have had : ‖d - a‖ = ‖v‖ := by
    rw [show d - a = (1 - q) * v by dsimp [a, d]; ring, norm_mul, hr, one_mul]
  have hdc : ‖c - d‖ = ‖v - u‖ := by
    rw [show c - d = q * (v - u) by dsimp [c, d]; ring, norm_mul, hq, one_mul]
  have hed : ‖d - e‖ = ‖u‖ := by
    rw [show d - e = q * u by dsimp [d, e]; ring, norm_mul, hq, one_mul]
  have hec : ‖c - e‖ = ‖v‖ := by
    rw [show c - e = q * v by dsimp [c, e]; ring, norm_mul, hq, one_mul]
  have hef : ‖f - e‖ = ‖u‖ := by
    rw [show f - e = -((1 - q) * u) by dsimp [f, e]; ring, norm_neg, norm_mul, hr, one_mul]
  have hpf : ‖f - p‖ = ‖v - u‖ := by simp [f, hr]
  have hpe : ‖e - p‖ = ‖v‖ := by simp [e, hr]
  have hdf : ‖f - d‖ = ‖u‖ := by
    rw [show f - d = -u by dsimp [f, d]; ring, norm_neg]
  have hfg : ‖g - f‖ = ‖v - u‖ := by
    rw [show g - f = u - v by dsimp [g, f]; ring, norm_sub_rev]
  have hdg : ‖g - d‖ = ‖v‖ := by
    rw [show g - d = -v by dsimp [g, d]; ring, norm_neg]
  have hpa : ‖a - p‖ = ‖u‖ := by simp [a, hq]
  have hpg : ‖g - p‖ = ‖v - u‖ := by simp [g, hq, norm_sub_rev u v]
  have hag : ‖g - a‖ = ‖v‖ := by
    rw [show g - a = -(q * v) by dsimp [g, a]; ring, norm_neg, norm_mul, hq, one_mul]
  have flip (x y : ℂ) (s : ℝ) (h : ‖y - x‖ = s) : ‖x - y‖ = s :=
    (norm_sub_rev _ _).trans h
  have hcTransfer := transferColors (col p) (col b) (col a) (col c)
    (col d) (col e) (col f) (col g)
  constructor
  · intro h
    rcases hcTransfer.1 h with h | h | h | h | h | h
    · exact ⟨p, b, c, hpb, hbc, hpc, h⟩
    · exact ⟨a, b, d, hab, hbd, had, h⟩
    · exact ⟨e, d, c, hed, hdc, hec, h⟩
    · exact ⟨e, f, p, hef, flip _ _ _ hpf, flip _ _ _ hpe, h⟩
    · exact ⟨d, f, g, hdf, hfg, hdg, h⟩
    · exact ⟨a, p, g, flip _ _ _ hpa, hpg, hag, h⟩
  · intro h
    rcases hcTransfer.2 h with h | h | h | h | h | h
    · exact Or.inl ⟨p, b, a, hpb, flip _ _ _ hab, hpa, h⟩
    · exact Or.inr (Or.inl ⟨b, c, d, hbc, flip _ _ _ hdc, hbd, h⟩)
    · exact Or.inr (Or.inr ⟨p, c, e, hpc, flip _ _ _ hec, hpe, h⟩)
    · exact Or.inl ⟨d, e, f, flip _ _ _ hed, hef, hdf, h⟩
    · exact Or.inr (Or.inr ⟨a, d, g, had, hdg, hag, h⟩)
    · exact Or.inr (Or.inl ⟨f, g, p, hfg, flip _ _ _ hpg, flip _ _ _ hpf, h⟩)

private theorem two_norms_of_real_half (t k : ℝ) (hk : 0 ≤ k)
    (ht : 1 / 4 + t ^ 2 = k ^ 2) :
    ‖(⟨1 / 2, t⟩ : ℂ)‖ = k ∧ ‖1 - (⟨1 / 2, t⟩ : ℂ)‖ = k := by
  constructor <;> apply (sq_eq_sq₀ (norm_nonneg _) hk).mp <;>
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] <;>
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im] <;>
    nlinarith

private noncomputable def equilateralRoot : ℂ := ⟨1 / 2, Real.sqrt 3 / 2⟩

private theorem equilateralRoot_norms :
    ‖equilateralRoot‖ = 1 ∧ ‖1 - equilateralRoot‖ = 1 := by
  apply two_norms_of_real_half _ _ zero_le_one
  nlinarith [Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]

private theorem equilateral_of_shape {col : ℂ → Fin 2} {a b d : ℝ}
    (h : monoShape col a b d) :
    monoShape col a a a ∨ monoShape col b b b ∨ monoShape col d d d := by
  obtain ⟨x, y, z, hxy, hyz, hxz, hm⟩ := h
  have hd : z - x - (y - x) = z - y := by ring
  have h := (transferConfiguration col x (y - x) (z - x) equilateralRoot
    equilateralRoot_norms.1 equilateralRoot_norms.2).2
  simpa only [hd, hxy, hyz, hxz, add_sub_cancel_left] using h (by simpa using hm)

private theorem ratio_of_equilateral {u v : ℂ} (hu : ‖u‖ ≠ 0)
    (hv : ‖v‖ = ‖u‖) (hvu : ‖v - u‖ = ‖u‖) :
    ‖v / u‖ = 1 ∧ ‖1 - v / u‖ = 1 ∧ v / u * u = v := by
  have hne : u ≠ 0 := norm_ne_zero_iff.mp hu
  refine ⟨by rw [norm_div, hv, div_self hu], ?_, div_mul_cancel₀ v hne⟩
  rw [show 1 - v / u = (u - v) / u by field_simp, norm_div, norm_sub_rev u v, hvu,
    div_self hu]

private def dotZero (u v : ℂ) : Prop := u.re * v.re + u.im * v.im = 0

private theorem dotZero_iff_pythagoras (u v : ℂ) :
    dotZero u v ↔ Complex.normSq (v - u) = Complex.normSq u + Complex.normSq v := by
  simp only [dotZero, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  constructor <;> intro h <;> nlinarith

private theorem dotZero_symm {u v : ℂ} (h : dotZero u v) : dotZero v u := by
  simpa [dotZero, mul_comm] using h

private theorem dotZero_real_mul_left {u v : ℂ} (h : dotZero u v) (s : ℝ) :
    dotZero ((s : ℂ) * u) v := by
  simp only [dotZero, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, add_zero] at *
  linear_combination s * h

private theorem dotZero_neg_right {u v : ℂ} (h : dotZero u v) : dotZero u (-v) := by
  simp only [dotZero, Complex.neg_re, Complex.neg_im] at *
  linear_combination -h

private theorem dotZero_I_mul (u : ℂ) : dotZero u (Complex.I * u) := by
  simp only [dotZero, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_sub, zero_add]
  ring

private def monoRight (col : ℂ → Fin 2) (a b : ℝ) : Prop :=
  ∃ p u v : ℂ, ‖u‖ = a ∧ ‖v‖ = b ∧ dotZero u v ∧
    sameColor (col p) (col (p + u)) (col (p + v))

private theorem monoRight_swap {col : ℂ → Fin 2} {a b : ℝ}
    (h : monoRight col a b) : monoRight col b a := by
  obtain ⟨p, u, v, hu, hv, huv, hc⟩ := h
  exact ⟨p, v, u, hv, hu, dotZero_symm huv, hc.2, hc.1⟩

private theorem right_of_equilateral {col : ℂ → Fin 2} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (h : monoShape col a a a) : monoRight col a b := by
  obtain ⟨x, y, z, hxy, hyz, hxz, hc⟩ := h
  let u := y - x
  let w := z - x
  let q := w / u
  let v := ((b / a : ℝ) : ℂ) * (Complex.I * u)
  have hu : ‖u‖ = a := hxy
  have hw : ‖w‖ = ‖u‖ := hxz.trans hxy.symm
  have hwu : ‖w - u‖ = ‖u‖ := by
    rw [show w - u = z - y by dsimp [w,u]; ring, hyz, hu]
  have hq := ratio_of_equilateral (u := u) (v := w) (by rw [hu]; exact ha.ne') hw hwu
  have hpx : x + u = y := by dsimp [u]; ring
  have hpz : x + q * u = z := by
    rw [show q * u = w from hq.2.2]
    dsimp [w]
    ring
  have hstart : sameColor (col x) (col (x + u)) (col (x + q * u)) := by
    rw [hpx, hpz]
    exact hc
  have hv : ‖v‖ = b := by
    dsimp [v]
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (div_pos hb ha), hu, div_mul_cancel₀ _ ha.ne']
  have huv : dotZero u v :=
    dotZero_symm (dotZero_real_mul_left (dotZero_symm (dotZero_I_mul u)) _)
  obtain ⟨p, y', z', h₁, h₂, h₃, hmono⟩ :=
    (transferConfiguration col x u v q hq.1 hq.2.1).1 hstart
  refine ⟨p, y' - p, z' - p, h₁.trans hu, h₃.trans hv, ?_, ?_⟩
  · apply (dotZero_iff_pythagoras _ _).mpr
    rw [show z' - p - (y' - p) = z' - y' by ring]
    simpa only [Complex.normSq_eq_norm_sq, h₁, h₂, h₃] using
      (dotZero_iff_pythagoras _ _).mp huv
  · simpa using hmono

private def otherColor (a : Fin 2) : Fin 2 := if a = 0 then 1 else 0

private theorem eq_otherColor_of_ne {a b : Fin 2} (h : a ≠ b) : a = otherColor b := by
  fin_cases a <;> fin_cases b <;> first | rfl | exact (h rfl).elim

private theorem otherColor_otherColor (a : Fin 2) : otherColor (otherColor a) = a := by
  fin_cases a <;> rfl

private theorem otherColor_ne (a : Fin 2) : otherColor a ≠ a := by
  fin_cases a <;> decide

private theorem ladder {col : ℂ → Fin 2} {a b : ℝ} {k : ℕ} (hk : Odd k)
    (h : ¬ monoRight col a b) : ¬ monoRight col (k * a) b := by
  rintro ⟨p, U, v, hU, hv, hUv, hm⟩
  have hkPos : 0 < k := by obtain ⟨j, hj⟩ := hk; omega
  have hkReal : (k : ℝ) ≠ 0 := by exact_mod_cast hkPos.ne'
  have hkComplex : (k : ℂ) ≠ 0 := by exact_mod_cast hkPos.ne'
  let u : ℂ := ((k : ℝ)⁻¹ : ℝ) * U
  have hu : ‖u‖ = a := by
    dsimp [u]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), hU]
    field_simp
  have huv : dotZero u v := dotZero_real_mul_left hUv _
  let X (j : ℕ) := p + (j : ℂ) * u
  let Y (j : ℕ) := X j + v
  have hX (j : ℕ) : X (j + 1) = X j + u := by
    dsimp [X]
    push_cast
    ring
  have hY (j : ℕ) : Y (j + 1) = Y j + u := by
    rw [show Y (j + 1) = X (j + 1) + v from rfl, hX j]
    dsimp [Y]
    ring
  have hstep (j : ℕ) (hj : col (X j) = col (Y j)) :
      col (X (j + 1)) = otherColor (col (X j)) ∧
      col (Y (j + 1)) = otherColor (col (X j)) := by
    constructor
    · apply eq_otherColor_of_ne
      intro heq
      apply h
      refine ⟨X j, u, v, hu, hv, huv, ?_⟩
      rw [← hX j]
      exact ⟨heq.symm, hj⟩
    · apply eq_otherColor_of_ne
      intro heq
      apply h
      refine ⟨Y j, u, -v, hu, by simpa using hv, dotZero_neg_right huv, ?_⟩
      rw [← hY j, show Y j + -v = X j by simp [Y]]
      exact ⟨hj.symm.trans heq.symm, hj.symm⟩
  have hrows (j : ℕ) :
      col (X j) = col (Y j) ∧ col (X j) =
        if j % 2 = 0 then col p else otherColor (col p) := by
    induction j with
    | zero =>
      constructor
      · simpa [X, Y] using hm.2
      · simp [X]
    | succ j ih =>
      obtain ⟨hx, hy⟩ := hstep j ih.1
      refine ⟨hx.trans hy.symm, ?_⟩
      rw [hx, ih.2]
      by_cases hj : j % 2 = 0
      · have hjs : (j + 1) % 2 ≠ 0 := by omega
        simp [hj, hjs]
      · have hjs : (j + 1) % 2 = 0 := by omega
        simp [hj, hjs, otherColor_otherColor]
  have hParity : k % 2 ≠ 0 := by obtain ⟨j, hj⟩ := hk; omega
  have hEnd : X k = p + U := by
    dsimp [X, u]
    push_cast
    field_simp
  have hfinal := (hrows k).2
  rw [hEnd, if_neg hParity, ← hm.1] at hfinal
  exact otherColor_ne _ hfinal.symm

private theorem no_odd_equilateral_of_no_right {col : ℂ → Fin 2} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (h : ¬ monoRight col a b)
    (k : ℕ) (hk : Odd k) : ¬ monoShape col (k * a) (k * a) (k * a) := by
  intro hm
  have hka : 0 < (k : ℝ) * a := by
    have : 0 < (k : ℝ) := by
      exact_mod_cast (show 0 < k by obtain ⟨j, hj⟩ := hk; omega)
    positivity
  have hkb : 0 < (k : ℝ) * b := by
    have : 0 < (k : ℝ) := by
      exact_mod_cast (show 0 < k by obtain ⟨j, hj⟩ := hk; omega)
    positivity
  have hfirst : ¬ monoRight col (k * a) b := ladder hk h
  have hswap : ¬ monoRight col b (k * a) := fun h => hfirst (monoRight_swap h)
  exact ladder hk hswap (monoRight_swap (right_of_equilateral hka hkb hm))

def OMA.shaderLatticeDistSq (p q : ℤ × ℤ) : ℤ :=
  (p.1 - q.1) ^ 2 + (p.1 - q.1) * (p.2 - q.2) + (p.2 - q.2) ^ 2

def OMA.shaderLatticeAllowed (a b c : ℤ × ℤ) : Prop :=
  let lengths : Multiset ℤ :=
    {OMA.shaderLatticeDistSq a b, OMA.shaderLatticeDistSq a c, OMA.shaderLatticeDistSq b c}
  lengths = {1, 1, 1} ∨ lengths = {9, 9, 9} ∨ lengths = {25, 25, 25} ∨
    lengths = {49, 49, 49} ∨ lengths = {9, 25, 49}

instance (a b c : ℤ × ℤ) : Decidable (OMA.shaderLatticeAllowed a b c) := by
  unfold OMA.shaderLatticeAllowed
  infer_instance

lemma OMA.shaderLatticeOther {a : Fin 2} (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact (h rfl).elim
  · rfl

lemma OMA.shaderLatticeForced {a b c : Fin 2} (h : ¬ (a = b ∧ a = c)) (hab : a = b) :
    c = a + 1 := by
  have hac : a ≠ c := fun e => h ⟨hab, e⟩
  fin_cases a <;> fin_cases c
  · exact (hac rfl).elim
  · decide
  · decide
  · exact (hac rfl).elim

lemma OMA.shaderLatticeNormalized (c : ℤ × ℤ → Fin 2)
    (h_0_0 : c (0, 0) = 0) (h_8_0 : c (8, 0) = 0) (h_0_8 : c (0, 8) = 1)
    (hNo : ∀ a b d, OMA.shaderLatticeAllowed a b d →
      ¬ (c a = c b ∧ c a = c d)) : False := by
  by_cases hzero : c (0, 3) = 0
  · have h_0_3 := hzero
    have h_m5_0 : c (-5, 0) = 1 := by
      have h := OMA.shaderLatticeForced (hNo (0, 0) (0, 3) (-5, 0) (by decide))
        (h_0_0.trans h_0_3.symm)
      rw [h_0_0] at h
      exact h
    have h_m5_8 : c (-5, 8) = 1 := by
      have h := OMA.shaderLatticeForced (hNo (0, 0) (0, 3) (-5, 8) (by decide))
        (h_0_0.trans h_0_3.symm)
      rw [h_0_0] at h
      exact h
    have h_m3_3 : c (-3, 3) = 1 := by
      have h := OMA.shaderLatticeForced (hNo (0, 0) (0, 3) (-3, 3) (by decide))
        (h_0_0.trans h_0_3.symm)
      rw [h_0_0] at h
      exact h
    have h_5_m5 : c (5, -5) = 1 := by
      have h := OMA.shaderLatticeForced (hNo (0, 0) (0, 3) (5, -5) (by decide))
        (h_0_0.trans h_0_3.symm)
      rw [h_0_0] at h
      exact h
    have h_m5_5 : c (-5, 5) = 0 := by
      have h := OMA.shaderLatticeForced (hNo (-5, 8) (0, 8) (-5, 5) (by decide))
        (h_m5_8.trans h_0_8.symm)
      rw [h_m5_8] at h
      exact h
    have h_3_5 : c (3, 5) = 0 := by
      have h := OMA.shaderLatticeForced (hNo (-5, 8) (0, 8) (3, 5) (by decide))
        (h_m5_8.trans h_0_8.symm)
      rw [h_m5_8] at h
      exact h
    have h_m3_8 : c (-3, 8) = 0 := by
      have h := OMA.shaderLatticeForced (hNo (-3, 3) (0, 8) (-3, 8) (by decide))
        (h_m3_3.trans h_0_8.symm)
      rw [h_m3_3] at h
      exact h
    have h_5_0 : c (5, 0) = 0 := by
      have h := OMA.shaderLatticeForced (hNo (-3, 3) (0, 8) (5, 0) (by decide))
        (h_m3_3.trans h_0_8.symm)
      rw [h_m3_3] at h
      exact h
    have h_8_m3 : c (8, -3) = 1 := by
      have h := OMA.shaderLatticeForced (hNo (3, 5) (8, 0) (8, -3) (by decide))
        (h_3_5.trans h_8_0.symm)
      rw [h_3_5] at h
      exact h
    have h_0_m3 : c (0, -3) = 1 := by
      have h := OMA.shaderLatticeForced (hNo (-5, 5) (0, 0) (0, -3) (by decide))
        (h_m5_5.trans h_0_0.symm)
      rw [h_m5_5] at h
      exact h
    by_cases hzero : c (0, 2) = 0
    · have h_0_2 := hzero
      have h_m1_3 : c (-1, 3) = 1 := by
        have h := OMA.shaderLatticeForced (hNo (0, 2) (0, 3) (-1, 3) (by decide))
          (h_0_2.trans h_0_3.symm)
        rw [h_0_2] at h
        exact h
      by_cases hzero : c (2, 3) = 0
      · have h_2_3 := hzero
        have h_2_0 : c (2, 0) = 1 := by
          have h := OMA.shaderLatticeForced (hNo (-3, 8) (2, 3) (2, 0) (by decide))
            (h_m3_8.trans h_2_3.symm)
          rw [h_m3_8] at h
          exact h
        have h_7_0 : c (7, 0) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (-1, 3) (2, 0) (7, 0) (by decide))
            (h_m1_3.trans h_2_0.symm)
          rw [h_m1_3] at h
          exact h
        have h_0_7 : c (0, 7) = 1 := by
          have h := OMA.shaderLatticeForced (hNo (0, 0) (7, 0) (0, 7) (by decide))
            (h_0_0.trans h_7_0.symm)
          rw [h_0_0] at h
          exact h
        have h_1_7 : c (1, 7) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (0, 7) (0, 8) (1, 7) (by decide))
            (h_0_7.trans h_0_8.symm)
          rw [h_0_7] at h
          exact h
        have h_1_0 : c (1, 0) = 1 := by
          have h := OMA.shaderLatticeForced (hNo (1, 7) (8, 0) (1, 0) (by decide))
            (h_1_7.trans h_8_0.symm)
          rw [h_1_7] at h
          exact h
        have h_7_1 : c (7, 1) = 1 := by
          have h := OMA.shaderLatticeForced (hNo (7, 0) (8, 0) (7, 1) (by decide))
            (h_7_0.trans h_8_0.symm)
          rw [h_7_0] at h
          exact h
        have h_1_1 : c (1, 1) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (1, 0) (2, 0) (1, 1) (by decide))
            (h_1_0.trans h_2_0.symm)
          rw [h_1_0] at h
          exact h
        have h_0_1 : c (0, 1) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (0, 8) (7, 1) (0, 1) (by decide))
            (h_0_8.trans h_7_1.symm)
          rw [h_0_8] at h
          exact h
        exact hNo (0, 1) (0, 2) (1, 1) (by decide)
          ⟨h_0_1.trans h_0_2.symm, h_0_1.trans h_1_1.symm⟩
      · have h_2_3 := OMA.shaderLatticeOther hzero
        have h_m6_6 : c (-6, 6) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (-3, 3) (2, 3) (-6, 6) (by decide))
            (h_m3_3.trans h_2_3.symm)
          rw [h_m3_3] at h
          exact h
        have h_2_6 : c (2, 6) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (-3, 3) (2, 3) (2, 6) (by decide))
            (h_m3_3.trans h_2_3.symm)
          rw [h_m3_3] at h
          exact h
        have h_m1_6 : c (-1, 6) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (-1, 3) (2, 3) (-1, 6) (by decide))
            (h_m1_3.trans h_2_3.symm)
          rw [h_m1_3] at h
          exact h
        have h_2_0 : c (2, 0) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (-1, 3) (2, 3) (2, 0) (by decide))
            (h_m1_3.trans h_2_3.symm)
          rw [h_m1_3] at h
          exact h
        have h_2_5 : c (2, 5) = 1 := by
          have h := OMA.shaderLatticeForced (hNo (2, 6) (3, 5) (2, 5) (by decide))
            (h_2_6.trans h_3_5.symm)
          rw [h_2_6] at h
          exact h
        have h_m3_5 : c (-3, 5) = 1 := by
          have h := OMA.shaderLatticeForced (hNo (2, 0) (5, 0) (-3, 5) (by decide))
            (h_2_0.trans h_5_0.symm)
          rw [h_2_0] at h
          exact h
        have h_5_m3 : c (5, -3) = 1 := by
          have h := OMA.shaderLatticeForced (hNo (2, 0) (5, 0) (5, -3) (by decide))
            (h_2_0.trans h_5_0.symm)
          rw [h_2_0] at h
          exact h
        have h_8_2 : c (8, 2) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (5, -3) (8, -3) (8, 2) (by decide))
            (h_5_m3.trans h_8_m3.symm)
          rw [h_5_m3] at h
          exact h
        have h_m1_9 : c (-1, 9) = 1 := by
          have h := OMA.shaderLatticeForced (hNo (-6, 6) (-1, 6) (-1, 9) (by decide))
            (h_m6_6.trans h_m1_6.symm)
          rw [h_m6_6] at h
          exact h
        have h_5_2 : c (5, 2) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (-3, 5) (2, 5) (5, 2) (by decide))
            (h_m3_5.trans h_2_5.symm)
          rw [h_m3_5] at h
          exact h
        have h_0_7 : c (0, 7) = 1 := by
          have h := OMA.shaderLatticeForced (hNo (5, 2) (8, 2) (0, 7) (by decide))
            (h_5_2.trans h_8_2.symm)
          rw [h_5_2] at h
          exact h
        have h_0_9 : c (0, 9) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (-1, 9) (0, 8) (0, 9) (by decide))
            (h_m1_9.trans h_0_8.symm)
          rw [h_m1_9] at h
          exact h
        have h_1_7 : c (1, 7) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (0, 7) (0, 8) (1, 7) (by decide))
            (h_0_7.trans h_0_8.symm)
          rw [h_0_7] at h
          exact h
        have h_7_2 : c (7, 2) = 1 := by
          have h := OMA.shaderLatticeForced (hNo (0, 2) (0, 9) (7, 2) (by decide))
            (h_0_2.trans h_0_9.symm)
          rw [h_0_2] at h
          exact h
        have h_1_6 : c (1, 6) = 1 := by
          have h := OMA.shaderLatticeForced (hNo (1, 7) (2, 6) (1, 6) (by decide))
            (h_1_7.trans h_2_6.symm)
          rw [h_1_7] at h
          exact h
        have h_2_7 : c (2, 7) = 1 := by
          have h := OMA.shaderLatticeForced (hNo (1, 7) (2, 6) (2, 7) (by decide))
            (h_1_7.trans h_2_6.symm)
          rw [h_1_7] at h
          exact h
        have h_m1_7 : c (-1, 7) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (2, 7) (7, 2) (-1, 7) (by decide))
            (h_2_7.trans h_7_2.symm)
          rw [h_2_7] at h
          exact h
        have h_0_6 : c (0, 6) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (0, 7) (1, 6) (0, 6) (by decide))
            (h_0_7.trans h_1_6.symm)
          rw [h_0_7] at h
          exact h
        exact hNo (-1, 6) (-1, 7) (0, 6) (by decide)
          ⟨h_m1_6.trans h_m1_7.symm, h_m1_6.trans h_0_6.symm⟩
    · have h_0_2 := OMA.shaderLatticeOther hzero
      have h_m5_2 : c (-5, 2) = 0 := by
        have h := OMA.shaderLatticeForced (hNo (0, -3) (0, 2) (-5, 2) (by decide))
          (h_0_m3.trans h_0_2.symm)
        rw [h_0_m3] at h
        exact h
      have h_m3_5 : c (-3, 5) = 0 := by
        have h := OMA.shaderLatticeForced (hNo (0, -3) (0, 2) (-3, 5) (by decide))
          (h_0_m3.trans h_0_2.symm)
        rw [h_0_m3] at h
        exact h
      have h_3_2 : c (3, 2) = 0 := by
        have h := OMA.shaderLatticeForced (hNo (0, -3) (0, 2) (3, 2) (by decide))
          (h_0_m3.trans h_0_2.symm)
        rw [h_0_m3] at h
        exact h
      have h_m2_2 : c (-2, 2) = 1 := by
        have h := OMA.shaderLatticeForced (hNo (3, 2) (3, 5) (-2, 2) (by decide))
          (h_3_2.trans h_3_5.symm)
        rw [h_3_2] at h
        exact h
      have h_5_2 : c (5, 2) = 0 := by
        have h := OMA.shaderLatticeForced (hNo (-2, 2) (5, -5) (5, 2) (by decide))
          (h_m2_2.trans h_5_m5.symm)
        rw [h_m2_2] at h
        exact h
      have h_2_0 : c (2, 0) = 1 := by
        have h := OMA.shaderLatticeForced (hNo (-3, 5) (5, 0) (2, 0) (by decide))
          (h_m3_5.trans h_5_0.symm)
        rw [h_m3_5] at h
        exact h
      have h_2_m3 : c (2, -3) = 1 := by
        have h := OMA.shaderLatticeForced (hNo (-3, 5) (5, 2) (2, -3) (by decide))
          (h_m3_5.trans h_5_2.symm)
        rw [h_m3_5] at h
        exact h
      have h_m5_7 : c (-5, 7) = 0 := by
        have h := OMA.shaderLatticeForced (hNo (-5, 0) (2, 0) (-5, 7) (by decide))
          (h_m5_0.trans h_2_0.symm)
        rw [h_m5_0] at h
        exact h
      have h_m1_0 : c (-1, 0) = 0 := by
        have h := OMA.shaderLatticeForced (hNo (2, -3) (2, 0) (-1, 0) (by decide))
          (h_2_m3.trans h_2_0.symm)
        rw [h_2_m3] at h
        exact h
      have h_m2_m1 : c (-2, -1) = 1 := by
        have h := OMA.shaderLatticeForced (hNo (-5, 2) (-5, 7) (-2, -1) (by decide))
          (h_m5_2.trans h_m5_7.symm)
        rw [h_m5_2] at h
        exact h
      have h_m1_1 : c (-1, 1) = 1 := by
        have h := OMA.shaderLatticeForced (hNo (-1, 0) (0, 0) (-1, 1) (by decide))
          (h_m1_0.trans h_0_0.symm)
        rw [h_m1_0] at h
        exact h
      have h_1_m1 : c (1, -1) = 0 := by
        have h := OMA.shaderLatticeForced (hNo (-2, -1) (-2, 2) (1, -1) (by decide))
          (h_m2_m1.trans h_m2_2.symm)
        rw [h_m2_m1] at h
        exact h
      have h_m2_1 : c (-2, 1) = 0 := by
        have h := OMA.shaderLatticeForced (hNo (-2, 2) (-1, 1) (-2, 1) (by decide))
          (h_m2_2.trans h_m1_1.symm)
        rw [h_m2_2] at h
        exact h
      have h_m1_2 : c (-1, 2) = 0 := by
        have h := OMA.shaderLatticeForced (hNo (-2, 2) (-1, 1) (-1, 2) (by decide))
          (h_m2_2.trans h_m1_1.symm)
        rw [h_m2_2] at h
        exact h
      have h_1_0 : c (1, 0) = 1 := by
        have h := OMA.shaderLatticeForced (hNo (0, 0) (1, -1) (1, 0) (by decide))
          (h_0_0.trans h_1_m1.symm)
        rw [h_0_0] at h
        exact h
      have h_m2_0 : c (-2, 0) = 1 := by
        have h := OMA.shaderLatticeForced (hNo (-2, 1) (-1, 0) (-2, 0) (by decide))
          (h_m2_1.trans h_m1_0.symm)
        rw [h_m2_1] at h
        exact h
      have h_2_m1 : c (2, -1) = 0 := by
        have h := OMA.shaderLatticeForced (hNo (1, 0) (2, 0) (2, -1) (by decide))
          (h_1_0.trans h_2_0.symm)
        rw [h_1_0] at h
        exact h
      have h_m1_m1 : c (-1, -1) = 0 := by
        have h := OMA.shaderLatticeForced (hNo (-2, -1) (-2, 0) (-1, -1) (by decide))
          (h_m2_m1.trans h_m2_0.symm)
        rw [h_m2_m1] at h
        exact h
      exact hNo (-1, -1) (-1, 2) (2, -1) (by decide)
        ⟨h_m1_m1.trans h_m1_2.symm, h_m1_m1.trans h_2_m1.symm⟩
  · have h_0_3 := OMA.shaderLatticeOther hzero
    have h_m5_8 : c (-5, 8) = 0 := by
      have h := OMA.shaderLatticeForced (hNo (0, 3) (0, 8) (-5, 8) (by decide))
        (h_0_3.trans h_0_8.symm)
      rw [h_0_3] at h
      exact h
    have h_m3_3 : c (-3, 3) = 0 := by
      have h := OMA.shaderLatticeForced (hNo (0, 3) (0, 8) (-3, 3) (by decide))
        (h_0_3.trans h_0_8.symm)
      rw [h_0_3] at h
      exact h
    have h_3_0 : c (3, 0) = 0 := by
      have h := OMA.shaderLatticeForced (hNo (0, 3) (0, 8) (3, 0) (by decide))
        (h_0_3.trans h_0_8.symm)
      rw [h_0_3] at h
      exact h
    have h_5_3 : c (5, 3) = 0 := by
      have h := OMA.shaderLatticeForced (hNo (0, 3) (0, 8) (5, 3) (by decide))
        (h_0_3.trans h_0_8.symm)
      rw [h_0_3] at h
      exact h
    have h_3_m3 : c (3, -3) = 1 := by
      have h := OMA.shaderLatticeForced (hNo (3, 0) (8, 0) (3, -3) (by decide))
        (h_3_0.trans h_8_0.symm)
      rw [h_3_0] at h
      exact h
    have h_3_5 : c (3, 5) = 1 := by
      have h := OMA.shaderLatticeForced (hNo (3, 0) (8, 0) (3, 5) (by decide))
        (h_3_0.trans h_8_0.symm)
      rw [h_3_0] at h
      exact h
    have h_8_3 : c (8, 3) = 1 := by
      have h := OMA.shaderLatticeForced (hNo (3, 0) (8, 0) (8, 3) (by decide))
        (h_3_0.trans h_8_0.symm)
      rw [h_3_0] at h
      exact h
    have h_5_0 : c (5, 0) = 1 := by
      have h := OMA.shaderLatticeForced (hNo (5, 3) (8, 0) (5, 0) (by decide))
        (h_5_3.trans h_8_0.symm)
      rw [h_5_3] at h
      exact h
    have h_m5_5 : c (-5, 5) = 1 := by
      have h := OMA.shaderLatticeForced (hNo (-5, 8) (0, 0) (-5, 5) (by decide))
        (h_m5_8.trans h_0_0.symm)
      rw [h_m5_8] at h
      exact h
    have h_m3_0 : c (-3, 0) = 1 := by
      have h := OMA.shaderLatticeForced (hNo (-3, 3) (0, 0) (-3, 0) (by decide))
        (h_m3_3.trans h_0_0.symm)
      rw [h_m3_3] at h
      exact h
    have h_m3_8 : c (-3, 8) = 1 := by
      have h := OMA.shaderLatticeForced (hNo (-3, 3) (0, 0) (-3, 8) (by decide))
        (h_m3_3.trans h_0_0.symm)
      rw [h_m3_3] at h
      exact h
    have h_0_5 : c (0, 5) = 0 := by
      have h := OMA.shaderLatticeForced (hNo (0, 8) (3, 5) (0, 5) (by decide))
        (h_0_8.trans h_3_5.symm)
      rw [h_0_8] at h
      exact h
    by_cases hzero : c (2, 0) = 0
    · have h_2_0 := hzero
      have h_2_1 : c (2, 1) = 1 := by
        have h := OMA.shaderLatticeForced (hNo (2, 0) (3, 0) (2, 1) (by decide))
          (h_2_0.trans h_3_0.symm)
        rw [h_2_0] at h
        exact h
      by_cases hzero : c (2, -2) = 0
      · have h_2_m2 := hzero
        have h_m6_3 : c (-6, 3) = 1 := by
          have h := OMA.shaderLatticeForced (hNo (-3, 3) (2, -2) (-6, 3) (by decide))
            (h_m3_3.trans h_2_m2.symm)
          rw [h_m3_3] at h
          exact h
        have h_m3_6 : c (-3, 6) = 1 := by
          have h := OMA.shaderLatticeForced (hNo (-3, 3) (2, -2) (-3, 6) (by decide))
            (h_m3_3.trans h_2_m2.symm)
          rw [h_m3_3] at h
          exact h
        have h_m6_8 : c (-6, 8) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (-6, 3) (-3, 8) (-6, 8) (by decide))
            (h_m6_3.trans h_m3_8.symm)
          rw [h_m6_3] at h
          exact h
        have h_0_6 : c (0, 6) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (-3, 6) (0, 3) (0, 6) (by decide))
            (h_m3_6.trans h_0_3.symm)
          rw [h_m3_6] at h
          exact h
        have h_m1_6 : c (-1, 6) = 1 := by
          have h := OMA.shaderLatticeForced (hNo (0, 5) (0, 6) (-1, 6) (by decide))
            (h_0_5.trans h_0_6.symm)
          rw [h_0_5] at h
          exact h
        have h_m3_9 : c (-3, 9) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (-3, 6) (2, 1) (-3, 9) (by decide))
            (h_m3_6.trans h_2_1.symm)
          rw [h_m3_6] at h
          exact h
        have h_m1_3 : c (-1, 3) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (-6, 3) (-1, 6) (-1, 3) (by decide))
            (h_m6_3.trans h_m1_6.symm)
          rw [h_m6_3] at h
          exact h
        have h_m1_8 : c (-1, 8) = 1 := by
          have h := OMA.shaderLatticeForced (hNo (-6, 8) (-1, 3) (-1, 8) (by decide))
            (h_m6_8.trans h_m1_3.symm)
          rw [h_m6_8] at h
          exact h
        have h_0_9 : c (0, 9) = 1 := by
          have h := OMA.shaderLatticeForced (hNo (-3, 9) (0, 6) (0, 9) (by decide))
            (h_m3_9.trans h_0_6.symm)
          rw [h_m3_9] at h
          exact h
        have h_0_7 : c (0, 7) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (-1, 8) (0, 8) (0, 7) (by decide))
            (h_m1_8.trans h_0_8.symm)
          rw [h_m1_8] at h
          exact h
        have h_1_8 : c (1, 8) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (0, 8) (0, 9) (1, 8) (by decide))
            (h_0_8.trans h_0_9.symm)
          rw [h_0_8] at h
          exact h
        have h_m1_7 : c (-1, 7) = 1 := by
          have h := OMA.shaderLatticeForced (hNo (0, 6) (0, 7) (-1, 7) (by decide))
            (h_0_6.trans h_0_7.symm)
          rw [h_0_6] at h
          exact h
        have h_1_6 : c (1, 6) = 1 := by
          have h := OMA.shaderLatticeForced (hNo (0, 6) (0, 7) (1, 6) (by decide))
            (h_0_6.trans h_0_7.symm)
          rw [h_0_6] at h
          exact h
        have h_1_1 : c (1, 1) = 1 := by
          have h := OMA.shaderLatticeForced (hNo (-6, 8) (1, 8) (1, 1) (by decide))
            (h_m6_8.trans h_1_8.symm)
          rw [h_m6_8] at h
          exact h
        have h_m2_8 : c (-2, 8) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (-1, 7) (-1, 8) (-2, 8) (by decide))
            (h_m1_7.trans h_m1_8.symm)
          rw [h_m1_7] at h
          exact h
        have h_m2_9 : c (-2, 9) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (1, 1) (1, 6) (-2, 9) (by decide))
            (h_1_1.trans h_1_6.symm)
          rw [h_1_1] at h
          exact h
        exact hNo (-3, 9) (-2, 8) (-2, 9) (by decide)
          ⟨h_m3_9.trans h_m2_8.symm, h_m3_9.trans h_m2_9.symm⟩
      · have h_2_m2 := OMA.shaderLatticeOther hzero
        have h_2_5 : c (2, 5) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (-5, 5) (2, -2) (2, 5) (by decide))
            (h_m5_5.trans h_2_m2.symm)
          rw [h_m5_5] at h
          exact h
        have h_m3_m2 : c (-3, -2) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (2, -2) (2, 1) (-3, -2) (by decide))
            (h_2_m2.trans h_2_1.symm)
          rw [h_2_m2] at h
          exact h
        have h_m3_6 : c (-3, 6) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (2, -2) (2, 1) (-3, 6) (by decide))
            (h_2_m2.trans h_2_1.symm)
          rw [h_2_m2] at h
          exact h
        have h_m1_1 : c (-1, 1) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (2, -2) (2, 1) (-1, 1) (by decide))
            (h_2_m2.trans h_2_1.symm)
          rw [h_2_m2] at h
          exact h
        have h_2_m3 : c (2, -3) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (2, -2) (3, -3) (2, -3) (by decide))
            (h_2_m2.trans h_3_m3.symm)
          rw [h_2_m2] at h
          exact h
        have h_5_m2 : c (5, -2) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (2, -2) (2, 1) (5, -2) (by decide))
            (h_2_m2.trans h_2_1.symm)
          rw [h_2_m2] at h
          exact h
        have h_m1_0 : c (-1, 0) = 1 := by
          have h := OMA.shaderLatticeForced (hNo (2, -3) (2, 0) (-1, 0) (by decide))
            (h_2_m3.trans h_2_0.symm)
          rw [h_2_m3] at h
          exact h
        have h_m1_8 : c (-1, 8) = 1 := by
          have h := OMA.shaderLatticeForced (hNo (2, 0) (2, 5) (-1, 8) (by decide))
            (h_2_0.trans h_2_5.symm)
          rw [h_2_0] at h
          exact h
        have h_2_6 : c (2, 6) = 1 := by
          have h := OMA.shaderLatticeForced (hNo (-3, 6) (5, 3) (2, 6) (by decide))
            (h_m3_6.trans h_5_3.symm)
          rw [h_m3_6] at h
          exact h
        have h_m6_6 : c (-6, 6) = 1 := by
          have h := OMA.shaderLatticeForced (hNo (-3, -2) (-3, 3) (-6, 6) (by decide))
            (h_m3_m2.trans h_m3_3.symm)
          rw [h_m3_m2] at h
          exact h
        have h_0_1 : c (0, 1) = 1 := by
          have h := OMA.shaderLatticeForced (hNo (-1, 1) (0, 0) (0, 1) (by decide))
            (h_m1_1.trans h_0_0.symm)
          rw [h_m1_1] at h
          exact h
        have h_0_7 : c (0, 7) = 0 := by
          have h := OMA.shaderLatticeForced (hNo (-1, 8) (0, 8) (0, 7) (by decide))
            (h_m1_8.trans h_0_8.symm)
          rw [h_m1_8] at h
          exact h
        by_cases hzero : c (3, 3) = 0
        · have h_3_3 := hzero
          have h_m2_0 : c (-2, 0) = 1 := by
            have h := OMA.shaderLatticeForced (hNo (-5, 8) (3, 3) (-2, 0) (by decide))
              (h_m5_8.trans h_3_3.symm)
            rw [h_m5_8] at h
            exact h
          have h_m2_m1 : c (-2, -1) = 0 := by
            have h := OMA.shaderLatticeForced (hNo (-3, 0) (-2, 0) (-2, -1) (by decide))
              (h_m3_0.trans h_m2_0.symm)
            rw [h_m3_0] at h
            exact h
          have h_m2_1 : c (-2, 1) = 0 := by
            have h := OMA.shaderLatticeForced (hNo (-2, 0) (-1, 0) (-2, 1) (by decide))
              (h_m2_0.trans h_m1_0.symm)
            rw [h_m2_0] at h
            exact h
          have h_m1_m1 : c (-1, -1) = 0 := by
            have h := OMA.shaderLatticeForced (hNo (-2, 0) (-1, 0) (-1, -1) (by decide))
              (h_m2_0.trans h_m1_0.symm)
            rw [h_m2_0] at h
            exact h
          have h_m2_2 : c (-2, 2) = 1 := by
            have h := OMA.shaderLatticeForced (hNo (-2, 1) (-1, 1) (-2, 2) (by decide))
              (h_m2_1.trans h_m1_1.symm)
            rw [h_m2_1] at h
            exact h
          have h_3_2 : c (3, 2) = 0 := by
            have h := OMA.shaderLatticeForced (hNo (-2, 2) (3, -3) (3, 2) (by decide))
              (h_m2_2.trans h_3_m3.symm)
            rw [h_m2_2] at h
            exact h
          have h_2_3 : c (2, 3) = 1 := by
            have h := OMA.shaderLatticeForced (hNo (3, 2) (3, 3) (2, 3) (by decide))
              (h_3_2.trans h_3_3.symm)
            rw [h_3_2] at h
            exact h
          have h_m1_m2 : c (-1, -2) = 1 := by
            have h := OMA.shaderLatticeForced (hNo (-2, -1) (-1, -1) (-1, -2) (by decide))
              (h_m2_m1.trans h_m1_m1.symm)
            rw [h_m2_m1] at h
            exact h
          exact hNo (-6, 6) (-1, -2) (2, 3) (by decide)
            ⟨h_m6_6.trans h_m1_m2.symm, h_m6_6.trans h_2_3.symm⟩
        · have h_3_3 := OMA.shaderLatticeOther hzero
          have h_0_m2 : c (0, -2) = 0 := by
            have h := OMA.shaderLatticeForced (hNo (0, 3) (3, 3) (0, -2) (by decide))
              (h_0_3.trans h_3_3.symm)
            rw [h_0_3] at h
            exact h
          have h_0_6 : c (0, 6) = 0 := by
            have h := OMA.shaderLatticeForced (hNo (0, 3) (3, 3) (0, 6) (by decide))
              (h_0_3.trans h_3_3.symm)
            rw [h_0_3] at h
            exact h
          have h_m1_6 : c (-1, 6) = 1 := by
            have h := OMA.shaderLatticeForced (hNo (0, 5) (0, 6) (-1, 6) (by decide))
              (h_0_5.trans h_0_6.symm)
            rw [h_0_5] at h
            exact h
          have h_1_6 : c (1, 6) = 1 := by
            have h := OMA.shaderLatticeForced (hNo (0, 6) (0, 7) (1, 6) (by decide))
              (h_0_6.trans h_0_7.symm)
            rw [h_0_6] at h
            exact h
          have h_m6_3 : c (-6, 3) = 0 := by
            have h := OMA.shaderLatticeForced (hNo (-1, 6) (2, -2) (-6, 3) (by decide))
              (h_m1_6.trans h_2_m2.symm)
            rw [h_m1_6] at h
            exact h
          have h_m1_3 : c (-1, 3) = 1 := by
            have h := OMA.shaderLatticeForced (hNo (-6, 3) (2, 0) (-1, 3) (by decide))
              (h_m6_3.trans h_2_0.symm)
            rw [h_m6_3] at h
            exact h
          have h_1_7 : c (1, 7) = 0 := by
            have h := OMA.shaderLatticeForced (hNo (1, 6) (2, 6) (1, 7) (by decide))
              (h_1_6.trans h_2_6.symm)
            rw [h_1_6] at h
            exact h
          have h_5_1 : c (5, 1) = 1 := by
            have h := OMA.shaderLatticeForced (hNo (0, -2) (5, -2) (5, 1) (by decide))
              (h_0_m2.trans h_5_m2.symm)
            rw [h_0_m2] at h
            exact h
          have h_4_1 : c (4, 1) = 0 := by
            have h := OMA.shaderLatticeForced (hNo (5, 0) (5, 1) (4, 1) (by decide))
              (h_5_0.trans h_5_1.symm)
            rw [h_5_0] at h
            exact h
          have h_1_0 : c (1, 0) = 1 := by
            have h := OMA.shaderLatticeForced (hNo (1, 7) (8, 0) (1, 0) (by decide))
              (h_1_7.trans h_8_0.symm)
            rw [h_1_7] at h
            exact h
          have h_m4_6 : c (-4, 6) = 0 := by
            have h := OMA.shaderLatticeForced (hNo (-1, 3) (-1, 6) (-4, 6) (by decide))
              (h_m1_3.trans h_m1_6.symm)
            rw [h_m1_3] at h
            exact h
          have h_1_1 : c (1, 1) = 1 := by
            have h := OMA.shaderLatticeForced (hNo (-4, 6) (4, 1) (1, 1) (by decide))
              (h_m4_6.trans h_4_1.symm)
            rw [h_m4_6] at h
            exact h
          exact hNo (0, 1) (1, 0) (1, 1) (by decide)
            ⟨h_0_1.trans h_1_0.symm, h_0_1.trans h_1_1.symm⟩
    · have h_2_0 := OMA.shaderLatticeOther hzero
      have h_m6_3 : c (-6, 3) = 0 := by
        have h := OMA.shaderLatticeForced (hNo (-3, 0) (2, 0) (-6, 3) (by decide))
          (h_m3_0.trans h_2_0.symm)
        rw [h_m3_0] at h
        exact h
      have h_m3_m3 : c (-3, -3) = 0 := by
        have h := OMA.shaderLatticeForced (hNo (-3, 0) (2, 0) (-3, -3) (by decide))
          (h_m3_0.trans h_2_0.symm)
        rw [h_m3_0] at h
        exact h
      have h_m3_5 : c (-3, 5) = 0 := by
        have h := OMA.shaderLatticeForced (hNo (-3, 0) (2, 0) (-3, 5) (by decide))
          (h_m3_0.trans h_2_0.symm)
        rw [h_m3_0] at h
        exact h
      have h_2_3 : c (2, 3) = 0 := by
        have h := OMA.shaderLatticeForced (hNo (-3, 0) (2, 0) (2, 3) (by decide))
          (h_m3_0.trans h_2_0.symm)
        rw [h_m3_0] at h
        exact h
      have h_5_m3 : c (5, -3) = 0 := by
        have h := OMA.shaderLatticeForced (hNo (-3, 0) (2, 0) (5, -3) (by decide))
          (h_m3_0.trans h_2_0.symm)
        rw [h_m3_0] at h
        exact h
      have h_m6_6 : c (-6, 6) = 1 := by
        have h := OMA.shaderLatticeForced (hNo (-6, 3) (-3, 3) (-6, 6) (by decide))
          (h_m6_3.trans h_m3_3.symm)
        rw [h_m6_3] at h
        exact h
      have h_2_m2 : c (2, -2) = 1 := by
        have h := OMA.shaderLatticeForced (hNo (-6, 3) (-3, 3) (2, -2) (by decide))
          (h_m6_3.trans h_m3_3.symm)
        rw [h_m6_3] at h
        exact h
      have h_0_2 : c (0, 2) = 1 := by
        have h := OMA.shaderLatticeForced (hNo (-3, 5) (0, 5) (0, 2) (by decide))
          (h_m3_5.trans h_0_5.symm)
        rw [h_m3_5] at h
        exact h
      have h_8_2 : c (8, 2) = 1 := by
        have h := OMA.shaderLatticeForced (hNo (0, 5) (5, -3) (8, 2) (by decide))
          (h_0_5.trans h_5_m3.symm)
        rw [h_0_5] at h
        exact h
      have h_2_m3 : c (2, -3) = 0 := by
        have h := OMA.shaderLatticeForced (hNo (2, -2) (3, -3) (2, -3) (by decide))
          (h_2_m2.trans h_3_m3.symm)
        rw [h_2_m2] at h
        exact h
      have h_7_3 : c (7, 3) = 0 := by
        have h := OMA.shaderLatticeForced (hNo (8, 2) (8, 3) (7, 3) (by decide))
          (h_8_2.trans h_8_3.symm)
        rw [h_8_2] at h
        exact h
      have h_m3_2 : c (-3, 2) = 1 := by
        have h := OMA.shaderLatticeForced (hNo (-3, -3) (2, -3) (-3, 2) (by decide))
          (h_m3_m3.trans h_2_m3.symm)
        rw [h_m3_m3] at h
        exact h
      have h_m1_6 : c (-1, 6) = 1 := by
        have h := OMA.shaderLatticeForced (hNo (2, 3) (7, 3) (-1, 6) (by decide))
          (h_2_3.trans h_7_3.symm)
        rw [h_2_3] at h
        exact h
      have h_m1_1 : c (-1, 1) = 0 := by
        have h := OMA.shaderLatticeForced (hNo (-6, 6) (-1, 6) (-1, 1) (by decide))
          (h_m6_6.trans h_m1_6.symm)
        rw [h_m6_6] at h
        exact h
      have h_0_m1 : c (0, -1) = 0 := by
        have h := OMA.shaderLatticeForced (hNo (-3, 2) (0, 2) (0, -1) (by decide))
          (h_m3_2.trans h_0_2.symm)
        rw [h_m3_2] at h
        exact h
      have h_m1_3 : c (-1, 3) = 0 := by
        have h := OMA.shaderLatticeForced (hNo (0, 2) (0, 3) (-1, 3) (by decide))
          (h_0_2.trans h_0_3.symm)
        rw [h_0_2] at h
        exact h
      have h_0_1 : c (0, 1) = 1 := by
        have h := OMA.shaderLatticeForced (hNo (-1, 1) (0, 0) (0, 1) (by decide))
          (h_m1_1.trans h_0_0.symm)
        rw [h_m1_1] at h
        exact h
      have h_1_m1 : c (1, -1) = 1 := by
        have h := OMA.shaderLatticeForced (hNo (0, -1) (0, 0) (1, -1) (by decide))
          (h_0_m1.trans h_0_0.symm)
        rw [h_0_m1] at h
        exact h
      have h_m1_m2 : c (-1, -2) = 1 := by
        have h := OMA.shaderLatticeForced (hNo (-6, 3) (-1, 3) (-1, -2) (by decide))
          (h_m6_3.trans h_m1_3.symm)
        rw [h_m6_3] at h
        exact h
      have h_m1_2 : c (-1, 2) = 0 := by
        have h := OMA.shaderLatticeForced (hNo (0, 1) (0, 2) (-1, 2) (by decide))
          (h_0_1.trans h_0_2.symm)
        rw [h_0_1] at h
        exact h
      have h_m6_m1 : c (-6, -1) = 0 := by
        have h := OMA.shaderLatticeForced (hNo (-6, 6) (1, -1) (-6, -1) (by decide))
          (h_m6_6.trans h_1_m1.symm)
        rw [h_m6_6] at h
        exact h
      have h_1_m2 : c (1, -2) = 0 := by
        have h := OMA.shaderLatticeForced (hNo (1, -1) (2, -2) (1, -2) (by decide))
          (h_1_m1.trans h_2_m2.symm)
        rw [h_1_m1] at h
        exact h
      have h_m1_m1 : c (-1, -1) = 1 := by
        have h := OMA.shaderLatticeForced (hNo (-6, -1) (-1, 2) (-1, -1) (by decide))
          (h_m6_m1.trans h_m1_2.symm)
        rw [h_m6_m1] at h
        exact h
      have h_0_m2 : c (0, -2) = 1 := by
        have h := OMA.shaderLatticeForced (hNo (0, -1) (1, -2) (0, -2) (by decide))
          (h_0_m1.trans h_1_m2.symm)
        rw [h_0_m1] at h
        exact h
      exact hNo (-1, -2) (-1, -1) (0, -2) (by decide)
        ⟨h_m1_m2.trans h_m1_m1.symm, h_m1_m2.trans h_0_m2.symm⟩

theorem OMA.shaderLatticeCertificate (c : ℤ × ℤ → Fin 2)
    (hEq : c (0, 0) = c (8, 0)) (hNe : c (0, 0) ≠ c (0, 8))
    (hNo : ∀ a b d, OMA.shaderLatticeAllowed a b d →
      ¬ (c a = c b ∧ c a = c d)) : False := by
  let e := Equiv.swap (c (0, 0)) (0 : Fin 2)
  have h0 : e (c (0, 0)) = 0 := Equiv.swap_apply_left _ _
  have h8 : e (c (8, 0)) = 0 := hEq ▸ h0
  have h1 : e (c (0, 8)) = 1 := by
    apply OMA.shaderLatticeOther
    intro he
    exact hNe (e.injective (h0.trans he.symm))
  apply OMA.shaderLatticeNormalized (fun p => e (c p)) h0 h8 h1
  intro a b d ha hc
  exact hNo a b d ha ⟨e.injective hc.1, e.injective hc.2⟩

private theorem reorder_mixed_three (a b d : Fin 2) (h : ¬ sameColor a b d) :
    (a = b ∧ a ≠ d) ∨ (b = d ∧ b ≠ a) ∨ (d = a ∧ d ≠ b) := by
  fin_cases a <;> fin_cases b <;> fin_cases d <;>
    first
    | exact (h ⟨rfl, rfl⟩).elim
    | exact Or.inl ⟨rfl, by decide⟩
    | exact Or.inr (Or.inl ⟨rfl, by decide⟩)
    | exact Or.inr (Or.inr ⟨rfl, by decide⟩)

private theorem mixed_equilateral_eight (col : ℂ → Fin 2)
    (hunit : ¬ monoShape col 1 1 1) :
    ∃ x y z : ℂ, ‖y - x‖ = 8 ∧ ‖z - y‖ = 8 ∧ ‖z - x‖ = 8 ∧
      col x = col y ∧ col x ≠ col z := by
  have hex : ∃ x y z : ℂ, ‖y - x‖ = 8 ∧ ‖z - y‖ = 8 ∧ ‖z - x‖ = 8 ∧
      ¬ sameColor (col x) (col y) (col z) := by
    by_contra h
    -- If all side-eight equilateral triangles are monochromatic, length-eight
    -- steps preserve color. Two such steps realize any length-one displacement.
    have hstep (p u : ℂ) (hu : ‖u‖ = 8) : col p = col (p + u) := by
      let q := equilateralRoot
      have hs : sameColor (col p) (col (p + u)) (col (p + q * u)) := by
        by_contra hcolor
        apply h
        refine ⟨p, p + u, p + q * u, by simpa, ?_, ?_, hcolor⟩
        · rw [show p + q * u - (p + u) = -((1 - q) * u) by ring, norm_neg,
            norm_mul, equilateralRoot_norms.2, one_mul, hu]
        · rw [show p + q * u - p = q * u by ring, norm_mul,
            equilateralRoot_norms.1, one_mul, hu]
      exact hs.1
    let m : ℂ := ⟨1 / 2, Real.sqrt 255 / 2⟩
    have hm : ‖m‖ = 8 ∧ ‖1 - m‖ = 8 := by
      apply two_norms_of_real_half _ _ (by norm_num)
      nlinarith [Real.sq_sqrt (show 0 ≤ (255 : ℝ) by norm_num)]
    have hclose (u : ℂ) (hu : ‖u‖ = 1) : col 0 = col u := by
      have h₁ := hstep 0 (m * u) (by rw [norm_mul, hm.1, hu, mul_one])
      have h₂ := hstep (m * u) ((1 - m) * u) (by rw [norm_mul, hm.2, hu, mul_one])
      rw [zero_add] at h₁
      rw [show m * u + (1 - m) * u = u by ring] at h₂
      exact h₁.trans h₂
    apply hunit
    refine ⟨0, 1, equilateralRoot, by simp, ?_, ?_, ?_⟩
    · exact (norm_sub_rev _ _).trans equilateralRoot_norms.2
    · simpa only [sub_zero] using equilateralRoot_norms.1
    · exact ⟨hclose 1 (by simp), hclose _ equilateralRoot_norms.1⟩
  obtain ⟨x, y, z, hxy, hyz, hxz, hcol⟩ := hex
  rcases reorder_mixed_three _ _ _ hcol with h | h | h
  · exact ⟨x, y, z, hxy, hyz, hxz, h⟩
  · exact ⟨y, z, x, hyz, (norm_sub_rev _ _).trans hxz, (norm_sub_rev _ _).trans hxy, h⟩
  · exact ⟨z, x, y, (norm_sub_rev _ _).trans hxz, hxy, (norm_sub_rev _ _).trans hyz, h⟩

private theorem normSq_lattice_coordinates {q : ℂ} (hq : ‖q‖ = 1) (hr : ‖1 - q‖ = 1)
    (i j : ℤ) : Complex.normSq ((i : ℂ) + (j : ℂ) * q) = (i ^ 2 + i * j + j ^ 2 : ℤ) := by
  have h₁ : Complex.normSq q = 1 := by rw [Complex.normSq_eq_norm_sq, hq, one_pow]
  have h₂ : Complex.normSq (1 - q) = 1 := by rw [Complex.normSq_eq_norm_sq, hr, one_pow]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im] at h₁ h₂
  have hre : q.re = 1 / 2 := by nlinarith
  have him : q.im * q.im = 3 / 4 := by rw [hre] at h₁; nlinarith
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.intCast_re, Complex.intCast_im,
    Complex.mul_re, Complex.mul_im, zero_mul, sub_zero, add_zero, zero_add, hre]
  push_cast
  linear_combination ((j : ℝ) ^ 2) * him

private noncomputable def latticePoint (p u q : ℂ) (x : ℤ × ℤ) :=
  p + ((x.1 : ℂ) + (x.2 : ℂ) * q) * u

private theorem latticePoint_distSq {p u q : ℂ} (hu : ‖u‖ = 1)
    (hq : ‖q‖ = 1) (hr : ‖1 - q‖ = 1) (x y : ℤ × ℤ) :
    Complex.normSq (latticePoint p u q y - latticePoint p u q x) =
      (OMA.shaderLatticeDistSq x y : ℝ) := by
  rw [show latticePoint p u q y - latticePoint p u q x =
    -(((↑(x.1 - y.1) : ℂ) + (↑(x.2 - y.2) : ℂ) * q) * u) by
      dsimp [latticePoint]; push_cast; ring]
  rw [Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_eq_norm_sq u, hu, one_pow, mul_one]
  exact normSq_lattice_coordinates hq hr _ _

private theorem lattice_norm_is_odd (w : ℂ) (s : ℤ) (hw : Complex.normSq w = s)
    (hs : s = 1 ∨ s = 9 ∨ s = 25 ∨ s = 49) : ∃ k : ℕ, Odd k ∧ ‖w‖ = k := by
  have hnorm (k : ℕ) (hk : s = (k : ℤ) ^ 2) : ‖w‖ = k := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [← Complex.normSq_eq_norm_sq, hw, hk]
    push_cast
    rfl
  rcases hs with hs | hs | hs | hs
  · exact ⟨1, ⟨0, rfl⟩, hnorm 1 (by norm_num [hs])⟩
  · exact ⟨3, ⟨1, rfl⟩, hnorm 3 (by norm_num [hs])⟩
  · exact ⟨5, ⟨2, rfl⟩, hnorm 5 (by norm_num [hs])⟩
  · exact ⟨7, ⟨3, rfl⟩, hnorm 7 (by norm_num [hs])⟩

private theorem odd_equilateral (col : ℂ → Fin 2) :
    ∃ k : ℕ, Odd k ∧ monoShape col k k k := by
  by_contra! hn
  have hunit : ¬ monoShape col 1 1 1 := by simpa using hn 1 ⟨0, rfl⟩
  obtain ⟨x, y, z, hxy, hyz, hxz, hcolor, hmix⟩ := mixed_equilateral_eight col hunit
  let w := y - x
  let v := z - x
  let q := v / w
  let u := w / (8 : ℂ)
  have hw : ‖w‖ = 8 := hxy
  have hv : ‖v‖ = ‖w‖ := hxz.trans hw.symm
  have hvw : ‖v - w‖ = ‖w‖ := by
    rw [show v - w = z - y by dsimp [v, w]; ring, hyz, hw]
  have hq := ratio_of_equilateral (u := w) (v := v) (by rw [hw]; norm_num) hv hvw
  have hu : ‖u‖ = 1 := by dsimp [u]; rw [norm_div, hw]; norm_num
  let L := latticePoint x u q
  have horig : L (0, 0) = x := by simp [L, latticePoint]
  have hbase : L (8, 0) = y := calc
    L (8, 0) = x + (8 : ℂ) * u := by norm_num [L, latticePoint]
    _ = y := by dsimp [u, w]; ring
  have hthird : L (0, 8) = z := calc
    L (0, 8) = x + ((8 : ℂ) * q) * u := by norm_num [L, latticePoint]
    _ = x + q * w := by dsimp [u]; ring
    _ = z := by rw [show q * w = v from hq.2.2]; dsimp [v]; ring
  apply OMA.shaderLatticeCertificate (col ∘ L)
  · simpa only [Function.comp_apply, hbase, hthird, horig] using hcolor
  · simpa only [Function.comp_apply, hbase, hthird, horig] using hmix
  · intro A B C hshape hcol
    let sides : Multiset ℤ := {OMA.shaderLatticeDistSq A B, OMA.shaderLatticeDistSq A C,
      OMA.shaderLatticeDistSq B C}
    have hside {s : ℤ} (hs : s ∈ sides) : s = 1 ∨ s = 9 ∨ s = 25 ∨ s = 49 := by
      change sides = {1, 1, 1} ∨ sides = {9, 9, 9} ∨ sides = {25, 25, 25} ∨
        sides = {49, 49, 49} ∨ sides = {9, 25, 49} at hshape
      rcases hshape with h | h | h | h | h <;> rw [h] at hs <;> simp at hs <;> tauto
    have hnorm (X Y : ℤ × ℤ) (hXY : OMA.shaderLatticeDistSq X Y ∈ sides) :
        ∃ j : ℕ, Odd j ∧ ‖L Y - L X‖ = j :=
      lattice_norm_is_odd _ _ (latticePoint_distSq (p := x) hu hq.1 hq.2.1 X Y) (hside hXY)
    obtain ⟨a, ha, hab⟩ := hnorm A B (by simp [sides])
    obtain ⟨b, hb, hbc⟩ := hnorm B C (by simp [sides])
    obtain ⟨d, hd, hac⟩ := hnorm A C (by simp [sides])
    have hm : monoShape col a b d := ⟨L A, L B, L C, hab, hbc, hac, hcol⟩
    rcases equilateral_of_shape hm with h | h | h
    · exact hn a ha h
    · exact hn b hb h
    · exact hn d hd h

private theorem right_triangle_complex (col : ℂ → Fin 2) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) : monoRight col a b := by
  by_contra h
  let scale : ℂ → ℂ := fun z => (a : ℂ) * z
  obtain ⟨k, hk, x, y, z, hxy, hyz, hxz, hmono⟩ := odd_equilateral (col ∘ scale)
  have hdist (p q : ℂ) (hpq : ‖q - p‖ = k) : ‖scale q - scale p‖ = k * a := by
    dsimp [scale]
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, hpq, mul_comm]
  exact no_odd_equilateral_of_no_right ha hb h k hk
    ⟨scale x, scale y, scale z, hdist x y hxy, hdist y z hyz, hdist x z hxz, hmono⟩

theorem OMA.solution : type_of% @Erdos173.erdos_173.variants.right_triangle := by
  intro col T hT
  let repr := Complex.orthonormalBasisOneI.repr
  let a := dist (T.points 0) (T.points 1)
  let b := dist (T.points 2) (T.points 1)
  have ha : 0 < a := dist_pos.mpr (T.independent.injective.ne (by decide))
  have hb : 0 < b := dist_pos.mpr (T.independent.injective.ne (by decide))
  obtain ⟨p, u, v, hu, hv, huv, hc⟩ := right_triangle_complex (col ∘ repr) a b ha hb
  let x := repr (p + u)
  let y := repr p
  let z := repr (p + v)
  have hxy : dist x y = a := by
    change dist (repr (p + u)) (repr p) = a
    rw [repr.isometry.dist_eq, dist_eq_norm, add_sub_cancel_left, hu]
  have hzy : dist z y = b := by
    change dist (repr (p + v)) (repr p) = b
    rw [repr.isometry.dist_eq, dist_eq_norm, add_sub_cancel_left, hv]
  have hxz : dist x z = dist (T.points 0) (T.points 2) := by
    change dist (repr (p + u)) (repr (p + v)) = _
    rw [repr.isometry.dist_eq, dist_eq_norm, show p + u - (p + v) = u - v by ring,
      norm_sub_rev u v]
    apply (sq_eq_sq₀ (norm_nonneg _) dist_nonneg).mp
    rw [← Complex.normSq_eq_norm_sq, (dotZero_iff_pythagoras _ _).mp huv,
      Complex.normSq_eq_norm_sq u, Complex.normSq_eq_norm_sq v, hu, hv]
    have hp := (EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two
      (T.points 0) (T.points 1) (T.points 2)).mpr hT
    simpa only [pow_two, a, b] using hp.symm
  have hpoints : ![T.points 0, T.points 1, T.points 2] = T.points := by
    funext i
    fin_cases i <;> rfl
  have hcon : ![x, y, z] ≅ T.points := by
    rw [← hpoints]
    exact EuclideanGeometry.side_side_side hxy
      (by rw [dist_comm y z, dist_comm (T.points 1) (T.points 2)]; exact hzy)
      (by rw [dist_comm z x, dist_comm (T.points 2) (T.points 0)]; exact hxz)
  have hright : ∠ x y z = Real.pi / 2 :=
    (EuclideanGeometry.angle_eq_of_congruent hcon 0 1 2).trans hT
  have hindep : AffineIndependent ℝ ![x, y, z] := by
    apply affineIndependent_iff_not_collinear_set.mpr
    intro hcol
    rcases EuclideanGeometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi.mp hcol with
      h₁ | h₂ | h₃ | h₄
    · exact ha.ne' (by rw [← hxy, h₁, dist_self])
    · exact hb.ne' (by rw [← hzy, h₂, dist_self])
    · rw [hright] at h₃
      linarith [Real.pi_pos]
    · rw [hright] at h₄
      linarith [Real.pi_pos]
  refine ⟨⟨![x, y, z], hindep⟩, hcon, col y, ?_⟩
  intro i
  fin_cases i
  · exact hc.1.symm
  · rfl
  · exact hc.2.symm