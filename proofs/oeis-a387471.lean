import OMAStatements.S_oeis_a387471
import Mathlib.Tactic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex

-- Problem: A387471: a(n) = number of interior triple intersections for the equal-angle model with parameter m = 2*n-1.
-- Upstream: formal-conjectures statements/oeis-a387471.lean:0 (declaration OMA.S_oeis_a387471.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA_A387471

open OMA.S_oeis_a387471 Polynomial Complex

/-! ### Part 1: Trigonometric reduction -/

private lemma trig_product_to_sum (u v w : ℝ) :
    4 * (Real.sin (Real.pi / 6 + u) * Real.sin (Real.pi / 6 + v) * Real.sin (Real.pi / 6 + w) -
         Real.sin (Real.pi / 6 - u) * Real.sin (Real.pi / 6 - v) * Real.sin (Real.pi / 6 - w)) =
      Real.sqrt 3 * (Real.sin (u + v - w) + Real.sin (u - v + w) + Real.sin (-u + v + w)) := by
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hcube : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
    calc Real.sqrt 3 ^ 3 = Real.sqrt 3 ^ 2 * Real.sqrt 3 := by ring
    _ = 3 * Real.sqrt 3 := by rw [hsq]
  simp only [Real.sin_add, Real.sin_sub, Real.cos_add, Real.cos_sub,
    Real.sin_pi_div_six, Real.cos_pi_div_six, Real.sin_neg, Real.cos_neg]
  linear_combination (Real.sin u * Real.sin v * Real.sin w) * hcube

private noncomputable def ang (n i : ℕ) : ℝ :=
  ((i + 1 : ℝ) - n) * Real.pi / (6 * n)

private lemma ratio_prod_eq_one_iff {n : ℕ} (hn : 1 ≤ n)
    (t : Fin (2 * n - 1) × Fin (2 * n - 1) × Fin (2 * n - 1)) :
    ratio (2 * n - 1) t.1 * ratio (2 * n - 1) t.2.1 * ratio (2 * n - 1) t.2.2 = 1 ↔
      Real.sin (ang n t.1 + ang n t.2.1 - ang n t.2.2) +
      Real.sin (ang n t.1 - ang n t.2.1 + ang n t.2.2) +
      Real.sin (-ang n t.1 + ang n t.2.1 + ang n t.2.2) = 0 := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hm_cast : ((2 * n - 1 : ℕ) : ℝ) + 1 = 2 * (n : ℝ) := by
    have h2n : 1 ≤ 2 * n := by omega
    rw [Nat.cast_sub h2n]
    push_cast
    ring
  have hangle : ∀ (i : Fin (2 * n - 1)),
      ((i.1 : ℝ) + 1) * Real.pi / (3 * (((2 * n - 1 : ℕ) : ℝ) + 1)) =
        Real.pi / 6 + ang n i.1 := by
    intro i
    rw [hm_cast, ang]
    field_simp
    ring
  have hsub : ∀ (i : Fin (2 * n - 1)),
      Real.pi / 3 - (Real.pi / 6 + ang n i.1) = Real.pi / 6 - ang n i.1 := by
    intro i; ring
  have hsin_pos : ∀ (i : Fin (2 * n - 1)), 0 < Real.sin (Real.pi / 6 - ang n i.1) := by
    intro i
    apply Real.sin_pos_of_pos_of_lt_pi
    · have hi : (i.1 : ℝ) + 1 < 2 * (n : ℝ) := by
        have : i.1 + 1 < 2 * n := by omega
        exact_mod_cast this
      have hpi : 0 < Real.pi := Real.pi_pos
      have : Real.pi / 6 - ang n i.1 =
          (2 * (n : ℝ) - ((i.1 : ℝ) + 1)) * Real.pi / (6 * n) := by
        rw [ang]; field_simp; ring
      rw [this]
      exact div_pos (mul_pos (by linarith) hpi) (by positivity)
    · have hi0 : (0 : ℝ) < (i.1 : ℝ) + 1 := by positivity
      have hpi : 0 < Real.pi := Real.pi_pos
      have : Real.pi / 6 - ang n i.1 =
          (2 * (n : ℝ) - ((i.1 : ℝ) + 1)) * Real.pi / (6 * n) := by
        rw [ang]; field_simp; ring
      rw [this, div_lt_iff₀ (by positivity)]
      nlinarith
  have hd1 : Real.sin (Real.pi / 6 - ang n t.1) ≠ 0 := (hsin_pos t.1).ne'
  have hd2 : Real.sin (Real.pi / 6 - ang n t.2.1) ≠ 0 := (hsin_pos t.2.1).ne'
  have hd3 : Real.sin (Real.pi / 6 - ang n t.2.2) ≠ 0 := (hsin_pos t.2.2).ne'
  have hrat : ∀ (i : Fin (2 * n - 1)),
      ratio (2 * n - 1) i.1 =
        Real.sin (Real.pi / 6 + ang n i.1) / Real.sin (Real.pi / 6 - ang n i.1) := by
    intro i
    unfold ratio
    dsimp only
    rw [hangle i, hsub i]
  rw [hrat t.1, hrat t.2.1, hrat t.2.2]
  have hdiv : (Real.sin (Real.pi / 6 + ang n t.1) / Real.sin (Real.pi / 6 - ang n t.1)) *
      (Real.sin (Real.pi / 6 + ang n t.2.1) / Real.sin (Real.pi / 6 - ang n t.2.1)) *
      (Real.sin (Real.pi / 6 + ang n t.2.2) / Real.sin (Real.pi / 6 - ang n t.2.2)) = 1 ↔
      Real.sin (Real.pi / 6 + ang n t.1) * Real.sin (Real.pi / 6 + ang n t.2.1) *
        Real.sin (Real.pi / 6 + ang n t.2.2) -
      Real.sin (Real.pi / 6 - ang n t.1) * Real.sin (Real.pi / 6 - ang n t.2.1) *
        Real.sin (Real.pi / 6 - ang n t.2.2) = 0 := by
    rw [div_mul_div_comm, div_mul_div_comm,
      div_eq_one_iff_eq (mul_ne_zero (mul_ne_zero hd1 hd2) hd3), sub_eq_zero]
  rw [hdiv]
  have hid := trig_product_to_sum (ang n t.1) (ang n t.2.1) (ang n t.2.2)
  have hsqrt3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  constructor
  · intro h
    rw [h, mul_zero] at hid
    exact (mul_eq_zero.mp hid.symm).resolve_left hsqrt3.ne'
  · intro h
    rw [h, mul_zero] at hid
    linarith

/-! ### Part 2: Six-root decomposition and ruling out proper vanishing subsums -/

private lemma exp_sub_inv_eq_sin (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) - (Complex.exp ((θ : ℂ) * Complex.I))⁻¹ =
      2 * Complex.I * (Real.sin θ : ℂ) := by
  rw [← Complex.exp_neg, show -((θ : ℂ) * Complex.I) = (-θ : ℂ) * Complex.I by ring,
    Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, Complex.ofReal_sin]
  ring

private lemma three_unit_sum_zero_re {z1 z2 z3 : ℂ}
    (h1 : ‖z1‖ = 1) (h2 : ‖z2‖ = 1) (h3 : ‖z3‖ = 1) (hsum : z1 + z2 + z3 = 0) :
    (z1 * starRingEnd ℂ z2).re = -(1 / 2 : ℝ) := by
  have hz3 : z1 + z2 = -z3 := eq_neg_of_add_eq_zero_left hsum
  have hns : Complex.normSq (z1 + z2) = 1 := by
    rw [hz3, Complex.normSq_neg, Complex.normSq_eq_norm_sq, h3]
    norm_num
  have h1sq : Complex.normSq z1 = 1 := by rw [Complex.normSq_eq_norm_sq, h1]; norm_num
  have h2sq : Complex.normSq z2 = 1 := by rw [Complex.normSq_eq_norm_sq, h2]; norm_num
  have hexp : Complex.normSq (z1 + z2) =
      Complex.normSq z1 + Complex.normSq z2 + 2 * (z1 * starRingEnd ℂ z2).re := by
    rw [Complex.normSq_add]
  linarith

private lemma re_exp_mul_conj_neg_inv (a b : ℝ) :
    (Complex.exp ((a : ℂ) * Complex.I) *
      starRingEnd ℂ (-((Complex.exp ((b : ℂ) * Complex.I))⁻¹))).re = -Real.cos (a + b) := by
  rw [map_neg, ← Complex.exp_neg, ← Complex.exp_conj]
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_neg]
  rw [← Complex.exp_add]
  have hadd : (a : ℂ) * Complex.I + (b : ℂ) * Complex.I = ((a + b : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hadd, Complex.neg_re, Complex.exp_ofReal_mul_I_re]

private lemma six_root_proper_subsum {θ1 θ2 θ3 : ℝ}
    (h1 : |θ1| < Real.pi / 2) (h2 : |θ2| < Real.pi / 2) (h3 : |θ3| < Real.pi / 2)
    (h12 : |θ1 + θ2| < Real.pi / 3) (h13 : |θ1 + θ3| < Real.pi / 3) (h23 : |θ2 + θ3| < Real.pi / 3)
    (hsin : Real.sin θ1 + Real.sin θ2 + Real.sin θ3 = 0)
    (S : Finset (Fin 6)) (hSne : S.Nonempty) (hSnu : S ≠ Finset.univ)
    (hSsum : ∑ i ∈ S,
      (![Complex.exp ((θ1 : ℂ) * Complex.I), -(Complex.exp ((θ1 : ℂ) * Complex.I))⁻¹,
         Complex.exp ((θ2 : ℂ) * Complex.I), -(Complex.exp ((θ2 : ℂ) * Complex.I))⁻¹,
         Complex.exp ((θ3 : ℂ) * Complex.I), -(Complex.exp ((θ3 : ℂ) * Complex.I))⁻¹] i) = 0) :
    (θ1 = 0 ∧ θ2 + θ3 = 0) ∨ (θ2 = 0 ∧ θ1 + θ3 = 0) ∨ (θ3 = 0 ∧ θ1 + θ2 = 0) := by
  let f : Fin 6 → ℂ :=
    ![Complex.exp ((θ1 : ℂ) * Complex.I), -(Complex.exp ((θ1 : ℂ) * Complex.I))⁻¹,
      Complex.exp ((θ2 : ℂ) * Complex.I), -(Complex.exp ((θ2 : ℂ) * Complex.I))⁻¹,
      Complex.exp ((θ3 : ℂ) * Complex.I), -(Complex.exp ((θ3 : ℂ) * Complex.I))⁻¹]
  have hfull : ∑ i : Fin 6, f i = 0 := by
    rw [Fin.sum_univ_six]
    simp only [f, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    have e1 := exp_sub_inv_eq_sin θ1
    have e2 := exp_sub_inv_eq_sin θ2
    have e3 := exp_sub_inv_eq_sin θ3
    have hs : (Real.sin θ1 : ℂ) + (Real.sin θ2 : ℂ) + (Real.sin θ3 : ℂ) = 0 := by
      exact_mod_cast hsin
    linear_combination e1 + e2 + e3 + 2 * Complex.I * hs
  have hnorm : ∀ i : Fin 6, ‖f i‖ = 1 := by
    intro i
    fin_cases i <;>
      simp [f, Complex.norm_exp_ofReal_mul_I]
  have hre_pos : ∀ (θ : ℝ), |θ| < Real.pi / 2 → 0 < (Complex.exp ((θ : ℂ) * Complex.I)).re := by
    intro θ hθ
    rw [Complex.exp_ofReal_mul_I_re]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le θ, abs_lt.mp hθ], (abs_lt.mp hθ).2⟩
  have hre_neg : ∀ (θ : ℝ), |θ| < Real.pi / 2 →
      (-(Complex.exp ((θ : ℂ) * Complex.I))⁻¹).re < 0 := by
    intro θ hθ
    rw [← Complex.exp_neg, Complex.neg_re]
    have hneg : -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hneg, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    have := hre_pos θ hθ
    rw [Complex.exp_ofReal_mul_I_re] at this
    linarith
  have hre_sign : ∀ i : Fin 6, (i.1 % 2 = 0 → 0 < (f i).re) ∧ (i.1 % 2 = 1 → (f i).re < 0) := by
    intro i
    fin_cases i <;> constructor <;> intro h <;> simp at h
    · exact hre_pos θ1 h1
    · exact hre_neg θ1 h1
    · exact hre_pos θ2 h2
    · exact hre_neg θ2 h2
    · exact hre_pos θ3 h3
    · exact hre_neg θ3 h3
  have hsin_inj : ∀ a b : ℝ, |a| < Real.pi / 2 → |b| < Real.pi / 2 →
      Real.sin a + Real.sin b = 0 → a + b = 0 := by
    intro a b ha hb hs
    have hsin_eq : Real.sin a = Real.sin (-b) := by rw [Real.sin_neg]; linarith
    have hab := Real.strictMonoOn_sin.injOn
      ⟨by linarith [(abs_lt.mp ha).1], by linarith [(abs_lt.mp ha).2]⟩
      ⟨by linarith [(abs_lt.mp hb).2], by linarith [(abs_lt.mp hb).1]⟩
      hsin_eq
    linarith
  have hsin_zero : ∀ a : ℝ, |a| < Real.pi / 2 → Real.sin a = 0 → a = 0 := by
    intro a ha hs
    have := hsin_inj a a ha ha (by linarith)
    linarith
  have hpair_ordered : ∀ i j : Fin 6, i.1 % 2 = 0 → j.1 % 2 = 1 → f i + f j = 0 →
      (θ1 = 0 ∧ θ2 + θ3 = 0) ∨ (θ2 = 0 ∧ θ1 + θ3 = 0) ∨ (θ3 = 0 ∧ θ1 + θ2 = 0) := by
    intro i j hi0 hj1 h0
    have him0 : (f i).im + (f j).im = 0 := by
      have := congrArg Complex.im h0
      simpa using this
    have him_pos : ∀ θ : ℝ, (Complex.exp ((θ : ℂ) * Complex.I)).im = Real.sin θ :=
      Complex.exp_ofReal_mul_I_im
    have him_neg : ∀ θ : ℝ, (-(Complex.exp ((θ : ℂ) * Complex.I))⁻¹).im = Real.sin θ := by
      intro θ
      rw [← Complex.exp_neg, Complex.neg_im]
      have hneg : -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [hneg, Complex.exp_ofReal_mul_I_im, Real.sin_neg, neg_neg]
    have hi_cases : i = 0 ∨ i = 2 ∨ i = 4 := by
      have := i.2; omega
    have hj_cases : j = 1 ∨ j = 3 ∨ j = 5 := by
      have := j.2; omega
    rcases hi_cases with rfl | rfl | rfl <;> rcases hj_cases with rfl | rfl | rfl
    · simp only [f, Matrix.cons_val_zero, Matrix.cons_val_one, him_pos, him_neg] at him0
      have h10 := hsin_zero θ1 h1 (by linarith)
      exact Or.inl ⟨h10, hsin_inj θ2 θ3 h2 h3 (by rw [h10, Real.sin_zero] at hsin; linarith)⟩
    · simp only [f, Matrix.cons_val_zero, Matrix.cons_val, him_pos, him_neg] at him0
      have h12z := hsin_inj θ1 θ2 h1 h2 him0
      exact Or.inr (Or.inr ⟨hsin_zero θ3 h3 (by linarith), h12z⟩)
    · simp only [f, Matrix.cons_val_zero, Matrix.cons_val, him_pos, him_neg] at him0
      have h13z := hsin_inj θ1 θ3 h1 h3 him0
      exact Or.inr (Or.inl ⟨hsin_zero θ2 h2 (by linarith), h13z⟩)
    · simp only [f, Matrix.cons_val_one, Matrix.cons_val, him_pos, him_neg] at him0
      have h21z := hsin_inj θ2 θ1 h2 h1 him0
      exact Or.inr (Or.inr ⟨hsin_zero θ3 h3 (by linarith), by linarith⟩)
    · simp only [f, Matrix.cons_val, him_pos, him_neg] at him0
      have h20 := hsin_zero θ2 h2 (by linarith)
      exact Or.inr (Or.inl ⟨h20, hsin_inj θ1 θ3 h1 h3 (by rw [h20, Real.sin_zero] at hsin; linarith)⟩)
    · simp only [f, Matrix.cons_val, him_pos, him_neg] at him0
      have h23z := hsin_inj θ2 θ3 h2 h3 him0
      exact Or.inl ⟨hsin_zero θ1 h1 (by linarith), h23z⟩
    · simp only [f, Matrix.cons_val_one, Matrix.cons_val, him_pos, him_neg] at him0
      have h31z := hsin_inj θ3 θ1 h3 h1 him0
      exact Or.inr (Or.inl ⟨hsin_zero θ2 h2 (by linarith), by linarith⟩)
    · simp only [f, Matrix.cons_val, him_pos, him_neg] at him0
      have h32z := hsin_inj θ3 θ2 h3 h2 him0
      exact Or.inl ⟨hsin_zero θ1 h1 (by linarith), by linarith⟩
    · simp only [f, Matrix.cons_val, him_pos, him_neg] at him0
      have h30 := hsin_zero θ3 h3 (by linarith)
      exact Or.inr (Or.inr ⟨h30, hsin_inj θ1 θ2 h1 h2 (by rw [h30, Real.sin_zero] at hsin; linarith)⟩)
  have hpair : ∀ i j : Fin 6, i ≠ j → f i + f j = 0 →
      (θ1 = 0 ∧ θ2 + θ3 = 0) ∨ (θ2 = 0 ∧ θ1 + θ3 = 0) ∨ (θ3 = 0 ∧ θ1 + θ2 = 0) := by
    intro i j _ h0
    have hre0 : (f i).re + (f j).re = 0 := by
      have := congrArg Complex.re h0
      simpa using this
    by_cases hi : i.1 % 2 = 0
    · by_cases hj : j.1 % 2 = 0
      · exfalso; have := (hre_sign i).1 hi; have := (hre_sign j).1 hj; linarith
      · exact hpair_ordered i j hi (by omega) h0
    · by_cases hj : j.1 % 2 = 0
      · exact hpair_ordered j i hj (by omega) (by rw [add_comm]; exact h0)
      · exfalso; have := (hre_sign i).2 (by omega); have := (hre_sign j).2 (by omega); linarith
  have htriple_impossible : ∀ (T : Finset (Fin 6)), T.card = 3 → ∑ i ∈ T, f i = 0 → False := by
    intro T hTcard hTsum
    have hcos_gt : ∀ a : ℝ, |a| < Real.pi / 3 → (1 / 2 : ℝ) < Real.cos a := by
      intro a ha
      rw [← Real.cos_abs, ← Real.cos_pi_div_three]
      exact Real.strictAntiOn_cos ⟨abs_nonneg a, by linarith [Real.pi_pos]⟩
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩ ha
    have hcross_impossible : ∀ p q : Fin 6, p.1 % 2 = 0 → q.1 % 2 = 1 → p.1 / 2 ≠ q.1 / 2 →
        (f p * starRingEnd ℂ (f q)).re = -(1 / 2 : ℝ) → False := by
      intro p q hp0 hq1 hne hre
      have hp_cases : p = 0 ∨ p = 2 ∨ p = 4 := by have := p.2; omega
      have hq_cases : q = 1 ∨ q = 3 ∨ q = 5 := by have := q.2; omega
      rcases hp_cases with rfl | rfl | rfl <;> rcases hq_cases with rfl | rfl | rfl
      all_goals try exact hne rfl
      all_goals simp only [f, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        re_exp_mul_conj_neg_inv] at hre
      · have := hcos_gt (θ1 + θ2) h12; linarith
      · have := hcos_gt (θ1 + θ3) h13; linarith
      · have := hcos_gt (θ2 + θ1) (by rwa [add_comm]); linarith
      · have := hcos_gt (θ2 + θ3) h23; linarith
      · have := hcos_gt (θ3 + θ1) (by rwa [add_comm]); linarith
      · have := hcos_gt (θ3 + θ2) (by rwa [add_comm]); linarith
    have hpair_pos_neg : ∀ (U : Finset (Fin 6)), U.card = 3 → ∑ i ∈ U, f i = 0 →
        ∀ i j k : Fin 6, i ∈ U → j ∈ U → k ∈ U →
        i ≠ j → i.1 % 2 = 0 → j.1 % 2 = 0 → k.1 % 2 = 1 → False := by
      intro U hUcard hUsum i j k hi hj hk hij hip hjp hkp
      have hik : i ≠ k := by intro h; subst h; omega
      have hjk : j ≠ k := by intro h; subst h; omega
      have hUeq : U = {i, j, k} := by
        symm
        apply Finset.eq_of_subset_of_card_le
        · intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl <;> assumption
        · rw [hUcard, Finset.card_insert_of_notMem (by simp [hij, hik]),
            Finset.card_insert_of_notMem (by simp [hjk]), Finset.card_singleton]
      rw [hUeq, Finset.sum_insert (by simp [hij, hik]),
        Finset.sum_insert (by simp [hjk]), Finset.sum_singleton] at hUsum
      have hdiv_ne : i.1 / 2 ≠ j.1 / 2 := by
        intro heq
        apply hij
        exact Fin.ext (by omega)
      by_cases h1d : i.1 / 2 ≠ k.1 / 2
      · exact hcross_impossible i k hip hkp h1d
          (three_unit_sum_zero_re (hnorm i) (hnorm k) (hnorm j) (by linear_combination hUsum))
      · exact hcross_impossible j k hjp hkp (by omega)
          (three_unit_sum_zero_re (hnorm j) (hnorm k) (hnorm i) (by linear_combination hUsum))
    let Tpos := T.filter (fun i : Fin 6 => i.1 % 2 = 0)
    let Tneg := T.filter (fun i : Fin 6 => i.1 % 2 = 1)
    have hsplit : Tpos.card + Tneg.card = 3 := by
      have hu : Tpos ∪ Tneg = T := by
        ext i; simp only [Tpos, Tneg, Finset.mem_union, Finset.mem_filter]
        have : i.1 % 2 = 0 ∨ i.1 % 2 = 1 := by omega
        tauto
      have hd : Disjoint Tpos Tneg := by
        rw [Finset.disjoint_left]
        intro i hi1 hi2
        simp only [Tpos, Tneg, Finset.mem_filter] at hi1 hi2
        omega
      rw [← Finset.card_union_of_disjoint hd, hu, hTcard]
    have hpos_ne0 : Tpos.card ≠ 0 := by
      intro h0
      have hTneg_eq : Tneg = T := by
        apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
        change T.card ≤ Tneg.card
        omega
      have hre_sum : ∑ i ∈ T, (f i).re < 0 := by
        apply Finset.sum_neg (fun i hi => (hre_sign i).2 (by
          rw [← hTneg_eq] at hi; exact (Finset.mem_filter.mp hi).2))
        exact Finset.card_pos.mp (by omega)
      have hre0 : ∑ i ∈ T, (f i).re = 0 := by
        have := congrArg Complex.re hTsum
        simpa using this
      linarith
    have hneg_ne0 : Tneg.card ≠ 0 := by
      intro h0
      have hTpos_eq : Tpos = T := by
        apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
        change T.card ≤ Tpos.card
        omega
      have hre_sum : 0 < ∑ i ∈ T, (f i).re := by
        apply Finset.sum_pos (fun i hi => (hre_sign i).1 (by
          rw [← hTpos_eq] at hi; exact (Finset.mem_filter.mp hi).2))
        exact Finset.card_pos.mp (by omega)
      have hre0 : ∑ i ∈ T, (f i).re = 0 := by
        have := congrArg Complex.re hTsum
        simpa using this
      linarith
    have h2or1 : Tpos.card = 2 ∨ Tneg.card = 2 := by omega
    rcases h2or1 with h2pos | h2neg
    · rcases Finset.card_eq_two.mp h2pos with ⟨i, j, hij, hTposeq⟩
      have hTneg1 : Tneg.card = 1 := by omega
      rcases Finset.card_eq_one.mp hTneg1 with ⟨k, hTnegeq⟩
      have hi : i ∈ Tpos := by rw [hTposeq]; simp
      have hj : j ∈ Tpos := by rw [hTposeq]; simp
      have hk : k ∈ Tneg := by rw [hTnegeq]; simp
      simp only [Tpos, Tneg, Finset.mem_filter] at hi hj hk
      exact hpair_pos_neg T hTcard hTsum i j k hi.1 hj.1 hk.1 hij hi.2 hj.2 hk.2
    · let Tc := Tᶜ
      have hTccard : Tc.card = 3 := by
        have := Finset.card_compl T
        simp only [Fintype.card_fin] at this
        change Tᶜ.card = 3
        omega
      have hTcsum : ∑ i ∈ Tc, f i = 0 := by
        have := Finset.sum_add_sum_compl T f
        rw [hTsum, hfull, zero_add] at this
        exact this
      let Tcpos := Tc.filter (fun i : Fin 6 => i.1 % 2 = 0)
      let Tcneg := Tc.filter (fun i : Fin 6 => i.1 % 2 = 1)
      have hpos_tot : (Finset.univ.filter (fun i : Fin 6 => i.1 % 2 = 0)).card = 3 := by decide
      have hpos_disj : Disjoint Tpos Tcpos := by
        rw [Finset.disjoint_left]
        intro i hi1 hi2
        simp only [Tpos, Tcpos, Tc, Finset.mem_filter, Finset.mem_compl] at hi1 hi2
        exact hi2.1 hi1.1
      have hpos_union : Tpos ∪ Tcpos = Finset.univ.filter (fun i : Fin 6 => i.1 % 2 = 0) := by
        ext i; simp only [Tpos, Tcpos, Tc, Finset.mem_union, Finset.mem_filter, Finset.mem_compl,
          Finset.mem_univ, true_and]; tauto
      have hTcpos2 : Tcpos.card = 2 := by
        have := Finset.card_union_of_disjoint hpos_disj
        rw [hpos_union, hpos_tot] at this
        omega
      have hTcneg1 : Tcneg.card = 1 := by
        have hu : Tcpos ∪ Tcneg = Tc := by
          ext i; simp only [Tcpos, Tcneg, Finset.mem_union, Finset.mem_filter]
          have : i.1 % 2 = 0 ∨ i.1 % 2 = 1 := by omega
          tauto
        have hd : Disjoint Tcpos Tcneg := by
          rw [Finset.disjoint_left]
          intro i hi1 hi2
          simp only [Tcpos, Tcneg, Finset.mem_filter] at hi1 hi2
          omega
        have := Finset.card_union_of_disjoint hd
        rw [hu, hTccard] at this
        omega
      rcases Finset.card_eq_two.mp hTcpos2 with ⟨i, j, hij, hTcposeq⟩
      rcases Finset.card_eq_one.mp hTcneg1 with ⟨k, hTcnegeq⟩
      have hi : i ∈ Tcpos := by rw [hTcposeq]; simp
      have hj : j ∈ Tcpos := by rw [hTcposeq]; simp
      have hk : k ∈ Tcneg := by rw [hTcnegeq]; simp
      simp only [Tcpos, Tcneg, Finset.mem_filter] at hi hj hk
      exact hpair_pos_neg Tc hTccard hTcsum i j k hi.1 hj.1 hk.1 hij hi.2 hj.2 hk.2
  have hScard_pos : 0 < S.card := Finset.card_pos.mpr hSne
  have hScard_lt : S.card < 6 := by
    have hle : S.card ≤ 6 := by simpa using Finset.card_le_univ S
    have hne : S.card ≠ 6 := by
      intro h6
      exact hSnu (Finset.eq_univ_of_card S (by simpa using h6))
    omega
  have hSc_sum : ∑ i ∈ Sᶜ, f i = 0 := by
    have := Finset.sum_add_sum_compl S f
    rw [hSsum, hfull, zero_add] at this
    exact this
  have hSc_card : Sᶜ.card = 6 - S.card := by
    have := Finset.card_compl S
    simp only [Fintype.card_fin] at this
    omega
  interval_cases hc : S.card
  · rcases Finset.card_eq_one.mp hc with ⟨i, rfl⟩
    rw [Finset.sum_singleton] at hSsum
    change f i = 0 at hSsum
    have := hnorm i
    rw [hSsum, norm_zero] at this
    norm_num at this
  · rcases Finset.card_eq_two.mp hc with ⟨i, j, hij, rfl⟩
    rw [Finset.sum_pair hij] at hSsum
    exact hpair i j hij hSsum
  · exact absurd (htriple_impossible S hc hSsum) id
  · have hc2 : Sᶜ.card = 2 := by omega
    rcases Finset.card_eq_two.mp hc2 with ⟨i, j, hij, hSceq⟩
    rw [hSceq, Finset.sum_pair hij] at hSc_sum
    exact hpair i j hij hSc_sum
  · have hc1 : Sᶜ.card = 1 := by omega
    rcases Finset.card_eq_one.mp hc1 with ⟨i, hSceq⟩
    rw [hSceq, Finset.sum_singleton] at hSc_sum
    have := hnorm i
    rw [hSc_sum, norm_zero] at this
    norm_num at this

/-! ### Part 3: Mann's Theorem (1965) via cyclotomic polynomials -/

private lemma exists_pow_eq_of_pow_eq_one {m : ℕ} (hm : 0 < m) {ω z : ℂ}
    (hω : IsPrimitiveRoot ω m) (hz : z ^ m = 1) : ∃ j : Fin m, ω ^ j.1 = z := by
  let P : Polynomial ℂ := Polynomial.X ^ m - 1
  have hPne : P ≠ 0 := by
    intro h0
    have h1 := congrArg (fun q : Polynomial ℂ => q.coeff m) h0
    simp [P, Polynomial.coeff_one, hm.ne'] at h1
  have hPdeg : P.natDegree ≤ m := by
    have h1 : (Polynomial.X ^ m : Polynomial ℂ).natDegree = m := Polynomial.natDegree_X_pow m
    have h2 : (1 : Polynomial ℂ).natDegree = 0 := Polynomial.natDegree_one
    exact (Polynomial.natDegree_sub_le _ _).trans (by omega)
  let imgs : Finset ℂ := Finset.univ.image (fun j : Fin m => ω ^ j.1)
  have hinj : Function.Injective (fun j : Fin m => ω ^ j.1) := by
    intro a b hab
    exact Fin.ext (hω.injOn_pow (Finset.mem_coe.mpr (Finset.mem_range.mpr a.2))
      (Finset.mem_coe.mpr (Finset.mem_range.mpr b.2)) hab)
  have himgs_card : imgs.card = m := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
  have hsub : imgs ⊆ P.roots.toFinset := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨j, _, rfl⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hPne, Polynomial.IsRoot.def]
    simp only [P, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow, sub_self]
  have hroots_le : P.roots.toFinset.card ≤ m :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' P).trans hPdeg)
  have heq : imgs = P.roots.toFinset :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hzmem : z ∈ P.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hPne, Polynomial.IsRoot.def]
    simp [P, hz]
  rw [← heq] at hzmem
  rcases Finset.mem_image.mp hzmem with ⟨j, _, hj⟩
  exact ⟨j, hj⟩

private lemma mann_minimal_order {k : ℕ} (hk : 0 < k) (ζ : Fin k → ℂ)
    (h0 : ζ ⟨0, hk⟩ = 1)
    (hroot : ∃ M : ℕ, 0 < M ∧ ∀ i : Fin k, (ζ i) ^ M = 1)
    (hsum : ∑ i : Fin k, ζ i = 0)
    (hmin : ∀ S : Finset (Fin k), S.Nonempty → S ≠ Finset.univ → ∑ i ∈ S, ζ i ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ (∀ i : Fin k, (ζ i) ^ m = 1) ∧
      (∀ p : ℕ, Nat.Prime p → p ∣ m → ¬ p ^ 2 ∣ m) ∧
      (∀ p : ℕ, Nat.Prime p → p ∣ m → p ≤ k) := by
  classical
  let m := Nat.find hroot
  have hm_spec : 0 < m ∧ ∀ i : Fin k, (ζ i) ^ m = 1 := Nat.find_spec hroot
  have hm_pos : 0 < m := hm_spec.1
  have hm_pow : ∀ i : Fin k, (ζ i) ^ m = 1 := hm_spec.2
  have hm_min : ∀ d : ℕ, 0 < d → d < m → ¬ ∀ i : Fin k, (ζ i) ^ d = 1 := by
    intro d hdpos hdlt hall
    exact Nat.find_min hroot hdlt ⟨hdpos, hall⟩
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / m)
  have hω : IsPrimitiveRoot ω m := Complex.isPrimitiveRoot_exp m hm_pos.ne'
  have hex_e : ∀ i : Fin k, ∃ e : ℕ, ω ^ e = ζ i := fun i => by
    rcases exists_pow_eq_of_pow_eq_one hm_pos hω (hm_pow i) with ⟨j, hj⟩
    exact ⟨j.1, hj⟩
  let e : Fin k → ℕ := fun i => if i = ⟨0, hk⟩ then 0 else (hex_e i).choose
  have he : ∀ i : Fin k, ω ^ (e i) = ζ i := by
    intro i
    dsimp only [e]
    split_ifs with hi
    · rw [hi, h0, pow_zero]
    · exact (hex_e i).choose_spec
  have he0 : e ⟨0, hk⟩ = 0 := by simp [e]
  let P : Polynomial ℚ := ∑ i : Fin k, Polynomial.X ^ (e i)
  have hPω : Polynomial.aeval ω P = 0 := by
    simp only [P, map_sum, map_pow, Polynomial.aeval_X]
    simp_rw [he]
    exact hsum
  have hP_coprime : ∀ j : ℕ, Nat.Coprime j m → ∑ i : Fin k, (ω ^ j) ^ (e i) = 0 := by
    intro j hj
    have hωj : IsPrimitiveRoot (ω ^ j) m := hω.pow_of_coprime j hj
    have hdvd : minpoly ℚ ω ∣ P := minpoly.dvd ℚ ω hPω
    have hmeq : minpoly ℚ ω = minpoly ℚ (ω ^ j) := by
      rw [← Polynomial.cyclotomic_eq_minpoly_rat hω hm_pos,
        ← Polynomial.cyclotomic_eq_minpoly_rat hωj hm_pos]
    rw [hmeq] at hdvd
    rcases hdvd with ⟨Q, hQ⟩
    have h0j : Polynomial.aeval (ω ^ j) P = 0 := by
      rw [hQ, map_mul, minpoly.aeval, zero_mul]
    simpa only [P, map_sum, map_pow, Polynomial.aeval_X] using h0j
  -- Helper: given prime p | m, write m = p * d and construct F(T) = ∑_{r < p} A_r T^r
  have hprime_analysis : ∀ p : ℕ, Nat.Prime p → p ∣ m → ¬ p ^ 2 ∣ m ∧ p ≤ k := by
    intro p hp hpm
    rcases hpm with ⟨d, hmd⟩
    have hd_pos : 0 < d := by
      rcases Nat.eq_zero_or_pos d with rfl | h
      · simp at hmd; omega
      · exact h
    have hd_lt : d < m := by
      have hp2 : 2 ≤ p := hp.two_le
      nlinarith
    let η : ℂ := ω ^ d
    have hη_pow : η ^ p = 1 := by
      show (ω ^ d) ^ p = 1
      rw [← pow_mul, mul_comm, ← hmd, hω.pow_eq_one]
    have hη_inj : Function.Injective (fun t : Fin p => η ^ t.1) := by
      intro a b hab
      wlog hle : a.1 ≤ b.1 generalizing a b
      · exact (this hab.symm (le_of_not_ge hle)).symm
      dsimp only at hab
      have ha_ne : η ^ a.1 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (Complex.exp_ne_zero _))
      have hdiff : η ^ (b.1 - a.1) = 1 := by
        have hmul : η ^ a.1 * η ^ (b.1 - a.1) = η ^ a.1 * 1 := by
          rw [← pow_add, Nat.add_sub_cancel' hle, mul_one, hab]
        exact mul_left_cancel₀ ha_ne hmul
      have hω_eq : ω ^ (d * (b.1 - a.1)) = 1 := by
        simpa only [η, ← pow_mul] using hdiff
      have hdiv : p * d ∣ d * (b.1 - a.1) := by
        rw [← hmd]
        exact (hω.pow_eq_one_iff_dvd _).mp hω_eq
      have hpdiv : p ∣ b.1 - a.1 := by
        rw [mul_comm p d] at hdiv
        exact (Nat.mul_dvd_mul_iff_left hd_pos).mp hdiv
      have hlt : b.1 - a.1 < p := by omega
      have h0d : b.1 - a.1 = 0 := Nat.eq_zero_of_dvd_of_lt hpdiv hlt
      exact Fin.ext (by omega)
    let A : Fin p → ℂ := fun r =>
      ∑ i ∈ Finset.univ.filter (fun i : Fin k => e i % p = r.1), ω ^ (e i)
    let F : Polynomial ℂ := ∑ r : Fin p, Polynomial.C (A r) * Polynomial.X ^ r.1
    have hF_coeff : ∀ r : ℕ, F.coeff r = if hr : r < p then A ⟨r, hr⟩ else 0 := by
      intro r
      simp only [F, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
      split_ifs with hr
      · rw [Finset.sum_eq_single ⟨r, hr⟩]
        · simp
        · intro b _ hb
          have hne : r ≠ b.1 := fun h => hb (Fin.ext h.symm)
          simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · apply Finset.sum_eq_zero
        intro b _
        have hne : r ≠ b.1 := by omega
        simp [hne]
    have hF_deg : F.natDegree < p := by
      have hle : F.natDegree ≤ p - 1 := by
        apply Polynomial.natDegree_sum_le_of_forall_le
        intro r _
        exact (Polynomial.natDegree_C_mul_X_pow_le (A r) r.1).trans (by omega)
      have := hp.pos
      omega
    have hF_eval : ∀ t : ℕ, F.eval (η ^ t) = ∑ i : Fin k, (ω ^ (1 + t * d)) ^ (e i) := by
      intro t
      have hηt_p : (η ^ t) ^ p = 1 := by
        rw [← pow_mul, mul_comm t p, pow_mul, hη_pow, one_pow]
      have hterm : ∀ i : Fin k, (ω ^ (1 + t * d)) ^ (e i) = ω ^ (e i) * (η ^ t) ^ (e i % p) := by
        intro i
        have hdiv_mod : e i = p * (e i / p) + e i % p := (Nat.div_add_mod (e i) p).symm
        calc (ω ^ (1 + t * d)) ^ (e i)
            = (ω * η ^ t) ^ (e i) := by
              rw [pow_add, pow_one, mul_comm t d, pow_mul]
          _ = ω ^ (e i) * (η ^ t) ^ (e i) := mul_pow _ _ _
          _ = ω ^ (e i) * (η ^ t) ^ (p * (e i / p) + e i % p) := by rw [← hdiv_mod]
          _ = ω ^ (e i) * (η ^ t) ^ (e i % p) := by
              rw [pow_add, pow_mul, hηt_p, one_pow, one_mul]
      simp_rw [hterm]
      simp only [F, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, A, Finset.sum_mul]
      symm
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun i : Fin k => (⟨e i % p, Nat.mod_lt _ hp.pos⟩ : Fin p))
        (fun _ _ => Finset.mem_univ _)]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr
      · ext i; simp [Fin.ext_iff]
      · intro i hi
        have hmod : e i % p = r.1 := by simpa [Fin.ext_iff] using (Finset.mem_filter.mp hi).2
        rw [hmod]
    -- Auxiliary: A 0 ≠ 0! Because if A 0 = 0, minimality forces all e i divisible by p, contradicting m minimal!
    have hA0_ne : A ⟨0, hp.pos⟩ ≠ 0 := by
      intro hA0
      let S0 := Finset.univ.filter (fun i : Fin k => e i % p = 0)
      have hS0_ne : S0.Nonempty := ⟨⟨0, hk⟩, by simp [S0, he0]⟩
      have hS0_sum : ∑ i ∈ S0, ζ i = 0 := by
        have : ∑ i ∈ S0, ζ i = A ⟨0, hp.pos⟩ := by
          apply Finset.sum_congr rfl
          intro i _; exact (he i).symm
        rw [this, hA0]
      have hS0_univ : S0 = Finset.univ := by
        by_contra hnu
        exact hmin S0 hS0_ne hnu hS0_sum
      have hall_dvd : ∀ i : Fin k, p ∣ e i := by
        intro i
        have hi : i ∈ S0 := by rw [hS0_univ]; exact Finset.mem_univ i
        exact Nat.dvd_of_mod_eq_zero (Finset.mem_filter.mp hi).2
      apply hm_min d hd_pos hd_lt
      intro i
      rcases hall_dvd i with ⟨q, hq⟩
      rw [← he i, hq, ← pow_mul, mul_assoc, mul_comm q d, ← mul_assoc, ← hmd, pow_mul,
        hω.pow_eq_one, one_pow]
    have hnsq : ¬ p ^ 2 ∣ m := by
      intro hpsq
      have hpd : p ∣ d := by
        rw [hmd, sq] at hpsq
        exact (Nat.mul_dvd_mul_iff_left hp.pos).mp hpsq
      have hFeval0 : ∀ t : Fin p, F.eval (η ^ t.1) = 0 := by
        intro t
        rw [hF_eval t.1]
        apply hP_coprime (1 + t.1 * d)
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra hne1
        have hq := Nat.minFac_prime hne1
        have hq_gcd : Nat.minFac (Nat.gcd (1 + t.1 * d) m) ∣ Nat.gcd (1 + t.1 * d) m :=
          Nat.minFac_dvd _
        have hq1 : Nat.minFac (Nat.gcd (1 + t.1 * d) m) ∣ 1 + t.1 * d :=
          hq_gcd.trans (Nat.gcd_dvd_left _ _)
        have hqm : Nat.minFac (Nat.gcd (1 + t.1 * d) m) ∣ p * d := by
          rw [← hmd]; exact hq_gcd.trans (Nat.gcd_dvd_right _ _)
        have hqd : Nat.minFac (Nat.gcd (1 + t.1 * d) m) ∣ d := by
          rcases hq.dvd_mul.mp hqm with hqp | hqd
          · exact hqp.trans hpd
          · exact hqd
        have hq1' : Nat.minFac (Nat.gcd (1 + t.1 * d) m) ∣ 1 :=
          (Nat.dvd_add_left (dvd_mul_of_dvd_right hqd t.1)).mp hq1
        exact hq.not_dvd_one hq1'
      have hF0 : F = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero F hη_inj hFeval0
        (by simpa [Fintype.card_fin] using hF_deg)
      have hA0 : A ⟨0, hp.pos⟩ = 0 := by
        have := congrArg (fun q : Polynomial ℂ => q.coeff 0) hF0
        rw [hF_coeff 0, dif_pos hp.pos, Polynomial.coeff_zero] at this
        exact this
      exact hA0_ne hA0
    refine ⟨hnsq, ?_⟩
    -- Now p ∤ d; show all A r ≠ 0, hence p ≤ k
    have hnpd : ¬ p ∣ d := by
      intro hpd
      apply hnsq
      rw [hmd, sq]
      exact Nat.mul_dvd_mul_left p hpd
    have : Fact p.Prime := ⟨hp⟩
    have hd_zmod : (d : ZMod p) ≠ 0 := by
      intro h0
      exact hnpd ((ZMod.natCast_eq_zero_iff d p).mp h0)
    let t0 : Fin p := ⟨(-(d : ZMod p)⁻¹).val, ZMod.val_lt _⟩
    let G : Polynomial ℂ := (Polynomial.X - Polynomial.C (η ^ t0.1)) * F
    have hG_eval0 : ∀ t : Fin p, G.eval (η ^ t.1) = 0 := by
      intro t
      simp only [G, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      by_cases ht : t = t0
      · rw [ht, sub_self, zero_mul]
      · suffices hFt : F.eval (η ^ t.1) = 0 by rw [hFt, mul_zero]
        rw [hF_eval t.1]
        apply hP_coprime (1 + t.1 * d)
        rw [hmd, Nat.coprime_mul_iff_right]
        constructor
        · rw [Nat.coprime_comm]
          apply hp.coprime_iff_not_dvd.mpr
          intro hdiv
          have hz : ((1 + t.1 * d : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr hdiv
          push_cast at hz
          have htz : (t.1 : ZMod p) = -(d : ZMod p)⁻¹ := by
            apply mul_right_cancel₀ hd_zmod
            rw [neg_mul, inv_mul_cancel₀ hd_zmod]
            linear_combination hz
          have hval : t.1 = (-(d : ZMod p)⁻¹).val := by
            rw [← htz, ZMod.val_natCast, Nat.mod_eq_of_lt t.2]
          exact ht (Fin.ext hval)
        · rw [Nat.coprime_iff_gcd_eq_one]
          by_contra hne1
          have hq := Nat.minFac_prime hne1
          have hq1 : Nat.minFac (Nat.gcd (1 + t.1 * d) d) ∣ 1 + t.1 * d :=
            (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _)
          have hqd : Nat.minFac (Nat.gcd (1 + t.1 * d) d) ∣ d :=
            (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _)
          exact hq.not_dvd_one ((Nat.dvd_add_left (dvd_mul_of_dvd_right hqd t.1)).mp hq1)
    let c : ℂ := G.coeff p
    let H : Polynomial ℂ := G - Polynomial.C c * (Polynomial.X ^ p - 1)
    have hG_coeff_gt : ∀ n : ℕ, p < n → G.coeff n = 0 := by
      intro n hn
      have hGdeg : G.natDegree ≤ p := by
        by_cases hF0 : F = 0
        · simp [G, hF0]
        · calc G.natDegree ≤ (Polynomial.X - Polynomial.C (η ^ t0.1)).natDegree + F.natDegree :=
              Polynomial.natDegree_mul_le
            _ ≤ 1 + (p - 1) := by
              have hlin : (Polynomial.X - Polynomial.C (η ^ t0.1)).natDegree ≤ 1 := by
                exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
              omega
            _ = p := Nat.add_sub_cancel' hp.pos
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have hH_coeff_ge : ∀ n : ℕ, p ≤ n → H.coeff n = 0 := by
      intro n hn
      simp only [H, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        Polynomial.coeff_one]
      have hne0 : n ≠ 0 := by have := hp.pos; omega
      rw [if_neg hne0, sub_zero]
      by_cases hnp : n = p
      · subst hnp; simp [c]
      · rw [if_neg hnp, mul_zero, sub_zero]
        exact hG_coeff_gt n (by omega)
    have hH_deg : H.natDegree < p := by
      by_cases hH0 : H = 0
      · rw [hH0, Polynomial.natDegree_zero]; exact hp.pos
      · by_contra hge
        have hle : p ≤ H.natDegree := not_lt.mp hge
        exact Polynomial.leadingCoeff_ne_zero.mpr hH0 (hH_coeff_ge H.natDegree hle)
    have hH_eval0 : ∀ t : Fin p, H.eval (η ^ t.1) = 0 := by
      intro t
      simp only [H, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, hG_eval0 t]
      rw [← pow_mul, mul_comm t.1 p, pow_mul, hη_pow, one_pow, sub_self, mul_zero, sub_zero]
    have hH0 : H = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero H hη_inj hH_eval0
      (by simpa [Fintype.card_fin] using hH_deg)
    have hG_eq : G = Polynomial.C c * (Polynomial.X ^ p - 1) := sub_eq_zero.mp hH0
    have hA_rel : ∀ r : ℕ, (hr : r + 1 < p) →
        A ⟨r, by omega⟩ = η ^ t0.1 * A ⟨r + 1, hr⟩ := by
      intro r hr
      have hc0 : G.coeff (r + 1) = 0 := by
        rw [hG_eq, Polynomial.coeff_C_mul, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
          Polynomial.coeff_one, if_neg (by omega), if_neg (by omega)]
        ring
      have hcG : G.coeff (r + 1) = A ⟨r, by omega⟩ - η ^ t0.1 * A ⟨r + 1, hr⟩ := by
        simp only [G, sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul]
        rw [hF_coeff r, dif_pos (by omega), hF_coeff (r + 1), dif_pos hr]
      linear_combination hc0 - hcG
    have hA_ne : ∀ r : Fin p, A r ≠ 0 := by
      intro ⟨r, hr⟩
      induction r with
      | zero => exact hA0_ne
      | succ r ih =>
        have hprev : A ⟨r, by omega⟩ ≠ 0 := ih (by omega)
        have hrel := hA_rel r hr
        intro h0r
        rw [h0r, mul_zero] at hrel
        exact hprev hrel
    have hfib_ne : ∀ r : Fin p, (Finset.univ.filter (fun i : Fin k => e i % p = r.1)).Nonempty := by
      intro r
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      have h0r : A r = 0 := by simp [A, hemp]
      exact hA_ne r h0r
    let g : Fin p → Fin k := fun r => (hfib_ne r).choose
    have hginj : Function.Injective g := by
      intro r1 r2 heqg
      have h1 := (Finset.mem_filter.mp (hfib_ne r1).choose_spec).2
      have h2 := (Finset.mem_filter.mp (hfib_ne r2).choose_spec).2
      change e (g r1) % p = r1.1 at h1
      change e (g r2) % p = r2.1 at h2
      rw [heqg] at h1
      exact Fin.ext (h1.symm.trans h2)
    simpa [Fintype.card_fin] using Fintype.card_le_of_injective g hginj
  exact ⟨m, hm_pos, hm_pow, fun p hp hpm => (hprime_analysis p hp hpm).1,
    fun p hp hpm => (hprime_analysis p hp hpm).2⟩

private lemma dvd_thirty_of_sqfree_primes_le_six {m : ℕ} (hm : 0 < m)
    (hsq : ∀ p : ℕ, Nat.Prime p → p ∣ m → ¬ p ^ 2 ∣ m)
    (hle : ∀ p : ℕ, Nat.Prime p → p ∣ m → p ≤ 6) : m ∣ 30 := by
  suffices h : ∀ q : ℕ, 0 < q → q ∣ m → (∀ p : ℕ, Nat.Prime p → p ∣ q → p ≤ 6 ∧ ¬ p ^ 2 ∣ q) →
      q ∣ 30 by
    exact h m hm (dvd_refl m) (fun p hp hpq => ⟨hle p hp hpq, hsq p hp hpq⟩)
  intro q hqpos _ hprops
  -- Factor out 2, 3, 5 at most once each
  let q2 := if 2 ∣ q then q / 2 else q
  have hq2_eq : q = (if 2 ∣ q then 2 else 1) * q2 := by
    dsimp only [q2]; split_ifs with h
    · exact (Nat.mul_div_cancel' h).symm
    · simp
  have hq2_ndvd2 : ¬ 2 ∣ q2 := by
    dsimp only [q2]; split_ifs with h
    · intro h2
      have h4 : 2 ^ 2 ∣ q := by
        rcases h2 with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        have := Nat.mul_div_cancel' h
        linarith
      exact (hprops 2 Nat.prime_two h).2 h4
    · exact h
  let q3 := if 3 ∣ q2 then q2 / 3 else q2
  have hq3_eq : q2 = (if 3 ∣ q2 then 3 else 1) * q3 := by
    dsimp only [q3]; split_ifs with h
    · exact (Nat.mul_div_cancel' h).symm
    · simp
  have hq3_ndvd3 : ¬ 3 ∣ q3 := by
    dsimp only [q3]; split_ifs with h
    · intro h3
      have h9 : 3 ^ 2 ∣ q := by
        have h3q : 3 ∣ q := h.trans (by rw [hq2_eq]; exact dvd_mul_left _ _)
        rcases h3 with ⟨t, ht⟩
        have h9q2 : 3 ^ 2 ∣ q2 := ⟨t, by have := Nat.mul_div_cancel' h; linarith⟩
        exact h9q2.trans (by rw [hq2_eq]; exact dvd_mul_left _ _)
      exact (hprops 3 Nat.prime_three (h.trans (by rw [hq2_eq]; exact dvd_mul_left _ _))).2 h9
    · exact h
  let q5 := if 5 ∣ q3 then q3 / 5 else q3
  have hq5_eq : q3 = (if 5 ∣ q3 then 5 else 1) * q5 := by
    dsimp only [q5]; split_ifs with h
    · exact (Nat.mul_div_cancel' h).symm
    · simp
  have hq5_ndvd5 : ¬ 5 ∣ q5 := by
    dsimp only [q5]; split_ifs with h
    · intro h5
      have h25q3 : 5 ^ 2 ∣ q3 := by
        rcases h5 with ⟨t, ht⟩
        exact ⟨t, by have := Nat.mul_div_cancel' h; linarith⟩
      have hq3_dvd_q2 : q3 ∣ q2 := by rw [hq3_eq]; exact dvd_mul_left _ _
      have hq2_dvd_q : q2 ∣ q := by rw [hq2_eq]; exact dvd_mul_left _ _
      have hq3_dvd_q : q3 ∣ q := hq3_dvd_q2.trans hq2_dvd_q
      exact (hprops 5 Nat.prime_five (h.trans hq3_dvd_q)).2 (h25q3.trans hq3_dvd_q)
    · exact h
  have hq5_dvd_q3 : q5 ∣ q3 := by rw [hq5_eq]; exact dvd_mul_left _ _
  have hq3_dvd_q2 : q3 ∣ q2 := by rw [hq3_eq]; exact dvd_mul_left _ _
  have hq2_dvd_q : q2 ∣ q := by rw [hq2_eq]; exact dvd_mul_left _ _
  have hq5_dvd_q2 : q5 ∣ q2 := hq5_dvd_q3.trans hq3_dvd_q2
  have hq5_dvd_q : q5 ∣ q := hq5_dvd_q2.trans hq2_dvd_q
  have hq5_eq1 : q5 = 1 := by
    by_contra hne1
    have hp := Nat.minFac_prime hne1
    have hpd := Nat.minFac_dvd q5
    have hple := (hprops q5.minFac hp (hpd.trans hq5_dvd_q)).1
    have hge2 := hp.two_le
    interval_cases hf : q5.minFac
    · exact hq2_ndvd2 (hpd.trans hq5_dvd_q2)
    · exact hq3_ndvd3 (hpd.trans hq5_dvd_q3)
    · norm_num at hp
    · exact hq5_ndvd5 hpd
    · norm_num at hp
  rw [hq2_eq, hq3_eq, hq5_eq, hq5_eq1, mul_one]
  split_ifs <;> norm_num

/-! ### Part 4: Exact finite classification mod Phi_60 -/

private def sinVecNat : Fin 15 → List ℤ
  | ⟨0, _⟩  => [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | ⟨1, _⟩  => [-1, 0, -1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, -2, 0]
  | ⟨2, _⟩  => [0, -1, 0, -1, 0, 0, 0, 1, 0, 1, 0, 1, 0, -1, 0, -1]
  | ⟨3, _⟩  => [1, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0]
  | ⟨4, _⟩  => [0, 1, 0, 0, 0, -1, 0, -1, 0, 0, 0, -1, 0, 1, 0, 1]
  | ⟨5, _⟩  => [-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  | ⟨6, _⟩  => [0, -1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0]
  | ⟨7, _⟩  => [0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0]
  | ⟨8, _⟩  => [0, 0, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0]
  | ⟨9, _⟩  => [0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0]
  | ⟨10, _⟩ => [0, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
  | ⟨11, _⟩ => [-1, 0, -1, 0, -1, 0, 0, 0, 1, 0, 1, 0, 0, 0, -1, 0]
  | ⟨12, _⟩ => [0, -1, 0, -2, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, -1]
  | ⟨13, _⟩ => [1, 0, -1, 0, -1, 0, -1, 0, -1, 0, 0, 0, 1, 0, 1, 0]
  | ⟨14, _⟩ => [0, 0, 0, 0, 0, -1, 0, -1, 0, -1, 0, 0, 0, 1, 0, 1]

private def sinCoeff (k : ℤ) (j : Fin 16) : ℤ :=
  if _h : 0 ≤ k then
    if hlt : k.toNat < 15 then (sinVecNat ⟨k.toNat, hlt⟩).getD j.1 0 else 0
  else
    if hlt : (-k).toNat < 15 then -((sinVecNat ⟨(-k).toNat, hlt⟩).getD j.1 0) else 0

private def evalList (w : ℂ) (l : List ℤ) : ℂ :=
  ∑ j : Fin 16, ((l.getD j.1 0 : ℤ) : ℂ) * w ^ j.1

private lemma phi60_root (w : ℂ) (hw : IsPrimitiveRoot w 60) :
    w ^ 16 + w ^ 14 - w ^ 10 - w ^ 8 - w ^ 6 + w ^ 2 + 1 = 0 := by
  have hw60 : w ^ 60 = 1 := hw.pow_eq_one
  have hw30 : w ^ 30 = -1 := by
    have hsq : (w ^ 30 - 1) * (w ^ 30 + 1) = 0 := by
      linear_combination hw60
    rcases mul_eq_zero.mp hsq with h1 | h2
    · exfalso
      have := (hw.pow_eq_one_iff_dvd 30).mp (sub_eq_zero.mp h1)
      norm_num at this
    · exact eq_neg_of_add_eq_zero_left h2
  have hprod : (w ^ 16 + w ^ 14 - w ^ 10 - w ^ 8 - w ^ 6 + w ^ 2 + 1) *
      (w ^ 4 - w ^ 2 + 1) * (w ^ 10 + 1) = 0 := by
    linear_combination hw30
  have hne1 : w ^ 10 + 1 ≠ 0 := by
    intro h0
    have h20 : w ^ 20 = 1 := by linear_combination (w ^ 10 - 1) * h0
    have := (hw.pow_eq_one_iff_dvd 20).mp h20
    norm_num at this
  have hne2 : w ^ 4 - w ^ 2 + 1 ≠ 0 := by
    intro h0
    have h6 : w ^ 6 + 1 = 0 := by linear_combination (w ^ 2 + 1) * h0
    have h12 : w ^ 12 = 1 := by linear_combination (w ^ 6 - 1) * h6
    have := (hw.pow_eq_one_iff_dvd 12).mp h12
    norm_num at this
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hne1)).resolve_right hne2

private lemma evalList_sinVecNat (w : ℂ) (hw : IsPrimitiveRoot w 60) (k : Fin 15) :
    evalList w (sinVecNat k) = w ^ (15 + k.1) - w ^ (15 - k.1) := by
  have hΦ := phi60_root w hw
  fin_cases k
  all_goals
    simp only [evalList, sinVecNat, Fin.sum_univ_succ, Fin.sum_univ_zero, List.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
      Fin.val_zero, Fin.val_succ, Int.cast_zero, Int.cast_one, Int.cast_neg, Int.cast_ofNat,
      zero_mul, one_mul, neg_mul, add_zero, zero_add, pow_zero, pow_one]
  · ring
  · linear_combination -hΦ
  · linear_combination -w * hΦ
  · linear_combination -((-1 + w ^ 2) * hΦ)
  · linear_combination -((-w + w ^ 3) * hΦ)
  · linear_combination -((1 - w ^ 2 + w ^ 4) * hΦ)
  · linear_combination -((w - w ^ 3 + w ^ 5) * hΦ)
  · linear_combination -((w ^ 2 - w ^ 4 + w ^ 6) * hΦ)
  · linear_combination -((w ^ 3 - w ^ 5 + w ^ 7) * hΦ)
  · linear_combination -((w ^ 4 - w ^ 6 + w ^ 8) * hΦ)
  · linear_combination -((w ^ 5 - w ^ 7 + w ^ 9) * hΦ)
  · linear_combination -((1 + w ^ 6 - w ^ 8 + w ^ 10) * hΦ)
  · linear_combination -((w + w ^ 7 - w ^ 9 + w ^ 11) * hΦ)
  · linear_combination -((-1 + w ^ 2 + w ^ 8 - w ^ 10 + w ^ 12) * hΦ)
  · linear_combination -((-w + w ^ 3 + w ^ 9 - w ^ 11 + w ^ 13) * hΦ)

private lemma eval_sinCoeff (w : ℂ) (hw : IsPrimitiveRoot w 60) {k : ℤ}
    (hk : -14 ≤ k ∧ k ≤ 14) :
    ∑ j : Fin 16, ((sinCoeff k j : ℤ) : ℂ) * w ^ j.1 =
      w ^ (15 + k).toNat - w ^ (15 - k).toNat := by
  by_cases h0 : 0 ≤ k
  · have hlt : k.toNat < 15 := by omega
    have h1 : (15 + k).toNat = 15 + k.toNat := by omega
    have h2 : (15 - k).toNat = 15 - k.toNat := by omega
    rw [h1, h2, ← evalList_sinVecNat w hw ⟨k.toNat, hlt⟩]
    apply Finset.sum_congr rfl
    intro j _
    simp [sinCoeff, h0, hlt]
  · have hlt : (-k).toNat < 15 := by omega
    have h1 : (15 + k).toNat = 15 - (-k).toNat := by omega
    have h2 : (15 - k).toNat = 15 + (-k).toNat := by omega
    rw [h1, h2]
    have hsum : ∑ j : Fin 16, ((sinCoeff k j : ℤ) : ℂ) * w ^ j.1 =
        -evalList w (sinVecNat ⟨(-k).toNat, hlt⟩) := by
      simp only [evalList, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp [sinCoeff, h0, hlt]
    rw [hsum, evalList_sinVecNat w hw ⟨(-k).toNat, hlt⟩]
    ring

private lemma coeff_zero_of_aeval_w60 (w : ℂ) (hw : IsPrimitiveRoot w 60) (c : Fin 16 → ℤ)
    (h0 : ∑ j : Fin 16, ((c j : ℤ) : ℂ) * w ^ j.1 = 0) : ∀ j : Fin 16, c j = 0 := by
  let P : Polynomial ℚ := ∑ j : Fin 16, Polynomial.C (c j : ℚ) * Polynomial.X ^ j.1
  have hPa : Polynomial.aeval w P = 0 := by
    simpa [P, map_sum, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X] using h0
  have hdvd : minpoly ℚ w ∣ P := minpoly.dvd ℚ w hPa
  have hmindeg : (minpoly ℚ w).natDegree = 16 := by
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hw (by norm_num),
      Polynomial.natDegree_cyclotomic 60 ℚ]
    decide
  have hPdeg : P.natDegree < 16 := by
    have hle : P.natDegree ≤ 15 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro j _
      exact (Polynomial.natDegree_C_mul_X_pow_le (c j : ℚ) j.1).trans (by omega)
    omega
  have hP0 : P = 0 := by
    by_contra hne
    have hle := Polynomial.natDegree_le_of_dvd hdvd hne
    omega
  intro j
  have hcj := congrArg (fun q : Polynomial ℚ => q.coeff j.1) hP0
  simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at hcj
  rw [Finset.sum_eq_single j] at hcj
  · simp only [ite_true] at hcj
    exact_mod_cast hcj
  · intro b _ hb
    have hne : j.1 ≠ b.1 := fun h => hb (Fin.ext h.symm)
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ j) h

private def checkReducedTriple (a b c : Fin 29) : Bool :=
  let k1 : ℤ := (a.1 : ℤ) - 14
  let k2 : ℤ := (b.1 : ℤ) - 14
  let k3 : ℤ := (c.1 : ℤ) - 14
  if decide (k1 ≤ k2 ∧ k2 ≤ k3 ∧ 0 ≤ k2 ∧
      |k1 + k2| < 10 ∧ |k1 + k3| < 10 ∧ |k2 + k3| < 10) then
    if (List.finRange 16).all (fun j => sinCoeff k1 j + sinCoeff k2 j + sinCoeff k3 j == 0) then
      decide ((k2 == 0 && k1 + k3 == 0) || (k1 == -9 && k2 == 3 && k3 == 5))
    else true
  else true

private lemma checkReducedTriple_all :
    ∀ b : Fin 5, ∀ c : Fin 10, ∀ a : Fin 29,
      checkReducedTriple a ⟨b.1 + 14, by omega⟩ ⟨c.1 + 14, by omega⟩ = true := by
  decide

private lemma classify_reduced_int_triple {k1 k2 k3 : ℤ}
    (hlo1 : -14 ≤ k1) (hhi1 : k1 ≤ 14) (hlo2 : -14 ≤ k2) (hhi2 : k2 ≤ 14)
    (hlo3 : -14 ≤ k3) (hhi3 : k3 ≤ 14)
    (h12 : k1 ≤ k2) (h23 : k2 ≤ k3) (h02 : 0 ≤ k2)
    (hb12 : |k1 + k2| < 10) (hb13 : |k1 + k3| < 10) (hb23 : |k2 + k3| < 10)
    (hzero : ∀ j : Fin 16, sinCoeff k1 j + sinCoeff k2 j + sinCoeff k3 j = 0) :
    (k2 = 0 ∧ k1 + k3 = 0) ∨ (k1 = -9 ∧ k2 = 3 ∧ k3 = 5) := by
  have hb23' := abs_lt.mp hb23
  have hb_lt : k2.toNat < 5 := by omega
  have hc_lt : k3.toNat < 10 := by omega
  have ha_lt : (k1 + 14).toNat < 29 := by omega
  have hchk := checkReducedTriple_all ⟨k2.toNat, hb_lt⟩ ⟨k3.toNat, hc_lt⟩ ⟨(k1 + 14).toNat, ha_lt⟩
  have hk1 : ((k1 + 14).toNat : ℤ) - 14 = k1 := by omega
  have hk2 : ((k2.toNat + 14 : ℕ) : ℤ) - 14 = k2 := by omega
  have hk3 : ((k3.toNat + 14 : ℕ) : ℤ) - 14 = k3 := by omega
  simp only [checkReducedTriple, hk1, hk2, hk3] at hchk
  have hcond : decide (k1 ≤ k2 ∧ k2 ≤ k3 ∧ 0 ≤ k2 ∧
      |k1 + k2| < 10 ∧ |k1 + k3| < 10 ∧ |k2 + k3| < 10) = true := by
    simp [h12, h23, h02, hb12, hb13, hb23]
  have hall : (List.finRange 16).all (fun j => sinCoeff k1 j + sinCoeff k2 j + sinCoeff k3 j == 0) =
      true := by
    rw [List.all_eq_true]
    intro j _
    simp [hzero j]
  rw [hcond, if_pos rfl, hall, if_pos rfl] at hchk
  simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hchk
  tauto

private lemma sinCoeff_neg (k : ℤ) (j : Fin 16) : sinCoeff (-k) j = -sinCoeff k j := by
  by_cases h0 : k = 0
  · subst h0
    fin_cases j <;> rfl
  · by_cases hp : 0 ≤ k
    · have hnp : ¬ (0 : ℤ) ≤ -k := by omega
      simp only [sinCoeff, hp, hnp, neg_neg, dite_true, dite_false]
      split_ifs <;> ring
    · have hnp : (0 : ℤ) ≤ -k := by omega
      simp only [sinCoeff, hp, hnp, dite_true, dite_false]
      split_ifs <;> ring

private lemma ms3_12 {α : Type*} (a b c : α) : ({a, b, c} : Multiset α) = {b, a, c} := by
  simp only [Multiset.insert_eq_cons]
  exact Multiset.cons_swap a b {c}

private lemma ms3_23 {α : Type*} (a b c : α) : ({a, b, c} : Multiset α) = {a, c, b} := by
  change a ::ₘ b ::ₘ c ::ₘ 0 = a ::ₘ c ::ₘ b ::ₘ 0
  rw [Multiset.cons_swap b c 0]

private lemma ms3_cases {α : Type*} {a b c x y z : α} (h : ({a, b, c} : Multiset α) = {x, y, z}) :
    (a = x ∧ b = y ∧ c = z) ∨ (a = x ∧ b = z ∧ c = y) ∨
    (a = y ∧ b = x ∧ c = z) ∨ (a = y ∧ b = z ∧ c = x) ∨
    (a = z ∧ b = x ∧ c = y) ∨ (a = z ∧ b = y ∧ c = x) := by
  have h2_cases : ∀ u v p q : α, ({u, v} : Multiset α) = {p, q} →
      (u = p ∧ v = q) ∨ (u = q ∧ v = p) := by
    intro u v p q hpq
    have hu : u ∈ ({p, q} : Multiset α) := by rw [← hpq]; simp
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hu
    rcases hu with hu | hu
    · left; refine ⟨hu, ?_⟩
      rw [hu] at hpq
      simpa [Multiset.insert_eq_cons] using hpq
    · right; refine ⟨hu, ?_⟩
      rw [hu, Multiset.pair_comm p q] at hpq
      simpa [Multiset.insert_eq_cons] using hpq
  have ha : a ∈ ({x, y, z} : Multiset α) := by rw [← h]; simp
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ha
  rcases ha with ha | ha | ha
  · have hbc : ({b, c} : Multiset α) = {y, z} := by
      rw [ha] at h; simpa [Multiset.insert_eq_cons] using h
    rcases h2_cases b c y z hbc with ⟨hb, hc⟩ | ⟨hb, hc⟩
    · left; exact ⟨ha, hb, hc⟩
    · right; left; exact ⟨ha, hb, hc⟩
  · have hbc : ({b, c} : Multiset α) = {x, z} := by
      rw [ha, ms3_12 x y z] at h; simpa [Multiset.insert_eq_cons] using h
    rcases h2_cases b c x z hbc with ⟨hb, hc⟩ | ⟨hb, hc⟩
    · right; right; left; exact ⟨ha, hb, hc⟩
    · right; right; right; left; exact ⟨ha, hb, hc⟩
  · have hbc : ({b, c} : Multiset α) = {x, y} := by
      rw [ha, ms3_23 x y z, ms3_12 x z y] at h; simpa [Multiset.insert_eq_cons] using h
    rcases h2_cases b c x y hbc with ⟨hb, hc⟩ | ⟨hb, hc⟩
    · right; right; right; right; left; exact ⟨ha, hb, hc⟩
    · right; right; right; right; right; exact ⟨ha, hb, hc⟩

private lemma classify_int_triple {k1 k2 k3 : ℤ}
    (h1 : -14 ≤ k1 ∧ k1 ≤ 14) (h2 : -14 ≤ k2 ∧ k2 ≤ 14) (h3 : -14 ≤ k3 ∧ k3 ≤ 14)
    (hb12 : |k1 + k2| < 10) (hb13 : |k1 + k3| < 10) (hb23 : |k2 + k3| < 10)
    (hzero : ∀ j : Fin 16, sinCoeff k1 j + sinCoeff k2 j + sinCoeff k3 j = 0) :
    (k1 = 0 ∧ k2 + k3 = 0) ∨ (k2 = 0 ∧ k1 + k3 = 0) ∨ (k3 = 0 ∧ k1 + k2 = 0) ∨
    ({k1, k2, k3} : Multiset ℤ) = {-9, 3, 5} ∨ ({k1, k2, k3} : Multiset ℤ) = {9, -3, -5} := by
  have hsorted : ∀ a b c : ℤ,
      (-14 ≤ a ∧ a ≤ 14) → (-14 ≤ b ∧ b ≤ 14) → (-14 ≤ c ∧ c ≤ 14) →
      |a + b| < 10 → |a + c| < 10 → |b + c| < 10 →
      a ≤ b → b ≤ c →
      (∀ j : Fin 16, sinCoeff a j + sinCoeff b j + sinCoeff c j = 0) →
      (b = 0 ∧ a + c = 0) ∨ (a = -9 ∧ b = 3 ∧ c = 5) ∨ (a = -5 ∧ b = -3 ∧ c = 9) := by
    intro a b c ha hb hc hab hac hbc hle1 hle2 hz
    by_cases hb0 : 0 ≤ b
    · rcases classify_reduced_int_triple ha.1 ha.2 hb.1 hb.2 hc.1 hc.2 hle1 hle2 hb0
          hab hac hbc hz with ht | hs
      · left; exact ht
      · right; left; exact hs
    · have hz' : ∀ j : Fin 16, sinCoeff (-c) j + sinCoeff (-b) j + sinCoeff (-a) j = 0 := by
        intro j; simp only [sinCoeff_neg]; linarith [hz j]
      rcases classify_reduced_int_triple (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega)
          (by rw [show -c + -b = -(b + c) by ring, abs_neg]; exact hbc)
          (by rw [show -c + -a = -(a + c) by ring, abs_neg]; exact hac)
          (by rw [show -b + -a = -(a + b) by ring, abs_neg]; exact hab)
          hz' with ht | hs
      · left; omega
      · right; right; omega
  have hperm : ∀ a b c : ℤ, ({k1, k2, k3} : Multiset ℤ) = {a, b, c} →
      (b = 0 ∧ a + c = 0) ∨ (a = -9 ∧ b = 3 ∧ c = 5) ∨ (a = -5 ∧ b = -3 ∧ c = 9) →
      (k1 = 0 ∧ k2 + k3 = 0) ∨ (k2 = 0 ∧ k1 + k3 = 0) ∨ (k3 = 0 ∧ k1 + k2 = 0) ∨
      ({k1, k2, k3} : Multiset ℤ) = {-9, 3, 5} ∨ ({k1, k2, k3} : Multiset ℤ) = {9, -3, -5} := by
    intro a b c hmeq hres
    rcases hres with ⟨hb0, hac⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have hsum_eq := congrArg Multiset.sum hmeq
      simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton] at hsum_eq
      have h0mem : (0 : ℤ) ∈ ({k1, k2, k3} : Multiset ℤ) := by
        rw [hmeq, hb0]; simp
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at h0mem
      rcases h0mem with h | h | h
      · left; exact ⟨h.symm, by omega⟩
      · right; left; exact ⟨h.symm, by omega⟩
      · right; right; left; exact ⟨h.symm, by omega⟩
    · right; right; right; left; exact hmeq
    · right; right; right; right
      rw [hmeq, ms3_23 (-5) (-3) 9, ms3_12 (-5) 9 (-3), ms3_23 9 (-5) (-3)]
  rcases le_total k1 k2 with h12 | h21
  · rcases le_total k2 k3 with h23 | h32
    · exact hperm k1 k2 k3 rfl (hsorted k1 k2 k3 h1 h2 h3 hb12 hb13 hb23 h12 h23 hzero)
    · rcases le_total k1 k3 with h13 | h31
      · exact hperm k1 k3 k2 (ms3_23 k1 k2 k3)
          (hsorted k1 k3 k2 h1 h3 h2 hb13 hb12 (by rwa [add_comm]) h13 h32
            (fun j => by linarith [hzero j]))
      · exact hperm k3 k1 k2 ((ms3_23 k1 k2 k3).trans (ms3_12 k1 k3 k2))
          (hsorted k3 k1 k2 h3 h1 h2 (by rwa [add_comm]) (by rwa [add_comm]) hb12 h31 h12
            (fun j => by linarith [hzero j]))
  · rcases le_total k1 k3 with h13 | h31
    · exact hperm k2 k1 k3 (ms3_12 k1 k2 k3)
        (hsorted k2 k1 k3 h2 h1 h3 (by rwa [add_comm]) hb23 hb13 h21 h13
          (fun j => by linarith [hzero j]))
    · rcases le_total k2 k3 with h23 | h32
      · exact hperm k2 k3 k1 ((ms3_12 k1 k2 k3).trans (ms3_23 k2 k1 k3))
          (hsorted k2 k3 k1 h2 h3 h1 hb23 (by rwa [add_comm]) (by rwa [add_comm]) h23 h31
            (fun j => by linarith [hzero j]))
      · exact hperm k3 k2 k1 (((ms3_12 k1 k2 k3).trans (ms3_23 k2 k1 k3)).trans (ms3_12 k2 k3 k1))
          (hsorted k3 k2 k1 h3 h2 h1 (by rwa [add_comm]) (by rwa [add_comm]) (by rwa [add_comm])
            h32 h21 (fun j => by linarith [hzero j]))

/-! ### Part 5: Combining all pieces and exact counting -/

private lemma classify_solution {n : ℕ} (hn : 1 ≤ n)
    (t : Fin (2 * n - 1) × Fin (2 * n - 1) × Fin (2 * n - 1))
    (hsol : ratio (2 * n - 1) t.1 * ratio (2 * n - 1) t.2.1 * ratio (2 * n - 1) t.2.2 = 1) :
    let a : ℕ := t.1.1 + 1
    let b : ℕ := t.2.1.1 + 1
    let c : ℕ := t.2.2.1 + 1
    ((a = n ∧ b + c = 2 * n) ∨ (b = n ∧ a + c = 2 * n) ∨ (c = n ∧ a + b = 2 * n)) ∨
    (5 ∣ n ∧ (({a, b, c} : Multiset ℕ) = {n / 5, 7 * (n / 5), 8 * (n / 5)} ∨
              ({a, b, c} : Multiset ℕ) = {2 * (n / 5), 3 * (n / 5), 9 * (n / 5)})) := by
  intro a b c
  let u : ℝ := ang n t.1
  let v : ℝ := ang n t.2.1
  let w : ℝ := ang n t.2.2
  have hsin : Real.sin (u + v - w) + Real.sin (u - v + w) + Real.sin (-u + v + w) = 0 :=
    (ratio_prod_eq_one_iff hn t).mp hsol
  let θ1 : ℝ := u + v - w
  let θ2 : ℝ := u - v + w
  let θ3 : ℝ := -u + v + w
  have ha_bd : 1 ≤ a ∧ a ≤ 2 * n - 1 := ⟨by omega, by omega⟩
  have hb_bd : 1 ≤ b ∧ b ≤ 2 * n - 1 := ⟨by omega, by omega⟩
  have hc_bd : 1 ≤ c ∧ c ≤ 2 * n - 1 := ⟨by omega, by omega⟩
  have hang_lt : ∀ i : Fin (2 * n - 1), |ang n i.1| < Real.pi / 6 := by
    intro i
    have hi1 : (-(n : ℤ)) < (i.1 + 1 : ℤ) - n := by omega
    have hi2 : (i.1 + 1 : ℤ) - n < (n : ℤ) := by omega
    have hdiff : |(i.1 + 1 : ℝ) - n| < n := by
      rw [abs_lt]
      exact ⟨by exact_mod_cast hi1, by exact_mod_cast hi2⟩
    have hn_pos : (0 : ℝ) < n := by positivity
    have hpi : 0 < Real.pi := Real.pi_pos
    have : |ang n i.1| = |(i.1 + 1 : ℝ) - n| * Real.pi / (6 * n) := by
      simp only [ang, abs_div, abs_mul, abs_of_pos hpi, abs_of_pos (by positivity : (0 : ℝ) < 6 * n)]
    rw [this, div_lt_iff₀ (by positivity)]
    nlinarith
  have hu_lt : |u| < Real.pi / 6 := hang_lt t.1
  have hv_lt : |v| < Real.pi / 6 := hang_lt t.2.1
  have hw_lt : |w| < Real.pi / 6 := hang_lt t.2.2
  have hθ1_lt : |θ1| < Real.pi / 2 := by
    rw [abs_lt] at hu_lt hv_lt hw_lt ⊢; constructor <;> dsimp only [θ1] <;> linarith
  have hθ2_lt : |θ2| < Real.pi / 2 := by
    rw [abs_lt] at hu_lt hv_lt hw_lt ⊢; constructor <;> dsimp only [θ2] <;> linarith
  have hθ3_lt : |θ3| < Real.pi / 2 := by
    rw [abs_lt] at hu_lt hv_lt hw_lt ⊢; constructor <;> dsimp only [θ3] <;> linarith
  have h12_lt : |θ1 + θ2| < Real.pi / 3 := by
    have : θ1 + θ2 = 2 * u := by dsimp only [θ1, θ2]; ring
    rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
  have h13_lt : |θ1 + θ3| < Real.pi / 3 := by
    have : θ1 + θ3 = 2 * v := by dsimp only [θ1, θ3]; ring
    rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
  have h23_lt : |θ2 + θ3| < Real.pi / 3 := by
    have : θ2 + θ3 = 2 * w := by dsimp only [θ2, θ3]; ring
    rw [this, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
  have hang_eq_zero : ∀ i : ℕ, ang n i = 0 → i + 1 = n := by
    intro i hi
    have hn_ne : (6 * (n : ℝ)) ≠ 0 := by positivity
    have h1 : ((i + 1 : ℝ) - n) * Real.pi = 0 := by
      have := congrArg (· * (6 * (n : ℝ))) hi
      dsimp only [ang] at this
      rw [div_mul_cancel₀ _ hn_ne, zero_mul] at this
      exact this
    have h2 : (i + 1 : ℝ) - n = 0 := (mul_eq_zero.mp h1).resolve_right Real.pi_ne_zero
    have h3 : ((i + 1 : ℕ) : ℝ) = (n : ℝ) := by push_cast; linarith
    exact_mod_cast h3
  have hang_add_zero : ∀ i j : ℕ, ang n i + ang n j = 0 → (i + 1) + (j + 1) = 2 * n := by
    intro i j hij
    have hn_ne : (6 * (n : ℝ)) ≠ 0 := by positivity
    have h1 : (((i + 1 : ℝ) - n) + ((j + 1 : ℝ) - n)) * Real.pi = 0 := by
      have := congrArg (· * (6 * (n : ℝ))) hij
      dsimp only [ang] at this
      rw [add_mul, div_mul_cancel₀ _ hn_ne, div_mul_cancel₀ _ hn_ne, zero_mul] at this
      linarith
    have h2 : ((i + 1 : ℝ) - n) + ((j + 1 : ℝ) - n) = 0 :=
      (mul_eq_zero.mp h1).resolve_right Real.pi_ne_zero
    have h3 : (((i + 1) + (j + 1) : ℕ) : ℝ) = ((2 * n : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast h3
  have htriv_of_θ :
      ((θ1 = 0 ∧ θ2 + θ3 = 0) ∨ (θ2 = 0 ∧ θ1 + θ3 = 0) ∨ (θ3 = 0 ∧ θ1 + θ2 = 0)) →
      ((a = n ∧ b + c = 2 * n) ∨ (b = n ∧ a + c = 2 * n) ∨ (c = n ∧ a + b = 2 * n)) := by
    rintro (⟨hA, hB⟩ | ⟨hA, hB⟩ | ⟨hA, hB⟩)
    · right; right
      exact ⟨hang_eq_zero t.2.2.1 (by dsimp only [θ2, θ3] at hB; linarith),
        hang_add_zero t.1.1 t.2.1.1 (by dsimp only [θ1] at hA; linarith)⟩
    · right; left
      exact ⟨hang_eq_zero t.2.1.1 (by dsimp only [θ1, θ3] at hB; linarith),
        hang_add_zero t.1.1 t.2.2.1 (by dsimp only [θ2] at hA; linarith)⟩
    · left
      exact ⟨hang_eq_zero t.1.1 (by dsimp only [θ1, θ2] at hB; linarith),
        hang_add_zero t.2.1.1 t.2.2.1 (by dsimp only [θ3] at hA; linarith)⟩
  let f : Fin 6 → ℂ :=
    ![Complex.exp ((θ1 : ℂ) * Complex.I), -(Complex.exp ((θ1 : ℂ) * Complex.I))⁻¹,
      Complex.exp ((θ2 : ℂ) * Complex.I), -(Complex.exp ((θ2 : ℂ) * Complex.I))⁻¹,
      Complex.exp ((θ3 : ℂ) * Complex.I), -(Complex.exp ((θ3 : ℂ) * Complex.I))⁻¹]
  by_cases hprop : ∃ S : Finset (Fin 6), S.Nonempty ∧ S ≠ Finset.univ ∧ ∑ i ∈ S, f i = 0
  · rcases hprop with ⟨S, hSne, hSnu, hSsum⟩
    left
    exact htriv_of_θ (six_root_proper_subsum hθ1_lt hθ2_lt hθ3_lt h12_lt h13_lt h23_lt hsin S hSne hSnu hSsum)
  · push Not at hprop
    -- Apply Mann's theorem to g i = f i / f 0
    have hf0_ne : f 0 ≠ 0 := Complex.exp_ne_zero _
    let g : Fin 6 → ℂ := fun i => f i / f 0
    have hg0 : g ⟨0, by norm_num⟩ = 1 := div_self hf0_ne
    have hf_full : ∑ i : Fin 6, f i = 0 := by
      rw [Fin.sum_univ_six]
      simp only [f, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      have hs : (Real.sin θ1 : ℂ) + (Real.sin θ2 : ℂ) + (Real.sin θ3 : ℂ) = 0 := by
        exact_mod_cast hsin
      linear_combination exp_sub_inv_eq_sin θ1 + exp_sub_inv_eq_sin θ2 +
        exp_sub_inv_eq_sin θ3 + 2 * Complex.I * hs
    have hg_sum : ∑ i : Fin 6, g i = 0 := by
      simp only [g, ← Finset.sum_div, hf_full, zero_div]
    have hg_min : ∀ S : Finset (Fin 6), S.Nonempty → S ≠ Finset.univ → ∑ i ∈ S, g i ≠ 0 := by
      intro S hSne hSnu h0
      apply hprop S hSne hSnu
      simp only [g, ← Finset.sum_div] at h0
      exact (div_eq_zero_iff.mp h0).resolve_right hf0_ne
    have hexp_12n : ∀ (z : ℤ), (Complex.exp (((z : ℝ) * Real.pi / (6 * n) : ℝ) * Complex.I)) ^ (12 * n) = 1 := by
      intro z
      rw [← Complex.exp_nat_mul]
      have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have harg : (12 * n : ℕ) * (((z : ℝ) * Real.pi / (6 * n) : ℝ) * Complex.I) =
          (z : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast
        field_simp [hn_ne]
        ring
      rw [harg]
      exact Complex.exp_int_mul_two_pi_mul_I z
    have hθ_form : ∀ (x : ℝ), (∃ z : ℤ, x = (z : ℝ) * Real.pi / (6 * n)) →
        (Complex.exp ((x : ℂ) * Complex.I)) ^ (12 * n) = 1 := by
      rintro x ⟨z, rfl⟩
      exact hexp_12n z
    have hf_pow : ∀ i : Fin 6, (f i) ^ (12 * n) = 1 := by
      have h1_pow : (Complex.exp ((θ1 : ℂ) * Complex.I)) ^ (12 * n) = 1 :=
        hθ_form θ1 ⟨(a : ℤ) + b - c - n, by dsimp only [θ1, u, v, w, ang, a, b, c]; push_cast; ring⟩
      have h2_pow : (Complex.exp ((θ2 : ℂ) * Complex.I)) ^ (12 * n) = 1 :=
        hθ_form θ2 ⟨(a : ℤ) - b + c - n, by dsimp only [θ2, u, v, w, ang, a, b, c]; push_cast; ring⟩
      have h3_pow : (Complex.exp ((θ3 : ℂ) * Complex.I)) ^ (12 * n) = 1 :=
        hθ_form θ3 ⟨-(a : ℤ) + b + c - n, by dsimp only [θ3, u, v, w, ang, a, b, c]; push_cast; ring⟩
      have hneg_even : ∀ z : ℂ, z ^ (12 * n) = 1 → (-z⁻¹) ^ (12 * n) = 1 := by
        intro z hz
        rw [neg_pow, inv_pow, hz, inv_one, mul_one]
        have hev : Even (12 * n) := ⟨6 * n, by ring⟩
        exact hev.neg_one_pow
      intro i
      fin_cases i
      · exact h1_pow
      · exact hneg_even _ h1_pow
      · exact h2_pow
      · exact hneg_even _ h2_pow
      · exact h3_pow
      · exact hneg_even _ h3_pow
    have hg_root : ∃ M : ℕ, 0 < M ∧ ∀ i : Fin 6, (g i) ^ M = 1 :=
      ⟨12 * n, by omega, fun i => by simp only [g, div_pow, hf_pow i, hf_pow 0, div_one]⟩
    rcases mann_minimal_order (by norm_num) g hg0 hg_root hg_sum hg_min with
      ⟨m, hm_pos, hm_pow, hm_sq, hm_le⟩
    have hm30 : m ∣ 30 := dvd_thirty_of_sqfree_primes_le_six hm_pos hm_sq hm_le
    have hg30 : ∀ i : Fin 6, (g i) ^ 30 = 1 := by
      intro i
      rcases hm30 with ⟨q, hq⟩
      rw [hq, pow_mul, hm_pow i, one_pow]
    have hζ1_60 : (Complex.exp ((θ1 : ℂ) * Complex.I)) ^ 60 = 1 := by
      have h1 := hg30 1
      simp only [g, f, Matrix.cons_val_one, Matrix.cons_val_zero] at h1
      have hev : (-1 : ℂ) ^ 30 = 1 := by norm_num
      have hne : Complex.exp ((θ1 : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
      have hinv : ((Complex.exp ((θ1 : ℂ) * Complex.I)) ^ 60)⁻¹ = 1 := by
        have hstep : (-((Complex.exp ((θ1 : ℂ) * Complex.I))⁻¹) /
            Complex.exp ((θ1 : ℂ) * Complex.I)) ^ 30 =
            (-1 : ℂ) ^ 30 * ((Complex.exp ((θ1 : ℂ) * Complex.I)) ^ 60)⁻¹ := by
          have : -((Complex.exp ((θ1 : ℂ) * Complex.I))⁻¹) / Complex.exp ((θ1 : ℂ) * Complex.I) =
              (-1 : ℂ) * ((Complex.exp ((θ1 : ℂ) * Complex.I)) ^ 2)⁻¹ := by
            field_simp [hne]
          rw [this, mul_pow, inv_pow, ← pow_mul]
        rw [hstep, hev, one_mul] at h1
        exact h1
      exact inv_eq_one.mp hinv
    have hζ2_60 : (Complex.exp ((θ2 : ℂ) * Complex.I)) ^ 60 = 1 := by
      have h2 := hg30 2
      simp only [g, f, Matrix.cons_val_zero, Matrix.cons_val] at h2
      have h2' : (Complex.exp ((θ2 : ℂ) * Complex.I) / Complex.exp ((θ1 : ℂ) * Complex.I)) ^ 60 = 1 := by
        rw [show (60 : ℕ) = 30 * 2 by norm_num, pow_mul, h2, one_pow]
      rw [div_pow, hζ1_60, div_one] at h2'
      exact h2'
    have hζ3_60 : (Complex.exp ((θ3 : ℂ) * Complex.I)) ^ 60 = 1 := by
      have h4 := hg30 4
      simp only [g, f, Matrix.cons_val_zero, Matrix.cons_val] at h4
      have h4' : (Complex.exp ((θ3 : ℂ) * Complex.I) / Complex.exp ((θ1 : ℂ) * Complex.I)) ^ 60 = 1 := by
        rw [show (60 : ℕ) = 30 * 2 by norm_num, pow_mul, h4, one_pow]
      rw [div_pow, hζ1_60, div_one] at h4'
      exact h4'
    have hex_k : ∀ θ : ℝ, (Complex.exp ((θ : ℂ) * Complex.I)) ^ 60 = 1 →
        ∃ k : ℤ, θ = (k : ℝ) * Real.pi / 30 := by
      intro θ h60
      rw [← Complex.exp_nat_mul] at h60
      rcases Complex.exp_eq_one_iff.mp h60 with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      have hI : Complex.I ≠ 0 := Complex.I_ne_zero
      have hmul : ((60 : ℕ) : ℂ) * (θ : ℂ) = (k : ℂ) * (2 * Real.pi) := by
        apply mul_right_cancel₀ hI
        linear_combination hk
      have hre' : 60 * θ = (k : ℝ) * (2 * Real.pi) := by
        have hcast : ((60 * θ : ℝ) : ℂ) = (((k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) := by
          push_cast; simpa using hmul
        exact Complex.ofReal_injective hcast
      linarith
    rcases hex_k θ1 hζ1_60 with ⟨k1, hk1⟩
    rcases hex_k θ2 hζ2_60 with ⟨k2, hk2⟩
    rcases hex_k θ3 hζ3_60 with ⟨k3, hk3⟩
    have hpi : 0 < Real.pi := Real.pi_pos
    have hk_bd : ∀ (k : ℤ) (θ : ℝ), θ = (k : ℝ) * Real.pi / 30 → |θ| < Real.pi / 2 →
        -14 ≤ k ∧ k ≤ 14 := by
      intro k θ hθ hlt
      rw [hθ, abs_div, abs_mul, abs_of_pos hpi, abs_of_pos (by norm_num : (0 : ℝ) < 30)] at hlt
      have habs : |(k : ℝ)| < 15 := by nlinarith
      rw [abs_lt] at habs
      have h1 : (-15 : ℤ) < k := by exact_mod_cast habs.1
      have h2 : k < (15 : ℤ) := by exact_mod_cast habs.2
      omega
    have hk_sum_bd : ∀ (ka kb : ℤ) (θa θb : ℝ),
        θa = (ka : ℝ) * Real.pi / 30 → θb = (kb : ℝ) * Real.pi / 30 →
        |θa + θb| < Real.pi / 3 → |ka + kb| < 10 := by
      intro ka kb θa θb ha hb hlt
      have hsum' : θa + θb = ((ka + kb : ℤ) : ℝ) * Real.pi / 30 := by
        rw [ha, hb]; push_cast; ring
      rw [hsum', abs_div, abs_mul, abs_of_pos hpi, abs_of_pos (by norm_num : (0 : ℝ) < 30)] at hlt
      have habs : |((ka + kb : ℤ) : ℝ)| < 10 := by nlinarith
      exact_mod_cast habs
    have hk1_bd := hk_bd k1 θ1 hk1 hθ1_lt
    have hk2_bd := hk_bd k2 θ2 hk2 hθ2_lt
    have hk3_bd := hk_bd k3 θ3 hk3 hθ3_lt
    have hk12_bd := hk_sum_bd k1 k2 θ1 θ2 hk1 hk2 h12_lt
    have hk13_bd := hk_sum_bd k1 k3 θ1 θ3 hk1 hk3 h13_lt
    have hk23_bd := hk_sum_bd k2 k3 θ2 θ3 hk2 hk3 h23_lt
    -- Evaluate at primitive 60th root w60 = exp(pi * I / 30)
    let w60 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 60)
    have hw60 : IsPrimitiveRoot w60 60 := Complex.isPrimitiveRoot_exp 60 (by norm_num)
    have hw60_pow : ∀ (k : ℤ), -14 ≤ k ∧ k ≤ 14 →
        w60 ^ (15 + k).toNat - w60 ^ (15 - k).toNat =
          w60 ^ 15 * (Complex.exp (((k : ℝ) * Real.pi / 30 : ℝ) * Complex.I) -
            (Complex.exp (((k : ℝ) * Real.pi / 30 : ℝ) * Complex.I))⁻¹) := by
      intro k hk
      have h1 : w60 ^ (15 + k).toNat =
          w60 ^ 15 * Complex.exp (((k : ℝ) * Real.pi / 30 : ℝ) * Complex.I) := by
        simp only [w60, ← Complex.exp_nat_mul, ← Complex.exp_add]
        congr 1
        have hto : ((15 + k).toNat : ℂ) = 15 + (k : ℂ) := by
          have : ((15 + k).toNat : ℤ) = 15 + k := Int.toNat_of_nonneg (by omega)
          exact_mod_cast this
        rw [hto]
        push_cast
        ring
      have h2 : w60 ^ (15 - k).toNat =
          w60 ^ 15 * (Complex.exp (((k : ℝ) * Real.pi / 30 : ℝ) * Complex.I))⁻¹ := by
        rw [← Complex.exp_neg]
        simp only [w60, ← Complex.exp_nat_mul, ← Complex.exp_add]
        congr 1
        have hto : ((15 - k).toNat : ℂ) = 15 - (k : ℂ) := by
          have : ((15 - k).toNat : ℤ) = 15 - k := Int.toNat_of_nonneg (by omega)
          exact_mod_cast this
        rw [hto]
        push_cast
        ring
      rw [h1, h2, ← mul_sub]
    have hsum_w60 : ∑ j : Fin 16,
        (((sinCoeff k1 j + sinCoeff k2 j + sinCoeff k3 j : ℤ) : ℂ) * w60 ^ j.1) = 0 := by
      have hsplit : ∑ j : Fin 16,
          (((sinCoeff k1 j + sinCoeff k2 j + sinCoeff k3 j : ℤ) : ℂ) * w60 ^ j.1) =
          (∑ j : Fin 16, ((sinCoeff k1 j : ℤ) : ℂ) * w60 ^ j.1) +
          (∑ j : Fin 16, ((sinCoeff k2 j : ℤ) : ℂ) * w60 ^ j.1) +
          (∑ j : Fin 16, ((sinCoeff k3 j : ℤ) : ℂ) * w60 ^ j.1) := by
        simp only [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _; push_cast; ring
      rw [hsplit, eval_sinCoeff w60 hw60 hk1_bd, eval_sinCoeff w60 hw60 hk2_bd,
        eval_sinCoeff w60 hw60 hk3_bd, hw60_pow k1 hk1_bd, hw60_pow k2 hk2_bd, hw60_pow k3 hk3_bd,
        ← hk1, ← hk2, ← hk3]
      have hs : (Real.sin θ1 : ℂ) + (Real.sin θ2 : ℂ) + (Real.sin θ3 : ℂ) = 0 := by
        exact_mod_cast hsin
      linear_combination w60 ^ 15 * (exp_sub_inv_eq_sin θ1 + exp_sub_inv_eq_sin θ2 +
        exp_sub_inv_eq_sin θ3 + 2 * Complex.I * hs)
    have hcoeff0 : ∀ j : Fin 16, sinCoeff k1 j + sinCoeff k2 j + sinCoeff k3 j = 0 :=
      coeff_zero_of_aeval_w60 w60 hw60 (fun j => sinCoeff k1 j + sinCoeff k2 j + sinCoeff k3 j)
        hsum_w60
    have hrel_of_two : ∀ (x : ℕ) (s : ℤ),
        2 * ang n x = (s : ℝ) * Real.pi / 30 → 10 * (((x + 1 : ℕ) : ℤ) - n) = s * n := by
      intro x s hs
      have hn_ne : (6 * (n : ℝ)) ≠ 0 := by positivity
      have hmul : (10 * ((x + 1 : ℝ) - n) - (s : ℝ) * n) * Real.pi = 0 := by
        have h1 := congrArg (· * (30 * (n : ℝ))) hs
        dsimp only [ang] at h1
        have h2 : 2 * (((x + 1 : ℝ) - n) * Real.pi / (6 * n)) * (30 * n) =
            10 * ((x + 1 : ℝ) - n) * Real.pi := by
          have : (n : ℝ) ≠ 0 := by positivity
          field_simp [this]; ring
        have h3 : (s : ℝ) * Real.pi / 30 * (30 * n) = (s : ℝ) * n * Real.pi := by ring
        linarith
      have hreal : 10 * (((x + 1 : ℕ) : ℝ) - n) = (s : ℝ) * n := by
        have := (mul_eq_zero.mp hmul).resolve_right Real.pi_ne_zero
        push_cast; linarith
      exact_mod_cast hreal
    have hrel_a : 10 * ((a : ℤ) - n) = (k1 + k2) * n := by
      apply hrel_of_two t.1.1 (k1 + k2)
      have : 2 * u = θ1 + θ2 := by dsimp only [θ1, θ2]; ring
      change 2 * u = ((k1 + k2 : ℤ) : ℝ) * Real.pi / 30
      rw [this, hk1, hk2]; push_cast; ring
    have hrel_b : 10 * ((b : ℤ) - n) = (k1 + k3) * n := by
      apply hrel_of_two t.2.1.1 (k1 + k3)
      have : 2 * v = θ1 + θ3 := by dsimp only [θ1, θ3]; ring
      change 2 * v = ((k1 + k3 : ℤ) : ℝ) * Real.pi / 30
      rw [this, hk1, hk3]; push_cast; ring
    have hrel_c : 10 * ((c : ℤ) - n) = (k2 + k3) * n := by
      apply hrel_of_two t.2.2.1 (k2 + k3)
      have : 2 * w = θ2 + θ3 := by dsimp only [θ2, θ3]; ring
      change 2 * w = ((k2 + k3 : ℤ) : ℝ) * Real.pi / 30
      rw [this, hk2, hk3]; push_cast; ring
    rcases classify_int_triple hk1_bd hk2_bd hk3_bd hk12_bd hk13_bd hk23_bd hcoeff0 with
      ⟨h10, h230⟩ | ⟨h20, h130⟩ | ⟨h30, h120⟩ | hsp1 | hsp2
    · left; exact htriv_of_θ (Or.inl ⟨by rw [hk1, h10]; simp, by
        rw [hk2, hk3]
        have hs : (k2 : ℝ) + k3 = 0 := by exact_mod_cast h230
        linear_combination (Real.pi / 30) * hs⟩)
    · left; exact htriv_of_θ (Or.inr (Or.inl ⟨by rw [hk2, h20]; simp, by
        rw [hk1, hk3]
        have hs : (k1 : ℝ) + k3 = 0 := by exact_mod_cast h130
        linear_combination (Real.pi / 30) * hs⟩))
    · left; exact htriv_of_θ (Or.inr (Or.inr ⟨by rw [hk3, h30]; simp, by
        rw [hk1, hk2]
        have hs : (k1 : ℝ) + k2 = 0 := by exact_mod_cast h120
        linear_combination (Real.pi / 30) * hs⟩))
    · right
      have hpair_ms : ({k1 + k2, k1 + k3, k2 + k3} : Multiset ℤ) = {-6, -4, 8} := by
        rcases ms3_cases hsp1 with
          ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
          ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · norm_num
        · norm_num; exact ms3_12 (-4) (-6) 8
        · norm_num; exact Multiset.pair_comm 8 (-4)
        · norm_num; exact (ms3_12 8 (-6) (-4)).trans (ms3_23 (-6) 8 (-4))
        · norm_num; exact (ms3_23 (-4) 8 (-6)).trans (ms3_12 (-4) (-6) 8)
        · norm_num; exact ((ms3_12 8 (-4) (-6)).trans (ms3_23 (-4) 8 (-6))).trans (ms3_12 (-4) (-6) 8)
      have h5n : 5 ∣ n := by
        have hmem8 : (8 : ℤ) ∈ ({k1 + k2, k1 + k3, k2 + k3} : Multiset ℤ) := by
          rw [hpair_ms]; simp
        simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hmem8
        rcases hmem8 with h | h | h
        · rw [← h] at hrel_a; omega
        · rw [← h] at hrel_b; omega
        · rw [← h] at hrel_c; omega
      refine ⟨h5n, Or.inr ?_⟩
      set r := n / 5
      have hnr : n = 5 * r := (Nat.mul_div_cancel' h5n).symm
      have hmap2 := congrArg (Multiset.map (fun s : ℤ => (5 + s / 2).toNat * r)) hpair_ms
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton] at hmap2
      have hto2 : Int.toNat 2 = 2 := rfl
      have hto3 : Int.toNat 3 = 3 := rfl
      have hto9 : Int.toNat 9 = 9 := rfl
      have hfa : (5 + (k1 + k2) / 2).toNat * r = a := by
        have hmem : k1 + k2 ∈ ({-6, -4, 8} : Multiset ℤ) := by rw [← hpair_ms]; simp
        simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hmem
        rcases hmem with h | h | h <;> (rw [h] at hrel_a ⊢; norm_num; simp only [hto2, hto3, hto9]; omega)
      have hfb : (5 + (k1 + k3) / 2).toNat * r = b := by
        have hmem : k1 + k3 ∈ ({-6, -4, 8} : Multiset ℤ) := by rw [← hpair_ms]; simp
        simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hmem
        rcases hmem with h | h | h <;> (rw [h] at hrel_b ⊢; norm_num; simp only [hto2, hto3, hto9]; omega)
      have hfc : (5 + (k2 + k3) / 2).toNat * r = c := by
        have hmem : k2 + k3 ∈ ({-6, -4, 8} : Multiset ℤ) := by rw [← hpair_ms]; simp
        simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hmem
        rcases hmem with h | h | h <;> (rw [h] at hrel_c ⊢; norm_num; simp only [hto2, hto3, hto9]; omega)
      rw [hfa, hfb, hfc] at hmap2
      simpa [r] using hmap2
    · right
      have hpair_ms : ({k1 + k2, k1 + k3, k2 + k3} : Multiset ℤ) = {-8, 4, 6} := by
        rcases ms3_cases hsp2 with
          ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
          ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
        · norm_num; exact (ms3_23 6 4 (-8)).trans ((ms3_12 6 (-8) 4).trans (ms3_23 (-8) 6 4))
        · norm_num; exact (ms3_23 4 6 (-8)).trans (ms3_12 4 (-8) 6)
        · norm_num; exact (ms3_12 6 (-8) 4).trans (ms3_23 (-8) 6 4)
        · norm_num; exact Multiset.pair_comm 6 4
        · norm_num; exact ms3_12 4 (-8) 6
        · norm_num
      have h5n : 5 ∣ n := by
        have hmem8 : (-8 : ℤ) ∈ ({k1 + k2, k1 + k3, k2 + k3} : Multiset ℤ) := by
          rw [hpair_ms]; simp
        simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hmem8
        rcases hmem8 with h | h | h
        · rw [← h] at hrel_a; omega
        · rw [← h] at hrel_b; omega
        · rw [← h] at hrel_c; omega
      refine ⟨h5n, Or.inl ?_⟩
      set r := n / 5
      have hnr : n = 5 * r := (Nat.mul_div_cancel' h5n).symm
      have hmap2 := congrArg (Multiset.map (fun s : ℤ => (5 + s / 2).toNat * r)) hpair_ms
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton] at hmap2
      have hto7 : Int.toNat 7 = 7 := rfl
      have hto8 : Int.toNat 8 = 8 := rfl
      have hfa : (5 + (k1 + k2) / 2).toNat * r = a := by
        have hmem : k1 + k2 ∈ ({-8, 4, 6} : Multiset ℤ) := by rw [← hpair_ms]; simp
        simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hmem
        rcases hmem with h | h | h <;> (rw [h] at hrel_a ⊢; norm_num; (try simp only [hto7, hto8]); omega)
      have hfb : (5 + (k1 + k3) / 2).toNat * r = b := by
        have hmem : k1 + k3 ∈ ({-8, 4, 6} : Multiset ℤ) := by rw [← hpair_ms]; simp
        simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hmem
        rcases hmem with h | h | h <;> (rw [h] at hrel_b ⊢; norm_num; (try simp only [hto7, hto8]); omega)
      have hfc : (5 + (k2 + k3) / 2).toNat * r = c := by
        have hmem : k2 + k3 ∈ ({-8, 4, 6} : Multiset ℤ) := by rw [← hpair_ms]; simp
        simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hmem
        rcases hmem with h | h | h <;> (rw [h] at hrel_c ⊢; norm_num; (try simp only [hto7, hto8]); omega)
      rw [hfa, hfb, hfc] at hmap2
      simpa [r] using hmap2

private lemma sporadic_sin_zero :
    Real.sin (-(9 : ℝ) * Real.pi / 30) + Real.sin ((3 : ℝ) * Real.pi / 30) +
      Real.sin ((5 : ℝ) * Real.pi / 30) = 0 := by
  let w60 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 60)
  have hw60 : IsPrimitiveRoot w60 60 := Complex.isPrimitiveRoot_exp 60 (by norm_num)
  have h1 : evalList w60 (sinVecNat ⟨9, by norm_num⟩) = w60 ^ 24 - w60 ^ 6 :=
    evalList_sinVecNat w60 hw60 ⟨9, by norm_num⟩
  have h2 : evalList w60 (sinVecNat ⟨3, by norm_num⟩) = w60 ^ 18 - w60 ^ 12 :=
    evalList_sinVecNat w60 hw60 ⟨3, by norm_num⟩
  have h3 : evalList w60 (sinVecNat ⟨5, by norm_num⟩) = w60 ^ 20 - w60 ^ 10 :=
    evalList_sinVecNat w60 hw60 ⟨5, by norm_num⟩
  have hvec : -evalList w60 (sinVecNat ⟨9, by norm_num⟩) +
      evalList w60 (sinVecNat ⟨3, by norm_num⟩) +
      evalList w60 (sinVecNat ⟨5, by norm_num⟩) = 0 := by
    simp only [evalList, sinVecNat, Fin.sum_univ_succ, Fin.sum_univ_zero, List.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
      Fin.val_zero, Fin.val_succ, Int.cast_zero, Int.cast_one, Int.cast_neg,
      zero_mul, one_mul, neg_mul, add_zero, zero_add, pow_zero, pow_one]
    ring
  rw [h1, h2, h3] at hvec
  have hpow : ∀ (k : ℤ), -14 ≤ k ∧ k ≤ 14 →
      w60 ^ (15 + k).toNat - w60 ^ (15 - k).toNat =
        w60 ^ 15 * (2 * Complex.I * (Real.sin ((k : ℝ) * Real.pi / 30) : ℂ)) := by
    intro k hk
    rw [← exp_sub_inv_eq_sin ((k : ℝ) * Real.pi / 30)]
    have ha : w60 ^ (15 + k).toNat =
        w60 ^ 15 * Complex.exp ((((k : ℝ) * Real.pi / 30 : ℝ) : ℂ) * Complex.I) := by
      simp only [w60, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      have hto : ((15 + k).toNat : ℂ) = 15 + (k : ℂ) := by
        have : ((15 + k).toNat : ℤ) = 15 + k := Int.toNat_of_nonneg (by omega)
        exact_mod_cast this
      rw [hto]; push_cast; ring
    have hb : w60 ^ (15 - k).toNat =
        w60 ^ 15 * (Complex.exp ((((k : ℝ) * Real.pi / 30 : ℝ) : ℂ) * Complex.I))⁻¹ := by
      rw [← Complex.exp_neg]
      simp only [w60, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      have hto : ((15 - k).toNat : ℂ) = 15 - (k : ℂ) := by
        have : ((15 - k).toNat : ℤ) = 15 - k := Int.toNat_of_nonneg (by omega)
        exact_mod_cast this
      rw [hto]; push_cast; ring
    rw [ha, hb, ← mul_sub]
  have hp9 := hpow (-9) (by omega)
  have hp3 := hpow 3 (by omega)
  have hp5 := hpow 5 (by omega)
  rw [show (15 + (-9 : ℤ)).toNat = 6 by decide, show (15 - (-9 : ℤ)).toNat = 24 by decide,
    show (((-9 : ℤ) : ℝ) * Real.pi / 30) = -(9 : ℝ) * Real.pi / 30 by push_cast; ring] at hp9
  rw [show (15 + (3 : ℤ)).toNat = 18 by decide, show (15 - (3 : ℤ)).toNat = 12 by decide,
    show (((3 : ℤ) : ℝ) * Real.pi / 30) = (3 : ℝ) * Real.pi / 30 by push_cast; ring] at hp3
  rw [show (15 + (5 : ℤ)).toNat = 20 by decide, show (15 - (5 : ℤ)).toNat = 10 by decide,
    show (((5 : ℤ) : ℝ) * Real.pi / 30) = (5 : ℝ) * Real.pi / 30 by push_cast; ring] at hp5
  have hmul0 : w60 ^ 15 * (2 * Complex.I *
      ((Real.sin (-(9 : ℝ) * Real.pi / 30) + Real.sin ((3 : ℝ) * Real.pi / 30) +
        Real.sin ((5 : ℝ) * Real.pi / 30) : ℝ) : ℂ)) = 0 := by
    rw [Complex.ofReal_add, Complex.ofReal_add]
    linear_combination hvec - hp9 - hp3 - hp5
  have hne : w60 ^ 15 * (2 * Complex.I) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Complex.exp_ne_zero _)) (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  have hc0 : ((Real.sin (-(9 : ℝ) * Real.pi / 30) + Real.sin ((3 : ℝ) * Real.pi / 30) +
      Real.sin ((5 : ℝ) * Real.pi / 30) : ℝ) : ℂ) = 0 := by
    apply mul_left_cancel₀ hne
    linear_combination hmul0
  exact_mod_cast hc0

private lemma is_solution_iff {n : ℕ} (hn : 1 ≤ n)
    (t : Fin (2 * n - 1) × Fin (2 * n - 1) × Fin (2 * n - 1)) :
    ratio (2 * n - 1) t.1 * ratio (2 * n - 1) t.2.1 * ratio (2 * n - 1) t.2.2 = 1 ↔
      let a : ℕ := t.1.1 + 1
      let b : ℕ := t.2.1.1 + 1
      let c : ℕ := t.2.2.1 + 1
      ((a = n ∧ b + c = 2 * n) ∨ (b = n ∧ a + c = 2 * n) ∨ (c = n ∧ a + b = 2 * n)) ∨
      (5 ∣ n ∧ (({a, b, c} : Multiset ℕ) = {n / 5, 7 * (n / 5), 8 * (n / 5)} ∨
                ({a, b, c} : Multiset ℕ) = {2 * (n / 5), 3 * (n / 5), 9 * (n / 5)})) := by
  constructor
  · exact classify_solution hn t
  · intro h
    rw [ratio_prod_eq_one_iff hn t]
    simp only [ang]
    let a : ℕ := t.1.1 + 1
    let b : ℕ := t.2.1.1 + 1
    let c : ℕ := t.2.2.1 + 1
    have ha_c : (t.1.1 : ℝ) + 1 = (a : ℝ) := by dsimp [a]; push_cast; rfl
    have hb_c : (t.2.1.1 : ℝ) + 1 = (b : ℝ) := by dsimp [b]; push_cast; rfl
    have hc_c : (t.2.2.1 : ℝ) + 1 = (c : ℝ) := by dsimp [c]; push_cast; rfl
    rw [ha_c, hb_c, hc_c]
    have hn_ne : (n : ℝ) ≠ 0 := by positivity
    rcases h with (⟨ha, hbc⟩ | ⟨hb, hac⟩ | ⟨hc, hab⟩) | ⟨h5n, hsp⟩
    · have ha' : (a : ℝ) = n := by exact_mod_cast ha
      have hbc' : (b : ℝ) + c = 2 * n := by exact_mod_cast hbc
      have h1 : (((a : ℝ) - n) * Real.pi / (6 * n) + ((b : ℝ) - n) * Real.pi / (6 * n) -
          ((c : ℝ) - n) * Real.pi / (6 * n)) =
          -((((a : ℝ) - n) * Real.pi / (6 * n) - ((b : ℝ) - n) * Real.pi / (6 * n) +
          ((c : ℝ) - n) * Real.pi / (6 * n))) := by
        rw [ha']; field_simp [hn_ne]; ring
      have h3 : (-(((a : ℝ) - n) * Real.pi / (6 * n)) + ((b : ℝ) - n) * Real.pi / (6 * n) +
          ((c : ℝ) - n) * Real.pi / (6 * n)) = 0 := by
        rw [ha']; field_simp [hn_ne]; linear_combination Real.pi * hbc'
      rw [h1, h3, Real.sin_neg, Real.sin_zero]; ring
    · have hb' : (b : ℝ) = n := by exact_mod_cast hb
      have hac' : (a : ℝ) + c = 2 * n := by exact_mod_cast hac
      have h1 : (((a : ℝ) - n) * Real.pi / (6 * n) + ((b : ℝ) - n) * Real.pi / (6 * n) -
          ((c : ℝ) - n) * Real.pi / (6 * n)) =
          -(-(((a : ℝ) - n) * Real.pi / (6 * n)) + ((b : ℝ) - n) * Real.pi / (6 * n) +
          ((c : ℝ) - n) * Real.pi / (6 * n)) := by
        rw [hb']; field_simp [hn_ne]; ring
      have h2 : (((a : ℝ) - n) * Real.pi / (6 * n) - ((b : ℝ) - n) * Real.pi / (6 * n) +
          ((c : ℝ) - n) * Real.pi / (6 * n)) = 0 := by
        rw [hb']; field_simp [hn_ne]; linear_combination Real.pi * hac'
      rw [h1, h2, Real.sin_neg, Real.sin_zero]; ring
    · have hc' : (c : ℝ) = n := by exact_mod_cast hc
      have hab' : (a : ℝ) + b = 2 * n := by exact_mod_cast hab
      have h1 : (((a : ℝ) - n) * Real.pi / (6 * n) + ((b : ℝ) - n) * Real.pi / (6 * n) -
          ((c : ℝ) - n) * Real.pi / (6 * n)) = 0 := by
        rw [hc']; field_simp [hn_ne]; linear_combination Real.pi * hab'
      have h2 : (((a : ℝ) - n) * Real.pi / (6 * n) - ((b : ℝ) - n) * Real.pi / (6 * n) +
          ((c : ℝ) - n) * Real.pi / (6 * n)) =
          -(-(((a : ℝ) - n) * Real.pi / (6 * n)) + ((b : ℝ) - n) * Real.pi / (6 * n) +
          ((c : ℝ) - n) * Real.pi / (6 * n)) := by
        rw [hc']; field_simp [hn_ne]; ring
      rw [h1, h2, Real.sin_neg, Real.sin_zero]; ring
    · set r := n / 5
      have hnr : (n : ℝ) = 5 * r := by exact_mod_cast (Nat.mul_div_cancel' h5n).symm
      have hr_ne : (r : ℝ) ≠ 0 := by
        have : 0 < r := Nat.div_pos (Nat.le_of_dvd (by omega) h5n) (by norm_num)
        positivity
      have hsp_zero_neg : Real.sin ((9 : ℝ) * Real.pi / 30) + Real.sin (-(3 : ℝ) * Real.pi / 30) +
          Real.sin (-(5 : ℝ) * Real.pi / 30) = 0 := by
        have h := sporadic_sin_zero
        have s1 : Real.sin (-(9 : ℝ) * Real.pi / 30) = -Real.sin ((9 : ℝ) * Real.pi / 30) := by
          rw [show -(9 : ℝ) * Real.pi / 30 = -((9 : ℝ) * Real.pi / 30) by ring, Real.sin_neg]
        have s2 : Real.sin (-(3 : ℝ) * Real.pi / 30) = -Real.sin ((3 : ℝ) * Real.pi / 30) := by
          rw [show -(3 : ℝ) * Real.pi / 30 = -((3 : ℝ) * Real.pi / 30) by ring, Real.sin_neg]
        have s3 : Real.sin (-(5 : ℝ) * Real.pi / 30) = -Real.sin ((5 : ℝ) * Real.pi / 30) := by
          rw [show -(5 : ℝ) * Real.pi / 30 = -((5 : ℝ) * Real.pi / 30) by ring, Real.sin_neg]
        linarith
      rcases hsp with hsp1 | hsp2
      · rcases ms3_cases hsp1 with
          ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩
        · change a = _ at ha; change b = _ at hb; change c = _ at hc
          rw [ha, hb, hc]; simp only [hnr]; push_cast
          rw [show ((r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((7 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) - ((8 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = -(5 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring,
              show ((r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) - ((7 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((8 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = -(3 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring,
              show -(((r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r))) + ((7 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((8 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = (9 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring]
          linarith [hsp_zero_neg]
        · change a = _ at ha; change b = _ at hb; change c = _ at hc
          rw [ha, hb, hc]; simp only [hnr]; push_cast
          rw [show ((r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((8 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) - ((7 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = -(3 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring,
              show ((r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) - ((8 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((7 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = -(5 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring,
              show -(((r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r))) + ((8 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((7 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = (9 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring]
          linarith [hsp_zero_neg]
        · change a = _ at ha; change b = _ at hb; change c = _ at hc
          rw [ha, hb, hc]; simp only [hnr]; push_cast
          rw [show ((7 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) - ((8 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = -(5 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring,
              show ((7 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) - ((r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((8 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = (9 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring,
              show -(((7 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r))) + ((r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((8 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = -(3 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring]
          linarith [hsp_zero_neg]
        · change a = _ at ha; change b = _ at hb; change c = _ at hc
          rw [ha, hb, hc]; simp only [hnr]; push_cast
          rw [show ((7 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((8 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) - ((r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = (9 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring,
              show ((7 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) - ((8 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = -(5 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring,
              show -(((7 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r))) + ((8 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = -(3 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring]
          linarith [hsp_zero_neg]
        · change a = _ at ha; change b = _ at hb; change c = _ at hc
          rw [ha, hb, hc]; simp only [hnr]; push_cast
          rw [show ((8 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) - ((7 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = -(3 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring,
              show ((8 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) - ((r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((7 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = (9 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring,
              show -(((8 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r))) + ((r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((7 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = -(5 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring]
          linarith [hsp_zero_neg]
        · change a = _ at ha; change b = _ at hb; change c = _ at hc
          rw [ha, hb, hc]; simp only [hnr]; push_cast
          rw [show ((8 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((7 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) - ((r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = (9 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring,
              show ((8 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) - ((7 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = -(3 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring,
              show -(((8 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r))) + ((7 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = -(5 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring]
          linarith [hsp_zero_neg]
      · rcases ms3_cases hsp2 with
          ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩
        · change a = _ at ha; change b = _ at hb; change c = _ at hc
          rw [ha, hb, hc]; simp only [hnr]; push_cast
          rw [show ((2 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((3 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) - ((9 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = -(9 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring,
              show ((2 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) - ((3 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((9 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = (3 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring,
              show -(((2 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r))) + ((3 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((9 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = (5 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring]
          linarith [sporadic_sin_zero]
        · change a = _ at ha; change b = _ at hb; change c = _ at hc
          rw [ha, hb, hc]; simp only [hnr]; push_cast
          rw [show ((2 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((9 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) - ((3 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = (3 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring,
              show ((2 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) - ((9 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((3 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = -(9 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring,
              show -(((2 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r))) + ((9 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((3 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = (5 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring]
          linarith [sporadic_sin_zero]
        · change a = _ at ha; change b = _ at hb; change c = _ at hc
          rw [ha, hb, hc]; simp only [hnr]; push_cast
          rw [show ((3 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((2 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) - ((9 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = -(9 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring,
              show ((3 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) - ((2 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((9 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = (5 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring,
              show -(((3 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r))) + ((2 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((9 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = (3 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring]
          linarith [sporadic_sin_zero]
        · change a = _ at ha; change b = _ at hb; change c = _ at hc
          rw [ha, hb, hc]; simp only [hnr]; push_cast
          rw [show ((3 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((9 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) - ((2 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = (5 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring,
              show ((3 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) - ((9 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((2 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = -(9 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring,
              show -(((3 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r))) + ((9 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((2 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = (3 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring]
          linarith [sporadic_sin_zero]
        · change a = _ at ha; change b = _ at hb; change c = _ at hc
          rw [ha, hb, hc]; simp only [hnr]; push_cast
          rw [show ((9 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((2 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) - ((3 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = (3 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring,
              show ((9 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) - ((2 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((3 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = (5 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring,
              show -(((9 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r))) + ((2 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((3 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = -(9 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring]
          linarith [sporadic_sin_zero]
        · change a = _ at ha; change b = _ at hb; change c = _ at hc
          rw [ha, hb, hc]; simp only [hnr]; push_cast
          rw [show ((9 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((3 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) - ((2 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = (5 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring,
              show ((9 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) - ((3 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((2 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = (3 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring,
              show -(((9 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r))) + ((3 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) + ((2 * r : ℝ) - 5 * r) * Real.pi / (6 * (5 * r)) = -(9 : ℝ) * Real.pi / 30 by field_simp [hr_ne]; ring]
          linarith [sporadic_sin_zero]

private lemma main_proof : ∀ n : ℕ, 1 ≤ n →
    d (2 * n - 1) = if 5 ∣ n then 6 * n + 7 else 6 * n - 5 := by
  intro n hn
  let m := 2 * n - 1
  have hm : m = 2 * n - 1 := rfl
  let S_triv : Finset (Fin m × Fin m × Fin m) := Finset.univ.filter fun t =>
    ((t.1.1 + 1 = n ∧ (t.2.1.1 + 1) + (t.2.2.1 + 1) = 2 * n) ∨
     (t.2.1.1 + 1 = n ∧ (t.1.1 + 1) + (t.2.2.1 + 1) = 2 * n) ∨
     (t.2.2.1 + 1 = n ∧ (t.1.1 + 1) + (t.2.1.1 + 1) = 2 * n))
  have htriv_card : S_triv.card = 6 * n - 5 := by
    let f1 : Fin m → Fin m × Fin m × Fin m := fun k => (⟨n - 1, by omega⟩, k, ⟨2 * n - 2 - k.1, by omega⟩)
    let f2 : Fin m → Fin m × Fin m × Fin m := fun k => (k, ⟨n - 1, by omega⟩, ⟨2 * n - 2 - k.1, by omega⟩)
    let f3 : Fin m → Fin m × Fin m × Fin m := fun k => (k, ⟨2 * n - 2 - k.1, by omega⟩, ⟨n - 1, by omega⟩)
    let A1 := Finset.univ.image f1
    let A2 := Finset.univ.image f2
    let A3 := Finset.univ.image f3
    have hA1 : A1.card = m := by
      rw [Finset.card_image_of_injective _ (fun a b h => by injection h with _ h'; injection h'),
        Finset.card_fin]
    have hA2 : A2.card = m := by
      rw [Finset.card_image_of_injective _ (fun a b h => by injection h), Finset.card_fin]
    have hA3 : A3.card = m := by
      rw [Finset.card_image_of_injective _ (fun a b h => by injection h), Finset.card_fin]
    let mid : Fin m × Fin m × Fin m := (⟨n - 1, by omega⟩, ⟨n - 1, by omega⟩, ⟨n - 1, by omega⟩)
    have h12 : A1 ∩ A2 = {mid} := by
      ext t
      simp only [A1, A2, Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · rintro ⟨⟨k1, hk1⟩, ⟨k2, hk2⟩⟩
        rw [← hk1] at hk2 ⊢
        simp only [f1, f2, Prod.mk.injEq, Fin.ext_iff] at hk2
        have hk1_eq : k1 = ⟨n - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
        rw [hk1_eq]
        simp only [f1, mid, Prod.mk.injEq, Fin.ext_iff, true_and]
        omega
      · rintro rfl
        refine ⟨⟨⟨n - 1, by omega⟩, ?_⟩, ⟨⟨n - 1, by omega⟩, ?_⟩⟩ <;>
          (simp only [f1, f2, mid, Prod.mk.injEq, Fin.ext_iff, true_and]; omega)
    have h12_3 : (A1 ∪ A2) ∩ A3 = {mid} := by
      ext t
      simp only [A1, A2, A3, Finset.mem_inter, Finset.mem_union, Finset.mem_image,
        Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨(⟨k1, hk1⟩ | ⟨k2, hk2⟩), ⟨k3, hk3⟩⟩
        · rw [← hk1] at hk3 ⊢
          simp only [f1, f3, Prod.mk.injEq, Fin.ext_iff] at hk3
          have hk1_eq : k1 = ⟨n - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
          rw [hk1_eq]
          simp only [f1, mid, Prod.mk.injEq, Fin.ext_iff, true_and]
          omega
        · rw [← hk2] at hk3 ⊢
          simp only [f2, f3, Prod.mk.injEq, Fin.ext_iff] at hk3
          have hk2_eq : k2 = ⟨n - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
          rw [hk2_eq]
          simp only [f2, mid, Prod.mk.injEq, Fin.ext_iff, true_and]
          omega
      · rintro rfl
        refine ⟨Or.inl ⟨⟨n - 1, by omega⟩, ?_⟩, ⟨⟨n - 1, by omega⟩, ?_⟩⟩
        · simp only [f1, mid, Prod.mk.injEq, Fin.ext_iff, true_and]; omega
        · simp only [f3, mid, Prod.mk.injEq, Fin.ext_iff, true_and, and_true]; omega
    have hStriv_eq : S_triv = (A1 ∪ A2) ∪ A3 := by
      ext ⟨i, j, k⟩
      simp only [S_triv, A1, A2, A3, Finset.mem_filter, Finset.mem_union, Finset.mem_image,
        Finset.mem_univ, true_and, f1, f2, f3, Prod.mk.injEq, Fin.ext_iff]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
        · left; left; exact ⟨j, by omega, rfl, by omega⟩
        · left; right; exact ⟨i, rfl, by omega, by omega⟩
        · right; exact ⟨i, rfl, by omega, by omega⟩
      · rintro ((⟨x, h1, h2, h3⟩ | ⟨x, h1, h2, h3⟩) | ⟨x, h1, h2, h3⟩)
        · left; have := x.2; omega
        · right; left; have := x.2; omega
        · right; right; have := x.2; omega
    have hu12 : (A1 ∪ A2).card = 2 * m - 1 := by
      have := Finset.card_union_add_card_inter A1 A2
      rw [hA1, hA2, h12, Finset.card_singleton] at this
      omega
    have hu123 : ((A1 ∪ A2) ∪ A3).card = 3 * m - 2 := by
      have := Finset.card_union_add_card_inter (A1 ∪ A2) A3
      rw [hu12, hA3, h12_3, Finset.card_singleton] at this
      omega
    rw [hStriv_eq, hu123]
    omega
  by_cases h5 : 5 ∣ n
  · rw [if_pos h5]
    set r := n / 5
    have hnr : n = 5 * r := (Nat.mul_div_cancel' h5).symm
    have hr_pos : 0 < r := by omega
    let p1 : Fin m := ⟨r - 1, by omega⟩
    let p2 : Fin m := ⟨2 * r - 1, by omega⟩
    let p3 : Fin m := ⟨3 * r - 1, by omega⟩
    let p7 : Fin m := ⟨7 * r - 1, by omega⟩
    let p8 : Fin m := ⟨8 * r - 1, by omega⟩
    let p9 : Fin m := ⟨9 * r - 1, by omega⟩
    let L_sp : List (Fin m × Fin m × Fin m) :=
      [(p1, p7, p8), (p1, p8, p7), (p7, p1, p8), (p7, p8, p1), (p8, p1, p7), (p8, p7, p1),
       (p2, p3, p9), (p2, p9, p3), (p3, p2, p9), (p3, p9, p2), (p9, p2, p3), (p9, p3, p2)]
    let S_sp : Finset (Fin m × Fin m × Fin m) := L_sp.toFinset
    have hsp_card : S_sp.card = 12 := by
      have hnodup : L_sp.Nodup := by
        simp only [L_sp, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
          List.nodup_nil, not_or, Prod.mk.injEq, Fin.ext_iff, p1, p2, p3, p7, p8, p9]
        repeat (first | constructor | omega | trivial)
      rw [List.toFinset_card_of_nodup hnodup]
      rfl
    have hdisj : Disjoint S_triv S_sp := by
      rw [Finset.disjoint_right]
      intro t htsp htriv
      simp only [S_triv, Finset.mem_filter, Finset.mem_univ, true_and] at htriv
      simp only [S_sp, L_sp, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at htsp
      rcases htsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (dsimp only [p1, p2, p3, p7, p8, p9] at htriv; omega)
    have hset_eq : {t : Fin m × Fin m × Fin m | ratio m t.1 * ratio m t.2.1 * ratio m t.2.2 = 1} =
        ((S_triv ∪ S_sp : Finset (Fin m × Fin m × Fin m)) : Set (Fin m × Fin m × Fin m)) := by
      ext t
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_union]
      rw [is_solution_iff hn t]
      constructor
      · rintro (ht | ⟨_, hsp⟩)
        · left; simp [S_triv, ht]
        · right
          have hmk : ∀ q1 q2 q3 : Fin m, t.1.1 = q1.1 → t.2.1.1 = q2.1 → t.2.2.1 = q3.1 →
              t = (q1, q2, q3) := fun q1 q2 q3 h1 h2 h3 =>
            Prod.ext (Fin.ext h1) (Prod.ext (Fin.ext h2) (Fin.ext h3))
          rcases hsp with hsp1 | hsp2
          · rcases ms3_cases hsp1 with
              ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
              ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
            · rw [hmk p1 p7 p8 (by dsimp [p1]; omega) (by dsimp [p7]; omega) (by dsimp [p8]; omega)]; simp [S_sp, L_sp]
            · rw [hmk p1 p8 p7 (by dsimp [p1]; omega) (by dsimp [p8]; omega) (by dsimp [p7]; omega)]; simp [S_sp, L_sp]
            · rw [hmk p7 p1 p8 (by dsimp [p7]; omega) (by dsimp [p1]; omega) (by dsimp [p8]; omega)]; simp [S_sp, L_sp]
            · rw [hmk p7 p8 p1 (by dsimp [p7]; omega) (by dsimp [p8]; omega) (by dsimp [p1]; omega)]; simp [S_sp, L_sp]
            · rw [hmk p8 p1 p7 (by dsimp [p8]; omega) (by dsimp [p1]; omega) (by dsimp [p7]; omega)]; simp [S_sp, L_sp]
            · rw [hmk p8 p7 p1 (by dsimp [p8]; omega) (by dsimp [p7]; omega) (by dsimp [p1]; omega)]; simp [S_sp, L_sp]
          · rcases ms3_cases hsp2 with
              ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
              ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
            · rw [hmk p2 p3 p9 (by dsimp [p2]; omega) (by dsimp [p3]; omega) (by dsimp [p9]; omega)]; simp [S_sp, L_sp]
            · rw [hmk p2 p9 p3 (by dsimp [p2]; omega) (by dsimp [p9]; omega) (by dsimp [p3]; omega)]; simp [S_sp, L_sp]
            · rw [hmk p3 p2 p9 (by dsimp [p3]; omega) (by dsimp [p2]; omega) (by dsimp [p9]; omega)]; simp [S_sp, L_sp]
            · rw [hmk p3 p9 p2 (by dsimp [p3]; omega) (by dsimp [p9]; omega) (by dsimp [p2]; omega)]; simp [S_sp, L_sp]
            · rw [hmk p9 p2 p3 (by dsimp [p9]; omega) (by dsimp [p2]; omega) (by dsimp [p3]; omega)]; simp [S_sp, L_sp]
            · rw [hmk p9 p3 p2 (by dsimp [p9]; omega) (by dsimp [p3]; omega) (by dsimp [p2]; omega)]; simp [S_sp, L_sp]
      · rintro (ht | hsp)
        · left; exact (Finset.mem_filter.mp ht).2
        · right
          refine ⟨h5, ?_⟩
          simp only [S_sp, L_sp, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hsp
          rcases hsp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · left; dsimp [p1, p7, p8]; rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]
          · left; dsimp [p1, p7, p8]; rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]; exact ms3_23 r (8 * r) (7 * r)
          · left; dsimp [p1, p7, p8]; rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]; exact ms3_12 (7 * r) r (8 * r)
          · left; dsimp [p1, p7, p8]; rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]; exact (ms3_23 (7 * r) (8 * r) r).trans (ms3_12 (7 * r) r (8 * r))
          · left; dsimp [p1, p7, p8]; rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]; exact (ms3_12 (8 * r) r (7 * r)).trans (ms3_23 r (8 * r) (7 * r))
          · left; dsimp [p1, p7, p8]; rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]; exact ((ms3_23 (8 * r) (7 * r) r).trans (ms3_12 (8 * r) r (7 * r))).trans (ms3_23 r (8 * r) (7 * r))
          · right; dsimp [p2, p3, p9]; rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]
          · right; dsimp [p2, p3, p9]; rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]; exact ms3_23 (2 * r) (9 * r) (3 * r)
          · right; dsimp [p2, p3, p9]; rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]; exact ms3_12 (3 * r) (2 * r) (9 * r)
          · right; dsimp [p2, p3, p9]; rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]; exact (ms3_23 (3 * r) (9 * r) (2 * r)).trans (ms3_12 (3 * r) (2 * r) (9 * r))
          · right; dsimp [p2, p3, p9]; rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]; exact (ms3_12 (9 * r) (2 * r) (3 * r)).trans (ms3_23 (2 * r) (9 * r) (3 * r))
          · right; dsimp [p2, p3, p9]; rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)]; exact ((ms3_23 (9 * r) (3 * r) (2 * r)).trans (ms3_12 (9 * r) (2 * r) (3 * r))).trans (ms3_23 (2 * r) (9 * r) (3 * r))
    unfold d
    rw [hset_eq, Set.ncard_coe_finset, Finset.card_union_of_disjoint hdisj, htriv_card, hsp_card]
    omega
  · rw [if_neg h5]
    have hset_eq : {t : Fin m × Fin m × Fin m | ratio m t.1 * ratio m t.2.1 * ratio m t.2.2 = 1} =
        (S_triv : Set (Fin m × Fin m × Fin m)) := by
      ext t
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, S_triv, Finset.mem_filter, Finset.mem_univ,
        true_and]
      rw [is_solution_iff hn t]
      constructor
      · rintro (ht | ⟨h5', _⟩)
        · exact ht
        · exact absurd h5' h5
      · exact Or.inl
    unfold d
    rw [hset_eq, Set.ncard_coe_finset, htriv_card]

end OMA_A387471

theorem OMA.solution : type_of% @OMA.S_oeis_a387471.main := OMA_A387471.main_proof
