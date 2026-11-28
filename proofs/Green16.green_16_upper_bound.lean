import FormalConjectures.GreensOpenProblems.«16»

/-!
# Upper bound for Ben Green's Open Problem 16

Proof of `Green16.green_16_upper_bound` via Schoen–Sisask (2016) `L^∞`-almost-periodicity on
regular Bohr sets and Sanders's local Chang lemma, adapted to `x + 3y = 2z + 2w` with distinctness.
-/

open Finset Real Complex Filter Topology
open scoped BigOperators ComplexConjugate

namespace Green16TryB

/- ## Section 1: Convolutions, L^p norms, and Fourier analysis on finite abelian groups -/

section ConvFourier

variable {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]

/-- Real indicator function of a finset `A ⊆ G`. -/
noncomputable def indR (A : Finset G) (x : G) : ℝ :=
  if x ∈ A then 1 else 0

/-- Complex indicator function of a finset `A ⊆ G`. -/
noncomputable def indC (A : Finset G) (x : G) : ℂ :=
  if x ∈ A then 1 else 0

/-- Normalized uniform probability measure on a finset `A ⊆ G` (real-valued). -/
noncomputable def muR (A : Finset G) (x : G) : ℝ :=
  if x ∈ A then (A.card : ℝ)⁻¹ else 0

/-- Normalized uniform probability measure on a finset `A ⊆ G` (complex-valued). -/
noncomputable def muC (A : Finset G) (x : G) : ℂ :=
  if x ∈ A then (A.card : ℂ)⁻¹ else 0

/-- Discrete convolution of real-valued functions on `G`. -/
noncomputable def convR (f g : G → ℝ) (x : G) : ℝ :=
  ∑ y : G, f y * g (x - y)

/-- Discrete convolution of complex-valued functions on `G`. -/
noncomputable def convC (f g : G → ℂ) (x : G) : ℂ :=
  ∑ y : G, f y * g (x - y)

/-- Discrete Fourier transform `f̂(ψ) = ∑ x, f(x) * conj(ψ(x))`. -/
noncomputable def dftG (f : G → ℂ) (ψ : AddChar G ℂ) : ℂ :=
  ∑ x : G, f x * star (ψ x)

lemma indR_nonneg (A : Finset G) (x : G) : 0 ≤ indR A x := by
  unfold indR; split_ifs <;> norm_num

lemma muR_nonneg (A : Finset G) (x : G) : 0 ≤ muR A x := by
  unfold muR; split_ifs <;> positivity

lemma sum_indR (A : Finset G) : ∑ x : G, indR A x = (A.card : ℝ) := by
  simp [indR]

lemma sum_muR {A : Finset G} (hA : A.Nonempty) : ∑ x : G, muR A x = 1 := by
  have hc : (A.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hA.card_pos.ne'
  simp [muR, hc]

lemma indC_eq_ofReal_indR (A : Finset G) (x : G) : indC A x = (indR A x : ℂ) := by
  unfold indC indR; split_ifs <;> simp

lemma muC_eq_ofReal_muR (A : Finset G) (x : G) : muC A x = (muR A x : ℂ) := by
  unfold muC muR; split_ifs <;> simp

lemma convC_ofReal (f g : G → ℝ) (x : G) :
    convC (fun y => (f y : ℂ)) (fun y => (g y : ℂ)) x = (convR f g x : ℂ) := by
  simp [convC, convR]

lemma convR_comm (f g : G → ℝ) (x : G) : convR f g x = convR g f x := by
  unfold convR
  refine Fintype.sum_equiv (Equiv.subLeft x) _ _ fun y => ?_
  simp [Equiv.subLeft_apply, mul_comm]

lemma convR_assoc (f g h : G → ℝ) (x : G) :
    convR (convR f g) h x = convR f (convR g h) x := by
  unfold convR
  simp_rw [sum_mul, mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine Fintype.sum_equiv (Equiv.subRight y) _ _ fun z => ?_
  simp only [Equiv.subRight_apply]
  have hsub : x - y - (z - y) = x - z := by abel
  rw [hsub, mul_assoc]

lemma convC_assoc (f g h : G → ℂ) (x : G) :
    convC (convC f g) h x = convC f (convC g h) x := by
  unfold convC
  simp_rw [sum_mul, mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine Fintype.sum_equiv (Equiv.subRight y) _ _ fun z => ?_
  simp only [Equiv.subRight_apply]
  have hsub : x - y - (z - y) = x - z := by abel
  rw [hsub, mul_assoc]

lemma convR_nonneg {f g : G → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) (x : G) :
    0 ≤ convR f g x :=
  Finset.sum_nonneg fun y _ => mul_nonneg (hf y) (hg (x - y))

lemma convR_le_convR {f₁ f₂ g : G → ℝ} (hf : ∀ x, f₁ x ≤ f₂ x) (hg : ∀ x, 0 ≤ g x) (x : G) :
    convR f₁ g x ≤ convR f₂ g x :=
  Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_right (hf y) (hg (x - y))

lemma convR_le_convR_right {f g₁ g₂ : G → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, g₁ x ≤ g₂ x)
    (x : G) : convR f g₁ x ≤ convR f g₂ x :=
  Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hg (x - y)) (hf y)

lemma convR_sub_left (f₁ f₂ g : G → ℝ) (x : G) :
    convR (fun y => f₁ y - f₂ y) g x = convR f₁ g x - convR f₂ g x := by
  simp [convR, sub_mul, Finset.sum_sub_distrib]

lemma convR_sub_right (f g₁ g₂ : G → ℝ) (x : G) :
    convR f (fun y => g₁ y - g₂ y) x = convR f g₁ x - convR f g₂ x := by
  simp [convR, mul_sub, Finset.sum_sub_distrib]

lemma convR_add_right (f g₁ g₂ : G → ℝ) (x : G) :
    convR f (fun y => g₁ y + g₂ y) x = convR f g₁ x + convR f g₂ x := by
  simp [convR, mul_add, Finset.sum_add_distrib]

lemma convR_translate (f g : G → ℝ) (x t : G) :
    convR f g (x + t) = convR (fun y => f (y + t)) g x := by
  unfold convR
  refine Fintype.sum_equiv (Equiv.subRight t) _ _ fun y => ?_
  simp only [Equiv.subRight_apply, sub_add_cancel]
  have hsub : x - (y - t) = x + t - y := by abel
  rw [hsub]

lemma convR_indR_muR (A B : Finset G) (x : G) :
    convR (indR A) (muR B) x =
      ((B.filter (fun b => x - b ∈ A)).card : ℝ) / (B.card : ℝ) := by
  by_cases hB : B.card = 0
  · simp [convR, muR, hB]
  · rw [convR_comm]
    unfold convR muR indR
    have : ∑ y : G, (if y ∈ B then (B.card : ℝ)⁻¹ else 0) * (if x - y ∈ A then 1 else 0) =
        ∑ y ∈ B, if x - y ∈ A then (B.card : ℝ)⁻¹ else 0 := by
      rw [← Finset.sum_subset (Finset.subset_univ B)]
      · refine Finset.sum_congr rfl fun y hy => ?_
        split_ifs <;> simp [hy]
      · intro y _ hy
        simp [hy]
    rw [this, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      div_eq_mul_inv]

/-- Fourier inversion formula on `G`. -/
lemma dftG_inversion (f : G → ℂ) (x : G) :
    f x = (Fintype.card G : ℂ)⁻¹ * ∑ ψ : AddChar G ℂ, dftG f ψ * ψ x := by
  unfold dftG
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm : ∀ y : G, ∑ ψ : AddChar G ℂ, f y * star (ψ y) * ψ x =
      f y * ∑ ψ : AddChar G ℂ, ψ (x - y) := by
    intro y
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [mul_assoc, Complex.star_def, ← AddChar.map_neg_eq_conj, sub_eq_add_neg,
      AddChar.map_add_eq_mul, mul_comm (ψ x)]
  simp_rw [hterm, AddChar.sum_apply_eq_ite]
  have hcond : ∀ y : G, x - y = 0 ↔ y = x := fun y => by rw [sub_eq_zero, eq_comm]
  simp_rw [hcond]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hG : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp [hG]

/-- Parseval's identity on `G`. -/
lemma dftG_parseval (f : G → ℂ) :
    (Fintype.card G : ℝ)⁻¹ * ∑ ψ : AddChar G ℂ, ‖dftG f ψ‖ ^ 2 = ∑ x : G, ‖f x‖ ^ 2 := by
  suffices hC : ((Fintype.card G : ℂ)⁻¹ * ∑ ψ : AddChar G ℂ, dftG f ψ * star (dftG f ψ)) =
      ∑ x : G, f x * star (f x) by
    have h1 : ∀ z : ℂ, z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp_rw [h1] at hC
    have hC' : (((Fintype.card G : ℝ)⁻¹ * ∑ ψ : AddChar G ℂ, ‖dftG f ψ‖ ^ 2 : ℝ) : ℂ) =
        ((∑ x : G, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
      simpa using hC
    exact Complex.ofReal_injective hC'
  unfold dftG
  have hstar : ∀ ψ : AddChar G ℂ,
      star (∑ y : G, f y * star (ψ y)) = ∑ y : G, star (f y) * ψ y := by
    intro ψ
    simp
  simp_rw [hstar]
  have hswap : ∑ ψ : AddChar G ℂ, (∑ x : G, f x * star (ψ x)) * (∑ y : G, star (f y) * ψ y) =
      ∑ x : G, ∑ y : G, f x * star (f y) * ∑ ψ : AddChar G ℂ, ψ (y - x) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    refine Finset.sum_congr rfl fun ψ _ => ?_
    have hψ : star (ψ x) * ψ y = ψ (y - x) := by
      rw [Complex.star_def, ← AddChar.map_neg_eq_conj, sub_eq_add_neg, AddChar.map_add_eq_mul,
        mul_comm]
    calc f x * star (ψ x) * (star (f y) * ψ y)
        = f x * star (f y) * (star (ψ x) * ψ y) := by ring
      _ = f x * star (f y) * ψ (y - x) := by rw [hψ]
  rw [hswap]
  simp_rw [AddChar.sum_apply_eq_ite]
  have hcond : ∀ x y : G, y - x = 0 ↔ y = x := fun x y => sub_eq_zero
  simp only [hcond, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_mul]
  have hG : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp [hG]

/-- Convolution theorem for `dftG`. -/
lemma dftG_convC (f g : G → ℂ) (ψ : AddChar G ℂ) :
    dftG (convC f g) ψ = dftG f ψ * dftG g ψ := by
  unfold dftG convC
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.subRight y) _ _ fun x => ?_
  simp only [Equiv.subRight_apply]
  have hψ : star (ψ x) = star (ψ y) * star (ψ (x - y)) := by
    rw [← star_mul', ← AddChar.map_add_eq_mul, add_sub_cancel]
  rw [hψ]
  ring

/-- Translation identity for `dftG`. -/
lemma dftG_translate (f : G → ℂ) (t : G) (ψ : AddChar G ℂ) :
    dftG (fun x => f (x + t)) ψ = ψ t * dftG f ψ := by
  unfold dftG
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight t) _ _ fun x => ?_
  change f (x + t) * star (ψ x) = ψ t * (f (x + t) * star (ψ (x + t)))
  have hψ : ψ t * star (ψ (x + t)) = star (ψ x) := by
    rw [AddChar.map_add_eq_mul, star_mul', mul_left_comm, Complex.star_def,
      Complex.mul_conj, Complex.normSq_eq_norm_sq, ψ.norm_apply]
    simp
  calc f (x + t) * star (ψ x)
      = f (x + t) * (ψ t * star (ψ (x + t))) := by rw [hψ]
    _ = ψ t * (f (x + t) * star (ψ (x + t))) := by ring

lemma norm_dftG_indC_le (A : Finset G) (ψ : AddChar G ℂ) :
    ‖dftG (indC A) ψ‖ ≤ (A.card : ℝ) := by
  unfold dftG indC
  calc ‖∑ x : G, (if x ∈ A then (1 : ℂ) else 0) * star (ψ x)‖
      ≤ ∑ x : G, ‖(if x ∈ A then (1 : ℂ) else 0) * star (ψ x)‖ := norm_sum_le _ _
    _ = ∑ x : G, if x ∈ A then (1 : ℝ) else 0 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        split_ifs <;> simp [ψ.norm_apply]
    _ = (A.card : ℝ) := by simp

lemma sum_sq_norm_indC (A : Finset G) :
    ∑ x : G, ‖indC A x‖ ^ 2 = (A.card : ℝ) := by
  have : ∀ x : G, ‖indC A x‖ ^ 2 = if x ∈ A then (1 : ℝ) else 0 := by
    intro x; unfold indC; split_ifs <;> norm_num
  simp [this]

lemma norm_dftG_muC_le_one (A : Finset G) (ψ : AddChar G ℂ) :
    ‖dftG (muC A) ψ‖ ≤ 1 := by
  by_cases hA : A.card = 0
  · simp [dftG, muC, hA]
  · unfold dftG muC
    calc ‖∑ x : G, (if x ∈ A then (A.card : ℂ)⁻¹ else 0) * star (ψ x)‖
        ≤ ∑ x : G, ‖(if x ∈ A then (A.card : ℂ)⁻¹ else 0) * star (ψ x)‖ := norm_sum_le _ _
      _ = ∑ x : G, if x ∈ A then (A.card : ℝ)⁻¹ else 0 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          split_ifs <;> simp [ψ.norm_apply]
      _ = (A.card : ℝ) * (A.card : ℝ)⁻¹ := by simp
      _ = 1 := mul_inv_cancel₀ (Nat.cast_ne_zero.2 hA)

lemma norm_dftG_muC_translate (T : Finset G) (z : G) (ψ : AddChar G ℂ) :
    ‖dftG (muC (T.image (fun t => t - z))) ψ‖ = ‖dftG (muC T) ψ‖ := by
  have hcard : (T.image (fun t => t - z)).card = T.card :=
    Finset.card_image_of_injective T (sub_left_injective)
  have hmu : ∀ x : G, muC (T.image (fun t => t - z)) x = muC T (x + z) := by
    intro x
    unfold muC
    have hmem : x ∈ T.image (fun t => t - z) ↔ x + z ∈ T := by
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨t, ht, rfl⟩; simpa using ht
      · intro hx; exact ⟨x + z, hx, by abel⟩
    simp [hmem, hcard]
  have hfun : muC (T.image (fun t => t - z)) = fun x => muC T (x + z) := funext hmu
  rw [hfun, dftG_translate, norm_mul, ψ.norm_apply, one_mul]

/-- Iterated convolution `f^{*k}` (complex-valued) for `k ≥ 1`. -/
noncomputable def iterConvC (f : G → ℂ) : ℕ → G → ℂ
  | 0 => fun x => if x = 0 then 1 else 0
  | k + 1 => convC (iterConvC f k) f

lemma dftG_iterConvC (f : G → ℂ) (k : ℕ) (ψ : AddChar G ℂ) :
    dftG (iterConvC f k) ψ = (dftG f ψ) ^ k := by
  induction k with
  | zero =>
    simp [iterConvC, dftG]
  | succ k ih =>
    rw [iterConvC, dftG_convC, ih, pow_succ]

/-- Iterated convolution `f^{*k}` (real-valued). -/
noncomputable def iterConvR (f : G → ℝ) : ℕ → G → ℝ
  | 0 => fun x => if x = 0 then 1 else 0
  | k + 1 => convR (iterConvR f k) f

lemma iterConvC_ofReal (f : G → ℝ) (k : ℕ) (x : G) :
    iterConvC (fun y => (f y : ℂ)) k x = (iterConvR f k x : ℂ) := by
  induction k generalizing x with
  | zero =>
    unfold iterConvC iterConvR
    split_ifs <;> simp
  | succ k ih =>
    rw [iterConvC, iterConvR]
    have : iterConvC (fun y => (f y : ℂ)) k = fun y => (iterConvR f k y : ℂ) := funext ih
    rw [this, convC_ofReal]

lemma sum_iterConvR_muR {X : Finset G} (hX : X.Nonempty) (k : ℕ) :
    ∑ x : G, iterConvR (muR X) k x = 1 := by
  induction k with
  | zero => simp [iterConvR]
  | succ k ih =>
    simp only [iterConvR, convR]
    rw [Finset.sum_comm]
    have : ∀ y : G, ∑ x : G, iterConvR (muR X) k y * muR X (x - y) =
        iterConvR (muR X) k y * ∑ z : G, muR X z := by
      intro y
      rw [← Finset.mul_sum]
      congr 1
      exact Fintype.sum_equiv (Equiv.subRight y) _ _ (fun _ => rfl)
    simp_rw [this, sum_muR hX, mul_one]
    exact ih

lemma iterConvR_muR_nonneg (X : Finset G) (k : ℕ) (x : G) :
    0 ≤ iterConvR (muR X) k x := by
  induction k generalizing x with
  | zero => unfold iterConvR; split_ifs <;> norm_num
  | succ k ih => exact convR_nonneg ih (muR_nonneg X) x

end ConvFourier

/- ## Section 2: Circle geometry, Bohr sets, BohrGrowth, BohrReg, and Regularity -/

section CircleGeom

lemma norm_exp_mul_I_sub_one (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin (θ / 2)| := by
  have h1 : ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ^ 2 = (2 * |Real.sin (θ / 2)|) ^ 2 := by
    rw [Complex.exp_mul_I, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.cos_ofReal_re, Complex.mul_re,
      Complex.sin_ofReal_re, Complex.I_re, mul_zero, Complex.sin_ofReal_im, Complex.I_im, mul_one,
      sub_zero, add_zero, Complex.one_re, Complex.sub_im, Complex.add_im, Complex.cos_ofReal_im,
      Complex.mul_im, zero_add, Complex.one_im]
    have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
      have := Real.cos_two_mul' (θ / 2)
      have h2 : 2 * (θ / 2) = θ := by ring
      rw [h2] at this
      have hsc := Real.sin_sq_add_cos_sq (θ / 2)
      linarith
    have hsc2 := Real.sin_sq_add_cos_sq θ
    rw [mul_pow, sq_abs]
    nlinarith
  have hnn1 : 0 ≤ ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ := norm_nonneg _
  have hnn2 : 0 ≤ 2 * |Real.sin (θ / 2)| := by positivity
  nlinarith

lemma norm_exp_mul_I_sub_one_le (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ≤ |θ| := by
  rw [norm_exp_mul_I_sub_one]
  have h : |Real.sin (θ / 2)| ≤ |θ / 2| := Real.abs_sin_le_abs
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  linarith

lemma norm_sub_le_abs_arg_sub {z₁ z₂ : ℂ} (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) :
    ‖z₁ - z₂‖ ≤ |z₁.arg - z₂.arg| := by
  have hz₁ : Complex.exp ((z₁.arg : ℂ) * Complex.I) = z₁ := by
    have := Complex.norm_mul_exp_arg_mul_I z₁
    rw [h₁, Complex.ofReal_one, one_mul] at this
    exact this
  have hz₂ : Complex.exp ((z₂.arg : ℂ) * Complex.I) = z₂ := by
    have := Complex.norm_mul_exp_arg_mul_I z₂
    rw [h₂, Complex.ofReal_one, one_mul] at this
    exact this
  have hmul : z₁ - z₂ = z₂ * (Complex.exp (((z₁.arg - z₂.arg : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, mul_sub, mul_one, hz₁, hz₂]
    have hne : z₂ ≠ 0 := by rw [← hz₂]; exact Complex.exp_ne_zero _
    field_simp [hne]
  rw [hmul, norm_mul, h₂, one_mul]
  exact norm_exp_mul_I_sub_one_le (z₁.arg - z₂.arg)

lemma abs_arg_le_pi_div_two_mul_norm_sub_one {z : ℂ} (hz : ‖z‖ = 1) :
    |z.arg| ≤ (Real.pi / 2) * ‖z - 1‖ := by
  have he : Complex.exp ((z.arg : ℂ) * Complex.I) = z := by
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hz, Complex.ofReal_one, one_mul] at this
    exact this
  have hnorm : ‖z - 1‖ = 2 * |Real.sin (z.arg / 2)| := by
    conv_lhs => rw [← he]
    exact norm_exp_mul_I_sub_one z.arg
  rw [hnorm]
  have hlt : -Real.pi < z.arg := Complex.neg_pi_lt_arg z
  have hle : z.arg ≤ Real.pi := Complex.arg_le_pi z
  have habs : |z.arg / 2| ≤ Real.pi / 2 := by
    rw [abs_le]; constructor <;> linarith
  have hsin : (2 / Real.pi) * |z.arg / 2| ≤ Real.sin |z.arg / 2| :=
    Real.mul_le_sin (abs_nonneg _) habs
  have hsin_abs : Real.sin |z.arg / 2| = |Real.sin (z.arg / 2)| := by
    rcases le_or_gt 0 (z.arg / 2) with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith))]
    · rw [abs_of_neg h, Real.sin_neg, abs_of_nonpos]
      have := Real.sin_nonneg_of_nonneg_of_le_pi (neg_nonneg.2 h.le) (by linarith)
      rw [Real.sin_neg] at this
      linarith
  rw [hsin_abs, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hsin
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2 : (1 / Real.pi) * |z.arg| ≤ |Real.sin (z.arg / 2)| := by
    have heq : 2 / Real.pi * (|z.arg| / 2) = 1 / Real.pi * |z.arg| := by ring
    linarith
  have hmul := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ Real.pi by positivity)
  have hpi_ne : Real.pi ≠ 0 := hpi.ne'
  have hlhs : Real.pi * (1 / Real.pi * |z.arg|) = |z.arg| := by field_simp [hpi_ne]
  have hrhs : Real.pi / 2 * (2 * |Real.sin (z.arg / 2)|) = Real.pi * |Real.sin (z.arg / 2)| := by
    ring
  linarith

end CircleGeom

section BohrSets

variable {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]

/-- The Bohr set `Bohr(Γ, ρ) = {x ∈ G | ∀ γ ∈ Γ, ‖γ x - 1‖ ≤ ρ}`. -/
noncomputable def bohr (Γ : Finset (AddChar G ℂ)) (ρ : ℝ) : Finset G :=
  Finset.univ.filter fun x => ∀ γ ∈ Γ, ‖γ x - 1‖ ≤ ρ

lemma mem_bohr {Γ : Finset (AddChar G ℂ)} {ρ : ℝ} {x : G} :
    x ∈ bohr Γ ρ ↔ ∀ γ ∈ Γ, ‖γ x - 1‖ ≤ ρ := by
  simp [bohr]

lemma zero_mem_bohr (Γ : Finset (AddChar G ℂ)) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (0 : G) ∈ bohr Γ ρ := by
  rw [mem_bohr]
  intro γ _
  simp [hρ]

lemma bohr_nonempty (Γ : Finset (AddChar G ℂ)) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (bohr Γ ρ).Nonempty :=
  ⟨0, zero_mem_bohr Γ hρ⟩

lemma bohr_card_pos (Γ : Finset (AddChar G ℂ)) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    0 < (bohr Γ ρ).card :=
  (bohr_nonempty Γ hρ).card_pos

lemma bohr_mono_radius (Γ : Finset (AddChar G ℂ)) {ρ₁ ρ₂ : ℝ} (h : ρ₁ ≤ ρ₂) :
    bohr Γ ρ₁ ⊆ bohr Γ ρ₂ := by
  intro x hx
  rw [mem_bohr] at hx ⊢
  exact fun γ hγ => (hx γ hγ).trans h

lemma bohr_antitone_freq {Γ₁ Γ₂ : Finset (AddChar G ℂ)} (h : Γ₁ ⊆ Γ₂) (ρ : ℝ) :
    bohr Γ₂ ρ ⊆ bohr Γ₁ ρ := by
  intro x hx
  rw [mem_bohr] at hx ⊢
  exact fun γ hγ => hx γ (h hγ)

lemma neg_mem_bohr {Γ : Finset (AddChar G ℂ)} {ρ : ℝ} {x : G} (hx : x ∈ bohr Γ ρ) :
    -x ∈ bohr Γ ρ := by
  rw [mem_bohr] at hx ⊢
  intro γ hγ
  have h1 : γ (-x) - 1 = -(γ (-x)) * (γ x - 1) := by
    have hmul : γ (-x) * γ x = 1 := by
      rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    calc γ (-x) - 1 = γ (-x) - γ (-x) * γ x := by rw [hmul]
      _ = -(γ (-x)) * (γ x - 1) := by ring
  rw [h1, norm_mul, norm_neg, γ.norm_apply, one_mul]
  exact hx γ hγ

lemma add_mem_bohr {Γ : Finset (AddChar G ℂ)} {ρ₁ ρ₂ : ℝ} {x y : G}
    (hx : x ∈ bohr Γ ρ₁) (hy : y ∈ bohr Γ ρ₂) :
    x + y ∈ bohr Γ (ρ₁ + ρ₂) := by
  rw [mem_bohr] at hx hy ⊢
  intro γ hγ
  have h1 : γ (x + y) - 1 = γ x * (γ y - 1) + (γ x - 1) := by
    rw [AddChar.map_add_eq_mul]; ring
  calc ‖γ (x + y) - 1‖
      ≤ ‖γ x * (γ y - 1)‖ + ‖γ x - 1‖ := by rw [h1]; exact norm_add_le _ _
    _ = ‖γ y - 1‖ + ‖γ x - 1‖ := by rw [norm_mul, γ.norm_apply, one_mul]
    _ ≤ ρ₁ + ρ₂ := by linarith [hx γ hγ, hy γ hγ]

lemma sub_mem_bohr {Γ : Finset (AddChar G ℂ)} {ρ₁ ρ₂ : ℝ} {x y : G}
    (hx : x ∈ bohr Γ ρ₁) (hy : y ∈ bohr Γ ρ₂) :
    x - y ∈ bohr Γ (ρ₁ + ρ₂) := by
  rw [sub_eq_add_neg]
  exact add_mem_bohr hx (neg_mem_bohr hy)

lemma nsmul_mem_bohr {Γ : Finset (AddChar G ℂ)} {ρ : ℝ} (hρ : 0 ≤ ρ) {x : G} (hx : x ∈ bohr Γ ρ)
    (k : ℕ) : k • x ∈ bohr Γ ((k : ℝ) * ρ) := by
  induction k with
  | zero => simpa using zero_mem_bohr Γ le_rfl
  | succ k ih =>
    rw [succ_nsmul, Nat.cast_succ, add_mul, one_mul]
    exact add_mem_bohr ih hx

lemma bohr_eq_univ_of_two_le (Γ : Finset (AddChar G ℂ)) {ρ : ℝ} (hρ : 2 ≤ ρ) :
    bohr Γ ρ = Finset.univ := by
  ext x
  simp only [mem_bohr, Finset.mem_univ, iff_true]
  intro γ _
  calc ‖γ x - 1‖ ≤ ‖γ x‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by simp [γ.norm_apply]; norm_num
    _ ≤ ρ := hρ

lemma bohr_singleton_one (ρ : ℝ) (hρ : 0 ≤ ρ) :
    bohr ({(1 : AddChar G ℂ)} : Finset (AddChar G ℂ)) ρ = Finset.univ := by
  ext x
  simp [mem_bohr, hρ]

/-- Pushing a Bohr set through an additive group equivalence `e : G ≃+ G`. -/
lemma image_bohr_addEquiv (e : G ≃+ G) (Γ : Finset (AddChar G ℂ)) (ρ : ℝ) :
    (bohr Γ ρ).image e =
      bohr (Γ.image fun γ => γ.compAddMonoidHom e.symm.toAddMonoidHom) ρ := by
  ext y
  simp only [Finset.mem_image, mem_bohr]
  constructor
  · rintro ⟨x, hx, rfl⟩ ψ ⟨γ, hγ, rfl⟩
    simpa [AddChar.compAddMonoidHom_apply] using hx γ hγ
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    intro γ hγ
    exact hy (γ.compAddMonoidHom e.symm.toAddMonoidHom) ⟨γ, hγ, rfl⟩

lemma card_image_freq_addEquiv (e : G ≃+ G) (Γ : Finset (AddChar G ℂ)) :
    (Γ.image fun γ => γ.compAddMonoidHom e.symm.toAddMonoidHom).card = Γ.card := by
  refine Finset.card_image_of_injective _ ?_
  intro γ₁ γ₂ h
  ext x
  have hx := DFunLike.congr_fun h (e x)
  simpa [AddChar.compAddMonoidHom_apply] using hx

/-- Size lower bound for Bohr sets: `|Bohr(Γ, ρ)| ≥ (ρ / 9)^|Γ| * |G|` for `ρ ∈ (0, 2]`. -/
lemma bohr_card_ge (Γ : Finset (AddChar G ℂ)) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 2) :
    (ρ / 9) ^ Γ.card * (Fintype.card G : ℝ) ≤ ((bohr Γ ρ).card : ℝ) := by
  let M : ℕ := Nat.floor (2 * Real.pi / ρ) + 1
  let b : G → (Γ → Fin M) := fun x γ =>
    ⟨Nat.floor (((γ.1 x).arg + Real.pi) / ρ), by
      have harg_le : (γ.1 x).arg ≤ Real.pi := Complex.arg_le_pi _
      have hdiv : ((γ.1 x).arg + Real.pi) / ρ ≤ 2 * Real.pi / ρ := by
        apply div_le_div_of_nonneg_right (by linarith) hρ0.le
      have hfl : Nat.floor (((γ.1 x).arg + Real.pi) / ρ) ≤ Nat.floor (2 * Real.pi / ρ) :=
        Nat.floor_mono hdiv
      omega⟩
  have hfiber : ∀ c : Γ → Fin M, (Finset.univ.filter fun x => b x = c).card ≤ (bohr Γ ρ).card := by
    intro c
    by_cases hne : (Finset.univ.filter fun x => b x = c).Nonempty
    · obtain ⟨y₀, hy₀⟩ := hne
      have hy₀' : b y₀ = c := (Finset.mem_filter.1 hy₀).2
      refine Finset.card_le_card_of_injOn (fun x => x - y₀) ?_ ?_
      · intro x hx
        have hx' : b x = c := (Finset.mem_filter.1 hx).2
        rw [Finset.mem_coe, mem_bohr]
        intro γ hγ
        have heq : (b x ⟨γ, hγ⟩).1 = (b y₀ ⟨γ, hγ⟩).1 := by rw [hx', hy₀']
        dsimp only [b] at heq
        have hpos1 : 0 ≤ ((γ x).arg + Real.pi) / ρ := by
          apply div_nonneg (by linarith [Complex.neg_pi_lt_arg (γ x)]) hρ0.le
        have hpos2 : 0 ≤ ((γ y₀).arg + Real.pi) / ρ := by
          apply div_nonneg (by linarith [Complex.neg_pi_lt_arg (γ y₀)]) hρ0.le
        have h1a := Nat.floor_le hpos1
        have h1b := Nat.lt_floor_add_one (((γ x).arg + Real.pi) / ρ)
        have h2a := Nat.floor_le hpos2
        have h2b := Nat.lt_floor_add_one (((γ y₀).arg + Real.pi) / ρ)
        rw [heq] at h1a h1b
        have habs_div : |((γ x).arg + Real.pi) / ρ - ((γ y₀).arg + Real.pi) / ρ| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith
        have habs : |(γ x).arg - (γ y₀).arg| ≤ ρ := by
          have hsub : ((γ x).arg + Real.pi) / ρ - ((γ y₀).arg + Real.pi) / ρ =
              ((γ x).arg - (γ y₀).arg) / ρ := by ring
          rw [hsub, abs_div, abs_of_pos hρ0, div_le_one hρ0] at habs_div
          exact habs_div
        have hchar : ‖γ (x - y₀) - 1‖ = ‖γ x - γ y₀‖ := by
          have hmul : γ x - γ y₀ = γ y₀ * (γ (x - y₀) - 1) := by
            rw [mul_sub, mul_one, ← AddChar.map_add_eq_mul, add_sub_cancel]
          rw [hmul, norm_mul, γ.norm_apply, one_mul]
        rw [hchar]
        exact (norm_sub_le_abs_arg_sub (γ.norm_apply x) (γ.norm_apply y₀)).trans habs
      · intro x₁ _ x₂ _ h
        exact sub_left_injective h
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.card_empty]
      exact Nat.zero_le _
  have hsum : Fintype.card G ≤ Fintype.card (Γ → Fin M) * (bohr Γ ρ).card := by
    calc Fintype.card G
        = (Finset.univ : Finset G).card := rfl
      _ = ∑ c : Γ → Fin M, (Finset.univ.filter fun x => b x = c).card := by
          rw [Finset.card_eq_sum_card_fiberwise (f := b) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
      _ ≤ ∑ _c : Γ → Fin M, (bohr Γ ρ).card := Finset.sum_le_sum fun c _ => hfiber c
      _ = Fintype.card (Γ → Fin M) * (bohr Γ ρ).card := by simp
  have hcard_fn : Fintype.card (Γ → Fin M) = M ^ Γ.card := by
    simp [Fintype.card_pi]
  rw [hcard_fn] at hsum
  have hM_le : (M : ℝ) ≤ 9 / ρ := by
    have hfl : (Nat.floor (2 * Real.pi / ρ) : ℝ) ≤ 2 * Real.pi / ρ :=
      Nat.floor_le (by positivity)
    have hpi : Real.pi < 3.5 := by linarith [Real.pi_lt_d2]
    have h1 : (M : ℝ) = (Nat.floor (2 * Real.pi / ρ) : ℝ) + 1 := by simp [M]
    rw [h1]
    have h2 : 1 ≤ 2 / ρ := by rw [le_div_iff₀ hρ0]; linarith
    have h3 : 2 * Real.pi / ρ ≤ 7 / ρ := div_le_div_of_nonneg_right (by linarith) hρ0.le
    have h4 : 7 / ρ + 2 / ρ = 9 / ρ := by ring
    linarith
  have hpow : ((M : ℝ) ^ Γ.card) ≤ (9 / ρ) ^ Γ.card :=
    pow_le_pow_left₀ (by positivity) hM_le Γ.card
  have hsumR : (Fintype.card G : ℝ) ≤ (M : ℝ) ^ Γ.card * ((bohr Γ ρ).card : ℝ) := by
    exact_mod_cast hsum
  have hsumR2 : (Fintype.card G : ℝ) ≤ (9 / ρ) ^ Γ.card * ((bohr Γ ρ).card : ℝ) := by
    calc (Fintype.card G : ℝ)
        ≤ (M : ℝ) ^ Γ.card * ((bohr Γ ρ).card : ℝ) := hsumR
      _ ≤ (9 / ρ) ^ Γ.card * ((bohr Γ ρ).card : ℝ) :=
          mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)
  have hpos : (0 : ℝ) < (9 / ρ) ^ Γ.card := by positivity
  calc (ρ / 9) ^ Γ.card * (Fintype.card G : ℝ)
      = ((9 / ρ) ^ Γ.card)⁻¹ * (Fintype.card G : ℝ) := by
          rw [← inv_pow, inv_div]
    _ ≤ ((9 / ρ) ^ Γ.card)⁻¹ * ((9 / ρ) ^ Γ.card * ((bohr Γ ρ).card : ℝ)) :=
          mul_le_mul_of_nonneg_left hsumR2 (by positivity)
    _ = ((bohr Γ ρ).card : ℝ) := by field_simp [hpos.ne']

/-- General Bohr scaling bound: `|Bohr(Γ, R)| ≤ (⌊π R / r⌋ + 1)^|Γ| * |Bohr(Γ, r)|`. -/
lemma bohr_card_scale_le (Γ : Finset (AddChar G ℂ)) {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    ((bohr Γ R).card : ℝ) ≤ ((Nat.floor (Real.pi * R / r) + 1 : ℕ) : ℝ) ^ Γ.card *
      ((bohr Γ r).card : ℝ) := by
  let M : ℕ := Nat.floor (Real.pi * R / r) + 1
  let b : G → (Γ → Fin M) := fun x γ =>
    if hx : x ∈ bohr Γ R then
      ⟨Nat.floor (((γ.1 x).arg + (Real.pi / 2) * R) / r), by
        have hnorm : ‖γ.1 x - 1‖ ≤ R := (mem_bohr.1 hx) γ.1 γ.2
        have harg : |(γ.1 x).arg| ≤ (Real.pi / 2) * R :=
          (abs_arg_le_pi_div_two_mul_norm_sub_one (γ.1.norm_apply x)).trans
            (mul_le_mul_of_nonneg_left hnorm (by positivity))
        have hle : (γ.1 x).arg + (Real.pi / 2) * R ≤ Real.pi * R := by
          linarith [(abs_le.1 harg).2]
        have hdiv : ((γ.1 x).arg + (Real.pi / 2) * R) / r ≤ Real.pi * R / r :=
          div_le_div_of_nonneg_right hle hr.le
        have hfl := Nat.floor_mono hdiv
        omega⟩
    else ⟨0, Nat.succ_pos _⟩
  have hfiber : ∀ c : Γ → Fin M,
      ((bohr Γ R).filter fun x => b x = c).card ≤ (bohr Γ r).card := by
    intro c
    by_cases hne : ((bohr Γ R).filter fun x => b x = c).Nonempty
    · obtain ⟨y₀, hy₀⟩ := hne
      have hy₀_mem : y₀ ∈ bohr Γ R := (Finset.mem_filter.1 hy₀).1
      have hy₀_eq : b y₀ = c := (Finset.mem_filter.1 hy₀).2
      refine Finset.card_le_card_of_injOn (fun x => x - y₀) ?_ ?_
      · intro x hx
        have hx_mem : x ∈ bohr Γ R := (Finset.mem_filter.1 hx).1
        have hx_eq : b x = c := (Finset.mem_filter.1 hx).2
        rw [Finset.mem_coe, mem_bohr]
        intro γ hγ
        have heq0 : (b x ⟨γ, hγ⟩).1 = (b y₀ ⟨γ, hγ⟩).1 := by rw [hx_eq, hy₀_eq]
        dsimp only [b] at heq0
        rw [dif_pos hx_mem, dif_pos hy₀_mem] at heq0
        have heq : Nat.floor (((γ x).arg + (Real.pi / 2) * R) / r) =
            Nat.floor (((γ y₀).arg + (Real.pi / 2) * R) / r) := heq0
        have hpos1 : 0 ≤ ((γ x).arg + (Real.pi / 2) * R) / r := by
          have harg := (abs_arg_le_pi_div_two_mul_norm_sub_one (γ.norm_apply x)).trans
            (mul_le_mul_of_nonneg_left ((mem_bohr.1 hx_mem) γ hγ) (by positivity))
          exact div_nonneg (by linarith [(abs_le.1 harg).1]) hr.le
        have hpos2 : 0 ≤ ((γ y₀).arg + (Real.pi / 2) * R) / r := by
          have harg := (abs_arg_le_pi_div_two_mul_norm_sub_one (γ.norm_apply y₀)).trans
            (mul_le_mul_of_nonneg_left ((mem_bohr.1 hy₀_mem) γ hγ) (by positivity))
          exact div_nonneg (by linarith [(abs_le.1 harg).1]) hr.le
        have h1a := Nat.floor_le hpos1
        have h1b := Nat.lt_floor_add_one (((γ x).arg + (Real.pi / 2) * R) / r)
        have h2a := Nat.floor_le hpos2
        have h2b := Nat.lt_floor_add_one (((γ y₀).arg + (Real.pi / 2) * R) / r)
        rw [heq] at h1a h1b
        have habs_div : |((γ x).arg + (Real.pi / 2) * R) / r -
            ((γ y₀).arg + (Real.pi / 2) * R) / r| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith
        have habs : |(γ x).arg - (γ y₀).arg| ≤ r := by
          have hsub : ((γ x).arg + (Real.pi / 2) * R) / r -
              ((γ y₀).arg + (Real.pi / 2) * R) / r = ((γ x).arg - (γ y₀).arg) / r := by ring
          rw [hsub, abs_div, abs_of_pos hr, div_le_one hr] at habs_div
          exact habs_div
        have hchar : ‖γ (x - y₀) - 1‖ = ‖γ x - γ y₀‖ := by
          have hmul : γ x - γ y₀ = γ y₀ * (γ (x - y₀) - 1) := by
            rw [mul_sub, mul_one, ← AddChar.map_add_eq_mul, add_sub_cancel]
          rw [hmul, norm_mul, γ.norm_apply, one_mul]
        rw [hchar]
        exact (norm_sub_le_abs_arg_sub (γ.norm_apply x) (γ.norm_apply y₀)).trans habs
      · intro x₁ _ x₂ _ h
        exact sub_left_injective h
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.card_empty]
      exact Nat.zero_le _
  have hsum : (bohr Γ R).card ≤ Fintype.card (Γ → Fin M) * (bohr Γ r).card := by
    calc (bohr Γ R).card
        = ∑ c : Γ → Fin M, ((bohr Γ R).filter fun x => b x = c).card := by
            rw [Finset.card_eq_sum_card_fiberwise (f := b) (t := Finset.univ)
              (fun _ _ => Finset.mem_univ _)]
      _ ≤ ∑ _c : Γ → Fin M, (bohr Γ r).card := Finset.sum_le_sum fun c _ => hfiber c
      _ = Fintype.card (Γ → Fin M) * (bohr Γ r).card := by simp
  have hcard_fn : Fintype.card (Γ → Fin M) = M ^ Γ.card := by
    simp [Fintype.card_pi]
  rw [hcard_fn] at hsum
  exact_mod_cast hsum

/-- Doubling bound: `|Bohr(Γ, 2ρ)| ≤ 7^|Γ| * |Bohr(Γ, ρ)|`. -/
lemma bohr_card_double_le (Γ : Finset (AddChar G ℂ)) {ρ : ℝ} (hρ : 0 < ρ) :
    ((bohr Γ (2 * ρ)).card : ℝ) ≤ (7 : ℝ) ^ Γ.card * ((bohr Γ ρ).card : ℝ) := by
  have h := bohr_card_scale_le Γ hρ (show 0 ≤ 2 * ρ by positivity)
  have hratio : Real.pi * (2 * ρ) / ρ = 2 * Real.pi := by field_simp [hρ.ne']
  rw [hratio] at h
  have hfl : Nat.floor (2 * Real.pi) ≤ 6 := by
    apply Nat.lt_succ_iff.1
    rw [Nat.floor_lt (by positivity)]
    have := Real.pi_lt_d2
    norm_num at this ⊢
    linarith
  have hM : ((Nat.floor (2 * Real.pi) + 1 : ℕ) : ℝ) ≤ 7 := by
    exact_mod_cast Nat.succ_le_succ hfl
  calc ((bohr Γ (2 * ρ)).card : ℝ)
      ≤ ((Nat.floor (2 * Real.pi) + 1 : ℕ) : ℝ) ^ Γ.card * ((bohr Γ ρ).card : ℝ) := h
    _ ≤ (7 : ℝ) ^ Γ.card * ((bohr Γ ρ).card : ℝ) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hM _) (Nat.cast_nonneg _)

/-- Decay bound: `|Bohr(Γ, δρ)| ≥ (δ / 5)^|Γ| * |Bohr(Γ, ρ)|` for `δ ∈ (0, 1]`. -/
lemma bohr_card_decay_ge (Γ : Finset (AddChar G ℂ)) {ρ δ : ℝ} (hρ : 0 < ρ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (δ / 5) ^ Γ.card * ((bohr Γ ρ).card : ℝ) ≤ ((bohr Γ (δ * ρ)).card : ℝ) := by
  have h := bohr_card_scale_le Γ (show 0 < δ * ρ by positivity) hρ.le
  have hratio : Real.pi * ρ / (δ * ρ) = Real.pi / δ := by field_simp [hρ.ne', hδ0.ne']
  rw [hratio] at h
  have hM : ((Nat.floor (Real.pi / δ) + 1 : ℕ) : ℝ) ≤ 5 / δ := by
    have hfl : (Nat.floor (Real.pi / δ) : ℝ) ≤ Real.pi / δ := Nat.floor_le (by positivity)
    have hpi : Real.pi < 4 := by linarith [Real.pi_lt_d2]
    have h1 : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ0]; linarith
    push_cast
    have h2 : Real.pi / δ ≤ 4 / δ := div_le_div_of_nonneg_right hpi.le hδ0.le
    have h3 : 4 / δ + 1 / δ = 5 / δ := by ring
    linarith
  have hpow : ((Nat.floor (Real.pi / δ) + 1 : ℕ) : ℝ) ^ Γ.card ≤ (5 / δ) ^ Γ.card :=
    pow_le_pow_left₀ (by positivity) hM _
  have h2 : ((bohr Γ ρ).card : ℝ) ≤ (5 / δ) ^ Γ.card * ((bohr Γ (δ * ρ)).card : ℝ) :=
    h.trans (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _))
  have hpos : (0 : ℝ) < (5 / δ) ^ Γ.card := by positivity
  calc (δ / 5) ^ Γ.card * ((bohr Γ ρ).card : ℝ)
      = ((5 / δ) ^ Γ.card)⁻¹ * ((bohr Γ ρ).card : ℝ) := by rw [← inv_pow, inv_div]
    _ ≤ ((5 / δ) ^ Γ.card)⁻¹ * ((5 / δ) ^ Γ.card * ((bohr Γ (δ * ρ)).card : ℝ)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ((bohr Γ (δ * ρ)).card : ℝ) := by field_simp [hpos.ne']

/- ### Elementary 1-D Finite Vitali Covering for Bohr Regularity -/

/-- If `[a, b]` is covered by a finite list of closed intervals, then `b - a` is at most the sum
of their lengths. -/
private lemma interval_cover_sum_ge : ∀ (L : List (ℝ × ℝ)) (a b : ℝ),
    (∀ p ∈ L, p.1 ≤ p.2) →
    (∀ x ∈ Set.Icc a b, ∃ p ∈ L, x ∈ Set.Icc p.1 p.2) →
    b - a ≤ (L.map fun p => p.2 - p.1).sum
  | [], a, b, _, hcov => by
    by_cases hab : a ≤ b
    · obtain ⟨p, hp, _⟩ := hcov a ⟨le_rfl, hab⟩
      simp at hp
    · simp; linarith
  | p₀ :: rest, a, b, hle, hcov => by
    by_cases hab : b ≤ a
    · have hnn : 0 ≤ ((p₀ :: rest).map fun p => p.2 - p.1).sum :=
        List.sum_nonneg fun x hx => by
          rcases List.mem_map.1 hx with ⟨p, hp, rfl⟩
          linarith [hle p hp]
      linarith
    · push Not at hab
      obtain ⟨p, hp, hpa, hpb⟩ := hcov a ⟨le_rfl, hab.le⟩
      have hlen_lt : ((p₀ :: rest).erase p).length < (p₀ :: rest).length := by
        rw [List.length_erase_of_mem hp]
        exact Nat.sub_lt (List.length_pos_of_mem hp) Nat.zero_lt_one
      have hsub_le : ∀ q ∈ (p₀ :: rest).erase p, q.1 ≤ q.2 :=
        fun q hq => hle q (List.mem_of_mem_erase hq)
      have hsum_eq : ((p₀ :: rest).map fun q => q.2 - q.1).sum =
          (p.2 - p.1) + (((p₀ :: rest).erase p).map fun q => q.2 - q.1).sum := by
        have hperm := List.perm_cons_erase hp
        have hmap := (hperm.map (fun q : ℝ × ℝ => q.2 - q.1)).sum_eq
        simpa using hmap
      by_cases hpb_ge : b ≤ p.2
      · have hnn : 0 ≤ (((p₀ :: rest).erase p).map fun q => q.2 - q.1).sum :=
          List.sum_nonneg fun x hx => by
            rcases List.mem_map.1 hx with ⟨q, hq, rfl⟩
            linarith [hsub_le q hq]
        linarith
      · push Not at hpb_ge
        have hcov_eps : ∀ ε : ℝ, 0 < ε → p.2 + ε ≤ b →
            b - (p.2 + ε) ≤ (((p₀ :: rest).erase p).map fun q => q.2 - q.1).sum := by
          intro ε hε hle_b
          refine interval_cover_sum_ge ((p₀ :: rest).erase p) (p.2 + ε) b hsub_le fun x hx => ?_
          obtain ⟨q, hq, hqx⟩ := hcov x ⟨by linarith [hx.1, hpb], hx.2⟩
          have hqp : q ≠ p := by
            intro heq; subst heq; linarith [hx.1, hqx.2]
          exact ⟨q, (List.mem_erase_of_ne hqp).2 hq, hqx⟩
        have hrest : b - p.2 ≤ (((p₀ :: rest).erase p).map fun q => q.2 - q.1).sum := by
          by_contra hlt
          push Not at hlt
          set S := (((p₀ :: rest).erase p).map fun q => q.2 - q.1).sum
          set ε := min ((b - p.2) / 2) ((b - p.2 - S) / 2)
          have hε : 0 < ε := lt_min (by linarith) (by linarith)
          have h1 := hcov_eps ε hε (by linarith [min_le_left ((b - p.2) / 2) ((b - p.2 - S) / 2)])
          have h2 : ε ≤ (b - p.2 - S) / 2 := min_le_right _ _
          linarith
        linarith
termination_by L => L.length
decreasing_by exact hlen_lt

private lemma list_exists_max_by {α : Type*} (val : α → ℝ) :
    ∀ (L : List α), L ≠ [] → ∃ q ∈ L, ∀ p ∈ L, val p ≤ val q
  | [], h => absurd rfl h
  | [a], _ => ⟨a, by simp, by simp⟩
  | a :: b :: l, _ => by
    obtain ⟨q, hq, hqmax⟩ := list_exists_max_by val (b :: l) (List.cons_ne_nil _ _)
    by_cases h : val q ≤ val a
    · refine ⟨a, by simp, fun p hp => ?_⟩
      rcases List.mem_cons.1 hp with rfl | hp'
      · exact le_rfl
      · exact (hqmax p hp').trans h
    · refine ⟨q, List.mem_cons_of_mem _ hq, fun p hp => ?_⟩
      rcases List.mem_cons.1 hp with rfl | hp'
      · linarith
      · exact hqmax p hp'

/-- Finite 1-D 3× Vitali covering lemma on a list of intervals `(a, b)` with `a < b`. -/
private lemma finite_vitali_1d : ∀ (L : List (ℝ × ℝ)),
    (∀ p ∈ L, p.1 < p.2) →
    ∃ J : List (ℝ × ℝ),
      (∀ p ∈ J, p ∈ L) ∧
      J.Pairwise (fun p q => p.2 ≤ q.1 ∨ q.2 ≤ p.1) ∧
      ∀ p ∈ L, ∃ q ∈ J, q.1 - (q.2 - q.1) ≤ p.1 ∧ p.2 ≤ q.2 + (q.2 - q.1)
  | [], _ => ⟨[], by simp, List.Pairwise.nil, by simp⟩
  | p₀ :: rest, hlt => by
    obtain ⟨q, hqL, hqmax⟩ :=
      list_exists_max_by (fun p : ℝ × ℝ => p.2 - p.1) (p₀ :: rest) (List.cons_ne_nil _ _)
    have hL'_len :
        ((p₀ :: rest).filter (fun p => decide (p.2 ≤ q.1 ∨ q.2 ≤ p.1))).length <
          (p₀ :: rest).length := by
      have hnotmem : q ∉ (p₀ :: rest).filter (fun p => decide (p.2 ≤ q.1 ∨ q.2 ≤ p.1)) := by
        simp only [List.mem_filter, decide_eq_true_eq, not_and]
        intro _ h
        have hqlt := hlt q hqL
        rcases h with h | h <;> linarith
      have hsub := List.filter_sublist
        (p := fun p : ℝ × ℝ => decide (p.2 ≤ q.1 ∨ q.2 ≤ p.1)) (l := p₀ :: rest)
      have hle := hsub.length_le
      by_contra hge
      have heq : ((p₀ :: rest).filter (fun p => decide (p.2 ≤ q.1 ∨ q.2 ≤ p.1))).length =
          (p₀ :: rest).length := by omega
      have hEq := hsub.eq_of_length heq
      rw [hEq] at hnotmem
      exact hnotmem hqL
    have hL'_lt :
        ∀ p ∈ (p₀ :: rest).filter (fun p => decide (p.2 ≤ q.1 ∨ q.2 ≤ p.1)), p.1 < p.2 :=
      fun p hp => hlt p (List.mem_of_mem_filter hp)
    obtain ⟨J', hJ'sub, hJ'disj, hJ'cov⟩ :=
      finite_vitali_1d ((p₀ :: rest).filter (fun p => decide (p.2 ≤ q.1 ∨ q.2 ≤ p.1))) hL'_lt
    refine ⟨q :: J', ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp'
      · exact hqL
      · exact List.mem_of_mem_filter (hJ'sub p hp')
    · refine List.Pairwise.cons ?_ hJ'disj
      intro p hp
      have hpL' := hJ'sub p hp
      have hdisj : p.2 ≤ q.1 ∨ q.2 ≤ p.1 := of_decide_eq_true (List.mem_filter.1 hpL').2
      exact hdisj.symm
    · intro p hpL
      by_cases hdisj : p.2 ≤ q.1 ∨ q.2 ≤ p.1
      · have hpL' : p ∈ (p₀ :: rest).filter (fun p => decide (p.2 ≤ q.1 ∨ q.2 ≤ p.1)) :=
          List.mem_filter.2 ⟨hpL, decide_eq_true hdisj⟩
        obtain ⟨r, hrJ', hr1, hr2⟩ := hJ'cov p hpL'
        exact ⟨r, List.mem_cons_of_mem _ hrJ', hr1, hr2⟩
      · push Not at hdisj
        refine ⟨q, by simp, ?_, ?_⟩
        · have hlen := hqmax p hpL
          linarith [hdisj.1]
        · have hlen := hqmax p hpL
          linarith [hdisj.2]
termination_by L => L.length
decreasing_by exact hL'_len

/-- Sum of `f b - f a` over pairwise disjoint non-degenerate intervals inside `[u, v]` is at most
`f v - f u`. -/
private lemma sum_monotone_disjoint_le (f : ℝ → ℝ) :
    ∀ (J : List (ℝ × ℝ)) (u v : ℝ),
      u ≤ v →
      MonotoneOn f (Set.Icc u v) →
      (∀ p ∈ J, u ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ v) →
      J.Pairwise (fun p q => p.2 ≤ q.1 ∨ q.2 ≤ p.1) →
      (J.map fun p => f p.2 - f p.1).sum ≤ f v - f u
  | [], u, v, huv, hf, _, _ => by
    simp only [List.map_nil, List.sum_nil]
    linarith [hf ⟨le_rfl, huv⟩ ⟨huv, le_rfl⟩ huv]
  | p₀ :: rest, u, v, huv, hf, hmem, hdisj => by
    obtain ⟨p, hpJ, hpmin⟩ :=
      list_exists_max_by (fun q : ℝ × ℝ => -q.1) (p₀ :: rest) (List.cons_ne_nil _ _)
    have hpmin' : ∀ q ∈ p₀ :: rest, p.1 ≤ q.1 := fun q hq => by linarith [hpmin q hq]
    have hperm := List.perm_cons_erase hpJ
    have hdisj' : (p :: (p₀ :: rest).erase p).Pairwise (fun a b => a.2 ≤ b.1 ∨ b.2 ≤ a.1) :=
      (List.Perm.pairwise_iff (fun h => h.symm) hperm).1 hdisj
    rw [List.pairwise_cons] at hdisj'
    have hlen_lt : ((p₀ :: rest).erase p).length < (p₀ :: rest).length := by
      rw [List.length_erase_of_mem hpJ]
      exact Nat.sub_lt (List.length_pos_of_mem hpJ) Nat.zero_lt_one
    have hp_bounds := hmem p hpJ
    have hrest_bounds : ∀ q ∈ (p₀ :: rest).erase p, p.2 ≤ q.1 ∧ q.1 < q.2 ∧ q.2 ≤ v := by
      intro q hq
      have hqJ : q ∈ p₀ :: rest := List.mem_of_mem_erase hq
      have hqb := hmem q hqJ
      refine ⟨?_, hqb.2.1, hqb.2.2⟩
      rcases hdisj'.1 q hq with h1 | h2
      · exact h1
      · have hmin := hpmin' q hqJ
        linarith [hqb.2.1]
    have hf_sub : MonotoneOn f (Set.Icc p.2 v) :=
      hf.mono fun x hx => ⟨hp_bounds.1.trans (hp_bounds.2.1.le.trans hx.1), hx.2⟩
    have hrec := sum_monotone_disjoint_le f ((p₀ :: rest).erase p) p.2 v
      hp_bounds.2.2 hf_sub hrest_bounds hdisj'.2
    have hsum_eq : ((p₀ :: rest).map fun q => f q.2 - f q.1).sum =
        (f p.2 - f p.1) + (((p₀ :: rest).erase p).map fun q => f q.2 - f q.1).sum := by
      have := (hperm.map (fun q : ℝ × ℝ => f q.2 - f q.1)).sum_eq
      simpa using this
    have hfp : f u ≤ f p.1 :=
      hf ⟨le_rfl, huv⟩ ⟨hp_bounds.1, hp_bounds.2.1.le.trans hp_bounds.2.2⟩ hp_bounds.1
    linarith
termination_by J => J.length
decreasing_by exact hlen_lt

/-- A Bohr set `Bohr(Γ, ρ)` is regular if `1 - 100 |Γ| |η| ≤ |B_{(1+η)}| / |B| ≤ 1 + 100 |Γ| |η|`
for all `|η| ≤ 1 / (100 |Γ|)`. -/
def IsRegularBohr (Γ : Finset (AddChar G ℂ)) (ρ : ℝ) : Prop :=
  ∀ η : ℝ, |η| ≤ 1 / (100 * (Γ.card : ℝ)) →
    (1 - 100 * (Γ.card : ℝ) * |η|) * ((bohr Γ ρ).card : ℝ) ≤
      ((bohr Γ ((1 + η) * ρ)).card : ℝ) ∧
    ((bohr Γ ((1 + η) * ρ)).card : ℝ) ≤
      (1 + 100 * (Γ.card : ℝ) * |η|) * ((bohr Γ ρ).card : ℝ)

lemma isRegularBohr_singleton_one (ρ : ℝ) (hρ : 0 < ρ) :
    IsRegularBohr ({(1 : AddChar G ℂ)} : Finset (AddChar G ℂ)) ρ := by
  intro η hη
  have h1 : 0 ≤ (1 + η) * ρ := by
    have hcard : (({(1 : AddChar G ℂ)} : Finset (AddChar G ℂ)).card : ℝ) = 1 := by simp
    rw [hcard] at hη
    have habs := abs_le.1 hη
    have : 0 ≤ 1 + η := by linarith
    positivity
  rw [bohr_singleton_one ρ hρ.le, bohr_singleton_one ((1 + η) * ρ) h1]
  have hnn : 0 ≤ 100 * (({(1 : AddChar G ℂ)} : Finset (AddChar G ℂ)).card : ℝ) * |η| := by
    positivity
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) (Finset.univ : Finset G).card]

lemma isRegularBohr_image_addEquiv (e : G ≃+ G) {Γ : Finset (AddChar G ℂ)} {ρ : ℝ}
    (hreg : IsRegularBohr Γ ρ) :
    IsRegularBohr (Γ.image fun γ => γ.compAddMonoidHom e.symm.toAddMonoidHom) ρ := by
  intro η hη
  rw [card_image_freq_addEquiv] at hη ⊢
  have h1 : (bohr (Γ.image fun γ => γ.compAddMonoidHom e.symm.toAddMonoidHom) ρ).card =
      (bohr Γ ρ).card := by
    rw [← image_bohr_addEquiv e Γ ρ, Finset.card_image_of_injective _ e.injective]
  have h2 : (bohr (Γ.image fun γ => γ.compAddMonoidHom e.symm.toAddMonoidHom) ((1 + η) * ρ)).card =
      (bohr Γ ((1 + η) * ρ)).card := by
    rw [← image_bohr_addEquiv e Γ ((1 + η) * ρ), Finset.card_image_of_injective _ e.injective]
  rw [h1, h2]
  exact hreg η hη

/-- Existence of a regular rescaling `t ∈ [1/2, 1]` for any Bohr set of rank `d ≥ 1`. -/
lemma exists_regular_bohr (Γ : Finset (AddChar G ℂ)) (hΓ : Γ.Nonempty) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ t : ℝ, 1 / 2 ≤ t ∧ t ≤ 1 ∧ IsRegularBohr Γ (t * ρ) := by
  let d : ℝ := (Γ.card : ℝ)
  have hd_pos : 0 < d := Nat.cast_pos.2 hΓ.card_pos
  have hd_ge1 : 1 ≤ d := Nat.one_le_cast.2 hΓ.card_pos
  let f : ℝ → ℝ := fun t => Real.log ((bohr Γ (t * ρ)).card : ℝ)
  have hf_mono : MonotoneOn f (Set.Icc (1 / 2) 1) := by
    intro a ha b hb hab
    have hca : 0 < ((bohr Γ (a * ρ)).card : ℝ) :=
      Nat.cast_pos.2 (bohr_card_pos Γ (by nlinarith [ha.1]))
    have hsub : bohr Γ (a * ρ) ⊆ bohr Γ (b * ρ) := bohr_mono_radius Γ (by nlinarith)
    exact Real.log_le_log hca (Nat.cast_le.2 (Finset.card_le_card hsub))
  have hf_range : f 1 - f (1 / 2) ≤ 2 * d := by
    have hdouble := bohr_card_double_le Γ (show 0 < (1 / 2) * ρ by positivity)
    have h2eq : 2 * (1 / 2 * ρ) = 1 * ρ := by ring
    rw [h2eq] at hdouble
    have hc1 : 0 < ((bohr Γ (1 * ρ)).card : ℝ) := Nat.cast_pos.2 (bohr_card_pos Γ (by positivity))
    have hc2 : 0 < ((bohr Γ ((1 / 2) * ρ)).card : ℝ) :=
      Nat.cast_pos.2 (bohr_card_pos Γ (by positivity))
    have hlog := Real.log_le_log hc1 hdouble
    rw [Real.log_mul (by positivity) hc2.ne', Real.log_pow] at hlog
    have hlog7 : Real.log 7 ≤ 2 := by
      have hexp : (7 : ℝ) ≤ Real.exp 2 := by
        have h1 : (2.71828 : ℝ) < Real.exp 1 := by
          have := Real.exp_one_gt_d9
          linarith
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        rw [h2]
        nlinarith
      calc Real.log 7 ≤ Real.log (Real.exp 2) := Real.log_le_log (by norm_num) hexp
        _ = 2 := Real.log_exp 2
    dsimp only [f]
    have hmul : d * Real.log 7 ≤ d * 2 := mul_le_mul_of_nonneg_left hlog7 hd_pos.le
    linarith
  -- Show ∃ t ∈ [5/8, 7/8] such that ∀ h ∈ (0, 1/8], f(t + h) - f(t - h) ≤ 50 * d * h.
  have hex_good : ∃ t ∈ Set.Icc (5 / 8 : ℝ) (7 / 8),
      ∀ h : ℝ, 0 < h → h ≤ 1 / 8 → f (t + h) - f (t - h) ≤ 50 * d * h := by
    by_contra hall
    push Not at hall
    have hcov_open : Set.Icc (5 / 8 : ℝ) (7 / 8) ⊆
        ⋃ (p : {q : ℝ × ℝ // 1 / 2 ≤ q.1 ∧ q.1 < q.2 ∧ q.2 ≤ 1 ∧
          25 * d * (q.2 - q.1) < f q.2 - f q.1}), Set.Ioo p.1.1 p.1.2 := by
      intro t ht
      obtain ⟨h, hh0, hh8, hbad⟩ := hall t ht
      refine Set.mem_iUnion.2 ⟨⟨(t - h, t + h), ?_, ?_, ?_, ?_⟩, ?_⟩
      · linarith [ht.1]
      · linarith
      · linarith [ht.2]
      · linarith
      · exact ⟨by linarith, by linarith⟩
    obtain ⟨S, hScov⟩ := isCompact_Icc.elim_finite_subcover
      (fun p : {q : ℝ × ℝ // 1 / 2 ≤ q.1 ∧ q.1 < q.2 ∧ q.2 ≤ 1 ∧
          25 * d * (q.2 - q.1) < f q.2 - f q.1} => Set.Ioo p.1.1 p.1.2)
      (fun _ => isOpen_Ioo) hcov_open
    let L : List (ℝ × ℝ) := S.toList.map Subtype.val
    have hL_prop : ∀ p ∈ L, 1 / 2 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 1 ∧
        25 * d * (p.2 - p.1) < f p.2 - f p.1 := by
      intro p hp
      rcases List.mem_map.1 hp with ⟨q, _, rfl⟩
      exact q.2
    obtain ⟨J, hJsub, hJdisj, hJcov⟩ := finite_vitali_1d L fun p hp => (hL_prop p hp).2.1
    let J3 : List (ℝ × ℝ) := J.map fun q => (q.1 - (q.2 - q.1), q.2 + (q.2 - q.1))
    have hJ3_le : ∀ r ∈ J3, r.1 ≤ r.2 := by
      intro r hr
      rcases List.mem_map.1 hr with ⟨q, hq, rfl⟩
      linarith [(hL_prop q (hJsub q hq)).2.1]
    have hJ3_cov : ∀ x ∈ Set.Icc (5 / 8 : ℝ) (7 / 8), ∃ r ∈ J3, x ∈ Set.Icc r.1 r.2 := by
      intro x hx
      have hxU := hScov hx
      simp only [Set.mem_iUnion] at hxU
      obtain ⟨p, hpS, hxIoo⟩ := hxU
      have hpL : p.1 ∈ L := List.mem_map.2 ⟨p, Finset.mem_toList.2 hpS, rfl⟩
      obtain ⟨q, hqJ, hq1, hq2⟩ := hJcov p.1 hpL
      refine ⟨(q.1 - (q.2 - q.1), q.2 + (q.2 - q.1)), List.mem_map.2 ⟨q, hqJ, rfl⟩, ?_⟩
      exact ⟨by linarith [hxIoo.1], by linarith [hxIoo.2]⟩
    have hlen_ge : (7 / 8 : ℝ) - 5 / 8 ≤ (J3.map fun r => r.2 - r.1).sum :=
      interval_cover_sum_ge J3 (5 / 8) (7 / 8) hJ3_le hJ3_cov
    have hJ3_sum : (J3.map fun r => r.2 - r.1).sum = 3 * (J.map fun q => q.2 - q.1).sum := by
      simp only [J3, List.map_map]
      have hfn : (fun q : ℝ × ℝ => (q.2 + (q.2 - q.1)) - (q.1 - (q.2 - q.1))) =
          fun q => 3 * (q.2 - q.1) := by ext q; ring
      rw [show (fun x => x.2 - x.1) ∘ (fun q : ℝ × ℝ => (q.1 - (q.2 - q.1), q.2 + (q.2 - q.1))) =
          fun q => 3 * (q.2 - q.1) by ext q; simp; ring]
      clear hlen_ge hJ3_cov hJ3_le hJcov hJdisj hJsub hL_prop
      induction J with
      | nil => simp
      | cons a l ih => simp [ih, mul_add]
    have hsum_f : (J.map fun q => f q.2 - f q.1).sum ≤ f 1 - f (1 / 2) :=
      sum_monotone_disjoint_le f J (1 / 2) 1 (by norm_num) hf_mono
        (fun q hq => by
          have h := hL_prop q (hJsub q hq)
          exact ⟨h.1, h.2.1, h.2.2.1⟩)
        hJdisj
    have hsum_cmp : 25 * d * (J.map fun q => q.2 - q.1).sum ≤
        (J.map fun q => f q.2 - f q.1).sum := by
      have h1 : 25 * d * (J.map fun q => q.2 - q.1).sum =
          (J.map fun q => 25 * d * (q.2 - q.1)).sum := by
        clear hlen_ge hJ3_sum hsum_f hJ3_cov hJ3_le hJcov hJdisj hJsub hL_prop
        induction J with
        | nil => simp
        | cons a l ih => simp [ih, mul_add]
      rw [h1]
      clear h1 hlen_ge hJ3_sum hsum_f hJ3_cov hJ3_le hJcov hJdisj
      induction J with
      | nil => simp
      | cons a l ih =>
        simp only [List.map_cons, List.sum_cons]
        have ha := (hL_prop a (hJsub a (by simp))).2.2.2
        have hl := ih (fun q hq => hJsub q (List.mem_cons_of_mem _ hq))
        linarith
    have hcontra : 25 * d * (1 / 4) ≤ 3 * (2 * d) := by nlinarith
    nlinarith
  obtain ⟨t, ht, hgood⟩ := hex_good
  refine ⟨t, by linarith [ht.1], by linarith [ht.2], ?_⟩
  intro η hη
  have hη_abs : |η| ≤ 1 / (100 * d) := hη
  have ht_pos : 0 < t := by linarith [ht.1]
  have hB_pos : 0 < ((bohr Γ (t * ρ)).card : ℝ) :=
    Nat.cast_pos.2 (bohr_card_pos Γ (by positivity))
  have hBη_pos : 0 < ((bohr Γ ((1 + η) * (t * ρ))).card : ℝ) := by
    have h1η : 0 ≤ 1 + η := by
      have := (abs_le.1 hη_abs).1
      have : 1 / (100 * d) ≤ 1 / 100 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
      linarith
    exact Nat.cast_pos.2 (bohr_card_pos Γ (by positivity))
  by_cases hη0 : η = 0
  · subst hη0; simp
  · have h_pos : 0 < t * |η| := mul_pos ht_pos (abs_pos.2 hη0)
    have h_le8 : t * |η| ≤ 1 / 8 := by
      have h1 : |η| ≤ 1 / 100 := hη_abs.trans (by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith))
      nlinarith [ht.2]
    have hdiff := hgood (t * |η|) h_pos h_le8
    have hdiff2 : f (t + t * |η|) - f (t - t * |η|) ≤ 50 * d * |η| := by
      have ht_le1 : t ≤ 1 := by linarith [ht.2]
      have hmul : 50 * d * (t * |η|) ≤ 50 * d * |η| := by
        have hnn : 0 ≤ 50 * d * |η| := by positivity
        nlinarith
      linarith
    have h50_le : 50 * d * |η| ≤ 1 / 2 := by
      have hmul := mul_le_mul_of_nonneg_left hη_abs (show (0 : ℝ) ≤ 50 * d by positivity)
      have hsimp : 50 * d * (1 / (100 * d)) = 1 / 2 := by field_simp [hd_pos.ne']; ring
      linarith
    have hmono_pt : ∀ s₁ s₂ : ℝ, 1 / 2 ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ 1 → f s₁ ≤ f s₂ :=
      fun s₁ s₂ hs₁ h12 hs₂ => hf_mono ⟨hs₁, h12.trans hs₂⟩ ⟨hs₁.trans h12, hs₂⟩ h12
    have ht_lo : 1 / 2 ≤ t - t * |η| := by linarith [ht.1]
    have ht_hi : t + t * |η| ≤ 1 := by linarith [ht.2]
    have hreq : (1 + η) * (t * ρ) = (t + t * η) * ρ := by ring
    have hBη_pos' : 0 < ((bohr Γ ((t + t * η) * ρ)).card : ℝ) := by rwa [← hreq]
    rw [hreq]
    have hlog_hi : f (t + t * η) - f t ≤ 50 * d * |η| := by
      have h1 : f (t + t * η) ≤ f (t + t * |η|) :=
        hmono_pt _ _ (by nlinarith [ht.1, neg_abs_le η]) (by nlinarith [le_abs_self η]) ht_hi
      have h2 : f (t - t * |η|) ≤ f t :=
        hmono_pt _ _ ht_lo (by linarith) (by linarith [ht.2])
      linarith
    have hlog_lo : f t - f (t + t * η) ≤ 50 * d * |η| := by
      have h1 : f t ≤ f (t + t * |η|) :=
        hmono_pt _ _ (by linarith [ht.1]) (by linarith) ht_hi
      have h2 : f (t - t * |η|) ≤ f (t + t * η) :=
        hmono_pt _ _ ht_lo (by nlinarith [neg_abs_le η]) (by nlinarith [ht.2, le_abs_self η])
      linarith
    have hexp_le : ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 2 → Real.exp u ≤ 1 + 2 * u := by
      intro u hu0 hu1
      have h1 := Real.exp_bound (x := u) (n := 2) (by rw [abs_of_nonneg hu0]; linarith) (by norm_num)
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.factorial_zero,
        Nat.cast_one, div_one, pow_one, Nat.factorial_one, zero_add] at h1
      have habs := (abs_le.1 h1).2
      rw [abs_of_nonneg hu0] at habs
      norm_num at habs
      nlinarith
    constructor
    · -- Lower bound: (1 - 100 d |η|) |B| ≤ |B_{1+η}|
      have hdiv_ge : Real.exp (-(50 * d * |η|)) ≤
          ((bohr Γ ((t + t * η) * ρ)).card : ℝ) / ((bohr Γ (t * ρ)).card : ℝ) := by
        rw [← Real.exp_log (div_pos hBη_pos' hB_pos),
          Real.log_div hBη_pos'.ne' hB_pos.ne']
        exact Real.exp_le_exp.2 (by dsimp only [f] at hlog_lo; linarith)
      have h1sub : 1 - 100 * d * |η| ≤ Real.exp (-(50 * d * |η|)) := by
        have := Real.add_one_le_exp (-(50 * d * |η|))
        have hnn : 0 ≤ 50 * d * |η| := by positivity
        linarith
      have hmul := mul_le_mul_of_nonneg_right (h1sub.trans hdiv_ge) hB_pos.le
      rwa [div_mul_cancel₀ _ hB_pos.ne'] at hmul
    · -- Upper bound: |B_{1+η}| ≤ (1 + 100 d |η|) |B|
      have hdiv_le : ((bohr Γ ((t + t * η) * ρ)).card : ℝ) / ((bohr Γ (t * ρ)).card : ℝ) ≤
          Real.exp (50 * d * |η|) := by
        rw [← Real.exp_log (div_pos hBη_pos' hB_pos),
          Real.log_div hBη_pos'.ne' hB_pos.ne']
        exact Real.exp_le_exp.2 (by dsimp only [f] at hlog_hi; linarith)
      have h1add : Real.exp (50 * d * |η|) ≤ 1 + 100 * d * |η| := by
        have := hexp_le (50 * d * |η|) (by positivity) h50_le
        linarith
      have hmul := mul_le_mul_of_nonneg_right (hdiv_le.trans h1add) hB_pos.le
      rwa [div_mul_cancel₀ _ hB_pos.ne'] at hmul

/-- Translation stability of `μ_B` in `L^1` for a regular Bohr set `B`. -/
lemma norm_L1_muR_translate_sub_le {Γ : Finset (AddChar G ℂ)} {ρ δ : ℝ}
    (hρ : 0 < ρ) (hreg : IsRegularBohr Γ ρ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (100 * (Γ.card : ℝ)))
    {t : G} (ht : t ∈ bohr Γ (δ * ρ)) :
    ∑ x : G, |muR (bohr Γ ρ) (x - t) - muR (bohr Γ ρ) x| ≤ 200 * (Γ.card : ℝ) * δ := by
  let B := bohr Γ ρ
  let B_lo := bohr Γ ((1 - δ) * ρ)
  have hB_pos : (0 : ℝ) < (B.card : ℝ) := Nat.cast_pos.2 (bohr_card_pos Γ hρ.le)
  have hsub_lo : B_lo ⊆ B := bohr_mono_radius Γ (by nlinarith)
  have hsub_tr : B_lo ⊆ B.filter (fun x => x - t ∈ B) := by
    intro x hx
    rw [Finset.mem_filter]
    refine ⟨hsub_lo hx, ?_⟩
    have := sub_mem_bohr hx ht
    have heq : (1 - δ) * ρ + δ * ρ = ρ := by ring
    rwa [heq] at this
  have hreg_lo : (1 - 100 * (Γ.card : ℝ) * δ) * (B.card : ℝ) ≤ (B_lo.card : ℝ) := by
    have h := (hreg (-δ) (by rwa [abs_neg, abs_of_nonneg hδ0])).1
    rw [abs_neg, abs_of_nonneg hδ0] at h
    have heq : (1 + -δ) * ρ = (1 - δ) * ρ := by ring
    rwa [heq] at h
  -- Rewrite the L^1 norm using symmetric difference
  let Bt := B.image (fun y => y + t)
  have hBt_mem : ∀ x : G, x ∈ Bt ↔ x - t ∈ B := by
    intro x
    simp only [Bt, Finset.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩; simpa using hy
    · intro hx; exact ⟨x - t, hx, by abel⟩
  have hBt_card : Bt.card = B.card := Finset.card_image_of_injective B (add_left_injective t)
  have hterm : ∀ x : G, |muR B (x - t) - muR B x| =
      if (x ∈ Bt ∧ x ∉ B) ∨ (x ∉ Bt ∧ x ∈ B) then (B.card : ℝ)⁻¹ else 0 := by
    intro x
    unfold muR
    by_cases h1 : x ∈ Bt <;> by_cases h2 : x ∈ B
    · have h1' : x - t ∈ B := (hBt_mem x).1 h1
      simp [h1, h2, h1']
    · have h1' : x - t ∈ B := (hBt_mem x).1 h1
      simp [h1, h2, h1', abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg (α := ℝ) B.card))]
    · have h1' : x - t ∉ B := fun hc => h1 ((hBt_mem x).2 hc)
      simp [h1, h2, h1', abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg (α := ℝ) B.card))]
    · have h1' : x - t ∉ B := fun hc => h1 ((hBt_mem x).2 hc)
      simp [h1, h2, h1']
  change ∑ x : G, |muR B (x - t) - muR B x| ≤ 200 * (Γ.card : ℝ) * δ
  simp_rw [hterm]
  have hdisj : Disjoint (Bt \ B) (B \ Bt) := disjoint_sdiff_sdiff
  have hsum_eq : ∑ x : G, (if (x ∈ Bt ∧ x ∉ B) ∨ (x ∉ Bt ∧ x ∈ B) then (B.card : ℝ)⁻¹ else 0) =
      (((Bt \ B).card : ℝ) + ((B \ Bt).card : ℝ)) * (B.card : ℝ)⁻¹ := by
    have hpred : ∀ x : G, ((x ∈ Bt ∧ x ∉ B) ∨ (x ∉ Bt ∧ x ∈ B)) ↔ x ∈ (Bt \ B) ∪ (B \ Bt) := by
      intro x; simp [Finset.mem_union, Finset.mem_sdiff, and_comm]
    simp_rw [hpred, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hfilt : (Finset.univ.filter fun x => x ∈ (Bt \ B) ∪ (B \ Bt)) = (Bt \ B) ∪ (B \ Bt) := by
      ext x; simp
    rw [hfilt, Finset.card_union_of_disjoint hdisj, Nat.cast_add]
  rw [hsum_eq]
  have hcard_inter : (B ∩ Bt).card = (B.filter (fun x => x - t ∈ B)).card := by
    congr 1; ext x; simp [Finset.mem_inter, Finset.mem_filter, hBt_mem]
  have hcard_sdiff1 : (B \ Bt).card = B.card - (B ∩ Bt).card := by
    have := Finset.card_sdiff_add_card_inter B Bt
    omega
  have hcard_sdiff2 : (Bt \ B).card = B.card - (B ∩ Bt).card := by
    have := Finset.card_sdiff_add_card_inter Bt B
    rw [Finset.inter_comm, hBt_card] at this
    omega
  have hlo_le : B_lo.card ≤ (B ∩ Bt).card := by
    rw [hcard_inter]; exact Finset.card_le_card hsub_tr
  have hdiff_le : ((B \ Bt).card : ℝ) ≤ 100 * (Γ.card : ℝ) * δ * (B.card : ℝ) := by
    have hle_B : (B ∩ Bt).card ≤ B.card := Finset.card_le_card Finset.inter_subset_left
    rw [hcard_sdiff1, Nat.cast_sub hle_B]
    have hloR : (B_lo.card : ℝ) ≤ ((B ∩ Bt).card : ℝ) := Nat.cast_le.2 hlo_le
    linarith
  have hdiff2_le : ((Bt \ B).card : ℝ) ≤ 100 * (Γ.card : ℝ) * δ * (B.card : ℝ) := by
    rwa [hcard_sdiff2, ← hcard_sdiff1]
  have htot : ((Bt \ B).card : ℝ) + ((B \ Bt).card : ℝ) ≤
      200 * (Γ.card : ℝ) * δ * (B.card : ℝ) := by linarith
  calc (((Bt \ B).card : ℝ) + ((B \ Bt).card : ℝ)) * (B.card : ℝ)⁻¹
      ≤ (200 * (Γ.card : ℝ) * δ * (B.card : ℝ)) * (B.card : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right htot (by positivity)
    _ = 200 * (Γ.card : ℝ) * δ := by field_simp [hB_pos.ne']

/-- Regular convolution stability (`Lemma 4.4` of Schoen–Sisask):
if `B` is regular of rank `d` and `S ⊆ B_δ` is nonempty with `δ ≤ 1 / (100 d)`, then
`‖μ_B * μ_S - μ_B‖₁ ≤ 200 d δ`. -/
lemma norm_L1_convR_muR_sub_le {Γ : Finset (AddChar G ℂ)} {ρ δ : ℝ}
    (hρ : 0 < ρ) (hreg : IsRegularBohr Γ ρ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / (100 * (Γ.card : ℝ)))
    {S : Finset G} (hSne : S.Nonempty) (hSsub : S ⊆ bohr Γ (δ * ρ)) :
    ∑ x : G, |convR (muR (bohr Γ ρ)) (muR S) x - muR (bohr Γ ρ) x| ≤
      200 * (Γ.card : ℝ) * δ := by
  let B := bohr Γ ρ
  have hpt : ∀ x : G, |convR (muR B) (muR S) x - muR B x| ≤
      ∑ t : G, muR S t * |muR B (x - t) - muR B x| := by
    intro x
    rw [convR_comm]
    have hsub : convR (muR S) (muR B) x - muR B x =
        ∑ t : G, muR S t * (muR B (x - t) - muR B x) := by
      unfold convR
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_muR hSne, one_mul]
    rw [hsub]
    calc |∑ t : G, muR S t * (muR B (x - t) - muR B x)|
        ≤ ∑ t : G, |muR S t * (muR B (x - t) - muR B x)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ t : G, muR S t * |muR B (x - t) - muR B x| := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [abs_mul, abs_of_nonneg (muR_nonneg S t)]
  calc ∑ x : G, |convR (muR B) (muR S) x - muR B x|
      ≤ ∑ x : G, ∑ t : G, muR S t * |muR B (x - t) - muR B x| := Finset.sum_le_sum fun x _ => hpt x
    _ = ∑ t : G, muR S t * ∑ x : G, |muR B (x - t) - muR B x| := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => by rw [← Finset.mul_sum]
    _ ≤ ∑ t : G, muR S t * (200 * (Γ.card : ℝ) * δ) := by
        refine Finset.sum_le_sum fun t _ => ?_
        by_cases ht : t ∈ S
        · exact mul_le_mul_of_nonneg_left
            (norm_L1_muR_translate_sub_le hρ hreg hδ0 hδ (hSsub ht)) (muR_nonneg S t)
        · simp [muR, ht]
    _ = 200 * (Γ.card : ℝ) * δ := by
        rw [← Finset.sum_mul, sum_muR hSne, one_mul]

end BohrSets

/- ## Section 3: Elementary Khintchine and Croot–Sisask L^{2m}-Almost-Periodicity -/

section CrootSisask

/-- Elementary factorial inequality `2^k * k! ≤ (2k)!`. -/
private lemma two_pow_mul_factorial_le (k : ℕ) :
    2 ^ k * k.factorial ≤ (2 * k).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    rw [h1, Nat.factorial_succ, Nat.factorial_succ, pow_succ, Nat.factorial_succ]
    have hstep1 : 2 ^ k * 2 * ((k + 1) * k.factorial) = (2 * k + 2) * (2 ^ k * k.factorial) := by
      ring
    have hstep2 : (2 * k + 2) * (2 ^ k * k.factorial) ≤ (2 * k + 2) * (2 * k).factorial :=
      Nat.mul_le_mul_left _ ih
    have hstep3 : (2 * k).factorial ≤ (2 * k + 1) * (2 * k).factorial :=
      Nat.le_mul_of_pos_left _ (by omega)
    have hstep4 : (2 * k + 2) * (2 * k).factorial ≤
        (2 * k + 1 + 1) * ((2 * k + 1) * (2 * k).factorial) :=
      Nat.mul_le_mul_left (2 * k + 2) hstep3
    omega

/-- Double-factorial constant `K(m) = (2m)! / (2^m * m!)`. -/
private noncomputable def doubleFactR (m : ℕ) : ℝ :=
  ((2 * m).factorial : ℝ) / ((2 : ℝ) ^ m * (m.factorial : ℝ))

private lemma doubleFactR_zero : doubleFactR 0 = 1 := by
  simp [doubleFactR]

private lemma doubleFactR_nonneg (m : ℕ) : 0 ≤ doubleFactR m := by
  unfold doubleFactR; positivity

private lemma doubleFactR_le_pow (m : ℕ) : doubleFactR m ≤ (2 * (m : ℝ)) ^ m := by
  induction m with
  | zero => simp [doubleFactR]
  | succ m ih =>
    have hstep : doubleFactR (m + 1) = (2 * (m : ℝ) + 1) * doubleFactR m := by
      unfold doubleFactR
      have h1 : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
      rw [h1, Nat.factorial_succ, Nat.factorial_succ, pow_succ, Nat.factorial_succ]
      push_cast
      have h2 : (2 : ℝ) ^ m ≠ 0 := by positivity
      have h3 : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
      have h4 : ((m : ℝ) + 1) ≠ 0 := by positivity
      field_simp [h2, h3, h4]
      ring
    rw [hstep]
    have hpow : (2 * (m : ℝ)) ^ m ≤ (2 * ((m + 1 : ℕ) : ℝ)) ^ m :=
      pow_le_pow_left₀ (by positivity) (by push_cast; linarith) m
    have h1 : 2 * (m : ℝ) + 1 ≤ 2 * ((m + 1 : ℕ) : ℝ) := by push_cast; linarith
    calc (2 * (m : ℝ) + 1) * doubleFactR m
        ≤ (2 * ((m + 1 : ℕ) : ℝ)) * (2 * ((m + 1 : ℕ) : ℝ)) ^ m :=
          mul_le_mul h1 (ih.trans hpow) (doubleFactR_nonneg m) (by positivity)
      _ = (2 * ((m + 1 : ℕ) : ℝ)) ^ (m + 1) := by rw [pow_succ']

/-- Binomial parity identity: `(S + a)^(2m) + (S - a)^(2m) = 2 * ∑ j ∈ range (m+1), C(2m, 2j) S^(2(m-j)) a^(2j)`. -/
private lemma add_pow_add_sub_pow_even (S a : ℝ) (m : ℕ) :
    (S + a) ^ (2 * m) + (S - a) ^ (2 * m) =
      2 * ∑ j ∈ Finset.range (m + 1),
        ((Nat.choose (2 * m) (2 * j) : ℝ) * S ^ (2 * (m - j)) * a ^ (2 * j)) := by
  rw [add_pow, sub_eq_add_neg, add_pow, ← Finset.sum_add_distrib]
  have hpair : ∀ k ∈ Finset.range (2 * m + 1),
      S ^ k * a ^ (2 * m - k) * (Nat.choose (2 * m) k : ℝ) +
        S ^ k * (-a) ^ (2 * m - k) * (Nat.choose (2 * m) k : ℝ) =
      if Even k then 2 * ((Nat.choose (2 * m) k : ℝ) * S ^ k * a ^ (2 * m - k)) else 0 := by
    intro k hk
    have hkle : k ≤ 2 * m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    by_cases he : Even k
    · have he2 : Even (2 * m - k) := by
        rcases he with ⟨t, rfl⟩
        exact ⟨m - t, by omega⟩
      rw [if_pos he, he2.neg_pow]
      ring
    · have ho2 : Odd (2 * m - k) := by
        rw [Nat.not_even_iff_odd] at he
        rcases he with ⟨t, rfl⟩
        exact ⟨m - 1 - t, by omega⟩
      rw [if_neg he, ho2.neg_pow]
      ring
  have h1 : ∑ k ∈ Finset.range (2 * m + 1),
      (S ^ k * a ^ (2 * m - k) * (Nat.choose (2 * m) k : ℝ) +
        S ^ k * (-a) ^ (2 * m - k) * (Nat.choose (2 * m) k : ℝ)) =
      ∑ k ∈ Finset.range (2 * m + 1),
        if Even k then 2 * ((Nat.choose (2 * m) k : ℝ) * S ^ k * a ^ (2 * m - k)) else 0 :=
    Finset.sum_congr rfl hpair
  rw [h1, Finset.mul_sum]
  -- Reindex even `k = 2 * (m - j)` via `j ↦ 2 * (m - j)`
  have hbij : ∑ j ∈ Finset.range (m + 1),
      2 * ((Nat.choose (2 * m) (2 * j) : ℝ) * S ^ (2 * (m - j)) * a ^ (2 * j)) =
      ∑ k ∈ (Finset.range (2 * m + 1)).filter Even,
        2 * ((Nat.choose (2 * m) k : ℝ) * S ^ k * a ^ (2 * m - k)) := by
    refine Finset.sum_nbij (fun j => 2 * (m - j)) ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_filter, Finset.mem_range]
      have hjle : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      exact ⟨by omega, ⟨m - j, by omega⟩⟩
    · intro j₁ hj₁ j₂ hj₂ heq
      dsimp only at heq
      have h1' : j₁ ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj₁)
      have h2' : j₂ ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj₂)
      omega
    · intro k hk
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk
      rcases hk.2 with ⟨t, rfl⟩
      refine ⟨m - t, Finset.mem_coe.2 (Finset.mem_range.2 (by omega)), ?_⟩
      dsimp only; omega
    · intro j hj
      have hjle : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      have hsub : 2 * m - 2 * (m - j) = 2 * j := by omega
      have hch : Nat.choose (2 * m) (2 * (m - j)) = Nat.choose (2 * m) (2 * j) := by
        rw [← Nat.choose_symm (by omega : 2 * (m - j) ≤ 2 * m), hsub]
      rw [hsub, hch]
  rw [hbij, Finset.sum_filter]

/-- Coefficient inequality `C(2m, 2j) * K(m - j) ≤ K(m) * C(m, j)`. -/
private lemma choose_mul_doubleFactR_le {m j : ℕ} (hj : j ≤ m) :
    (Nat.choose (2 * m) (2 * j) : ℝ) * doubleFactR (m - j) ≤
      doubleFactR m * (Nat.choose m j : ℝ) := by
  unfold doubleFactR
  have h1 : (Nat.choose (2 * m) (2 * j) : ℝ) =
      ((2 * m).factorial : ℝ) / (((2 * j).factorial : ℝ) * ((2 * m - 2 * j).factorial : ℝ)) := by
    have := Nat.choose_mul_factorial_mul_factorial (show 2 * j ≤ 2 * m by omega)
    have hne1 : ((2 * j).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hne2 : ((2 * m - 2 * j).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hR : (Nat.choose (2 * m) (2 * j) : ℝ) * ((2 * j).factorial : ℝ) *
        ((2 * m - 2 * j).factorial : ℝ) = ((2 * m).factorial : ℝ) := by exact_mod_cast this
    field_simp [hne1, hne2]
    linarith
  have h2 : (Nat.choose m j : ℝ) =
      (m.factorial : ℝ) / ((j.factorial : ℝ) * ((m - j).factorial : ℝ)) := by
    have := Nat.choose_mul_factorial_mul_factorial hj
    have hne1 : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hne2 : ((m - j).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hR : (Nat.choose m j : ℝ) * (j.factorial : ℝ) * ((m - j).factorial : ℝ) =
        (m.factorial : ℝ) := by exact_mod_cast this
    field_simp [hne1, hne2]
    linarith
  have hsub : 2 * (m - j) = 2 * m - 2 * j := by omega
  rw [h1, h2, hsub]
  have h2pow : (2 : ℝ) ^ m = (2 : ℝ) ^ j * (2 : ℝ) ^ (m - j) := by
    rw [← pow_add, Nat.add_sub_of_le hj]
  have hfact : (2 : ℝ) ^ j * (j.factorial : ℝ) ≤ ((2 * j).factorial : ℝ) := by
    exact_mod_cast two_pow_mul_factorial_le j
  have hp1 : (0 : ℝ) < ((2 * j).factorial : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos _)
  have hp2 : (0 : ℝ) < ((2 * m - 2 * j).factorial : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos _)
  have hp3 : (0 : ℝ) < (2 : ℝ) ^ (m - j) := by positivity
  have hp4 : (0 : ℝ) < ((m - j).factorial : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos _)
  have hp5 : (0 : ℝ) < (m.factorial : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos _)
  have hp6 : (0 : ℝ) < (j.factorial : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos _)
  have hp7 : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hlhs : ((2 * m).factorial : ℝ) / (((2 * j).factorial : ℝ) * ((2 * m - 2 * j).factorial : ℝ)) *
      (((2 * m - 2 * j).factorial : ℝ) / ((2 : ℝ) ^ (m - j) * ((m - j).factorial : ℝ))) =
      ((2 * m).factorial : ℝ) / (((2 * j).factorial : ℝ) * ((2 : ℝ) ^ (m - j) * ((m - j).factorial : ℝ))) := by
    field_simp [hp1.ne', hp2.ne', hp3.ne', hp4.ne']
  have hrhs : ((2 * m).factorial : ℝ) / ((2 : ℝ) ^ m * (m.factorial : ℝ)) *
      ((m.factorial : ℝ) / ((j.factorial : ℝ) * ((m - j).factorial : ℝ))) =
      ((2 * m).factorial : ℝ) / (((2 : ℝ) ^ j * (j.factorial : ℝ)) * ((2 : ℝ) ^ (m - j) * ((m - j).factorial : ℝ))) := by
    rw [h2pow]
    field_simp [hp3.ne', hp4.ne', hp5.ne', hp6.ne', hp7.ne']
  rw [hlhs, hrhs]
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
    (mul_le_mul_of_nonneg_right hfact (by positivity))

/-- Elementary Khintchine moment bound for Rademacher sums (even power `2m`). -/
private lemma rademacher_even_moment_le :
    ∀ (r : ℕ) (m : ℕ) (c : Fin r → ℝ),
      ((2 : ℝ) ^ r)⁻¹ *
        ∑ ε : Fin r → Bool, (∑ i : Fin r, (if ε i then c i else -c i)) ^ (2 * m) ≤
      doubleFactR m * (∑ i : Fin r, c i ^ 2) ^ m
  | 0, m, c => by
    cases m with
    | zero => simp [doubleFactR_zero]
    | succ m =>
      simp only [pow_zero, inv_one, one_mul, Finset.univ_eq_empty, Finset.sum_empty,
        Fintype.sum_unique, zero_pow (by omega : 2 * (m + 1) ≠ 0),
        zero_pow (Nat.succ_ne_zero m), mul_zero, le_rfl]
  | r + 1, m, c => by
    let c' : Fin r → ℝ := fun i => c i.castSucc
    let a : ℝ := c (Fin.last r)
    -- Split sum over `Fin (r + 1) → Bool` into `ε' : Fin r → Bool` and `b : Bool`.
    have hsplit : ∑ ε : Fin (r + 1) → Bool,
        (∑ i : Fin (r + 1), (if ε i then c i else -c i)) ^ (2 * m) =
        ∑ ε' : Fin r → Bool,
          ((∑ i : Fin r, (if ε' i then c' i else -c' i)) + a) ^ (2 * m) +
        ∑ ε' : Fin r → Bool,
          ((∑ i : Fin r, (if ε' i then c' i else -c' i)) - a) ^ (2 * m) := by
      let e : (Fin (r + 1) → Bool) ≃ (Fin r → Bool) × Bool :=
        { toFun := fun ε => (fun i => ε i.castSucc, ε (Fin.last r))
          invFun := fun p => Fin.snoc p.1 p.2
          left_inv := fun ε => by
            ext i
            refine Fin.lastCases ?_ (fun j => ?_) i
            · simp [Fin.snoc]
            · simp [Fin.snoc]
          right_inv := fun p => by
            ext i
            · simp [Fin.snoc]
            · simp [Fin.snoc] }
      rw [Fintype.sum_equiv e _ (fun p =>
        ((∑ i : Fin r, (if p.1 i then c' i else -c' i)) + (if p.2 then a else -a)) ^ (2 * m))
        (fun ε => by
          rw [Fin.sum_univ_castSucc]
          rfl)]
      rw [Fintype.sum_prod_type]
      simp [Fintype.sum_bool, sub_eq_add_neg, Finset.sum_add_distrib]
    rw [hsplit, ← Finset.sum_add_distrib]
    simp_rw [add_pow_add_sub_pow_even, ← Finset.mul_sum]
    rw [Finset.sum_comm]
    have hpow2 : ((2 : ℝ) ^ (r + 1))⁻¹ * (2 * ∑ j ∈ Finset.range (m + 1),
        ∑ ε' : Fin r → Bool, (Nat.choose (2 * m) (2 * j) : ℝ) *
          (∑ i : Fin r, (if ε' i then c' i else -c' i)) ^ (2 * (m - j)) * a ^ (2 * j)) =
        ∑ j ∈ Finset.range (m + 1),
          (Nat.choose (2 * m) (2 * j) : ℝ) *
            (((2 : ℝ) ^ r)⁻¹ * ∑ ε' : Fin r → Bool,
              (∑ i : Fin r, (if ε' i then c' i else -c' i)) ^ (2 * (m - j))) * a ^ (2 * j) := by
      have h2cancel : ((2 : ℝ) ^ (r + 1))⁻¹ * 2 = ((2 : ℝ) ^ r)⁻¹ := by
        rw [pow_succ, mul_inv]
        field_simp [(pow_pos (show (0 : ℝ) < 2 by norm_num) r).ne']
      rw [← mul_assoc, h2cancel, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      ring
    rw [hpow2]
    let V : ℝ := ∑ i : Fin r, c' i ^ 2
    have hV_eq : ∑ i : Fin (r + 1), c i ^ 2 = V + a ^ 2 := by
      rw [Fin.sum_univ_castSucc]
    rw [hV_eq, add_pow]
    have hbin : doubleFactR m * ∑ j ∈ Finset.range (m + 1),
        V ^ j * (a ^ 2) ^ (m - j) * (Nat.choose m j : ℝ) =
        ∑ j ∈ Finset.range (m + 1),
          doubleFactR m * (Nat.choose m j : ℝ) * V ^ (m - j) * a ^ (2 * j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_nbij (fun j => m - j) ?_ ?_ ?_ ?_
      · intro j hj; rw [Finset.mem_range] at hj ⊢; omega
      · intro j₁ hj₁ j₂ hj₂ heq
        dsimp only at heq
        rw [Finset.mem_coe, Finset.mem_range] at hj₁ hj₂; omega
      · intro j hj
        rw [Finset.mem_coe, Finset.mem_range] at hj
        refine ⟨m - j, Finset.mem_coe.2 (Finset.mem_range.2 (by omega)), ?_⟩
        dsimp only; omega
      · intro j hj
        have hjle : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        have hsub : m - (m - j) = j := by omega
        rw [hsub, Nat.choose_symm hjle, ← pow_mul]
        ring
    rw [hbin]
    refine Finset.sum_le_sum fun j hj => ?_
    have hjle : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hih := rademacher_even_moment_le r (m - j) c'
    have hcoeff := choose_mul_doubleFactR_le hjle
    have ha2 : 0 ≤ a ^ (2 * j) := Even.pow_nonneg (even_two_mul j) a
    have hVnn : 0 ≤ V ^ (m - j) := pow_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) _
    calc (Nat.choose (2 * m) (2 * j) : ℝ) *
          (((2 : ℝ) ^ r)⁻¹ * ∑ ε' : Fin r → Bool,
            (∑ i : Fin r, (if ε' i then c' i else -c' i)) ^ (2 * (m - j))) * a ^ (2 * j)
        ≤ (Nat.choose (2 * m) (2 * j) : ℝ) * (doubleFactR (m - j) * V ^ (m - j)) * a ^ (2 * j) := by
          gcongr
      _ = ((Nat.choose (2 * m) (2 * j) : ℝ) * doubleFactR (m - j)) * V ^ (m - j) * a ^ (2 * j) := by
          ring
      _ ≤ (doubleFactR m * (Nat.choose m j : ℝ)) * V ^ (m - j) * a ^ (2 * j) := by
          gcongr

variable {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]

/-- Mean `L^{2m}` approximation error of empirical convolution over `r` i.i.d. samples from `A`. -/
private lemma empirical_conv_moment_le {A L : Finset G} (hA : A.Nonempty)
    {m r : ℕ} (hm : 1 ≤ m) (hr : 1 ≤ r) :
    ((A.card : ℝ) ^ r)⁻¹ *
      ∑ a : Fin r → A, ∑ x : G,
        (((r : ℝ)⁻¹ * ∑ i : Fin r, indR L (x - (a i).1)) -
          (A.card : ℝ)⁻¹ * convR (indR A) (indR L) x) ^ (2 * m) ≤
      2 * (2 * (m : ℝ) / (r : ℝ)) ^ m * (L.card : ℝ) := by
  have hApos : (0 : ℝ) < (A.card : ℝ) := Nat.cast_pos.2 hA.card_pos
  have hrpos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.2 (by omega)
  have hAr_pos : (0 : ℝ) < (A.card : ℝ) ^ r := pow_pos hApos r
  have hcard_fn : (Fintype.card (Fin r → A) : ℝ) = (A.card : ℝ) ^ r := by
    simp [Fintype.card_pi]
  let emp : (Fin r → A) → G → ℝ := fun a x => (r : ℝ)⁻¹ * ∑ i : Fin r, indR L (x - (a i).1)
  -- Step 1: Mean of `emp b x` over `b : Fin r → A` is `|A|⁻¹ * (1_A * 1_L)(x)`.
  have hmean : ∀ x : G,
      ((A.card : ℝ) ^ r)⁻¹ * ∑ b : Fin r → A, emp b x =
        (A.card : ℝ)⁻¹ * convR (indR A) (indR L) x := by
    intro x
    dsimp only [emp]
    rw [← Finset.mul_sum, Finset.sum_comm]
    have hcoord : ∀ i : Fin r, ∑ b : Fin r → A, indR L (x - (b i).1) =
        (A.card : ℝ) ^ (r - 1) * convR (indR A) (indR L) x := by
      intro i
      -- Split `Fin r → A` into `b i : A` and the remaining `r - 1` coordinates.
      let e : (Fin r → A) ≃ A × ({j : Fin r // j ≠ i} → A) :=
        (Equiv.piSplitAt i (fun _ : Fin r => A))
      have hsplit_e : ∑ b : Fin r → A, indR L (x - (b i).1) =
          ∑ p : A × ({j : Fin r // j ≠ i} → A), indR L (x - p.1.1) :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      rw [hsplit_e, Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      have hsub_card : Fintype.card ({j : Fin r // j ≠ i} → A) = A.card ^ (r - 1) := by
        simp only [Fintype.card_fun, Fintype.card_coe]
        congr 1
        rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
      rw [hsub_card, Nat.cast_pow]
      congr 1
      unfold convR indR
      have h1 : ∑ b : A, (if x - b.1 ∈ L then (1 : ℝ) else 0) =
          ∑ y ∈ A, if x - y ∈ L then (1 : ℝ) else 0 :=
        Finset.sum_coe_sort A (fun y => if x - y ∈ L then (1 : ℝ) else 0)
      rw [h1]
      have h2 : ∑ y : G, (if y ∈ A then (1 : ℝ) else 0) * (if x - y ∈ L then 1 else 0) =
          ∑ y ∈ A, if x - y ∈ L then (1 : ℝ) else 0 := by
        rw [← Finset.sum_subset (Finset.subset_univ A)]
        · refine Finset.sum_congr rfl fun y hy => by simp [hy]
        · intro y _ hy; simp [hy]
      rw [h2]
    simp_rw [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hpow : (A.card : ℝ) ^ r = (A.card : ℝ) * (A.card : ℝ) ^ (r - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hr, pow_succ']
    rw [hpow]
    field_simp [hrpos.ne', hApos.ne', (pow_pos hApos (r - 1)).ne']
  -- Step 2: Symmetrization via Jensen's inequality for `t ↦ t^(2m)` on `b : Fin r → A`.
  have hsym : ∀ x : G,
      ((A.card : ℝ) ^ r)⁻¹ * ∑ a : Fin r → A,
        (emp a x - (A.card : ℝ)⁻¹ * convR (indR A) (indR L) x) ^ (2 * m) ≤
      (((A.card : ℝ) ^ r)⁻¹ * ((A.card : ℝ) ^ r)⁻¹) *
        ∑ a : Fin r → A, ∑ b : Fin r → A, (emp a x - emp b x) ^ (2 * m) := by
    intro x
    have hjen : ∀ a : Fin r → A,
        (emp a x - (A.card : ℝ)⁻¹ * convR (indR A) (indR L) x) ^ (2 * m) ≤
          ((A.card : ℝ) ^ r)⁻¹ * ∑ b : Fin r → A, (emp a x - emp b x) ^ (2 * m) := by
      intro a
      have hconv := (even_two_mul m).convexOn_pow (𝕜 := ℝ)
      have hsum_w : ∑ _b : Fin r → A, ((A.card : ℝ) ^ r)⁻¹ = 1 := by
        simp [hcard_fn, hAr_pos.ne']
      have hpt := hconv.map_sum_le (t := Finset.univ) (w := fun _ : Fin r → A => ((A.card : ℝ) ^ r)⁻¹)
        (p := fun b => emp a x - emp b x) (fun _ _ => by positivity) hsum_w (fun _ _ => trivial)
      simp only [smul_eq_mul] at hpt
      have havg : ∑ b : Fin r → A, ((A.card : ℝ) ^ r)⁻¹ * (emp a x - emp b x) =
          emp a x - (A.card : ℝ)⁻¹ * convR (indR A) (indR L) x := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, hcard_fn, mul_sub, inv_mul_cancel_left₀ hAr_pos.ne', hmean x]
      rw [havg, ← Finset.mul_sum] at hpt
      exact hpt
    calc ((A.card : ℝ) ^ r)⁻¹ * ∑ a : Fin r → A,
            (emp a x - (A.card : ℝ)⁻¹ * convR (indR A) (indR L) x) ^ (2 * m)
        ≤ ((A.card : ℝ) ^ r)⁻¹ * ∑ a : Fin r → A,
            (((A.card : ℝ) ^ r)⁻¹ * ∑ b : Fin r → A, (emp a x - emp b x) ^ (2 * m)) := by
          gcongr with a _
          exact hjen a
      _ = (((A.card : ℝ) ^ r)⁻¹ * ((A.card : ℝ) ^ r)⁻¹) *
            ∑ a : Fin r → A, ∑ b : Fin r → A, (emp a x - emp b x) ^ (2 * m) := by
          rw [← Finset.mul_sum, mul_assoc]
  -- Step 3: Introduce Rademacher signs via coordinatewise swapping of `(a i, b i)`.
  have hrad : ∀ x : G,
      ∑ a : Fin r → A, ∑ b : Fin r → A, (emp a x - emp b x) ^ (2 * m) =
        ((2 : ℝ) ^ r)⁻¹ * ∑ ε : Fin r → Bool,
          ∑ a : Fin r → A, ∑ b : Fin r → A,
            ((r : ℝ)⁻¹ * ∑ i : Fin r,
              (if ε i then (indR L (x - (a i).1) - indR L (x - (b i).1))
               else -(indR L (x - (a i).1) - indR L (x - (b i).1)))) ^ (2 * m) := by
    intro x
    have hinv : ∀ ε : Fin r → Bool,
        ∑ a : Fin r → A, ∑ b : Fin r → A,
          ((r : ℝ)⁻¹ * ∑ i : Fin r,
            (if ε i then (indR L (x - (a i).1) - indR L (x - (b i).1))
             else -(indR L (x - (a i).1) - indR L (x - (b i).1)))) ^ (2 * m) =
        ∑ a : Fin r → A, ∑ b : Fin r → A, (emp a x - emp b x) ^ (2 * m) := by
      intro ε
      let swap : ((Fin r → A) × (Fin r → A)) ≃ ((Fin r → A) × (Fin r → A)) :=
        { toFun := fun p => (fun i => if ε i then p.1 i else p.2 i,
                             fun i => if ε i then p.2 i else p.1 i)
          invFun := fun p => (fun i => if ε i then p.1 i else p.2 i,
                              fun i => if ε i then p.2 i else p.1 i)
          left_inv := fun p => by
            ext i <;> by_cases h : ε i <;> simp [h]
          right_inv := fun p => by
            ext i <;> by_cases h : ε i <;> simp [h] }
      rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
      refine Fintype.sum_equiv swap _ _ fun p => ?_
      dsimp only [emp, swap]
      congr 1
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : ε i <;> simp [h]
    simp_rw [hinv, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard_bool : (Fintype.card (Fin r → Bool) : ℝ) = (2 : ℝ) ^ r := by simp
    rw [hcard_bool, inv_mul_cancel_left₀ (by positivity)]
  -- Step 4: Apply Khintchine and sum over `x : G`.
  have hpoint : ∀ x : G,
      ∑ a : Fin r → A, ∑ b : Fin r → A, (emp a x - emp b x) ^ (2 * m) ≤
        ((r : ℝ)⁻¹ ^ (2 * m) * doubleFactR m * (r : ℝ) ^ (m - 1)) *
          ∑ a : Fin r → A, ∑ b : Fin r → A,
            ∑ i : Fin r, (indR L (x - (a i).1) + indR L (x - (b i).1)) := by
    intro x
    rw [hrad x]
    have hswap_sum :
        ((2 : ℝ) ^ r)⁻¹ * ∑ ε : Fin r → Bool,
          ∑ a : Fin r → A, ∑ b : Fin r → A,
            ((r : ℝ)⁻¹ * ∑ i : Fin r,
              (if ε i then (indR L (x - (a i).1) - indR L (x - (b i).1))
               else -(indR L (x - (a i).1) - indR L (x - (b i).1)))) ^ (2 * m) =
        (r : ℝ)⁻¹ ^ (2 * m) *
          ∑ a : Fin r → A, ∑ b : Fin r → A,
            (((2 : ℝ) ^ r)⁻¹ * ∑ ε : Fin r → Bool,
              (∑ i : Fin r,
                (if ε i then (indR L (x - (a i).1) - indR L (x - (b i).1))
                 else -(indR L (x - (a i).1) - indR L (x - (b i).1)))) ^ (2 * m)) := by
      simp_rw [mul_pow, ← Finset.mul_sum]
      rw [Finset.sum_comm]
      have hcomm2 : ∀ a : Fin r → A,
          ∑ ε : Fin r → Bool, ∑ b : Fin r → A,
            (∑ i : Fin r, (if ε i then (indR L (x - (a i).1) - indR L (x - (b i).1))
              else -(indR L (x - (a i).1) - indR L (x - (b i).1)))) ^ (2 * m) =
          ∑ b : Fin r → A, ∑ ε : Fin r → Bool,
            (∑ i : Fin r, (if ε i then (indR L (x - (a i).1) - indR L (x - (b i).1))
              else -(indR L (x - (a i).1) - indR L (x - (b i).1)))) ^ (2 * m) :=
        fun a => Finset.sum_comm
      simp_rw [hcomm2]
      ring
    rw [hswap_sum]
    have hle_inner : ∀ (a b : Fin r → A),
        ((2 : ℝ) ^ r)⁻¹ * ∑ ε : Fin r → Bool,
          (∑ i : Fin r,
            (if ε i then (indR L (x - (a i).1) - indR L (x - (b i).1))
             else -(indR L (x - (a i).1) - indR L (x - (b i).1)))) ^ (2 * m) ≤
        doubleFactR m * (r : ℝ) ^ (m - 1) *
          ∑ i : Fin r, (indR L (x - (a i).1) + indR L (x - (b i).1)) := by
      intro a b
      have hkh := rademacher_even_moment_le r m (fun i => indR L (x - (a i).1) - indR L (x - (b i).1))
      have hsq_le_one : ∀ i : Fin r, (indR L (x - (a i).1) - indR L (x - (b i).1)) ^ 2 ≤ 1 := by
        intro i; unfold indR; split_ifs <;> norm_num
      have hsq_le_sum : ∀ i : Fin r,
          (indR L (x - (a i).1) - indR L (x - (b i).1)) ^ 2 ≤
            indR L (x - (a i).1) + indR L (x - (b i).1) := by
        intro i; unfold indR; split_ifs <;> norm_num
      have hsum_le_r : ∑ i : Fin r, (indR L (x - (a i).1) - indR L (x - (b i).1)) ^ 2 ≤ (r : ℝ) := by
        calc ∑ i : Fin r, (indR L (x - (a i).1) - indR L (x - (b i).1)) ^ 2
            ≤ ∑ _i : Fin r, (1 : ℝ) := Finset.sum_le_sum fun i _ => hsq_le_one i
          _ = (r : ℝ) := by simp
      have hsum_nn : 0 ≤ ∑ i : Fin r, (indR L (x - (a i).1) - indR L (x - (b i).1)) ^ 2 :=
        Finset.sum_nonneg fun i _ => sq_nonneg _
      have hpow_split :
          (∑ i : Fin r, (indR L (x - (a i).1) - indR L (x - (b i).1)) ^ 2) ^ m ≤
            (r : ℝ) ^ (m - 1) * ∑ i : Fin r, (indR L (x - (a i).1) + indR L (x - (b i).1)) := by
        conv_lhs => rw [← Nat.sub_add_cancel hm, pow_succ]
        exact mul_le_mul (pow_le_pow_left₀ hsum_nn hsum_le_r (m - 1))
          (Finset.sum_le_sum fun i _ => hsq_le_sum i) hsum_nn (by positivity)
      calc _ ≤ doubleFactR m * (∑ i : Fin r, (indR L (x - (a i).1) - indR L (x - (b i).1)) ^ 2) ^ m := hkh
        _ ≤ doubleFactR m * ((r : ℝ) ^ (m - 1) * ∑ i : Fin r, (indR L (x - (a i).1) + indR L (x - (b i).1))) :=
            mul_le_mul_of_nonneg_left hpow_split (doubleFactR_nonneg m)
        _ = _ := by ring
    calc (r : ℝ)⁻¹ ^ (2 * m) * ∑ a : Fin r → A, ∑ b : Fin r → A, _
        ≤ (r : ℝ)⁻¹ ^ (2 * m) * ∑ a : Fin r → A, ∑ b : Fin r → A,
            (doubleFactR m * (r : ℝ) ^ (m - 1) *
              ∑ i : Fin r, (indR L (x - (a i).1) + indR L (x - (b i).1))) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hle_inner a b) (by positivity)
      _ = ((r : ℝ)⁻¹ ^ (2 * m) * doubleFactR m * (r : ℝ) ^ (m - 1)) *
            ∑ a : Fin r → A, ∑ b : Fin r → A,
              ∑ i : Fin r, (indR L (x - (a i).1) + indR L (x - (b i).1)) := by
          simp_rw [← Finset.mul_sum]; ring
  -- Step 5: Combine everything and sum over `x : G`.
  have hsum_L : ∀ (a b : Fin r → A) (i : Fin r),
      ∑ x : G, (indR L (x - (a i).1) + indR L (x - (b i).1)) = 2 * (L.card : ℝ) := by
    intro a b i
    rw [Finset.sum_add_distrib]
    have h1 : ∑ x : G, indR L (x - (a i).1) = (L.card : ℝ) :=
      (Fintype.sum_equiv (Equiv.subRight (a i).1) _ (fun z => indR L z) (fun _ => rfl)).trans (sum_indR L)
    have h2 : ∑ x : G, indR L (x - (b i).1) = (L.card : ℝ) :=
      (Fintype.sum_equiv (Equiv.subRight (b i).1) _ (fun z => indR L z) (fun _ => rfl)).trans (sum_indR L)
    linarith
  calc ((A.card : ℝ) ^ r)⁻¹ *
        ∑ a : Fin r → A, ∑ x : G,
          (emp a x - (A.card : ℝ)⁻¹ * convR (indR A) (indR L) x) ^ (2 * m)
      = ∑ x : G, ((A.card : ℝ) ^ r)⁻¹ *
          ∑ a : Fin r → A, (emp a x - (A.card : ℝ)⁻¹ * convR (indR A) (indR L) x) ^ (2 * m) := by
        rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ x : G, (((A.card : ℝ) ^ r)⁻¹ * ((A.card : ℝ) ^ r)⁻¹) *
          (((r : ℝ)⁻¹ ^ (2 * m) * doubleFactR m * (r : ℝ) ^ (m - 1)) *
            ∑ a : Fin r → A, ∑ b : Fin r → A,
              ∑ i : Fin r, (indR L (x - (a i).1) + indR L (x - (b i).1))) := by
        refine Finset.sum_le_sum fun x _ => (hsym x).trans ?_
        exact mul_le_mul_of_nonneg_left (hpoint x) (by positivity)
    _ = (((A.card : ℝ) ^ r)⁻¹ * ((A.card : ℝ) ^ r)⁻¹) *
          ((r : ℝ)⁻¹ ^ (2 * m) * doubleFactR m * (r : ℝ) ^ (m - 1)) *
          ∑ a : Fin r → A, ∑ b : Fin r → A, ∑ i : Fin r,
            ∑ x : G, (indR L (x - (a i).1) + indR L (x - (b i).1)) := by
        simp_rw [← Finset.mul_sum]
        rw [Finset.sum_comm]
        have hc1 : ∀ a : Fin r → A,
            ∑ x : G, ∑ b : Fin r → A, ∑ i : Fin r, (indR L (x - (a i).1) + indR L (x - (b i).1)) =
            ∑ b : Fin r → A, ∑ i : Fin r, ∑ x : G, (indR L (x - (a i).1) + indR L (x - (b i).1)) := by
          intro a
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => Finset.sum_comm
        simp_rw [hc1]
        ring
    _ = 2 * doubleFactR m * (r : ℝ)⁻¹ ^ m * (L.card : ℝ) := by
        simp_rw [hsum_L, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          hcard_fn]
        have hr_pow : (r : ℝ)⁻¹ ^ (2 * m) * (r : ℝ) ^ (m - 1) * (r : ℝ) = (r : ℝ)⁻¹ ^ m := by
          have h1 : (r : ℝ) ^ (m - 1) * (r : ℝ) = (r : ℝ) ^ m := by
            conv_rhs => rw [← Nat.sub_add_cancel hm, pow_succ]
          rw [mul_assoc, h1, inv_pow, inv_pow, two_mul, pow_add]
          field_simp [(pow_pos hrpos m).ne']
        have hAr_cancel : ((A.card : ℝ) ^ r)⁻¹ * ((A.card : ℝ) ^ r)⁻¹ *
            ((A.card : ℝ) ^ r * ((A.card : ℝ) ^ r)) = 1 := by
          field_simp [hAr_pos.ne']
        calc (((A.card : ℝ) ^ r)⁻¹ * ((A.card : ℝ) ^ r)⁻¹) *
              ((r : ℝ)⁻¹ ^ (2 * m) * doubleFactR m * (r : ℝ) ^ (m - 1)) *
              ((A.card : ℝ) ^ r * ((A.card : ℝ) ^ r * ((r : ℝ) * (2 * (L.card : ℝ)))))
            = (((A.card : ℝ) ^ r)⁻¹ * ((A.card : ℝ) ^ r)⁻¹ *
                ((A.card : ℝ) ^ r * (A.card : ℝ) ^ r)) *
              (2 * doubleFactR m * ((r : ℝ)⁻¹ ^ (2 * m) * (r : ℝ) ^ (m - 1) * (r : ℝ)) *
                (L.card : ℝ)) := by ring
          _ = 2 * doubleFactR m * (r : ℝ)⁻¹ ^ m * (L.card : ℝ) := by rw [hAr_cancel, one_mul, hr_pow]
    _ ≤ 2 * (2 * (m : ℝ) / (r : ℝ)) ^ m * (L.card : ℝ) := by
        rw [div_eq_mul_inv, mul_pow]
        have hdf := doubleFactR_le_pow m
        calc 2 * doubleFactR m * (r : ℝ)⁻¹ ^ m * (L.card : ℝ)
            = doubleFactR m * (2 * (r : ℝ)⁻¹ ^ m * (L.card : ℝ)) := by ring
          _ ≤ (2 * (m : ℝ)) ^ m * (2 * (r : ℝ)⁻¹ ^ m * (L.card : ℝ)) :=
              mul_le_mul_of_nonneg_right hdf (by positivity)
          _ = 2 * ((2 * (m : ℝ)) ^ m * (r : ℝ)⁻¹ ^ m) * (L.card : ℝ) := by ring

set_option maxHeartbeats 800000 in
/-- Croot–Sisask `L^{2m}`-almost-periodicity (`Theorem 2.1` of Schoen–Sisask):
if `|A + S| ≤ K |A|`, then there is `T ⊆ S` with `|T| ≥ (99/100) K^{-r} |S|` where
`r = ⌈1600 m k^2 / ε^2⌉ + 1` such that for all `t ∈ k T - k T`,
`‖1_A * 1_L(· + t) - 1_A * 1_L‖_{2m} ≤ ε |A| |L|^{1/(2m)}`. -/
lemma croot_sisask_L2m {A L S : Finset G} (hA : A.Nonempty) (hS : S.Nonempty)
    {K ε : ℝ} (hK : 1 ≤ K) (hAS : ((A.image (fun a => a) ×ˢ S).image (fun p => p.1 + p.2)).card ≤
      K * (A.card : ℝ))
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) :
    let r : ℕ := Nat.ceil (1600 * (m : ℝ) * (k : ℝ) ^ 2 / ε ^ 2) + 1
    ∃ T : Finset G, T ⊆ S ∧
      (99 / 100 : ℝ) * K⁻¹ ^ r * (S.card : ℝ) ≤ (T.card : ℝ) ∧
      ∀ (t₁ t₂ : Fin k → G), (∀ i, t₁ i ∈ T) → (∀ i, t₂ i ∈ T) →
        (∑ x : G, |convR (indR A) (indR L) (x + ∑ i : Fin k, (t₁ i - t₂ i)) -
            convR (indR A) (indR L) x| ^ (2 * m : ℝ)) ^ (1 / (2 * m : ℝ)) ≤
          ε * (A.card : ℝ) * (L.card : ℝ) ^ (1 / (2 * m : ℝ)) := by
  intro r
  have hr_pos_nat : 1 ≤ r := Nat.succ_le_succ (Nat.zero_le _)
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.2 hr_pos_nat
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.2 hm
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.2 hk
  have h2m_ge1 : (1 : ℝ) ≤ (2 * m : ℝ) := by exact_mod_cast (show 1 ≤ 2 * m by omega)
  have h2m_pos : (0 : ℝ) < (2 * m : ℝ) := by positivity
  have hApos : (0 : ℝ) < (A.card : ℝ) := Nat.cast_pos.2 hA.card_pos
  have hSpos : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.2 hS.card_pos
  have hKpos : (0 : ℝ) < K := by linarith
  let emp : (Fin r → A) → G → ℝ := fun a x => (r : ℝ)⁻¹ * ∑ i : Fin r, indR L (x - (a i).1)
  let err : (Fin r → A) → ℝ := fun a =>
    ∑ x : G, (emp a x - (A.card : ℝ)⁻¹ * convR (indR A) (indR L) x) ^ (2 * m)
  let thresh : ℝ := (ε / (2 * (k : ℝ))) ^ (2 * m) * (L.card : ℝ)
  let Ω : Finset (Fin r → A) := Finset.univ.filter fun a => err a ≤ thresh
  have hcard_fn : (Fintype.card (Fin r → A) : ℝ) = (A.card : ℝ) ^ r := by
    simp [Fintype.card_pi]
  -- Step 1: Bound `|Ω| ≥ (99/100) * |A|^r` via Markov's inequality.
  have hΩ_card : (99 / 100 : ℝ) * (A.card : ℝ) ^ r ≤ (Ω.card : ℝ) := by
    by_cases hL : L.card = 0
    · have hL_empty : L = ∅ := Finset.card_eq_zero.1 hL
      have hΩ_univ : Ω = Finset.univ := by
        ext a
        simp only [Ω, Finset.mem_filter, Finset.mem_univ, true_and, err, emp, thresh, hL_empty,
          Finset.card_empty, Nat.cast_zero, mul_zero]
        have hzero : ∀ x : G,
            ((r : ℝ)⁻¹ * ∑ i : Fin r, indR (∅ : Finset G) (x - (a i).1) -
              (A.card : ℝ)⁻¹ * convR (indR A) (indR (∅ : Finset G)) x) = 0 := by
          intro x; simp [indR, convR]
        simp [hzero, zero_pow (by omega : 2 * m ≠ 0)]
      rw [hΩ_univ, Finset.card_univ, hcard_fn]
      nlinarith [pow_pos hApos r]
    · have hLpos : (0 : ℝ) < (L.card : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hL)
      have hthresh_pos : 0 < thresh := by positivity
      have hmom := empirical_conv_moment_le hA hm hr_pos_nat (L := L)
      have hr_ge : 1600 * (m : ℝ) * (k : ℝ) ^ 2 / ε ^ 2 ≤ (r : ℝ) := by
        have h1 : 1600 * (m : ℝ) * (k : ℝ) ^ 2 / ε ^ 2 ≤
            (Nat.ceil (1600 * (m : ℝ) * (k : ℝ) ^ 2 / ε ^ 2) : ℝ) := Nat.le_ceil _
        have h2 : (r : ℝ) = (Nat.ceil (1600 * (m : ℝ) * (k : ℝ) ^ 2 / ε ^ 2) : ℝ) + 1 := by
          simp [r]
        linarith
      have hratio : 2 * (m : ℝ) / (r : ℝ) ≤ (1 / 200 : ℝ) * (ε / (2 * (k : ℝ))) ^ 2 := by
        have h1 : (r : ℝ)⁻¹ ≤ (1600 * (m : ℝ) * (k : ℝ) ^ 2 / ε ^ 2)⁻¹ :=
          inv_anti₀ (by positivity) hr_ge
        calc 2 * (m : ℝ) / (r : ℝ) = 2 * (m : ℝ) * (r : ℝ)⁻¹ := div_eq_mul_inv _ _
          _ ≤ 2 * (m : ℝ) * (1600 * (m : ℝ) * (k : ℝ) ^ 2 / ε ^ 2)⁻¹ :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = (1 / 200 : ℝ) * (ε / (2 * (k : ℝ))) ^ 2 := by
              field_simp [hm_pos.ne', hk_pos.ne', hε0.ne']; ring
      have hpow_ratio : (2 * (m : ℝ) / (r : ℝ)) ^ m ≤
          (1 / 200 : ℝ) * (ε / (2 * (k : ℝ))) ^ (2 * m) := by
        have h1 : (2 * (m : ℝ) / (r : ℝ)) ^ m ≤
            ((1 / 200 : ℝ) * (ε / (2 * (k : ℝ))) ^ 2) ^ m :=
          pow_le_pow_left₀ (by positivity) hratio m
        rw [mul_pow, ← pow_mul] at h1
        have h200 : (1 / 200 : ℝ) ^ m ≤ (1 / 200 : ℝ) ^ 1 :=
          pow_le_pow_of_le_one (by positivity) (by norm_num) hm
        rw [pow_one] at h200
        exact h1.trans (mul_le_mul_of_nonneg_right h200 (by positivity))
      have hmom2 : ((A.card : ℝ) ^ r)⁻¹ * ∑ a : Fin r → A, err a ≤ (1 / 100 : ℝ) * thresh := by
        calc ((A.card : ℝ) ^ r)⁻¹ * ∑ a : Fin r → A, err a
            ≤ 2 * (2 * (m : ℝ) / (r : ℝ)) ^ m * (L.card : ℝ) := hmom
          _ ≤ 2 * ((1 / 200 : ℝ) * (ε / (2 * (k : ℝ))) ^ (2 * m)) * (L.card : ℝ) := by
              gcongr
          _ = (1 / 100 : ℝ) * thresh := by dsimp only [thresh]; ring
      let Ωc : Finset (Fin r → A) := Finset.univ.filter fun a => ¬ (err a ≤ thresh)
      have hmarkov : (Ωc.card : ℝ) * thresh ≤ ∑ a : Fin r → A, err a := by
        calc (Ωc.card : ℝ) * thresh
            = ∑ _a ∈ Ωc, thresh := by simp
          _ ≤ ∑ a ∈ Ωc, err a := Finset.sum_le_sum fun a ha => by
              have hlt := (Finset.mem_filter.1 ha).2
              linarith
          _ ≤ ∑ a : Fin r → A, err a := Finset.sum_le_univ_sum_of_nonneg fun a =>
              Finset.sum_nonneg fun x _ => Even.pow_nonneg (even_two_mul m) _
      have hΩc_le : (Ωc.card : ℝ) ≤ (1 / 100 : ℝ) * (A.card : ℝ) ^ r := by
        have h1 : (Ωc.card : ℝ) * thresh ≤ (1 / 100 : ℝ) * (A.card : ℝ) ^ r * thresh := by
          have := mul_le_mul_of_nonneg_left hmom2 (show (0 : ℝ) ≤ (A.card : ℝ) ^ r by positivity)
          rw [mul_inv_cancel_left₀ (pow_pos hApos r).ne'] at this
          linarith
        exact le_of_mul_le_mul_right h1 hthresh_pos
      have hpart : Ω.card + Ωc.card = Fintype.card (Fin r → A) := by
        simpa [Ω, Ωc] using Finset.card_filter_add_card_filter_not (s := Finset.univ)
          (p := fun a : Fin r → A => err a ≤ thresh)
      have hpartR : (Ω.card : ℝ) + (Ωc.card : ℝ) = (A.card : ℝ) ^ r := by
        rw [← hcard_fn]; exact_mod_cast hpart
      linarith
  -- Step 2: Pigeonhole over `u : Fin r → (A + S)` to find `T ⊆ S`.
  let AS : Finset G := (A.image (fun a => a) ×ˢ S).image (fun p => p.1 + p.2)
  have hAS_mem : ∀ (a : A) (s : G), s ∈ S → a.1 + s ∈ AS := by
    intro a s hs
    exact Finset.mem_image.2 ⟨(a.1, s), Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ a.2, hs⟩, rfl⟩
  let φ : (Fin r → A) × G → (Fin r → AS) := fun p i =>
    if hs : p.2 ∈ S then ⟨(p.1 i).1 + p.2, hAS_mem (p.1 i) p.2 hs⟩
    else ⟨(p.1 i).1 + hS.choose, hAS_mem (p.1 i) hS.choose hS.choose_spec⟩
  have hAS_ne : AS.Nonempty := ⟨hA.choose + hS.choose, hAS_mem ⟨hA.choose, hA.choose_spec⟩ hS.choose hS.choose_spec⟩
  have hAS_pos : (0 : ℝ) < (AS.card : ℝ) := Nat.cast_pos.2 hAS_ne.card_pos
  have hcard_AS_fn : (Fintype.card (Fin r → AS) : ℝ) = (AS.card : ℝ) ^ r := by
    simp [Fintype.card_pi]
  have hsum_fibers : ∑ u : Fin r → AS, ((Ω ×ˢ S).filter fun p => φ p = u).card =
      Ω.card * S.card := by
    rw [← Finset.card_product, Finset.card_eq_sum_card_fiberwise (f := φ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
  have hex_u : ∃ u : Fin r → AS,
      (Ω.card : ℝ) * (S.card : ℝ) ≤ (AS.card : ℝ) ^ r *
        (((Ω ×ˢ S).filter fun p => φ p = u).card : ℝ) := by
    have huniv_ne : (Finset.univ : Finset (Fin r → AS)).Nonempty :=
      ⟨fun _ => ⟨hAS_ne.choose, hAS_ne.choose_spec⟩, Finset.mem_univ _⟩
    by_contra hall
    push Not at hall
    have hlt : ∑ u : Fin r → AS, (((Ω ×ˢ S).filter fun p => φ p = u).card : ℝ) * (AS.card : ℝ) ^ r <
        ∑ _u : Fin r → AS, (Ω.card : ℝ) * (S.card : ℝ) := by
      refine Finset.sum_lt_sum_of_nonempty huniv_ne fun u _ => ?_
      linarith [hall u]
    rw [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard_AS_fn] at hlt
    have hsumR : ∑ u : Fin r → AS, (((Ω ×ˢ S).filter fun p => φ p = u).card : ℝ) =
        (Ω.card : ℝ) * (S.card : ℝ) := by exact_mod_cast hsum_fibers
    rw [hsumR] at hlt
    linarith
  obtain ⟨u₀, hu₀⟩ := hex_u
  let fib := (Ω ×ˢ S).filter fun p => φ p = u₀
  let T : Finset G := fib.image Prod.snd
  have hT_sub : T ⊆ S := by
    intro s hs
    rcases Finset.mem_image.1 hs with ⟨p, hp, rfl⟩
    exact (Finset.mem_product.1 (Finset.mem_filter.1 hp).1).2
  have hT_card_eq : T.card = fib.card := by
    refine Finset.card_image_of_injOn ?_
    intro p₁ hp₁ p₂ hp₂ hs_eq
    have hp₁' := Finset.mem_filter.1 hp₁
    have hp₂' := Finset.mem_filter.1 hp₂
    have hs₁ : p₁.2 ∈ S := (Finset.mem_product.1 hp₁'.1).2
    have hs₂ : p₂.2 ∈ S := (Finset.mem_product.1 hp₂'.1).2
    refine Prod.ext ?_ hs_eq
    funext i
    have hφ : (φ p₁ i).1 = (φ p₂ i).1 := by rw [hp₁'.2, hp₂'.2]
    dsimp only [φ] at hφ
    rw [dif_pos hs₁, dif_pos hs₂] at hφ
    change (p₁.1 i).1 + p₁.2 = (p₂.1 i).1 + p₂.2 at hφ
    change p₁.2 = p₂.2 at hs_eq
    rw [hs_eq] at hφ
    exact Subtype.ext (add_right_cancel hφ)
  have hT_size : (99 / 100 : ℝ) * K⁻¹ ^ r * (S.card : ℝ) ≤ (T.card : ℝ) := by
    rw [hT_card_eq]
    have hAS_pow : (AS.card : ℝ) ^ r ≤ (K * (A.card : ℝ)) ^ r :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hAS r
    have h1 : (99 / 100 : ℝ) * (A.card : ℝ) ^ r * (S.card : ℝ) ≤
        K ^ r * (A.card : ℝ) ^ r * (fib.card : ℝ) := by
      calc (99 / 100 : ℝ) * (A.card : ℝ) ^ r * (S.card : ℝ)
          ≤ (Ω.card : ℝ) * (S.card : ℝ) := mul_le_mul_of_nonneg_right hΩ_card hSpos.le
        _ ≤ (AS.card : ℝ) ^ r * (fib.card : ℝ) := hu₀
        _ ≤ (K * (A.card : ℝ)) ^ r * (fib.card : ℝ) :=
            mul_le_mul_of_nonneg_right hAS_pow (Nat.cast_nonneg _)
        _ = K ^ r * (A.card : ℝ) ^ r * (fib.card : ℝ) := by rw [mul_pow]
    have hKA_pos : (0 : ℝ) < K ^ r * (A.card : ℝ) ^ r := by positivity
    have hmul := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hKA_pos.le)
    calc (99 / 100 : ℝ) * K⁻¹ ^ r * (S.card : ℝ)
        = (K ^ r * (A.card : ℝ) ^ r)⁻¹ * ((99 / 100 : ℝ) * (A.card : ℝ) ^ r * (S.card : ℝ)) := by
          rw [inv_pow]; field_simp [(pow_pos hKpos r).ne', (pow_pos hApos r).ne']
      _ ≤ (K ^ r * (A.card : ℝ) ^ r)⁻¹ * (K ^ r * (A.card : ℝ) ^ r * (fib.card : ℝ)) := hmul
      _ = (fib.card : ℝ) := by field_simp [hKA_pos.ne']
  -- Step 3: Prove L^{2m}-almost-periodicity for single differences `s₁ - s₂` with `s₁, s₂ ∈ T`.
  have hsingle : ∀ s₁ ∈ T, ∀ s₂ ∈ T,
      (∑ x : G, |convR (indR A) (indR L) (x + (s₁ - s₂)) -
          convR (indR A) (indR L) x| ^ (2 * m : ℝ)) ^ (1 / (2 * m : ℝ)) ≤
        (ε / (k : ℝ)) * (A.card : ℝ) * (L.card : ℝ) ^ (1 / (2 * m : ℝ)) := by
    intro s₁ hs₁ s₂ hs₂
    rcases Finset.mem_image.1 hs₁ with ⟨⟨a₁, s₁'⟩, hp₁, hs₁_eq⟩
    rcases Finset.mem_image.1 hs₂ with ⟨⟨a₂, s₂'⟩, hp₂, hs₂_eq⟩
    change s₁' = s₁ at hs₁_eq
    change s₂' = s₂ at hs₂_eq
    subst hs₁_eq; subst hs₂_eq
    have ha₁_Ω : a₁ ∈ Ω := (Finset.mem_product.1 (Finset.mem_filter.1 hp₁).1).1
    have ha₂_Ω : a₂ ∈ Ω := (Finset.mem_product.1 (Finset.mem_filter.1 hp₂).1).1
    have hs₁_S : s₁' ∈ S := (Finset.mem_product.1 (Finset.mem_filter.1 hp₁).1).2
    have hs₂_S : s₂' ∈ S := (Finset.mem_product.1 (Finset.mem_filter.1 hp₂).1).2
    have hshift : ∀ i : Fin r, (a₁ i).1 + s₁' = (a₂ i).1 + s₂' := by
      intro i
      have hφ : (φ (a₁, s₁') i).1 = (φ (a₂, s₂') i).1 := by
        rw [(Finset.mem_filter.1 hp₁).2, (Finset.mem_filter.1 hp₂).2]
      dsimp only [φ] at hφ
      rw [dif_pos hs₁_S, dif_pos hs₂_S] at hφ
      exact hφ
    have hemp_shift : ∀ x : G, emp a₂ (x + (s₁' - s₂')) = emp a₁ x := by
      intro x
      dsimp only [emp]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      have harg : x + (s₁' - s₂') - (a₂ i).1 = x - (a₁ i).1 := by
        have h := hshift i
        calc x + (s₁' - s₂') - (a₂ i).1
            = x + s₁' - ((a₂ i).1 + s₂') := by abel
          _ = x + s₁' - ((a₁ i).1 + s₁') := by rw [← h]
          _ = x - (a₁ i).1 := by abel
      rw [harg]
    have hnorm_a₁ :
        (∑ x : G, |emp a₁ x - (A.card : ℝ)⁻¹ * convR (indR A) (indR L) x| ^ (2 * m : ℝ)) ^
          (1 / (2 * m : ℝ)) ≤ (ε / (2 * (k : ℝ))) * (L.card : ℝ) ^ (1 / (2 * m : ℝ)) := by
      have h1 : err a₁ ≤ thresh := (Finset.mem_filter.1 ha₁_Ω).2
      have hpow_eq : ∀ x : G, |emp a₁ x - (A.card : ℝ)⁻¹ * convR (indR A) (indR L) x| ^ (2 * m : ℝ) =
          (emp a₁ x - (A.card : ℝ)⁻¹ * convR (indR A) (indR L) x) ^ (2 * m) := by
        intro x
        rw [show (2 * m : ℝ) = ((2 * m : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
          (even_two_mul m).pow_abs]
      simp_rw [hpow_eq]
      have hsum_nn : 0 ≤ err a₁ := Finset.sum_nonneg fun x _ => Even.pow_nonneg (even_two_mul m) _
      calc (err a₁) ^ (1 / (2 * m : ℝ))
          ≤ thresh ^ (1 / (2 * m : ℝ)) := Real.rpow_le_rpow hsum_nn h1 (by positivity)
        _ = ((ε / (2 * (k : ℝ))) ^ (2 * m) * (L.card : ℝ)) ^ (1 / (2 * m : ℝ)) := rfl
        _ = ((ε / (2 * (k : ℝ))) ^ (2 * m)) ^ (1 / (2 * m : ℝ)) * (L.card : ℝ) ^ (1 / (2 * m : ℝ)) :=
            Real.mul_rpow (by positivity) (Nat.cast_nonneg _)
        _ = (ε / (2 * (k : ℝ))) * (L.card : ℝ) ^ (1 / (2 * m : ℝ)) := by
            congr 1
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            have heq : ((2 * m : ℕ) : ℝ) * (1 / (2 * m : ℝ)) = 1 := by
              push_cast; field_simp [hm_pos.ne']
            rw [heq, Real.rpow_one]
    have hnorm_a₂ :
        (∑ x : G, |emp a₂ (x + (s₁' - s₂')) -
            (A.card : ℝ)⁻¹ * convR (indR A) (indR L) (x + (s₁' - s₂'))| ^ (2 * m : ℝ)) ^
          (1 / (2 * m : ℝ)) ≤ (ε / (2 * (k : ℝ))) * (L.card : ℝ) ^ (1 / (2 * m : ℝ)) := by
      have hshift_sum :
          ∑ x : G, |emp a₂ (x + (s₁' - s₂')) -
            (A.card : ℝ)⁻¹ * convR (indR A) (indR L) (x + (s₁' - s₂'))| ^ (2 * m : ℝ) =
          ∑ x : G, |emp a₂ x - (A.card : ℝ)⁻¹ * convR (indR A) (indR L) x| ^ (2 * m : ℝ) :=
        Fintype.sum_equiv (Equiv.addRight (s₁' - s₂')) _ _ (fun _ => rfl)
      rw [hshift_sum]
      have h1 : err a₂ ≤ thresh := (Finset.mem_filter.1 ha₂_Ω).2
      have hpow_eq : ∀ x : G, |emp a₂ x - (A.card : ℝ)⁻¹ * convR (indR A) (indR L) x| ^ (2 * m : ℝ) =
          (emp a₂ x - (A.card : ℝ)⁻¹ * convR (indR A) (indR L) x) ^ (2 * m) := by
        intro x
        rw [show (2 * m : ℝ) = ((2 * m : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
          (even_two_mul m).pow_abs]
      simp_rw [hpow_eq]
      have hsum_nn : 0 ≤ err a₂ := Finset.sum_nonneg fun x _ => Even.pow_nonneg (even_two_mul m) _
      calc (err a₂) ^ (1 / (2 * m : ℝ))
          ≤ thresh ^ (1 / (2 * m : ℝ)) := Real.rpow_le_rpow hsum_nn h1 (by positivity)
        _ = ((ε / (2 * (k : ℝ))) ^ (2 * m)) ^ (1 / (2 * m : ℝ)) * (L.card : ℝ) ^ (1 / (2 * m : ℝ)) :=
            Real.mul_rpow (by positivity) (Nat.cast_nonneg _)
        _ = (ε / (2 * (k : ℝ))) * (L.card : ℝ) ^ (1 / (2 * m : ℝ)) := by
            congr 1
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            have heq : ((2 * m : ℕ) : ℝ) * (1 / (2 * m : ℝ)) = 1 := by
              push_cast; field_simp [hm_pos.ne']
            rw [heq, Real.rpow_one]
    -- Apply Minkowski (L^{2m} triangle inequality)
    let f₁ : G → ℝ := fun x =>
      (A.card : ℝ)⁻¹ * convR (indR A) (indR L) (x + (s₁' - s₂')) - emp a₂ (x + (s₁' - s₂'))
    let f₂ : G → ℝ := fun x =>
      emp a₁ x - (A.card : ℝ)⁻¹ * convR (indR A) (indR L) x
    have hsum_f : ∀ x : G, f₁ x + f₂ x =
        (A.card : ℝ)⁻¹ * (convR (indR A) (indR L) (x + (s₁' - s₂')) - convR (indR A) (indR L) x) := by
      intro x
      dsimp only [f₁, f₂]
      rw [hemp_shift x]
      ring
    have hmink := Real.Lp_add_le (s := Finset.univ) (f := f₁) (g := f₂) h2m_ge1
    have hf₁_norm : (∑ x : G, |f₁ x| ^ (2 * m : ℝ)) ^ (1 / (2 * m : ℝ)) ≤
        (ε / (2 * (k : ℝ))) * (L.card : ℝ) ^ (1 / (2 * m : ℝ)) := by
      have : ∀ x : G, |f₁ x| = |emp a₂ (x + (s₁' - s₂')) -
          (A.card : ℝ)⁻¹ * convR (indR A) (indR L) (x + (s₁' - s₂'))| := fun x => abs_sub_comm _ _
      simp_rw [this]; exact hnorm_a₂
    have hscaled :
        (∑ x : G, |(A.card : ℝ)⁻¹ * (convR (indR A) (indR L) (x + (s₁' - s₂')) -
            convR (indR A) (indR L) x)| ^ (2 * m : ℝ)) ^ (1 / (2 * m : ℝ)) ≤
          (ε / (k : ℝ)) * (L.card : ℝ) ^ (1 / (2 * m : ℝ)) := by
      simp_rw [← hsum_f]
      calc (∑ x : G, |f₁ x + f₂ x| ^ (2 * m : ℝ)) ^ (1 / (2 * m : ℝ))
          ≤ (∑ x : G, |f₁ x| ^ (2 * m : ℝ)) ^ (1 / (2 * m : ℝ)) +
            (∑ x : G, |f₂ x| ^ (2 * m : ℝ)) ^ (1 / (2 * m : ℝ)) := hmink
        _ ≤ (ε / (2 * (k : ℝ))) * (L.card : ℝ) ^ (1 / (2 * m : ℝ)) +
            (ε / (2 * (k : ℝ))) * (L.card : ℝ) ^ (1 / (2 * m : ℝ)) := add_le_add hf₁_norm hnorm_a₁
        _ = (ε / (k : ℝ)) * (L.card : ℝ) ^ (1 / (2 * m : ℝ)) := by ring
    have hpull :
        (∑ x : G, |(A.card : ℝ)⁻¹ * (convR (indR A) (indR L) (x + (s₁' - s₂')) -
            convR (indR A) (indR L) x)| ^ (2 * m : ℝ)) ^ (1 / (2 * m : ℝ)) =
        (A.card : ℝ)⁻¹ * (∑ x : G, |convR (indR A) (indR L) (x + (s₁' - s₂')) -
            convR (indR A) (indR L) x| ^ (2 * m : ℝ)) ^ (1 / (2 * m : ℝ)) := by
      have hterm : ∀ x : G,
          |(A.card : ℝ)⁻¹ * (convR (indR A) (indR L) (x + (s₁' - s₂')) -
            convR (indR A) (indR L) x)| ^ (2 * m : ℝ) =
          ((A.card : ℝ)⁻¹ ^ (2 * m : ℝ)) *
            |convR (indR A) (indR L) (x + (s₁' - s₂')) - convR (indR A) (indR L) x| ^ (2 * m : ℝ) := by
        intro x
        rw [abs_mul, abs_of_nonneg (inv_nonneg.2 hApos.le),
          Real.mul_rpow (inv_nonneg.2 hApos.le) (abs_nonneg _)]
      simp_rw [hterm, ← Finset.mul_sum]
      rw [Real.mul_rpow (by positivity) (Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) _),
        ← Real.rpow_mul (inv_nonneg.2 hApos.le)]
      have heq : (2 * m : ℝ) * (1 / (2 * m : ℝ)) = 1 := by field_simp [h2m_pos.ne']
      rw [heq, Real.rpow_one]
    rw [hpull] at hscaled
    have hmul := mul_le_mul_of_nonneg_left hscaled hApos.le
    rw [mul_inv_cancel_left₀ hApos.ne'] at hmul
    calc _ ≤ (A.card : ℝ) * ((ε / (k : ℝ)) * (L.card : ℝ) ^ (1 / (2 * m : ℝ))) := hmul
      _ = (ε / (k : ℝ)) * (A.card : ℝ) * (L.card : ℝ) ^ (1 / (2 * m : ℝ)) := by ring
  -- Step 4: Iterate the L^{2m} triangle inequality `k` times for `t ∈ kT - kT`.
  refine ⟨T, hT_sub, hT_size, ?_⟩
  intro t₁ t₂ ht₁ ht₂
  suffices hgen : ∀ (n : ℕ) (u₁ u₂ : Fin n → G), (∀ i, u₁ i ∈ T) → (∀ i, u₂ i ∈ T) →
      (∑ x : G, |convR (indR A) (indR L) (x + ∑ i : Fin n, (u₁ i - u₂ i)) -
          convR (indR A) (indR L) x| ^ (2 * m : ℝ)) ^ (1 / (2 * m : ℝ)) ≤
        (n : ℝ) * ((ε / (k : ℝ)) * (A.card : ℝ) * (L.card : ℝ) ^ (1 / (2 * m : ℝ))) by
    have h := hgen k t₁ t₂ ht₁ ht₂
    have heq : (k : ℝ) * ((ε / (k : ℝ)) * (A.card : ℝ) * (L.card : ℝ) ^ (1 / (2 * m : ℝ))) =
        ε * (A.card : ℝ) * (L.card : ℝ) ^ (1 / (2 * m : ℝ)) := by
      field_simp [hk_pos.ne']
    linarith
  intro n
  induction n with
  | zero =>
    intro _ _ _ _
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, sub_self, abs_zero,
      Real.zero_rpow h2m_pos.ne', Finset.sum_const_zero,
      Real.zero_rpow (one_div_pos.2 h2m_pos).ne', Nat.cast_zero, zero_mul, le_rfl]
  | succ n ih =>
    intro u₁ u₂ hu₁ hu₂
    set s_rest : G := ∑ i : Fin n, (u₁ i.castSucc - u₂ i.castSucc)
    set s_last : G := u₁ (Fin.last n) - u₂ (Fin.last n)
    have hsum_split : ∑ i : Fin (n + 1), (u₁ i - u₂ i) = s_rest + s_last := by
      rw [Fin.sum_univ_castSucc]
    rw [hsum_split]
    let g₁ : G → ℝ := fun x =>
      convR (indR A) (indR L) (x + s_rest + s_last) - convR (indR A) (indR L) (x + s_rest)
    let g₂ : G → ℝ := fun x =>
      convR (indR A) (indR L) (x + s_rest) - convR (indR A) (indR L) x
    have hadd : ∀ x : G, g₁ x + g₂ x =
        convR (indR A) (indR L) (x + (s_rest + s_last)) - convR (indR A) (indR L) x := by
      intro x; dsimp only [g₁, g₂]; rw [add_assoc]; ring
    simp_rw [← hadd]
    have hmink := Real.Lp_add_le (s := Finset.univ) (f := g₁) (g := g₂) h2m_ge1
    have hg₁ : (∑ x : G, |g₁ x| ^ (2 * m : ℝ)) ^ (1 / (2 * m : ℝ)) ≤
        (ε / (k : ℝ)) * (A.card : ℝ) * (L.card : ℝ) ^ (1 / (2 * m : ℝ)) := by
      have heq_sum : ∑ x : G, |g₁ x| ^ (2 * m : ℝ) =
          ∑ x : G, |convR (indR A) (indR L) (x + s_last) - convR (indR A) (indR L) x| ^ (2 * m : ℝ) :=
        Fintype.sum_equiv (Equiv.addRight s_rest) _ _ (fun _ => rfl)
      rw [heq_sum]
      exact hsingle (u₁ (Fin.last n)) (hu₁ _) (u₂ (Fin.last n)) (hu₂ _)
    have hg₂ := ih (fun i => u₁ i.castSucc) (fun i => u₂ i.castSucc)
      (fun i => hu₁ _) (fun i => hu₂ _)
    have hstep : ((n + 1 : ℕ) : ℝ) *
        ((ε / (k : ℝ)) * (A.card : ℝ) * (L.card : ℝ) ^ (1 / (2 * m : ℝ))) =
        (ε / (k : ℝ)) * (A.card : ℝ) * (L.card : ℝ) ^ (1 / (2 * m : ℝ)) +
        (n : ℝ) * ((ε / (k : ℝ)) * (A.card : ℝ) * (L.card : ℝ) ^ (1 / (2 * m : ℝ))) := by
      push_cast; ring
    linarith

/-- `L^∞`-almost-periodicity for triple convolutions (`Theorem 5.1` of Schoen–Sisask). -/
lemma linfty_ap_triple {A M L S : Finset G} (hA : A.Nonempty) (hM : M.Nonempty)
    (hL : L.Nonempty) (hS : S.Nonempty)
    {K ε η : ℝ} (hK : 1 ≤ K)
    (hAS : ((A.image (fun a => a) ×ˢ S).image (fun p => p.1 + p.2)).card ≤ K * (A.card : ℝ))
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hη_le : η ≤ (M.card : ℝ) / (L.card : ℝ))
    {k : ℕ} (hk : 1 ≤ k) :
    let m : ℕ := Nat.ceil (Real.log (2 / η)) + 1
    let r : ℕ := Nat.ceil (1600 * (m : ℝ) * (k : ℝ) ^ 2 / (ε / 2) ^ 2) + 1
    ∃ T : Finset G, T ⊆ S ∧
      (99 / 100 : ℝ) * K⁻¹ ^ r * (S.card : ℝ) ≤ (T.card : ℝ) ∧
      ∀ (t₁ t₂ : Fin k → G), (∀ i, t₁ i ∈ T) → (∀ i, t₂ i ∈ T) →
        ∀ x : G,
          |convR (convR (indR A) (indR M)) (indR L) (x + ∑ i : Fin k, (t₁ i - t₂ i)) -
            convR (convR (indR A) (indR M)) (indR L) x| ≤
          ε * (A.card : ℝ) * (M.card : ℝ) := by
  intro m r
  have hm : 1 ≤ m := Nat.succ_le_succ (Nat.zero_le _)
  have hMpos : (0 : ℝ) < (M.card : ℝ) := Nat.cast_pos.2 hM.card_pos
  have hLpos : (0 : ℝ) < (L.card : ℝ) := Nat.cast_pos.2 hL.card_pos
  have hApos : (0 : ℝ) < (A.card : ℝ) := Nat.cast_pos.2 hA.card_pos
  obtain ⟨T, hTsub, hTsize, hTap⟩ :=
    croot_sisask_L2m hA hS hK hAS (show 0 < ε / 2 by positivity) (by linarith) hm hk (L := L)
  refine ⟨T, hTsub, hTsize, ?_⟩
  intro t₁ t₂ ht₁ ht₂ x
  set t : G := ∑ i : Fin k, (t₁ i - t₂ i)
  have hrewrite :
      convR (convR (indR A) (indR M)) (indR L) (x + t) -
        convR (convR (indR A) (indR M)) (indR L) x =
      ∑ y : G, indR M (x - y) *
        (convR (indR A) (indR L) (y + t) - convR (indR A) (indR L) y) := by
    have hcomm1 : ∀ z : G, convR (convR (indR A) (indR M)) (indR L) z =
        convR (indR M) (convR (indR A) (indR L)) z := by
      intro z
      rw [show convR (indR A) (indR M) = convR (indR M) (indR A) from funext (convR_comm _ _),
        convR_assoc]
    rw [hcomm1 (x + t), hcomm1 x]
    have hshift_y : convR (indR M) (convR (indR A) (indR L)) (x + t) =
        ∑ y : G, indR M (x - y) * convR (indR A) (indR L) (y + t) := by
      unfold convR
      refine Fintype.sum_equiv (Equiv.subLeft x) _ _ fun y => ?_
      simp only [Equiv.subLeft_apply, sub_sub_cancel]
      have harg : x + t - y = (x - y) + t := by abel
      rw [harg]
    have hshift_y2 : convR (indR M) (convR (indR A) (indR L)) x =
        ∑ y : G, indR M (x - y) * convR (indR A) (indR L) y := by
      unfold convR
      exact Fintype.sum_equiv (Equiv.subLeft x) _ _ fun y => by
        simp only [Equiv.subLeft_apply, sub_sub_cancel]
    rw [hshift_y, hshift_y2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => by ring
  rw [hrewrite]
  -- Apply Hölder with `p = 2m` and `q = 2m / (2m - 1)`.
  set p : ℝ := (2 * m : ℝ)
  set q : ℝ := p / (p - 1)
  have hp1 : 1 < p := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := Nat.one_le_cast.2 hm
    dsimp only [p]; linarith
  have hpq : Real.HolderConjugate p q := Real.holderConjugate_iff.2 ⟨hp1, by
    dsimp only [q]
    have hp0 : p ≠ 0 := by linarith
    have hp1' : p - 1 ≠ 0 := by linarith
    field_simp [hp0, hp1']
    ring⟩
  have h1q : 1 / p + 1 / q = 1 := by
    simpa [one_div] using hpq.inv_add_inv_eq_one
  have habs_le : |∑ y : G, indR M (x - y) *
      (convR (indR A) (indR L) (y + t) - convR (indR A) (indR L) y)| ≤
      ∑ y : G, indR M (x - y) *
        |convR (indR A) (indR L) (y + t) - convR (indR A) (indR L) y| := by
    calc |∑ y : G, _| ≤ ∑ y : G, |indR M (x - y) * _| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ y : G, indR M (x - y) * |_| := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [abs_mul, abs_of_nonneg (indR_nonneg M _)]
  have hholder := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ)
    (f := fun y => indR M (x - y))
    (g := fun y => |convR (indR A) (indR L) (y + t) - convR (indR A) (indR L) y|)
    hpq.symm (fun y _ => indR_nonneg M _) (fun y _ => abs_nonneg _)
  have hMq : ∑ y : G, indR M (x - y) ^ q = (M.card : ℝ) := by
    have hq_pos : 0 < q := hpq.symm.pos
    have hterm : ∀ y : G, indR M (x - y) ^ q = indR M (x - y) := by
      intro y; unfold indR; split_ifs
      · exact Real.one_rpow q
      · exact Real.zero_rpow hq_pos.ne'
    simp_rw [hterm]
    exact (Fintype.sum_equiv (Equiv.subLeft x) _ (fun z => indR M z) (fun _ => rfl)).trans (sum_indR M)
  rw [hMq] at hholder
  have hLp := hTap t₁ t₂ ht₁ ht₂
  -- Bound `(L.card / M.card)^(1/p) ≤ 2`.
  have hratio_le : (L.card : ℝ) ^ (1 / p) * (M.card : ℝ) ^ (1 / q) ≤ 2 * (M.card : ℝ) := by
    have hM_split : (M.card : ℝ) = (M.card : ℝ) ^ (1 / p) * (M.card : ℝ) ^ (1 / q) := by
      rw [← Real.rpow_add hMpos, h1q, Real.rpow_one]
    have hLM_rpow : ((L.card : ℝ) / (M.card : ℝ)) ^ (1 / p) ≤ 2 := by
      have hLM_le : (L.card : ℝ) / (M.card : ℝ) ≤ 2 / η := by
        have h1 : (L.card : ℝ) / (M.card : ℝ) ≤ 1 / η := by
          rw [div_le_div_iff₀ hMpos hη0, one_mul]
          have := (le_div_iff₀ hLpos).1 hη_le
          linarith
        have h2 : 1 / η ≤ 2 / η := div_le_div_of_nonneg_right (by norm_num) hη0.le
        linarith
      have h2η_ge2 : (2 : ℝ) ≤ 2 / η := by
        rw [le_div_iff₀ hη0]; linarith
      have hlog_pos : 0 < Real.log (2 / η) := Real.log_pos (by linarith)
      have hp_ge : 2 * Real.log (2 / η) ≤ p := by
        have hceil : Real.log (2 / η) ≤ (Nat.ceil (Real.log (2 / η)) : ℝ) := Nat.le_ceil _
        have hm_eq : (m : ℝ) = (Nat.ceil (Real.log (2 / η)) : ℝ) + 1 := by
          dsimp only [m]; push_cast; rfl
        dsimp only [p]
        linarith
      have hexp_le : (2 / η) ^ (1 / p) ≤ Real.exp (1 / 2) := by
        rw [Real.rpow_def_of_pos (by positivity)]
        apply Real.exp_le_exp.2
        have hmul : Real.log (2 / η) * (1 / p) ≤ Real.log (2 / η) * (1 / (2 * Real.log (2 / η))) :=
          mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by positivity) hp_ge) hlog_pos.le
        have hsimp : Real.log (2 / η) * (1 / (2 * Real.log (2 / η))) = 1 / 2 := by
          field_simp [hlog_pos.ne']
        linarith
      have hexp_half_le : Real.exp (1 / 2 : ℝ) ≤ 2 := by
        have h1 : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
          rw [sq, ← Real.exp_add]; norm_num
        have h2 : Real.exp 1 < 4 := by
          have := Real.exp_one_lt_d9
          linarith
        nlinarith [Real.exp_pos (1 / 2 : ℝ)]
      have h1p_nn : 0 ≤ 1 / p := div_nonneg zero_le_one (by linarith)
      calc ((L.card : ℝ) / (M.card : ℝ)) ^ (1 / p)
          ≤ (2 / η) ^ (1 / p) := Real.rpow_le_rpow (div_nonneg hLpos.le hMpos.le) hLM_le h1p_nn
        _ ≤ Real.exp (1 / 2) := hexp_le
        _ ≤ 2 := hexp_half_le
    calc (L.card : ℝ) ^ (1 / p) * (M.card : ℝ) ^ (1 / q)
        = ((L.card : ℝ) / (M.card : ℝ)) ^ (1 / p) * ((M.card : ℝ) ^ (1 / p) * (M.card : ℝ) ^ (1 / q)) := by
          rw [Real.div_rpow hLpos.le hMpos.le]
          have hMp_ne : ((M.card : ℝ) ^ (1 / p)) ≠ 0 := (Real.rpow_pos_of_pos hMpos (1 / p)).ne'
          rw [← mul_assoc, div_mul_cancel₀ _ hMp_ne]
      _ = ((L.card : ℝ) / (M.card : ℝ)) ^ (1 / p) * (M.card : ℝ) := by rw [← hM_split]
      _ ≤ 2 * (M.card : ℝ) := mul_le_mul_of_nonneg_right hLM_rpow hMpos.le
  calc |∑ y : G, indR M (x - y) *
          (convR (indR A) (indR L) (y + t) - convR (indR A) (indR L) y)|
      ≤ ∑ y : G, indR M (x - y) *
          |convR (indR A) (indR L) (y + t) - convR (indR A) (indR L) y| := habs_le
    _ ≤ (M.card : ℝ) ^ (1 / q) *
          (∑ y : G, |convR (indR A) (indR L) (y + t) - convR (indR A) (indR L) y| ^ p) ^ (1 / p) :=
        hholder
    _ ≤ (M.card : ℝ) ^ (1 / q) * ((ε / 2) * (A.card : ℝ) * (L.card : ℝ) ^ (1 / p)) :=
        mul_le_mul_of_nonneg_left hLp (by positivity)
    _ = (ε / 2) * (A.card : ℝ) * ((L.card : ℝ) ^ (1 / p) * (M.card : ℝ) ^ (1 / q)) := by ring
    _ ≤ (ε / 2) * (A.card : ℝ) * (2 * (M.card : ℝ)) := by gcongr
    _ = ε * (A.card : ℝ) * (M.card : ℝ) := by ring

end CrootSisask

/- ## Section 4: Local Chang Bound, Chang–Sanders Lemma, and L^∞-AP with Bohr Sets -/

section ChangSanders

variable {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]

/-- Elementary real inequality: `exp(t - t^2) ≤ 1 + t` for all `|t| ≤ 1/2`. -/
private lemma exp_sub_sq_le_one_add {t : ℝ} (ht : |t| ≤ 1 / 2) :
    Real.exp (t - t ^ 2) ≤ 1 + t := by
  let g : ℝ → ℝ := fun u => (1 + u) * Real.exp (u ^ 2 - u)
  have hderiv : ∀ u : ℝ, HasDerivAt g (Real.exp (u ^ 2 - u) * (u * (1 + 2 * u))) u := by
    intro u
    have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 u := (hasDerivAt_id u).const_add 1
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2 - x) (2 * u - 1) u := by
      have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * u) u := by
        simpa using hasDerivAt_pow 2 u
      exact hp.sub (hasDerivAt_id u)
    have h3 : HasDerivAt (fun x : ℝ => Real.exp (x ^ 2 - x))
        (Real.exp (u ^ 2 - u) * (2 * u - 1)) u := h2.exp
    have hmul : HasDerivAt g (1 * Real.exp (u ^ 2 - u) + (1 + u) * (Real.exp (u ^ 2 - u) * (2 * u - 1))) u :=
      h1.mul h3
    have heq : 1 * Real.exp (u ^ 2 - u) + (1 + u) * (Real.exp (u ^ 2 - u) * (2 * u - 1)) =
        Real.exp (u ^ 2 - u) * (u * (1 + 2 * u)) := by ring
    rwa [heq] at hmul
  have hg_ge1 : 1 ≤ g t := by
    have habs := abs_le.1 ht
    rcases le_or_gt 0 t with h0 | h0
    · have hmono : MonotoneOn g (Set.Icc 0 (1 / 2)) := by
        refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 / 2))
          (fun u _ => (hderiv u).continuousAt.continuousWithinAt)
          (fun u _ => (hderiv u).differentiableAt.differentiableWithinAt) ?_
        intro u hu
        rw [(hderiv u).deriv]
        have hu0 : 0 ≤ u := (interior_subset hu).1
        exact mul_nonneg (Real.exp_pos _).le (mul_nonneg hu0 (by linarith))
      have h := hmono ⟨le_rfl, by norm_num⟩ ⟨h0, habs.2⟩ h0
      simpa [g] using h
    · have hanti : AntitoneOn g (Set.Icc (-(1 / 2)) 0) := by
        refine antitoneOn_of_deriv_nonpos (convex_Icc (-(1 / 2)) 0)
          (fun u _ => (hderiv u).continuousAt.continuousWithinAt)
          (fun u _ => (hderiv u).differentiableAt.differentiableWithinAt) ?_
        intro u hu
        rw [(hderiv u).deriv]
        have hu' := interior_subset hu
        have hprod : u * (1 + 2 * u) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hu'.2 (by linarith [hu'.1])
        exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hprod
      have h := hanti ⟨habs.1, h0.le⟩ ⟨by norm_num, le_rfl⟩ h0.le
      simpa [g] using h
  have hmul := mul_le_mul_of_nonneg_right hg_ge1 (Real.exp_pos (t - t ^ 2)).le
  dsimp only [g] at hmul
  rw [one_mul, mul_assoc, ← Real.exp_add] at hmul
  have hzero : t ^ 2 - t + (t - t ^ 2) = 0 := by ring
  rw [hzero, Real.exp_zero, mul_one] at hmul
  exact hmul

/-- Riesz product `∏_{ψ ∈ Λ} (1 + Re(ω(ψ) * ψ(x)))`. -/
noncomputable def rieszProd (Λ : Finset (AddChar G ℂ)) (ω : AddChar G ℂ → ℂ) (x : G) : ℝ :=
  ∏ ψ ∈ Λ, (1 + (ω ψ * ψ x).re)

lemma rieszProd_nonneg {Λ : Finset (AddChar G ℂ)} {ω : AddChar G ℂ → ℂ}
    (hω : ∀ ψ ∈ Λ, ‖ω ψ‖ ≤ 1) (x : G) : 0 ≤ rieszProd Λ ω x := by
  refine Finset.prod_nonneg fun ψ hψ => ?_
  have hre : |(ω ψ * ψ x).re| ≤ 1 := by
    calc |(ω ψ * ψ x).re| ≤ ‖ω ψ * ψ x‖ := Complex.abs_re_le_norm _
      _ = ‖ω ψ‖ * ‖ψ x‖ := norm_mul _ _
      _ = ‖ω ψ‖ := by rw [ψ.norm_apply, mul_one]
      _ ≤ 1 := hω ψ hψ
  linarith [(abs_le.1 hre).1]

/-- `K`-dissociativity of `Λ` with respect to a measure `μ : G → ℝ` (Sanders 2012). -/
def IsDissoc (μ : G → ℝ) (K : ℝ) (Λ : Finset (AddChar G ℂ)) : Prop :=
  ∀ ω : AddChar G ℂ → ℂ, (∀ ψ ∈ Λ, ‖ω ψ‖ ≤ 1) →
    ∑ x : G, μ x * rieszProd Λ ω x ≤ Real.exp K

/-- Local Chang bound (15-line Jensen proof): if `Λ ⊆ Spec_δ(μ_X)` is `1`-dissociated w.r.t. `μ_B`
for `X ⊆ B`, then `|Λ| ≤ (4 / δ^2) * (1 + log(|B| / |X|))`. -/
lemma local_chang_bound {B X : Finset G} (hX : X.Nonempty) (hXB : X ⊆ B)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {Λ : Finset (AddChar G ℂ)}
    (hSpec : ∀ ψ ∈ Λ, δ ≤ ‖dftG (muC X) ψ‖)
    (hDiss : IsDissoc (muR B) 1 Λ) :
    (Λ.card : ℝ) ≤ 4 / δ ^ 2 * (1 + Real.log ((B.card : ℝ) / (X.card : ℝ))) := by
  have hXpos : (0 : ℝ) < (X.card : ℝ) := Nat.cast_pos.2 hX.card_pos
  have hBne : B.Nonempty := hX.mono hXB
  have hBpos : (0 : ℝ) < (B.card : ℝ) := Nat.cast_pos.2 hBne.card_pos
  let ω : AddChar G ℂ → ℂ := fun ψ =>
    if h : ‖dftG (muC X) ψ‖ = 0 then 0
    else ((δ / 2 : ℝ) : ℂ) * (dftG (muC X) ψ / (‖dftG (muC X) ψ‖ : ℂ))
  have hω_norm : ∀ ψ ∈ Λ, ‖ω ψ‖ ≤ δ / 2 := by
    intro ψ hψ
    have hpos : 0 < ‖dftG (muC X) ψ‖ := hδ0.trans_le (hSpec ψ hψ)
    dsimp only [ω]
    rw [dif_neg hpos.ne', norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hpos.le,
      div_self hpos.ne', mul_one]
  have hω_le1 : ∀ ψ ∈ Λ, ‖ω ψ‖ ≤ 1 := fun ψ hψ => (hω_norm ψ hψ).trans (by linarith)
  -- Pointwise lower bound: `exp(∑_{ψ ∈ Λ} (Re(ω ψ * ψ x) - (δ/2)^2)) ≤ rieszProd Λ ω x`.
  have hpt : ∀ x : G,
      Real.exp (∑ ψ ∈ Λ, ((ω ψ * ψ x).re - (δ / 2) ^ 2)) ≤ rieszProd Λ ω x := by
    intro x
    rw [Real.exp_sum]
    refine Finset.prod_le_prod (fun ψ _ => (Real.exp_pos _).le) fun ψ hψ => ?_
    set t : ℝ := (ω ψ * ψ x).re
    have ht_abs : |t| ≤ δ / 2 := by
      calc |t| ≤ ‖ω ψ * ψ x‖ := Complex.abs_re_le_norm _
        _ = ‖ω ψ‖ * ‖ψ x‖ := norm_mul _ _
        _ = ‖ω ψ‖ := by rw [ψ.norm_apply, mul_one]
        _ ≤ δ / 2 := hω_norm ψ hψ
    have ht_sq : t ^ 2 ≤ (δ / 2) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg t) ht_abs 2
    calc Real.exp (t - (δ / 2) ^ 2)
        ≤ Real.exp (t - t ^ 2) := Real.exp_le_exp.2 (by linarith)
      _ ≤ 1 + t := exp_sub_sq_le_one_add (ht_abs.trans (by linarith))
  -- Compute average of `(ω ψ * ψ x).re` over `x ∈ X`.
  have havg_ψ : ∀ ψ ∈ Λ,
      (X.card : ℝ)⁻¹ * ∑ x ∈ X, (ω ψ * ψ x).re ≥ δ ^ 2 / 2 := by
    intro ψ hψ
    have hspec := hSpec ψ hψ
    have hpos : 0 < ‖dftG (muC X) ψ‖ := hδ0.trans_le hspec
    have hstar_dft : star (dftG (muC X) ψ) = ∑ x ∈ X, ((X.card : ℂ)⁻¹ * ψ x) := by
      unfold dftG muC
      have : ∑ x : G, (if x ∈ X then (X.card : ℂ)⁻¹ else 0) * star (ψ x) =
          ∑ x ∈ X, (X.card : ℂ)⁻¹ * star (ψ x) := by
        rw [← Finset.sum_subset (Finset.subset_univ X)]
        · refine Finset.sum_congr rfl fun x hx => by simp [hx]
        · intro x _ hx; simp [hx]
      rw [this]
      simp
    have hsumC : ((X.card : ℝ)⁻¹ * ∑ x ∈ X, (ω ψ * ψ x).re : ℝ) =
        (ω ψ * star (dftG (muC X) ψ)).re := by
      rw [hstar_dft]
      have hmul : ω ψ * ∑ x ∈ X, (X.card : ℂ)⁻¹ * ψ x =
          (((X.card : ℝ)⁻¹ : ℝ) : ℂ) * ∑ x ∈ X, (ω ψ * ψ x) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => by push_cast; ring
      rw [hmul, Complex.re_ofReal_mul, Complex.re_sum]
    rw [hsumC]
    dsimp only [ω]
    rw [dif_neg hpos.ne']
    have hmulC : ((δ / 2 : ℝ) : ℂ) * (dftG (muC X) ψ / (‖dftG (muC X) ψ‖ : ℂ)) *
        star (dftG (muC X) ψ) = (((δ / 2) * ‖dftG (muC X) ψ‖ : ℝ) : ℂ) := by
      have hsq : dftG (muC X) ψ * star (dftG (muC X) ψ) = ((‖dftG (muC X) ψ‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have hne : (‖dftG (muC X) ψ‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
      calc ((δ / 2 : ℝ) : ℂ) * (dftG (muC X) ψ / (‖dftG (muC X) ψ‖ : ℂ)) * star (dftG (muC X) ψ)
          = ((δ / 2 : ℝ) : ℂ) * ((dftG (muC X) ψ * star (dftG (muC X) ψ)) / (‖dftG (muC X) ψ‖ : ℂ)) := by ring
        _ = ((δ / 2 : ℝ) : ℂ) * (((‖dftG (muC X) ψ‖ ^ 2 : ℝ) : ℂ) / (‖dftG (muC X) ψ‖ : ℂ)) := by rw [hsq]
        _ = (((δ / 2) * ‖dftG (muC X) ψ‖ : ℝ) : ℂ) := by
            push_cast; field_simp [hne]
    rw [hmulC, Complex.ofReal_re]
    nlinarith
  -- Apply Jensen for `exp` on `X`.
  have hsum_w : ∑ _x ∈ X, (X.card : ℝ)⁻¹ = 1 := by simp [hXpos.ne']
  have hjensen := convexOn_exp.map_sum_le (t := X) (w := fun _ => (X.card : ℝ)⁻¹)
    (p := fun x => ∑ ψ ∈ Λ, ((ω ψ * ψ x).re - (δ / 2) ^ 2))
    (fun _ _ => by positivity) hsum_w (fun _ _ => trivial)
  simp only [smul_eq_mul] at hjensen
  have hL_ge : (Λ.card : ℝ) * (δ ^ 2 / 4) ≤
      ∑ x ∈ X, (X.card : ℝ)⁻¹ * ∑ ψ ∈ Λ, ((ω ψ * ψ x).re - (δ / 2) ^ 2) := by
    rw [← Finset.mul_sum, Finset.sum_comm, Finset.mul_sum]
    calc (Λ.card : ℝ) * (δ ^ 2 / 4)
        = ∑ _ψ ∈ Λ, (δ ^ 2 / 4) := by simp
      _ ≤ ∑ ψ ∈ Λ, (X.card : ℝ)⁻¹ * ∑ x ∈ X, ((ω ψ * ψ x).re - (δ / 2) ^ 2) := by
          refine Finset.sum_le_sum fun ψ hψ => ?_
          rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_sub,
            inv_mul_cancel_left₀ hXpos.ne']
          have := havg_ψ ψ hψ
          linarith
  have hR_le : ∑ x ∈ X, (X.card : ℝ)⁻¹ * rieszProd Λ ω x ≤
      Real.exp (1 + Real.log ((B.card : ℝ) / (X.card : ℝ))) := by
    have hsub_sum : ∑ x ∈ X, (X.card : ℝ)⁻¹ * rieszProd Λ ω x ≤
        ((B.card : ℝ) / (X.card : ℝ)) * ∑ x : G, muR B x * rieszProd Λ ω x := by
      have hB_sum : ∑ x : G, muR B x * rieszProd Λ ω x =
          (B.card : ℝ)⁻¹ * ∑ x ∈ B, rieszProd Λ ω x := by
        unfold muR
        have : ∑ x : G, (if x ∈ B then (B.card : ℝ)⁻¹ else 0) * rieszProd Λ ω x =
            ∑ x ∈ B, (B.card : ℝ)⁻¹ * rieszProd Λ ω x := by
          rw [← Finset.sum_subset (Finset.subset_univ B)]
          · refine Finset.sum_congr rfl fun x hx => by simp [hx]
          · intro x _ hx; simp [hx]
        rw [this, ← Finset.mul_sum]
      rw [hB_sum, ← Finset.mul_sum]
      have hcancel : (B.card : ℝ) / (X.card : ℝ) * ((B.card : ℝ)⁻¹ * ∑ x ∈ B, rieszProd Λ ω x) =
          (X.card : ℝ)⁻¹ * ∑ x ∈ B, rieszProd Λ ω x := by
        field_simp [hBpos.ne', hXpos.ne']
      rw [hcancel]
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hXB fun x _ _ => rieszProd_nonneg hω_le1 x)
        (by positivity)
    calc ∑ x ∈ X, (X.card : ℝ)⁻¹ * rieszProd Λ ω x
        ≤ ((B.card : ℝ) / (X.card : ℝ)) * ∑ x : G, muR B x * rieszProd Λ ω x := hsub_sum
      _ ≤ ((B.card : ℝ) / (X.card : ℝ)) * Real.exp 1 :=
          mul_le_mul_of_nonneg_left (hDiss ω hω_le1) (by positivity)
      _ = Real.exp (1 + Real.log ((B.card : ℝ) / (X.card : ℝ))) := by
          rw [Real.exp_add, Real.exp_log (div_pos hBpos hXpos), mul_comm]
  have hexp_chain : Real.exp ((Λ.card : ℝ) * (δ ^ 2 / 4)) ≤
      Real.exp (1 + Real.log ((B.card : ℝ) / (X.card : ℝ))) := by
    calc Real.exp ((Λ.card : ℝ) * (δ ^ 2 / 4))
        ≤ Real.exp (∑ x ∈ X, (X.card : ℝ)⁻¹ * ∑ ψ ∈ Λ, ((ω ψ * ψ x).re - (δ / 2) ^ 2)) :=
          Real.exp_le_exp.2 hL_ge
      _ ≤ ∑ x ∈ X, (X.card : ℝ)⁻¹ * Real.exp (∑ ψ ∈ Λ, ((ω ψ * ψ x).re - (δ / 2) ^ 2)) := hjensen
      _ ≤ ∑ x ∈ X, (X.card : ℝ)⁻¹ * rieszProd Λ ω x :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpt x) (by positivity)
      _ ≤ Real.exp (1 + Real.log ((B.card : ℝ) / (X.card : ℝ))) := hR_le
  have hlin := Real.exp_le_exp.1 hexp_chain
  have hδ2 : 0 < δ ^ 2 := pow_pos hδ0 2
  have hmul := mul_le_mul_of_nonneg_left hlin (show (0 : ℝ) ≤ 4 / δ ^ 2 by positivity)
  have hlhs : 4 / δ ^ 2 * ((Λ.card : ℝ) * (δ ^ 2 / 4)) = (Λ.card : ℝ) := by
    field_simp [hδ2.ne']
  linarith

/-- Inductive Riesz product expansion (avoids explicit `addSpan`/`piFinset` indexing):
there exists a character `c` with `‖c t - 1‖ ≤ ∑_{ψ ∈ Λ} ‖ψ t - 1‖` for all `t` such that
`‖∑ x, μ(x) * rieszProd Λ ω x * γ(x)‖ ≤ 3^|Λ| * ‖∑ x, μ(x) * (c * γ)(x)‖`. -/
private lemma rieszProd_expand_exists (μ : G → ℝ) (ω : AddChar G ℂ → ℂ) :
    ∀ (Λ : Finset (AddChar G ℂ)), (∀ ψ ∈ Λ, ‖ω ψ‖ ≤ 1) → ∀ (γ : AddChar G ℂ),
      ∃ c : AddChar G ℂ,
        (∀ t : G, ‖c t - 1‖ ≤ ∑ ψ ∈ Λ, ‖ψ t - 1‖) ∧
        ‖∑ x : G, (μ x : ℂ) * (rieszProd Λ ω x : ℂ) * γ x‖ ≤
          (3 : ℝ) ^ Λ.card * ‖∑ x : G, (μ x : ℂ) * (c * γ) x‖ := by
  intro Λ
  induction Λ using Finset.induction_on with
  | empty =>
    intro _ γ
    refine ⟨1, fun t => by simp, ?_⟩
    simp [rieszProd]
  | @insert ψ Λ hψ ih =>
    intro hω γ
    have hω_sub : ∀ χ ∈ Λ, ‖ω χ‖ ≤ 1 := fun χ hχ => hω χ (Finset.mem_insert_of_mem hχ)
    have hωψ : ‖ω ψ‖ ≤ 1 := hω ψ (Finset.mem_insert_self ψ Λ)
    have hsplit_pt : ∀ x : G,
        (rieszProd (insert ψ Λ) ω x : ℂ) * γ x =
        (rieszProd Λ ω x : ℂ) * γ x +
        ((1 / 2 : ℂ) * ω ψ) * ((rieszProd Λ ω x : ℂ) * (ψ * γ) x) +
        ((1 / 2 : ℂ) * star (ω ψ)) * ((rieszProd Λ ω x : ℂ) * (ψ⁻¹ * γ) x) := by
      intro x
      unfold rieszProd
      rw [Finset.prod_insert hψ, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_one]
      have hre : ((ω ψ * ψ x).re : ℂ) =
          (1 / 2 : ℂ) * (ω ψ * ψ x) + (1 / 2 : ℂ) * star (ω ψ * ψ x) := by
        rw [Complex.re_eq_add_conj, Complex.star_def]
        ring
      have hstar_mul : star (ω ψ * ψ x) = star (ω ψ) * ψ⁻¹ x := by
        rw [star_mul', Complex.star_def, ← AddChar.map_neg_eq_conj, AddChar.inv_apply, mul_comm]
      rw [hre, hstar_mul]
      simp only [AddChar.mul_apply]
      ring
    have hsum_split :
        ∑ x : G, (μ x : ℂ) * (rieszProd (insert ψ Λ) ω x : ℂ) * γ x =
        (∑ x : G, (μ x : ℂ) * (rieszProd Λ ω x : ℂ) * γ x) +
        ((1 / 2 : ℂ) * ω ψ) * (∑ x : G, (μ x : ℂ) * (rieszProd Λ ω x : ℂ) * (ψ * γ) x) +
        ((1 / 2 : ℂ) * star (ω ψ)) * (∑ x : G, (μ x : ℂ) * (rieszProd Λ ω x : ℂ) * (ψ⁻¹ * γ) x) := by
      simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_assoc, hsplit_pt x]; ring
    set S₁ : ℂ := ∑ x : G, (μ x : ℂ) * (rieszProd Λ ω x : ℂ) * γ x
    set S₂ : ℂ := ∑ x : G, (μ x : ℂ) * (rieszProd Λ ω x : ℂ) * (ψ * γ) x
    set S₃ : ℂ := ∑ x : G, (μ x : ℂ) * (rieszProd Λ ω x : ℂ) * (ψ⁻¹ * γ) x
    have hnorm_half : ‖(1 / 2 : ℂ) * ω ψ‖ ≤ 1 := by
      rw [norm_mul, norm_div, norm_one, Complex.norm_ofNat]; linarith
    have hnorm_half' : ‖(1 / 2 : ℂ) * star (ω ψ)‖ ≤ 1 := by
      rw [norm_mul, norm_div, norm_one, Complex.norm_ofNat, norm_star]; linarith
    have htri : ‖∑ x : G, (μ x : ℂ) * (rieszProd (insert ψ Λ) ω x : ℂ) * γ x‖ ≤
        ‖S₁‖ + ‖S₂‖ + ‖S₃‖ := by
      rw [hsum_split]
      calc ‖S₁ + (1 / 2 : ℂ) * ω ψ * S₂ + (1 / 2 : ℂ) * star (ω ψ) * S₃‖
          ≤ ‖S₁ + (1 / 2 : ℂ) * ω ψ * S₂‖ + ‖(1 / 2 : ℂ) * star (ω ψ) * S₃‖ := norm_add_le _ _
        _ ≤ ‖S₁‖ + ‖(1 / 2 : ℂ) * ω ψ * S₂‖ + ‖(1 / 2 : ℂ) * star (ω ψ) * S₃‖ := by
            gcongr; exact norm_add_le _ _
        _ = ‖S₁‖ + ‖(1 / 2 : ℂ) * ω ψ‖ * ‖S₂‖ + ‖(1 / 2 : ℂ) * star (ω ψ)‖ * ‖S₃‖ := by
            simp_rw [norm_mul]
        _ ≤ ‖S₁‖ + 1 * ‖S₂‖ + 1 * ‖S₃‖ := by gcongr
        _ = ‖S₁‖ + ‖S₂‖ + ‖S₃‖ := by ring
    have hcard : (insert ψ Λ).card = Λ.card + 1 := Finset.card_insert_of_notMem hψ
    have hsum_ins : ∀ t : G, ∑ χ ∈ insert ψ Λ, ‖χ t - 1‖ = ‖ψ t - 1‖ + ∑ χ ∈ Λ, ‖χ t - 1‖ :=
      fun t => Finset.sum_insert hψ
    -- Case split on the maximum of `‖S₁‖, ‖S₂‖, ‖S₃‖`.
    by_cases h12 : ‖S₂‖ ≤ ‖S₁‖ ∧ ‖S₃‖ ≤ ‖S₁‖
    · obtain ⟨c, hc_bd, hc_norm⟩ := ih hω_sub γ
      refine ⟨c, fun t => ?_, ?_⟩
      · rw [hsum_ins t]; linarith [hc_bd t, norm_nonneg (ψ t - 1)]
      · rw [hcard, pow_succ']
        have h3 : ‖S₁‖ + ‖S₂‖ + ‖S₃‖ ≤ 3 * ‖S₁‖ := by linarith
        calc _ ≤ 3 * ‖S₁‖ := htri.trans h3
          _ ≤ 3 * ((3 : ℝ) ^ Λ.card * ‖∑ x : G, (μ x : ℂ) * (c * γ) x‖) := by gcongr
          _ = 3 * (3 : ℝ) ^ Λ.card * ‖∑ x : G, (μ x : ℂ) * (c * γ) x‖ := by ring
    · by_cases h23 : ‖S₃‖ ≤ ‖S₂‖
      · have h1le2 : ‖S₁‖ ≤ ‖S₂‖ := by
          by_contra hlt; push Not at hlt; exact h12 ⟨hlt.le, h23.trans hlt.le⟩
        obtain ⟨c, hc_bd, hc_norm⟩ := ih hω_sub (ψ * γ)
        refine ⟨c * ψ, fun t => ?_, ?_⟩
        · rw [hsum_ins t]
          have htri_c : ‖(c * ψ) t - 1‖ ≤ ‖c t - 1‖ + ‖ψ t - 1‖ := by
            have heq : (c * ψ) t - 1 = c t * (ψ t - 1) + (c t - 1) := by
              simp [AddChar.mul_apply]; ring
            rw [heq]
            calc ‖c t * (ψ t - 1) + (c t - 1)‖
                ≤ ‖c t * (ψ t - 1)‖ + ‖c t - 1‖ := norm_add_le _ _
              _ = ‖ψ t - 1‖ + ‖c t - 1‖ := by rw [norm_mul, c.norm_apply, one_mul]
              _ = ‖c t - 1‖ + ‖ψ t - 1‖ := add_comm _ _
          linarith [hc_bd t]
        · rw [hcard, pow_succ', mul_assoc c ψ γ]
          have h3 : ‖S₁‖ + ‖S₂‖ + ‖S₃‖ ≤ 3 * ‖S₂‖ := by linarith
          calc _ ≤ 3 * ‖S₂‖ := htri.trans h3
            _ ≤ 3 * ((3 : ℝ) ^ Λ.card * ‖∑ x : G, (μ x : ℂ) * (c * (ψ * γ)) x‖) := by gcongr
            _ = 3 * (3 : ℝ) ^ Λ.card * ‖∑ x : G, (μ x : ℂ) * (c * (ψ * γ)) x‖ := by ring
      · push Not at h23
        have h1le3 : ‖S₁‖ ≤ ‖S₃‖ := by
          by_contra hlt; push Not at hlt; exact h12 ⟨(h23.trans hlt).le, hlt.le⟩
        obtain ⟨c, hc_bd, hc_norm⟩ := ih hω_sub (ψ⁻¹ * γ)
        refine ⟨c * ψ⁻¹, fun t => ?_, ?_⟩
        · rw [hsum_ins t]
          have hinv_norm : ‖ψ⁻¹ t - 1‖ = ‖ψ t - 1‖ := by
            have heq : ψ⁻¹ t - 1 = -(ψ⁻¹ t) * (ψ t - 1) := by
              have hmul : ψ⁻¹ t * ψ t = 1 := by
                rw [← AddChar.mul_apply, inv_mul_cancel, AddChar.one_apply]
              calc ψ⁻¹ t - 1 = ψ⁻¹ t - ψ⁻¹ t * ψ t := by rw [hmul]
                _ = -(ψ⁻¹ t) * (ψ t - 1) := by ring
            rw [heq, norm_mul, norm_neg, ψ⁻¹.norm_apply, one_mul]
          have htri_c : ‖(c * ψ⁻¹) t - 1‖ ≤ ‖c t - 1‖ + ‖ψ t - 1‖ := by
            have heq : (c * ψ⁻¹) t - 1 = c t * (ψ⁻¹ t - 1) + (c t - 1) := by
              simp [AddChar.mul_apply]; ring
            rw [heq]
            calc ‖c t * (ψ⁻¹ t - 1) + (c t - 1)‖
                ≤ ‖c t * (ψ⁻¹ t - 1)‖ + ‖c t - 1‖ := norm_add_le _ _
              _ = ‖ψ⁻¹ t - 1‖ + ‖c t - 1‖ := by rw [norm_mul, c.norm_apply, one_mul]
              _ = ‖c t - 1‖ + ‖ψ t - 1‖ := by rw [hinv_norm, add_comm]
          linarith [hc_bd t]
        · rw [hcard, pow_succ', mul_assoc c ψ⁻¹ γ]
          have h3 : ‖S₁‖ + ‖S₂‖ + ‖S₃‖ ≤ 3 * ‖S₃‖ := by linarith
          calc _ ≤ 3 * ‖S₃‖ := htri.trans h3
            _ ≤ 3 * ((3 : ℝ) ^ Λ.card * ‖∑ x : G, (μ x : ℂ) * (c * (ψ⁻¹ * γ)) x‖) := by gcongr
            _ = 3 * (3 : ℝ) ^ Λ.card * ‖∑ x : G, (μ x : ℂ) * (c * (ψ⁻¹ * γ)) x‖ := by ring

set_option maxHeartbeats 1200000 in
/-- Chang–Sanders annihilator lemma (`Proposition 5.4` of Schoen–Sisask for `δ = 1/2`):
for a regular Bohr set `B = Bohr(Γ, ρ)` (`ρ ∈ (0, 2]`, `Γ.Nonempty`) and `X ⊆ B` nonempty,
there exists `Λ` of size `≤ k := ⌊16 (1 + log(|B|/|X|))⌋` such that every `γ ∈ Spec_{1/2}(μ_X)`
is `ν`-annihilated on `Bohr(Γ ∪ Λ, ρ')` with `ρ' = ρ * ν / (500000 * |Γ|^2 * (3k + 4))`. -/
lemma chang_sanders_half {Γ : Finset (AddChar G ℂ)} (hΓ : Γ.Nonempty)
    {ρ ν : ℝ} (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 2) (hreg : IsRegularBohr Γ ρ)
    {X : Finset G} (hX : X.Nonempty) (hXB : X ⊆ bohr Γ ρ)
    (hν0 : 0 < ν) (hν1 : ν ≤ 1) :
    let k : ℕ := Nat.floor (16 * (1 + Real.log (((bohr Γ ρ).card : ℝ) / (X.card : ℝ))))
    let ρ' : ℝ := ρ * ν / (500000 * (Γ.card : ℝ) ^ 2 * ((3 * k + 4 : ℕ) : ℝ))
    ∃ Λ : Finset (AddChar G ℂ), Λ.card ≤ k ∧
      ∀ γ : AddChar G ℂ, (1 / 2 : ℝ) ≤ ‖dftG (muC X) γ‖ →
        ∀ t ∈ bohr (Γ ∪ Λ) ρ', ‖γ t - 1‖ ≤ ν := by
  intro k ρ'
  let d : ℝ := (Γ.card : ℝ)
  have hd_pos : 0 < d := Nat.cast_pos.2 hΓ.card_pos
  have hd_ge1 : 1 ≤ d := Nat.one_le_cast.2 hΓ.card_pos
  let B := bohr Γ ρ
  have hBpos : (0 : ℝ) < (B.card : ℝ) := Nat.cast_pos.2 (bohr_card_pos Γ hρ0.le)
  have hXpos : (0 : ℝ) < (X.card : ℝ) := Nat.cast_pos.2 hX.card_pos
  have hlog_nn : 0 ≤ Real.log ((B.card : ℝ) / (X.card : ℝ)) := by
    apply Real.log_nonneg
    rw [one_le_div hXpos]
    exact Nat.cast_le.2 (Finset.card_le_card hXB)
  let L : ℕ := 3 * k + 4
  have hL_pos : (0 : ℝ) < (L : ℝ) := by positivity
  -- Choose regular `B_r` with `r ∈ [r₀/2, r₀]` where `r₀ = 1 / (300 d L)`.
  let r₀ : ℝ := 1 / (300 * d * (L : ℝ))
  have hr₀_pos : 0 < r₀ := by positivity
  obtain ⟨t_reg, ht_lo, ht_hi, hreg_r⟩ := exists_regular_bohr Γ hΓ (show 0 < r₀ * ρ by positivity)
  let r : ℝ := t_reg * r₀
  have hr_lo : 1 / (600 * d * (L : ℝ)) ≤ r := by
    dsimp only [r, r₀]
    calc 1 / (600 * d * (L : ℝ)) = (1 / 2) * (1 / (300 * d * (L : ℝ))) := by ring
      _ ≤ t_reg * (1 / (300 * d * (L : ℝ))) := mul_le_mul_of_nonneg_right ht_lo (by positivity)
  have hr_hi : r ≤ 1 / (300 * d * (L : ℝ)) := by
    dsimp only [r, r₀]
    calc t_reg * (1 / (300 * d * (L : ℝ))) ≤ 1 * (1 / (300 * d * (L : ℝ))) :=
          mul_le_mul_of_nonneg_right ht_hi (by positivity)
      _ = 1 / (300 * d * (L : ℝ)) := one_mul _
  have hr_pos : 0 < r := lt_of_lt_of_le (by positivity) hr_lo
  have hreg_Br : IsRegularBohr Γ (r * ρ) := by
    have : r * ρ = t_reg * (r₀ * ρ) := by dsimp only [r]; ring
    rwa [this]
  let Br : Finset G := bohr Γ (r * ρ)
  let Bplus : Finset G := bohr Γ ((1 + (L : ℝ) * r) * ρ)
  let βplus : G → ℝ := convR (muR Bplus) (iterConvR (muR Br) L)
  have hBr_ne : Br.Nonempty := bohr_nonempty Γ (by positivity)
  have hBplus_ne : Bplus.Nonempty := bohr_nonempty Γ (by positivity)
  have hBplus_pos : (0 : ℝ) < (Bplus.card : ℝ) := Nat.cast_pos.2 hBplus_ne.card_pos
  -- Step 1: Pointwise bound `μ_B(x) ≤ exp(1/2) * β^+(x)`.
  have hβ_dom : ∀ x : G, muR B x ≤ Real.exp (1 / 2) * βplus x := by
    have hLr_le : (L : ℝ) * r ≤ 1 / (300 * d) := by
      have hmul := mul_le_mul_of_nonneg_left hr_hi hL_pos.le
      have hsimp : (L : ℝ) * (1 / (300 * d * (L : ℝ))) = 1 / (300 * d) := by
        field_simp [hL_pos.ne', hd_pos.ne']
      linarith
    have hBplus_ratio : (Bplus.card : ℝ) / (B.card : ℝ) ≤ Real.exp (1 / 2) := by
      have hreg_up := (hreg ((L : ℝ) * r) (by
        rw [abs_of_nonneg (by positivity)]
        exact hLr_le.trans (div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)))).2
      rw [abs_of_nonneg (by positivity)] at hreg_up
      have h13 : 1 + 100 * d * ((L : ℝ) * r) ≤ 4 / 3 := by
        have hmul := mul_le_mul_of_nonneg_left hLr_le (show (0 : ℝ) ≤ 100 * d by positivity)
        have hsimp : 100 * d * (1 / (300 * d)) = 1 / 3 := by field_simp [hd_pos.ne']; ring
        linarith
      have h43_exp : (4 / 3 : ℝ) ≤ Real.exp (1 / 2) := by
        have := Real.add_one_le_exp (1 / 2 : ℝ)
        linarith
      rw [div_le_iff₀ hBpos]
      calc (Bplus.card : ℝ) ≤ (1 + 100 * d * ((L : ℝ) * r)) * (B.card : ℝ) := hreg_up
        _ ≤ (4 / 3 : ℝ) * (B.card : ℝ) := mul_le_mul_of_nonneg_right h13 hBpos.le
        _ ≤ Real.exp (1 / 2) * (B.card : ℝ) := mul_le_mul_of_nonneg_right h43_exp hBpos.le
    -- Show `iterConvR (muR Br) L` is supported on `bohr Γ (L * r * ρ)`.
    have hsupp : ∀ (n : ℕ) (y : G), iterConvR (muR Br) n y ≠ 0 →
        y ∈ bohr Γ ((n : ℝ) * (r * ρ)) := by
      intro n
      induction n with
      | zero =>
        intro y hy
        have hy0 : y = 0 := by
          by_contra hne; exact hy (by simp [iterConvR, hne])
        subst hy0; simpa using zero_mem_bohr Γ le_rfl
      | succ n ih =>
        intro y hy
        unfold iterConvR convR at hy
        have hex : ∃ z : G, iterConvR (muR Br) n z * muR Br (y - z) ≠ 0 := by
          by_contra hall; push Not at hall
          exact hy (Finset.sum_eq_zero fun z _ => hall z)
        obtain ⟨z, hz⟩ := hex
        have hz1 : iterConvR (muR Br) n z ≠ 0 := left_ne_zero_of_mul hz
        have hz2 : y - z ∈ Br := by
          by_contra hnot; exact right_ne_zero_of_mul hz (by simp [muR, hnot])
        have hmem := add_mem_bohr (ih z hz1) hz2
        rw [add_sub_cancel] at hmem
        have heq : (n : ℝ) * (r * ρ) + r * ρ = ((n + 1 : ℕ) : ℝ) * (r * ρ) := by push_cast; ring
        rwa [heq] at hmem
    intro x
    by_cases hx : x ∈ B
    · have hβ_eq : βplus x = (Bplus.card : ℝ)⁻¹ := by
        dsimp only [βplus]
        rw [convR_comm]
        unfold convR
        have hterm : ∀ y : G, iterConvR (muR Br) L y * muR Bplus (x - y) =
            iterConvR (muR Br) L y * (Bplus.card : ℝ)⁻¹ := by
          intro y
          by_cases hy0 : iterConvR (muR Br) L y = 0
          · simp [hy0]
          · have hy_mem : y ∈ bohr Γ ((L : ℝ) * (r * ρ)) := hsupp L y hy0
            have hxy : x - y ∈ Bplus := by
              have := sub_mem_bohr hx hy_mem
              have heq : ρ + (L : ℝ) * (r * ρ) = (1 + (L : ℝ) * r) * ρ := by ring
              rwa [heq] at this
            simp [muR, hxy]
        simp_rw [hterm, ← Finset.sum_mul, sum_iterConvR_muR hBr_ne L, one_mul]
      rw [hβ_eq]
      simp only [muR, hx, ite_true]
      have hmul := mul_le_mul_of_nonneg_right hBplus_ratio (show (0 : ℝ) ≤ (Bplus.card : ℝ)⁻¹ by positivity)
      have hlhs : (Bplus.card : ℝ) / (B.card : ℝ) * (Bplus.card : ℝ)⁻¹ = (B.card : ℝ)⁻¹ := by
        field_simp [hBpos.ne', hBplus_pos.ne']
      linarith
    · simp only [muR, hx, ite_false]
      exact mul_nonneg (Real.exp_pos _).le (convR_nonneg (muR_nonneg Bplus) (iterConvR_muR_nonneg Br L) x)
  -- Step 2: Any `(1/2)`-dissociated subset of `Spec_{1/2}(μ_X)` w.r.t. `β^+` has size `≤ k`.
  let Δ : Finset (AddChar G ℂ) := Finset.univ.filter fun γ => (1 / 2 : ℝ) ≤ ‖dftG (muC X) γ‖
  have hbound_diss : ∀ Λ ⊆ Δ, IsDissoc βplus (1 / 2) Λ → Λ.card ≤ k := by
    intro Λ hΛΔ hΛd
    have hΛB : IsDissoc (muR B) 1 Λ := by
      intro ω hω
      calc ∑ x : G, muR B x * rieszProd Λ ω x
          ≤ ∑ x : G, (Real.exp (1 / 2) * βplus x) * rieszProd Λ ω x :=
            Finset.sum_le_sum fun x _ =>
              mul_le_mul_of_nonneg_right (hβ_dom x) (rieszProd_nonneg hω x)
        _ = Real.exp (1 / 2) * ∑ x : G, βplus x * rieszProd Λ ω x := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => by ring
        _ ≤ Real.exp (1 / 2) * Real.exp (1 / 2) :=
            mul_le_mul_of_nonneg_left (hΛd ω hω) (Real.exp_pos _).le
        _ = Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have hchang := local_chang_bound hX hXB (show (0 : ℝ) < 1 / 2 by norm_num) (by norm_num)
      (fun ψ hψ => (Finset.mem_filter.1 (hΛΔ hψ)).2) hΛB
    have h16 : 4 / (1 / 2 : ℝ) ^ 2 = 16 := by norm_num
    rw [h16] at hchang
    exact Nat.le_floor hchang
  -- Step 3: Greedy iteration for `η_i = i / (2 (k + 1))` produces maximal `Λ ⊆ Δ` with `|Λ| ≤ k`.
  let η_step : ℝ := 1 / (2 * ((k + 1 : ℕ) : ℝ))
  have hη_step_pos : 0 < η_step := by positivity
  have hgreedy : ∀ n : ℕ,
      (∃ Λ : Finset (AddChar G ℂ), Λ ⊆ Δ ∧ Λ.card = n ∧ IsDissoc βplus ((n : ℝ) * η_step) Λ) ∨
      (∃ i < n, ∃ Λ : Finset (AddChar G ℂ), Λ ⊆ Δ ∧ Λ.card = i ∧
        IsDissoc βplus ((i : ℝ) * η_step) Λ ∧
        ∀ γ ∈ Δ, γ ∉ Λ → ¬ IsDissoc βplus (((i + 1 : ℕ) : ℝ) * η_step) (insert γ Λ)) := by
    intro n
    induction n with
    | zero =>
      left
      refine ⟨∅, Finset.empty_subset _, Finset.card_empty, ?_⟩
      intro ω _
      simp only [Nat.cast_zero, zero_mul, Real.exp_zero, rieszProd, Finset.prod_empty, mul_one]
      have hsumβ : ∑ x : G, βplus x = 1 := by
        dsimp only [βplus]
        unfold convR
        rw [Finset.sum_comm]
        have : ∀ y : G, ∑ x : G, muR Bplus y * iterConvR (muR Br) L (x - y) =
            muR Bplus y * 1 := by
          intro y
          rw [← Finset.mul_sum]
          congr 1
          exact (Fintype.sum_equiv (Equiv.subRight y) _ (fun z => iterConvR (muR Br) L z)
            (fun _ => rfl)).trans (sum_iterConvR_muR hBr_ne L)
        simp_rw [this, mul_one, sum_muR hBplus_ne]
      linarith
    | succ n ih =>
      rcases ih with ⟨Λ, hΛΔ, hΛc, hΛd⟩ | ⟨i, hi, Λ, hΛΔ, hΛc, hΛd, hmax⟩
      · by_cases hex : ∃ γ ∈ Δ, γ ∉ Λ ∧ IsDissoc βplus (((n + 1 : ℕ) : ℝ) * η_step) (insert γ Λ)
        · rcases hex with ⟨γ, hγΔ, hγΛ, hγd⟩
          left
          refine ⟨insert γ Λ, Finset.insert_subset_iff.2 ⟨hγΔ, hΛΔ⟩, ?_, hγd⟩
          rw [Finset.card_insert_of_notMem hγΛ, hΛc]
        · push Not at hex
          right
          exact ⟨n, Nat.lt_succ_self n, Λ, hΛΔ, hΛc, hΛd, hex⟩
      · right
        exact ⟨i, Nat.lt_succ_of_lt hi, Λ, hΛΔ, hΛc, hΛd, hmax⟩
  have hstep_done : ∃ i ≤ k, ∃ Λ : Finset (AddChar G ℂ), Λ ⊆ Δ ∧ Λ.card = i ∧
      IsDissoc βplus ((i : ℝ) * η_step) Λ ∧
      ∀ γ ∈ Δ, γ ∉ Λ → ¬ IsDissoc βplus (((i + 1 : ℕ) : ℝ) * η_step) (insert γ Λ) := by
    rcases hgreedy (k + 1) with ⟨Λ, hΛΔ, hΛc, hΛd⟩ | ⟨i, hi, Λ, hΛΔ, hΛc, hΛd, hmax⟩
    · have heq : ((k + 1 : ℕ) : ℝ) * η_step = 1 / 2 := by
        dsimp only [η_step]
        have hpos : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp [hpos]
      rw [heq] at hΛd
      have hle := hbound_diss Λ hΛΔ hΛd
      omega
    · exact ⟨i, Nat.lt_succ_iff.1 hi, Λ, hΛΔ, hΛc, hΛd, hmax⟩
  obtain ⟨i, hik, Λ, hΛΔ, hΛc, hΛd, hΛmax⟩ := hstep_done
  refine ⟨Λ, hΛc ▸ hik, ?_⟩
  -- Step 4: Show every `γ ∈ Δ` is `ν`-annihilated on `bohr (Γ ∪ Λ) ρ'`.
  intro γ hγSpec t ht
  have htΓ : t ∈ bohr Γ ρ' := bohr_antitone_freq Finset.subset_union_left ρ' ht
  have htΛ : t ∈ bohr Λ ρ' := bohr_antitone_freq Finset.subset_union_right ρ' ht
  have hρ'_le_ν : ρ' ≤ ν := by
    dsimp only [ρ']
    have hden : (2 : ℝ) ≤ 500000 * d ^ 2 * (L : ℝ) := by
      have hd2 : 1 ≤ d ^ 2 := by nlinarith
      have hL4 : (4 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (show 4 ≤ L by omega)
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  by_cases hγΛ : γ ∈ Λ
  · exact ((mem_bohr.1 htΛ) γ hγΛ).trans hρ'_le_ν
  · have hγΔ : γ ∈ Δ := Finset.mem_filter.2 ⟨Finset.mem_univ _, hγSpec⟩
    have hnot := hΛmax γ hγΔ hγΛ
    unfold IsDissoc at hnot
    push Not at hnot
    obtain ⟨ω, hω, hgt⟩ := hnot
    have hω_sub : ∀ ψ ∈ Λ, ‖ω ψ‖ ≤ 1 := fun ψ hψ => hω ψ (Finset.mem_insert_of_mem hψ)
    have hωγ : ‖ω γ‖ ≤ 1 := hω γ (Finset.mem_insert_self γ Λ)
    have hle_i := hΛd ω hω_sub
    have hsplit_gt :
        ∑ x : G, βplus x * rieszProd (insert γ Λ) ω x =
        (∑ x : G, βplus x * rieszProd Λ ω x) +
        (ω γ * ∑ x : G, (βplus x : ℂ) * (rieszProd Λ ω x : ℂ) * γ x).re := by
      have hpt : ∀ x : G,
          βplus x * rieszProd (insert γ Λ) ω x =
          βplus x * rieszProd Λ ω x +
          (ω γ * ((βplus x : ℂ) * (rieszProd Λ ω x : ℂ) * γ x)).re := by
        intro x
        unfold rieszProd
        rw [Finset.prod_insert hγΛ]
        have hreal : (ω γ * ((βplus x : ℂ) * (∏ ψ ∈ Λ, (1 + (ω ψ * ψ x).re) : ℝ) * γ x)).re =
            βplus x * (∏ ψ ∈ Λ, (1 + (ω ψ * ψ x).re)) * (ω γ * γ x).re := by
          have : ω γ * ((βplus x : ℂ) * ((∏ ψ ∈ Λ, (1 + (ω ψ * ψ x).re) : ℝ) : ℂ) * γ x) =
              (((βplus x * ∏ ψ ∈ Λ, (1 + (ω ψ * ψ x).re) : ℝ) : ℂ) * (ω γ * γ x)) := by
            push_cast; ring
          rw [this, Complex.re_ofReal_mul]
        rw [hreal]; ring
      simp_rw [hpt, Finset.sum_add_distrib, Finset.mul_sum, Complex.re_sum]
    rw [hsplit_gt] at hgt
    have hexp_diff : η_step ≤ Real.exp (((i + 1 : ℕ) : ℝ) * η_step) - Real.exp ((i : ℝ) * η_step) := by
      have h1 : Real.exp (((i + 1 : ℕ) : ℝ) * η_step) = Real.exp ((i : ℝ) * η_step) * Real.exp η_step := by
        rw [← Real.exp_add]; congr 1; push_cast; ring
      rw [h1]
      have he1 : 1 + η_step ≤ Real.exp η_step := by linarith [Real.add_one_le_exp η_step]
      have hei : 1 ≤ Real.exp ((i : ℝ) * η_step) := Real.one_le_exp (by positivity)
      nlinarith
    have hnorm_sum_gt : η_step < ‖∑ x : G, (βplus x : ℂ) * (rieszProd Λ ω x : ℂ) * γ x‖ := by
      have hre_gt : η_step < (ω γ * ∑ x : G, (βplus x : ℂ) * (rieszProd Λ ω x : ℂ) * γ x).re := by
        linarith
      calc η_step < (ω γ * ∑ x : G, (βplus x : ℂ) * (rieszProd Λ ω x : ℂ) * γ x).re := hre_gt
        _ ≤ ‖ω γ * ∑ x : G, (βplus x : ℂ) * (rieszProd Λ ω x : ℂ) * γ x‖ := Complex.re_le_norm _
        _ = ‖ω γ‖ * ‖∑ x : G, (βplus x : ℂ) * (rieszProd Λ ω x : ℂ) * γ x‖ := norm_mul _ _
        _ ≤ 1 * ‖∑ x : G, (βplus x : ℂ) * (rieszProd Λ ω x : ℂ) * γ x‖ :=
            mul_le_mul_of_nonneg_right hωγ (norm_nonneg _)
        _ = ‖∑ x : G, (βplus x : ℂ) * (rieszProd Λ ω x : ℂ) * γ x‖ := one_mul _
    obtain ⟨c, hc_bd, hc_norm⟩ := rieszProd_expand_exists βplus ω Λ hω_sub γ
    -- Compute `‖∑ x, β^+(x) * (c * γ)(x)‖ = ‖dftG(μ_{B^+})(ψ⁻¹)‖ * ‖dftG(μ_{B_r})(ψ⁻¹)‖^L`.
    set ψ : AddChar G ℂ := c * γ
    have hβ_fourier : ‖∑ x : G, (βplus x : ℂ) * ψ x‖ ≤ ‖dftG (muC Br) ψ⁻¹‖ ^ L := by
      have hsum_dft : ∑ x : G, (βplus x : ℂ) * ψ x = dftG (fun x => (βplus x : ℂ)) ψ⁻¹ := by
        unfold dftG
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Complex.star_def, AddChar.inv_apply, AddChar.map_neg_eq_conj, starRingEnd_self_apply]
      have hβC : (fun x => (βplus x : ℂ)) = convC (muC Bplus) (iterConvC (muC Br) L) := by
        funext x
        dsimp only [βplus]
        rw [← convC_ofReal]
        congr 1
        · funext y; exact (muC_eq_ofReal_muR Bplus y).symm
        · funext y; rw [← iterConvC_ofReal]; congr 1; funext z; exact (muC_eq_ofReal_muR Br z).symm
      rw [hsum_dft, hβC, dftG_convC, dftG_iterConvC, norm_mul, norm_pow]
      calc ‖dftG (muC Bplus) ψ⁻¹‖ * ‖dftG (muC Br) ψ⁻¹‖ ^ L
          ≤ 1 * ‖dftG (muC Br) ψ⁻¹‖ ^ L :=
            mul_le_mul_of_nonneg_right (norm_dftG_muC_le_one Bplus ψ⁻¹) (by positivity)
        _ = ‖dftG (muC Br) ψ⁻¹‖ ^ L := one_mul _
    -- Deduce `‖dftG (muC Br) ψ⁻¹‖ > 1 / 2` from `(3^k * 2(k+1)) < 2^L`.
    have hpow_gt : (1 / 2 : ℝ) ^ L < ‖dftG (muC Br) ψ⁻¹‖ ^ L := by
      have h1 : η_step < (3 : ℝ) ^ k * ‖dftG (muC Br) ψ⁻¹‖ ^ L := by
        have h3le : (3 : ℝ) ^ Λ.card ≤ (3 : ℝ) ^ k :=
          pow_le_pow_right₀ (by norm_num) (hΛc ▸ hik)
        calc η_step < ‖∑ x : G, (βplus x : ℂ) * (rieszProd Λ ω x : ℂ) * γ x‖ := hnorm_sum_gt
          _ ≤ (3 : ℝ) ^ Λ.card * ‖∑ x : G, (βplus x : ℂ) * ψ x‖ := hc_norm
          _ ≤ (3 : ℝ) ^ k * ‖dftG (muC Br) ψ⁻¹‖ ^ L :=
              mul_le_mul h3le hβ_fourier (norm_nonneg _) (by positivity)
      have h2L : (3 : ℝ) ^ k * (2 * ((k + 1 : ℕ) : ℝ)) < (2 : ℝ) ^ L := by
        have hk2 : ∀ n : ℕ, n + 1 ≤ 2 ^ (n + 1) := fun n => by
          induction n with
          | zero => norm_num
          | succ m ihm => rw [pow_succ]; omega
        have hk2R : ((k + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by exact_mod_cast hk2 k
        have hL_eq : (2 : ℝ) ^ L = 16 * (8 : ℝ) ^ k := by
          dsimp only [L]
          rw [pow_add, pow_mul]; norm_num; ring
        rw [hL_eq]
        have h68 : (6 : ℝ) ^ k ≤ (8 : ℝ) ^ k := pow_le_pow_left₀ (by positivity) (by norm_num) k
        have hprod : (3 : ℝ) ^ k * (2 * (2 : ℝ) ^ (k + 1)) = 4 * (6 : ℝ) ^ k := by
          rw [pow_succ, show (6 : ℝ) ^ k = (3 : ℝ) ^ k * (2 : ℝ) ^ k by rw [← mul_pow]; norm_num]
          ring
        calc (3 : ℝ) ^ k * (2 * ((k + 1 : ℕ) : ℝ))
            ≤ (3 : ℝ) ^ k * (2 * (2 : ℝ) ^ (k + 1)) := by gcongr
          _ = 4 * (6 : ℝ) ^ k := hprod
          _ ≤ 4 * (8 : ℝ) ^ k := by gcongr
          _ < 16 * (8 : ℝ) ^ k := by linarith [pow_pos (show (0 : ℝ) < 8 by norm_num) k]
      have hη_gt : (3 : ℝ) ^ k * (1 / 2 : ℝ) ^ L < η_step := by
        dsimp only [η_step]
        rw [one_div_pow, mul_one_div, div_lt_div_iff₀ (by positivity) (by positivity), one_mul]
        exact h2L
      have h3k_pos : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
      exact lt_of_mul_lt_mul_left (hη_gt.trans h1) h3k_pos.le
    have hdft_half : (1 / 2 : ℝ) < ‖dftG (muC Br) ψ⁻¹‖ := by
      by_contra hle; push Not at hle
      have := pow_le_pow_left₀ (norm_nonneg _) hle L
      linarith
    -- Step 5: Regularity of `B_r` implies `‖ψ t - 1‖ ≤ ν / 2` for `t ∈ bohr Γ ρ'`.
    have hψ_t : ‖ψ t - 1‖ ≤ ν / 2 := by
      let s : ℝ := ν / (800 * d)
      have hs0 : 0 ≤ s := by positivity
      have hs_le : s ≤ 1 / (100 * d) := by
        dsimp only [s]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have ht_Brs : t ∈ bohr Γ (s * (r * ρ)) := by
        refine bohr_mono_radius Γ ?_ htΓ
        have hsr : ρ' ≤ s * (r * ρ) := by
          dsimp only [ρ', s]
          have h1 : ν / (800 * d) * (1 / (600 * d * (L : ℝ)) * ρ) ≤ ν / (800 * d) * (r * ρ) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hr_lo hρ0.le) (by positivity)
          have h2 : ρ * ν / (500000 * d ^ 2 * (L : ℝ)) ≤
              ν / (800 * d) * (1 / (600 * d * (L : ℝ)) * ρ) := by
            have heq : ν / (800 * d) * (1 / (600 * d * (L : ℝ)) * ρ) =
                ρ * ν / (480000 * d ^ 2 * (L : ℝ)) := by
              field_simp [hd_pos.ne', hL_pos.ne']; ring
            rw [heq]
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
          exact h2.trans h1
        exact hsr
      have hL1 := norm_L1_muR_translate_sub_le (show 0 < r * ρ by positivity) hreg_Br hs0 hs_le ht_Brs
      have hchar_id : (1 - ψ t) * dftG (muC Br) ψ⁻¹ =
          ∑ x : G, ((muR Br x - muR Br (x - t) : ℝ) : ℂ) * ψ x := by
        have h1 : dftG (muC Br) ψ⁻¹ = ∑ x : G, (muR Br x : ℂ) * ψ x := by
          unfold dftG
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [muC_eq_ofReal_muR, Complex.star_def, AddChar.inv_apply, AddChar.map_neg_eq_conj,
            starRingEnd_self_apply]
        have h2 : ψ t * dftG (muC Br) ψ⁻¹ = ∑ x : G, (muR Br (x - t) : ℂ) * ψ x := by
          rw [h1, Finset.mul_sum]
          refine Fintype.sum_equiv (Equiv.addRight t) _ _ fun x => ?_
          change ψ t * ((muR Br x : ℂ) * ψ x) = (muR Br (x + t - t) : ℂ) * ψ (x + t)
          have hsub : x + t - t = x := add_sub_cancel_right x t
          rw [hsub, AddChar.map_add_eq_mul]
          ring
        rw [sub_mul, one_mul, h2, h1, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun x _ => by push_cast; ring
      have hnorm_prod : ‖ψ t - 1‖ * ‖dftG (muC Br) ψ⁻¹‖ ≤ 200 * d * s := by
        calc ‖ψ t - 1‖ * ‖dftG (muC Br) ψ⁻¹‖
            = ‖(1 - ψ t) * dftG (muC Br) ψ⁻¹‖ := by rw [norm_mul, norm_sub_rev]
          _ = ‖∑ x : G, ((muR Br x - muR Br (x - t) : ℝ) : ℂ) * ψ x‖ := by rw [hchar_id]
          _ ≤ ∑ x : G, ‖((muR Br x - muR Br (x - t) : ℝ) : ℂ) * ψ x‖ := norm_sum_le _ _
          _ = ∑ x : G, |muR Br (x - t) - muR Br x| := by
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [norm_mul, ψ.norm_apply, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
          _ ≤ 200 * d * s := hL1
      have h200s : 200 * d * s = ν / 4 := by
        dsimp only [s]; field_simp [hd_pos.ne']; ring
      nlinarith [norm_nonneg (ψ t - 1)]
    -- Step 6: `‖c t - 1‖ ≤ |Λ| * ρ' ≤ ν / 2`, combine with `ψ = c * γ`.
    have hc_t : ‖c t - 1‖ ≤ ν / 2 := by
      have h1 : ‖c t - 1‖ ≤ (Λ.card : ℝ) * ρ' := by
        calc ‖c t - 1‖ ≤ ∑ χ ∈ Λ, ‖χ t - 1‖ := hc_bd t
          _ ≤ ∑ _χ ∈ Λ, ρ' := Finset.sum_le_sum fun χ hχ => (mem_bohr.1 htΛ) χ hχ
          _ = (Λ.card : ℝ) * ρ' := by simp
      have h2 : (Λ.card : ℝ) * ρ' ≤ ν / 2 := by
        have hΛk : (Λ.card : ℝ) ≤ (k : ℝ) := by exact_mod_cast (hΛc ▸ hik)
        have hρ'_nn : 0 ≤ ρ' := by dsimp only [ρ']; positivity
        have hkL : (k : ℝ) ≤ (L : ℝ) := by exact_mod_cast (show k ≤ L by omega)
        calc (Λ.card : ℝ) * ρ' ≤ (k : ℝ) * ρ' := mul_le_mul_of_nonneg_right hΛk hρ'_nn
          _ ≤ (L : ℝ) * (ρ * ν / (500000 * d ^ 2 * (L : ℝ))) :=
              mul_le_mul_of_nonneg_right hkL hρ'_nn
          _ = ρ * ν / (500000 * d ^ 2) := by field_simp [hL_pos.ne', hd_pos.ne']
          _ ≤ 2 * ν / (500000 * 1) := by
              have hd2 : (1 : ℝ) ≤ d ^ 2 := by nlinarith
              have hnum : ρ * ν ≤ 2 * ν := mul_le_mul_of_nonneg_right hρ2 hν0.le
              have hden : 500000 * (1 : ℝ) ≤ 500000 * d ^ 2 := by linarith
              exact div_le_div₀ (by positivity) hnum (by positivity) hden
          _ ≤ ν / 2 := by linarith
      exact h1.trans h2
    -- Triangle inequality: `γ = c⁻¹ * ψ`.
    have hγ_eq : γ t - 1 = (c t)⁻¹ * ((ψ t - 1) - (c t - 1)) := by
      have hc0 : c t ≠ 0 := by
        intro hc0; have := c.norm_apply t; rw [hc0, norm_zero] at this; norm_num at this
      have hψt : ψ t = c t * γ t := rfl
      rw [hψt]
      field_simp [hc0]
      ring
    rw [hγ_eq, norm_mul, norm_inv, c.norm_apply, inv_one, one_mul]
    calc ‖(ψ t - 1) - (c t - 1)‖ ≤ ‖ψ t - 1‖ + ‖c t - 1‖ := norm_sub_le _ _
      _ ≤ ν / 2 + ν / 2 := add_le_add hψ_t hc_t
      _ = ν := by ring

set_option maxHeartbeats 1200000 in
/-- `L^∞`-almost-periodicity with Bohr sets (`Theorem 5.2` of Schoen–Sisask, simplified for `S = B`
regular Bohr set, i.e., `σ = 1`). -/
lemma linfty_ap_bohr {A M L : Finset G} (hA : A.Nonempty) (hM : M.Nonempty) (hL : L.Nonempty)
    {Γ : Finset (AddChar G ℂ)} (hΓ : Γ.Nonempty) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 2)
    (hreg : IsRegularBohr Γ ρ)
    {K ε η : ℝ} (hK : 1 ≤ K)
    (hAS : ((A.image (fun a => a) ×ˢ bohr Γ ρ).image (fun p => p.1 + p.2)).card ≤ K * (A.card : ℝ))
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hη_le : η ≤ (M.card : ℝ) / (L.card : ℝ)) :
    let ε₁ : ℝ := ε / 4
    let ν : ℝ := ε₁ * Real.sqrt η
    let k : ℕ := Nat.ceil (Real.log (2 / ν) / Real.log 2) + 1
    let m : ℕ := Nat.ceil (Real.log (2 / η)) + 1
    let r : ℕ := Nat.ceil (1600 * (m : ℝ) * (k : ℝ) ^ 2 / (ε₁ / 2) ^ 2) + 1
    let d' : ℕ := Nat.floor (16 * (1 + Real.log (2 * K ^ r)))
    ∃ (Γ' : Finset (AddChar G ℂ)) (ρ_out : ℝ),
      Γ'.Nonempty ∧ Γ'.card ≤ Γ.card + d' ∧
      0 < ρ_out ∧ ρ_out ≤ ρ ∧
      ρ * ν / (1000000 * (Γ.card : ℝ) ^ 2 * ((3 * d' + 4 : ℕ) : ℝ)) ≤ ρ_out ∧
      IsRegularBohr Γ' ρ_out ∧
      ∀ x : G,
        |convR (convR (convR (indR A) (indR M)) (indR L)) (muR (bohr Γ' ρ_out)) x -
          convR (convR (indR A) (indR M)) (indR L) x| ≤
        ε * (A.card : ℝ) * (M.card : ℝ) := by
  intro ε₁ ν k m r d'
  let S := bohr Γ ρ
  have hS : S.Nonempty := bohr_nonempty Γ hρ0.le
  have hSpos : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.2 hS.card_pos
  have hε₁0 : 0 < ε₁ := by dsimp only [ε₁]; positivity
  have hε₁1 : ε₁ ≤ 1 := by dsimp only [ε₁]; linarith
  have hν0 : 0 < ν := by dsimp only [ν]; positivity
  have hν1 : ν ≤ 1 := by
    dsimp only [ν, ε₁]
    have hsq : Real.sqrt η ≤ 1 := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hη1
    nlinarith
  have hk1 : 1 ≤ k := Nat.succ_le_succ (Nat.zero_le _)
  -- Step 1: Apply `linfty_ap_triple` with `ε₁ = ε / 4` and `k`.
  obtain ⟨T, hTS, hTsize, hTap⟩ :=
    linfty_ap_triple hA hM hL hS hK hAS hε₁0 hε₁1 hη0 hη1 hη_le hk1
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hTe
    rw [hTe, Finset.card_empty, Nat.cast_zero] at hTsize
    have hpos : (0 : ℝ) < (99 / 100 : ℝ) * K⁻¹ ^ r * (S.card : ℝ) := by positivity
    linarith
  have hTpos : (0 : ℝ) < (T.card : ℝ) := Nat.cast_pos.2 hTne.card_pos
  -- Bound `k_cs ≤ d'`.
  have hST_ratio : (S.card : ℝ) / (T.card : ℝ) ≤ 2 * K ^ r := by
    rw [div_le_iff₀ hTpos]
    have h1 : (1 / 2 : ℝ) * K⁻¹ ^ r * (S.card : ℝ) ≤ (T.card : ℝ) := by
      have hhalf : (1 / 2 : ℝ) ≤ (99 / 100 : ℝ) := by norm_num
      have hmul : (1 / 2 : ℝ) * K⁻¹ ^ r * (S.card : ℝ) ≤ (99 / 100 : ℝ) * K⁻¹ ^ r * (S.card : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hhalf (by positivity)) hSpos.le
      exact hmul.trans hTsize
    have hmul := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 2 * K ^ r by positivity)
    have hlhs : 2 * K ^ r * ((1 / 2 : ℝ) * K⁻¹ ^ r * (S.card : ℝ)) = (S.card : ℝ) := by
      rw [inv_pow]; field_simp [(pow_pos (show 0 < K by linarith) r).ne']
    linarith
  let k_cs : ℕ := Nat.floor (16 * (1 + Real.log ((S.card : ℝ) / (T.card : ℝ))))
  have hkcs_le : k_cs ≤ d' := by
    apply Nat.floor_mono
    have hlog := Real.log_le_log (div_pos hSpos hTpos) hST_ratio
    linarith
  -- Step 2: Apply `chang_sanders_half` to `T ⊆ S = bohr Γ ρ`.
  obtain ⟨Λ, hΛcard, hΛann⟩ := chang_sanders_half hΓ hρ0 hρ2 hreg hTne hTS hν0 hν1
  let ρ₁ : ℝ := ρ * ν / (500000 * (Γ.card : ℝ) ^ 2 * ((3 * k_cs + 4 : ℕ) : ℝ))
  have hρ₁_pos : 0 < ρ₁ := by dsimp only [ρ₁]; positivity
  let Γ' : Finset (AddChar G ℂ) := Γ ∪ Λ
  have hΓ'_ne : Γ'.Nonempty := hΓ.mono Finset.subset_union_left
  obtain ⟨t_reg, ht_lo, ht_hi, hreg'⟩ := exists_regular_bohr Γ' hΓ'_ne hρ₁_pos
  let ρ_out : ℝ := t_reg * ρ₁
  have hρ_out_pos : 0 < ρ_out := by dsimp only [ρ_out]; positivity
  have hρ_out_le_ρ₁ : ρ_out ≤ ρ₁ := by
    dsimp only [ρ_out]; nlinarith
  have hρ₁_le_ρ : ρ₁ ≤ ρ := by
    dsimp only [ρ₁]
    have hd_ge1 : (1 : ℝ) ≤ (Γ.card : ℝ) := Nat.one_le_cast.2 hΓ.card_pos
    have hden : (1 : ℝ) ≤ 500000 * (Γ.card : ℝ) ^ 2 * ((3 * k_cs + 4 : ℕ) : ℝ) := by
      have h4 : (4 : ℝ) ≤ ((3 * k_cs + 4 : ℕ) : ℝ) := by exact_mod_cast (show 4 ≤ 3 * k_cs + 4 by omega)
      nlinarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hρ_out_ge : ρ * ν / (1000000 * (Γ.card : ℝ) ^ 2 * ((3 * d' + 4 : ℕ) : ℝ)) ≤ ρ_out := by
    have hkd : ((3 * k_cs + 4 : ℕ) : ℝ) ≤ ((3 * d' + 4 : ℕ) : ℝ) := by
      exact_mod_cast (show 3 * k_cs + 4 ≤ 3 * d' + 4 by omega)
    have h1 : ρ * ν / (500000 * (Γ.card : ℝ) ^ 2 * ((3 * d' + 4 : ℕ) : ℝ)) ≤ ρ₁ := by
      dsimp only [ρ₁]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
    calc ρ * ν / (1000000 * (Γ.card : ℝ) ^ 2 * ((3 * d' + 4 : ℕ) : ℝ))
        = (1 / 2) * (ρ * ν / (500000 * (Γ.card : ℝ) ^ 2 * ((3 * d' + 4 : ℕ) : ℝ))) := by ring
      _ ≤ t_reg * ρ₁ := mul_le_mul ht_lo h1 (by positivity) (by linarith)
  refine ⟨Γ', ρ_out, hΓ'_ne, (Finset.card_union_le Γ Λ).trans (Nat.add_le_add_left (hΛcard.trans hkcs_le) _),
    hρ_out_pos, hρ_out_le_ρ₁.trans hρ₁_le_ρ, hρ_out_ge, hreg', ?_⟩
  -- Step 3: Pick `z ∈ T`, set `X = T - z`, and prove `|F(x + t) - F(x)| ≤ ε |A| |M|` for `t ∈ B'`.
  let F : G → ℝ := convR (convR (indR A) (indR M)) (indR L)
  obtain ⟨z, hzT⟩ := hTne
  let X : Finset G := T.image (fun s => s - z)
  have hXne : X.Nonempty := ⟨0, Finset.mem_image.2 ⟨z, hzT, sub_self z⟩⟩
  -- Show `iterConvR (muR X) k` is supported on `k T - k T`, so `|F * μ_X^{*k}(y) - F(y)| ≤ ε₁ |A| |M|`.
  have hsupp_X : ∀ (n : ℕ) (w : G), iterConvR (muR X) n w ≠ 0 →
      ∃ t₁ : Fin n → G, (∀ i, t₁ i ∈ T) ∧ w = ∑ i : Fin n, (t₁ i - z) := by
    intro n
    induction n with
    | zero =>
      intro w hw
      have hw0 : w = 0 := by by_contra h; exact hw (by simp [iterConvR, h])
      exact ⟨Fin.elim0, fun i => i.elim0, by simp [hw0]⟩
    | succ n ih =>
      intro w hw
      unfold iterConvR convR at hw
      have hex : ∃ u : G, iterConvR (muR X) n u * muR X (w - u) ≠ 0 := by
        by_contra hall; push Not at hall
        exact hw (Finset.sum_eq_zero fun u _ => hall u)
      obtain ⟨u, hu⟩ := hex
      obtain ⟨t₁, ht₁, hu_eq⟩ := ih u (left_ne_zero_of_mul hu)
      have hwu_X : w - u ∈ X := by
        by_contra hnot; exact right_ne_zero_of_mul hu (by simp [muR, hnot])
      rcases Finset.mem_image.1 hwu_X with ⟨s, hsT, hs_eq⟩
      refine ⟨Fin.snoc t₁ s, fun i => Fin.lastCases (by simpa using hsT) (fun j => by simpa using ht₁ j) i, ?_⟩
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [← hu_eq, hs_eq, add_sub_cancel]
  have hF_approx : ∀ y : G, |convR F (iterConvR (muR X) k) y - F y| ≤
      ε₁ * (A.card : ℝ) * (M.card : ℝ) := by
    intro y
    have hdiff : convR F (iterConvR (muR X) k) y - F y =
        ∑ w : G, iterConvR (muR X) k w * (F (y - w) - F y) := by
      rw [convR_comm]
      unfold convR
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_iterConvR_muR hXne k, one_mul]
    rw [hdiff]
    calc |∑ w : G, iterConvR (muR X) k w * (F (y - w) - F y)|
        ≤ ∑ w : G, |iterConvR (muR X) k w * (F (y - w) - F y)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ w : G, iterConvR (muR X) k w * |F (y - w) - F y| := by
          refine Finset.sum_congr rfl fun w _ => by
            rw [abs_mul, abs_of_nonneg (iterConvR_muR_nonneg X k w)]
      _ ≤ ∑ w : G, iterConvR (muR X) k w * (ε₁ * (A.card : ℝ) * (M.card : ℝ)) := by
          refine Finset.sum_le_sum fun w _ => ?_
          by_cases hw0 : iterConvR (muR X) k w = 0
          · simp [hw0]
          · obtain ⟨t₁, ht₁, rfl⟩ := hsupp_X k w hw0
            have hneg_sum : y - ∑ i : Fin k, (t₁ i - z) = y + ∑ i : Fin k, (z - t₁ i) := by
              rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
              congr 1; refine Finset.sum_congr rfl fun i _ => by abel
            rw [hneg_sum]
            exact mul_le_mul_of_nonneg_left
              (hTap (fun _ => z) t₁ (fun _ => hzT) ht₁ y)
              (iterConvR_muR_nonneg X k _)
      _ = ε₁ * (A.card : ℝ) * (M.card : ℝ) := by
          rw [← Finset.sum_mul, sum_iterConvR_muR hXne k, one_mul]
  -- Fourier bound on `|(F * μ_X^{*k})(x + t) - (F * μ_X^{*k})(x)| ≤ 2 ε₁ |A| |M|` for `t ∈ bohr Γ' ρ_out`.
  have h2k_le : (1 / 2 : ℝ) ^ k ≤ ν := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hk_ge : Real.log (2 / ν) / Real.log 2 ≤ (k : ℝ) := by
      have h1 := Nat.le_ceil (Real.log (2 / ν) / Real.log 2)
      have h2 : (k : ℝ) = (Nat.ceil (Real.log (2 / ν) / Real.log 2) : ℝ) + 1 := by simp [k]
      linarith
    have hmul : Real.log (2 / ν) ≤ (k : ℝ) * Real.log 2 := (div_le_iff₀ hlog2).1 hk_ge
    have hexp : 2 / ν ≤ (2 : ℝ) ^ k := by
      have h1 := Real.exp_le_exp.2 hmul
      rw [Real.exp_log (by positivity), Real.exp_nat_mul, Real.exp_log (by norm_num)] at h1
      exact h1
    rw [one_div_pow, div_le_iff₀ (by positivity)]
    have hmul2 := mul_le_mul_of_nonneg_left hexp hν0.le
    rw [mul_div_cancel₀ _ hν0.ne'] at hmul2
    linarith
  have hF_smooth : ∀ (x t : G), t ∈ bohr Γ' ρ_out →
      |convR F (iterConvR (muR X) k) (x + t) - convR F (iterConvR (muR X) k) x| ≤
        2 * ε₁ * (A.card : ℝ) * (M.card : ℝ) := by
    intro x t ht
    have ht1 : t ∈ bohr Γ' ρ₁ := bohr_mono_radius Γ' hρ_out_le_ρ₁ ht
    let gC : G → ℂ := convC (convC (convC (indC A) (indC M)) (indC L)) (iterConvC (muC X) k)
    have hgC_eq : ∀ y : G, gC y = (convR F (iterConvR (muR X) k) y : ℂ) := by
      intro y
      dsimp only [gC, F]
      rw [← convC_ofReal]
      congr 1
      · funext u
        rw [← convC_ofReal]
        congr 1
        · funext v
          rw [← convC_ofReal]
          congr 1 <;> (funext w; exact indC_eq_ofReal_indR _ w)
        · funext v; exact indC_eq_ofReal_indR L v
      · funext u; rw [← iterConvC_ofReal]; congr 1; funext v; exact muC_eq_ofReal_muR X v
    have hdiff_norm :
        |convR F (iterConvR (muR X) k) (x + t) - convR F (iterConvR (muR X) k) x| =
        ‖gC (x + t) - gC x‖ := by
      rw [hgC_eq (x + t), hgC_eq x, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [hdiff_norm]
    have hinv_diff : gC (x + t) - gC x =
        (Fintype.card G : ℂ)⁻¹ *
          ∑ ψ : AddChar G ℂ, dftG gC ψ * ψ x * (ψ t - 1) := by
      rw [dftG_inversion gC (x + t), dftG_inversion gC x, ← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun ψ _ => ?_
      rw [AddChar.map_add_eq_mul]; ring
    rw [hinv_diff, norm_mul, norm_inv, Complex.norm_natCast]
    have hdft_gC : ∀ ψ : AddChar G ℂ,
        dftG gC ψ = dftG (indC A) ψ * dftG (indC M) ψ * dftG (indC L) ψ * (dftG (muC X) ψ) ^ k := by
      intro ψ
      dsimp only [gC]
      rw [dftG_convC, dftG_convC, dftG_convC, dftG_iterConvC]
    have hterm_le : ∀ ψ : AddChar G ℂ,
        ‖dftG gC ψ * ψ x * (ψ t - 1)‖ ≤
        (2 * ν * (A.card : ℝ)) * (‖dftG (indC M) ψ‖ * ‖dftG (indC L) ψ‖) := by
      intro ψ
      rw [hdft_gC ψ, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow,
        ψ.norm_apply, mul_one]
      have hA_le := norm_dftG_indC_le A ψ
      have hprod_le : ‖dftG (muC X) ψ‖ ^ k * ‖ψ t - 1‖ ≤ 2 * ν := by
        by_cases hspec : (1 / 2 : ℝ) ≤ ‖dftG (muC T) ψ‖
        · have hann := hΛann ψ hspec t ht1
          have hmu1 : ‖dftG (muC X) ψ‖ ^ k ≤ 1 := by
            calc ‖dftG (muC X) ψ‖ ^ k ≤ 1 ^ k :=
                  pow_le_pow_left₀ (norm_nonneg _) (norm_dftG_muC_le_one X ψ) k
              _ = 1 := one_pow k
          calc ‖dftG (muC X) ψ‖ ^ k * ‖ψ t - 1‖ ≤ 1 * ν :=
                mul_le_mul hmu1 hann (norm_nonneg _) zero_le_one
            _ ≤ 2 * ν := by linarith
        · push Not at hspec
          have hmuX : ‖dftG (muC X) ψ‖ = ‖dftG (muC T) ψ‖ := norm_dftG_muC_translate T z ψ
          rw [hmuX]
          have hpow : ‖dftG (muC T) ψ‖ ^ k ≤ ν :=
            (pow_le_pow_left₀ (norm_nonneg _) hspec.le k).trans h2k_le
          have htri : ‖ψ t - 1‖ ≤ 2 := by
            calc ‖ψ t - 1‖ ≤ ‖ψ t‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
              _ = 2 := by rw [ψ.norm_apply, norm_one]; norm_num
          calc ‖dftG (muC T) ψ‖ ^ k * ‖ψ t - 1‖ ≤ ν * 2 :=
                mul_le_mul hpow htri (norm_nonneg _) hν0.le
            _ = 2 * ν := mul_comm _ _
      calc ‖dftG (indC A) ψ‖ * ‖dftG (indC M) ψ‖ * ‖dftG (indC L) ψ‖ * ‖dftG (muC X) ψ‖ ^ k * ‖ψ t - 1‖
          = (‖dftG (indC A) ψ‖ * (‖dftG (muC X) ψ‖ ^ k * ‖ψ t - 1‖)) *
              (‖dftG (indC M) ψ‖ * ‖dftG (indC L) ψ‖) := by ring
        _ ≤ ((A.card : ℝ) * (2 * ν)) * (‖dftG (indC M) ψ‖ * ‖dftG (indC L) ψ‖) := by
            gcongr
        _ = (2 * ν * (A.card : ℝ)) * (‖dftG (indC M) ψ‖ * ‖dftG (indC L) ψ‖) := by ring
    -- Cauchy-Schwarz + Parseval on `∑ ψ, ‖1̂_M(ψ)‖ * ‖1̂_L(ψ)‖`.
    have hcs : (Fintype.card G : ℝ)⁻¹ * ∑ ψ : AddChar G ℂ, ‖dftG (indC M) ψ‖ * ‖dftG (indC L) ψ‖ ≤
        Real.sqrt (M.card : ℝ) * Real.sqrt (L.card : ℝ) := by
      have h2 := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ)
        (f := fun ψ => ‖dftG (indC M) ψ‖) (g := fun ψ => ‖dftG (indC L) ψ‖)
        Real.HolderConjugate.two_two (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h2
      have hsq2 : ∀ z : ℝ, z ^ (2 : ℝ) = z ^ (2 : ℕ) := fun z => Real.rpow_two z
      simp_rw [hsq2] at h2
      have hGpos : (0 : ℝ) < (Fintype.card G : ℝ) := Nat.cast_pos.2 Fintype.card_pos
      have hpM : ∑ ψ : AddChar G ℂ, ‖dftG (indC M) ψ‖ ^ 2 = (Fintype.card G : ℝ) * (M.card : ℝ) := by
        have h := dftG_parseval (indC M)
        rw [sum_sq_norm_indC] at h
        have := congrArg ((Fintype.card G : ℝ) * ·) h
        rwa [mul_inv_cancel_left₀ hGpos.ne'] at this
      have hpL : ∑ ψ : AddChar G ℂ, ‖dftG (indC L) ψ‖ ^ 2 = (Fintype.card G : ℝ) * (L.card : ℝ) := by
        have h := dftG_parseval (indC L)
        rw [sum_sq_norm_indC] at h
        have := congrArg ((Fintype.card G : ℝ) * ·) h
        rwa [mul_inv_cancel_left₀ hGpos.ne'] at this
      rw [hpM, hpL, Real.sqrt_mul hGpos.le, Real.sqrt_mul hGpos.le] at h2
      have hmul := mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hGpos.le)
      have hrhs : (Fintype.card G : ℝ)⁻¹ *
          (Real.sqrt (Fintype.card G : ℝ) * Real.sqrt (M.card : ℝ) *
            (Real.sqrt (Fintype.card G : ℝ) * Real.sqrt (L.card : ℝ))) =
          Real.sqrt (M.card : ℝ) * Real.sqrt (L.card : ℝ) := by
        have hsq : Real.sqrt (Fintype.card G : ℝ) * Real.sqrt (Fintype.card G : ℝ) =
            (Fintype.card G : ℝ) := Real.mul_self_sqrt hGpos.le
        calc (Fintype.card G : ℝ)⁻¹ *
              (Real.sqrt (Fintype.card G : ℝ) * Real.sqrt (M.card : ℝ) *
                (Real.sqrt (Fintype.card G : ℝ) * Real.sqrt (L.card : ℝ)))
            = ((Fintype.card G : ℝ)⁻¹ * (Real.sqrt (Fintype.card G : ℝ) * Real.sqrt (Fintype.card G : ℝ))) *
              (Real.sqrt (M.card : ℝ) * Real.sqrt (L.card : ℝ)) := by ring
          _ = Real.sqrt (M.card : ℝ) * Real.sqrt (L.card : ℝ) := by
              rw [hsq, inv_mul_cancel₀ hGpos.ne', one_mul]
      linarith
    have hη_sq : Real.sqrt η * Real.sqrt (L.card : ℝ) ≤ Real.sqrt (M.card : ℝ) := by
      rw [← Real.sqrt_mul hη0.le]
      apply Real.sqrt_le_sqrt
      have hLpos : (0 : ℝ) < (L.card : ℝ) := Nat.cast_pos.2 hL.card_pos
      exact (le_div_iff₀ hLpos).1 hη_le
    calc (Fintype.card G : ℝ)⁻¹ * ‖∑ ψ : AddChar G ℂ, dftG gC ψ * ψ x * (ψ t - 1)‖
        ≤ (Fintype.card G : ℝ)⁻¹ * ∑ ψ : AddChar G ℂ, ‖dftG gC ψ * ψ x * (ψ t - 1)‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ (Fintype.card G : ℝ)⁻¹ *
            ∑ ψ : AddChar G ℂ, (2 * ν * (A.card : ℝ)) * (‖dftG (indC M) ψ‖ * ‖dftG (indC L) ψ‖) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ψ _ => hterm_le ψ) (by positivity)
      _ = (2 * ν * (A.card : ℝ)) *
            ((Fintype.card G : ℝ)⁻¹ * ∑ ψ : AddChar G ℂ, ‖dftG (indC M) ψ‖ * ‖dftG (indC L) ψ‖) := by
          rw [← Finset.mul_sum]; ring
      _ ≤ (2 * ν * (A.card : ℝ)) * (Real.sqrt (M.card : ℝ) * Real.sqrt (L.card : ℝ)) := by
          gcongr
      _ = 2 * ε₁ * (A.card : ℝ) * (Real.sqrt (M.card : ℝ) * (Real.sqrt η * Real.sqrt (L.card : ℝ))) := by
          dsimp only [ν]; ring
      _ ≤ 2 * ε₁ * (A.card : ℝ) * (Real.sqrt (M.card : ℝ) * Real.sqrt (M.card : ℝ)) := by
          gcongr
      _ = 2 * ε₁ * (A.card : ℝ) * (M.card : ℝ) := by
          rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]
  -- Step 4: Combine triangle inequality and average over `t ∈ bohr Γ' ρ_out`.
  intro x
  let B' := bohr Γ' ρ_out
  have hB'_ne : B'.Nonempty := bohr_nonempty Γ' hρ_out_pos.le
  have hpt_ap : ∀ t ∈ B', |F (x - t) - F x| ≤ ε * (A.card : ℝ) * (M.card : ℝ) := by
    intro t ht
    have hnt : -t ∈ B' := neg_mem_bohr ht
    have h1 := hF_approx (x + -t)
    have h2 := hF_smooth x (-t) hnt
    have h3 := hF_approx x
    have hsub : F (x - t) - F x =
        (F (x + -t) - convR F (iterConvR (muR X) k) (x + -t)) +
        (convR F (iterConvR (muR X) k) (x + -t) - convR F (iterConvR (muR X) k) x) +
        (convR F (iterConvR (muR X) k) x - F x) := by
      rw [sub_eq_add_neg x t]; ring
    rw [hsub]
    calc |(_ + _) + _|
        ≤ |F (x + -t) - convR F (iterConvR (muR X) k) (x + -t)| +
          |convR F (iterConvR (muR X) k) (x + -t) - convR F (iterConvR (muR X) k) x| +
          |convR F (iterConvR (muR X) k) x - F x| := by
            calc _ ≤ |(F (x + -t) - convR F (iterConvR (muR X) k) (x + -t)) +
                (convR F (iterConvR (muR X) k) (x + -t) - convR F (iterConvR (muR X) k) x)| +
                |convR F (iterConvR (muR X) k) x - F x| := abs_add_le _ _
              _ ≤ _ := by gcongr; exact abs_add_le _ _
      _ ≤ ε₁ * (A.card : ℝ) * (M.card : ℝ) + 2 * ε₁ * (A.card : ℝ) * (M.card : ℝ) +
          ε₁ * (A.card : ℝ) * (M.card : ℝ) := by
            rw [abs_sub_comm (F (x + -t))]
            linarith
      _ = ε * (A.card : ℝ) * (M.card : ℝ) := by dsimp only [ε₁]; ring
  have hdiff : convR F (muR B') x - F x = ∑ t : G, muR B' t * (F (x - t) - F x) := by
    rw [convR_comm]
    unfold convR
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_muR hB'_ne, one_mul]
  change |convR F (muR B') x - F x| ≤ ε * (A.card : ℝ) * (M.card : ℝ)
  rw [hdiff]
  calc |∑ t : G, muR B' t * (F (x - t) - F x)|
      ≤ ∑ t : G, |muR B' t * (F (x - t) - F x)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ t : G, muR B' t * |F (x - t) - F x| := by
        refine Finset.sum_congr rfl fun t _ => by rw [abs_mul, abs_of_nonneg (muR_nonneg B' t)]
    _ ≤ ∑ t : G, muR B' t * (ε * (A.card : ℝ) * (M.card : ℝ)) := by
        refine Finset.sum_le_sum fun t _ => ?_
        by_cases ht : t ∈ B'
        · exact mul_le_mul_of_nonneg_left (hpt_ap t ht) (muR_nonneg B' t)
        · simp [muR, ht]
    _ = ε * (A.card : ℝ) * (M.card : ℝ) := by
        rw [← Finset.sum_mul, sum_muR hB'_ne, one_mul]

end ChangSanders

/- ## Section 5: Density Increment for `x + 3y = 2z + 2w` on `ZMod P` -/

section DensityIncrement

variable {P : ℕ} [Fact P.Prime]

/-- A subset of `ZMod P` has no solution to `x + 3y = 2z + 2w` in 4 distinct elements. -/
def SolFreeMod (A : Finset (ZMod P)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, ∀ w ∈ A,
    [x, y, z, w].Nodup →
    x + 3 * y ≠ 2 * z + 2 * w

lemma solFreeMod_subset {A B : Finset (ZMod P)} (h : B ⊆ A) (hA : SolFreeMod A) :
    SolFreeMod B :=
  fun x hx y hy z hz w hw hnd => hA x (h hx) y (h hy) z (h hz) w (h hw) hnd

lemma solFreeMod_translate {A : Finset (ZMod P)} (hA : SolFreeMod A) (x₀ : ZMod P) :
    SolFreeMod (A.image (fun a => a - x₀)) := by
  intro x hx y hy z hz w hw hnd heq
  rcases Finset.mem_image.1 hx with ⟨x', hx', rfl⟩
  rcases Finset.mem_image.1 hy with ⟨y', hy', rfl⟩
  rcases Finset.mem_image.1 hz with ⟨z', hz', rfl⟩
  rcases Finset.mem_image.1 hw with ⟨w', hw', rfl⟩
  have hnd' : [x', y', z', w'].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      not_false_eq_true, List.nodup_nil, and_true] at hnd ⊢
    rcases hnd with ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6⟩
    exact ⟨⟨fun h => h1 (by rw [h]), fun h => h2 (by rw [h]), fun h => h3 (by rw [h])⟩,
      ⟨fun h => h4 (by rw [h]), fun h => h5 (by rw [h])⟩, fun h => h6 (by rw [h])⟩
  have heq' : x' + 3 * y' = 2 * z' + 2 * w' := by
    have h1 : (x' - x₀) + 3 * (y' - x₀) + 4 * x₀ = 2 * (z' - x₀) + 2 * (w' - x₀) + 4 * x₀ :=
      congrArg (· + 4 * x₀) heq
    ring_nf at h1 ⊢
    exact h1
  exact hA x' hx' y' hy' z' hz' w' hw' hnd' heq'

/-- For prime `P ≥ 5`, `2 ≠ 0` in `ZMod P`. -/
lemma two_ne_zero_zmod (hP : 5 ≤ P) : (2 : ZMod P) ≠ 0 := by
  intro h
  have hdvd : P ∣ 2 := (ZMod.natCast_eq_zero_iff 2 P).1 (by simpa using h)
  have hle : P ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- For prime `P ≥ 5`, `3 ≠ 0` in `ZMod P`. -/
lemma three_ne_zero_zmod (hP : 5 ≤ P) : (3 : ZMod P) ≠ 0 := by
  intro h
  have hdvd : P ∣ 3 := (ZMod.natCast_eq_zero_iff 3 P).1 (by simpa using h)
  have hle : P ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- Multiplication by a nonzero element `c : ZMod P` as an additive equivalence. -/
noncomputable def mulEquivZMod (c : ZMod P) (hc : c ≠ 0) : ZMod P ≃+ ZMod P where
  toFun x := c * x
  invFun x := c⁻¹ * x
  left_inv x := by dsimp only; rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  right_inv x := by dsimp only; rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  map_add' x y := mul_add c x y

/-- Negation as an additive equivalence on `ZMod P`. -/
def negEquivZMod : ZMod P ≃+ ZMod P where
  toFun x := -x
  invFun x := -x
  left_inv := neg_neg
  right_inv := neg_neg
  map_add' := neg_add

lemma convR_indR_muR_eq_density_translate {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
    (A W : Finset G) (hWsym : ∀ w ∈ W, -w ∈ W) (x : G) :
    convR (indR A) (muR W) x =
      (((A.image (fun a => a - x)) ∩ W).card : ℝ) / (W.card : ℝ) := by
  rw [convR_indR_muR]
  congr 1
  norm_cast
  refine Finset.card_nbij (fun b => -b) ?_ ?_ ?_
  · intro b hb
    rw [Finset.mem_coe, Finset.mem_filter] at hb
    rw [Finset.mem_coe, Finset.mem_inter, Finset.mem_image]
    exact ⟨⟨x - b, hb.2, by abel⟩, hWsym b hb.1⟩
  · intro b₁ _ b₂ _ h; exact neg_injective h
  · intro y hy
    rw [Finset.mem_coe, Finset.mem_inter, Finset.mem_image] at hy
    rcases hy.1 with ⟨a, ha, hay⟩
    refine ⟨-y, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hWsym y hy.2, ?_⟩), neg_neg y⟩
    have hsub : x - -y = a := by rw [← hay]; abel
    rwa [hsub]

lemma convR_indR_muR_image_addEquiv {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
    (e : G ≃+ G) (A W : Finset G) (x : G) :
    convR (indR (A.image e)) (muR (W.image e)) x = convR (indR A) (muR W) (e.symm x) := by
  rw [convR_indR_muR, convR_indR_muR, Finset.card_image_of_injective W e.injective]
  congr 1
  norm_cast
  refine Finset.card_nbij (fun y => e.symm y) ?_ ?_ ?_
  · intro y hy
    rw [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    rcases Finset.mem_image.1 hy.1 with ⟨w, hw, rfl⟩
    rcases Finset.mem_image.1 hy.2 with ⟨a, ha, hax⟩
    refine ⟨by simpa using hw, ?_⟩
    have hsub : e.symm x - w = a := by
      apply e.injective
      rw [map_sub, e.apply_symm_apply, hax]
    simpa [hsub] using ha
  · intro y₁ _ y₂ _ h; exact e.symm.injective h
  · intro w hw
    rw [Finset.mem_coe, Finset.mem_filter] at hw
    refine ⟨e w, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hw.1, ?_⟩),
      e.symm_apply_apply w⟩
    exact Finset.mem_image.2 ⟨e.symm x - w, hw.2, by rw [map_sub, e.apply_symm_apply]⟩

/-- Three-scales dichotomy (`Lemma 6.3` of Schoen–Sisask for 3 symmetric sets inside `B_δ`). -/
lemma three_scales_dichotomy {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]
    {Γ : Finset (AddChar G ℂ)} (hΓ : Γ.Nonempty) {ρ δ : ℝ} (hρ : 0 < ρ)
    (hreg : IsRegularBohr Γ ρ)
    {A : Finset G} (hAB : A ⊆ bohr Γ ρ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ ((A.card : ℝ) / ((bohr Γ ρ).card : ℝ)) / (20000 * (Γ.card : ℝ)))
    {W₁ W₂ W₃ : Finset G}
    (hW₁ne : W₁.Nonempty) (hW₂ne : W₂.Nonempty) (hW₃ne : W₃.Nonempty)
    (hW₁sub : W₁ ⊆ bohr Γ (δ * ρ)) (hW₂sub : W₂ ⊆ bohr Γ (δ * ρ)) (hW₃sub : W₃ ⊆ bohr Γ (δ * ρ)) :
    let α : ℝ := (A.card : ℝ) / ((bohr Γ ρ).card : ℝ)
    (∃ x : G, (11 / 10 : ℝ) * α ≤ convR (indR A) (muR W₁) x) ∨
    (∃ x : G, (11 / 10 : ℝ) * α ≤ convR (indR A) (muR W₂) x) ∨
    (∃ x : G, (11 / 10 : ℝ) * α ≤ convR (indR A) (muR W₃) x) ∨
    (∃ x ∈ bohr Γ ρ,
      (77 / 100 : ℝ) * α ≤ convR (indR A) (muR W₁) x ∧
      (77 / 100 : ℝ) * α ≤ convR (indR A) (muR W₂) x ∧
      (77 / 100 : ℝ) * α ≤ convR (indR A) (muR W₃) x) := by
  intro α
  let B := bohr Γ ρ
  have hBne : B.Nonempty := bohr_nonempty Γ hρ.le
  have hBpos : (0 : ℝ) < (B.card : ℝ) := Nat.cast_pos.2 hBne.card_pos
  have hd_pos : (0 : ℝ) < (Γ.card : ℝ) := Nat.cast_pos.2 hΓ.card_pos
  have hα_le1 : α ≤ 1 := by
    dsimp only [α]
    rw [div_le_one hBpos]
    exact Nat.cast_le.2 (Finset.card_le_card hAB)
  have hδ_reg : δ ≤ 1 / (100 * (Γ.card : ℝ)) := by
    calc δ ≤ α / (20000 * (Γ.card : ℝ)) := hδ
      _ ≤ 1 / (20000 * (Γ.card : ℝ)) := div_le_div_of_nonneg_right hα_le1 (by positivity)
      _ ≤ 1 / (100 * (Γ.card : ℝ)) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  have h200dδ : 200 * (Γ.card : ℝ) * δ ≤ (1 / 100 : ℝ) * α := by
    have hmul := mul_le_mul_of_nonneg_left hδ (show (0 : ℝ) ≤ 200 * (Γ.card : ℝ) by positivity)
    have hsimp : 200 * (Γ.card : ℝ) * (α / (20000 * (Γ.card : ℝ))) = (1 / 100 : ℝ) * α := by
      field_simp [hd_pos.ne']; ring
    linarith
  -- For any `W ⊆ B_δ` nonempty, average of `1_A * μ_W` over `B` is at least `(99/100) * α`.
  have havg : ∀ W : Finset G, W.Nonempty → W ⊆ bohr Γ (δ * ρ) →
      (99 / 100 : ℝ) * α ≤ (B.card : ℝ)⁻¹ * ∑ x ∈ B, convR (indR A) (muR W) x := by
    intro W hWne hWsub
    have hL1 := norm_L1_convR_muR_sub_le hρ hreg hδ0 hδ_reg hWne hWsub
    have hsum_eq : (B.card : ℝ)⁻¹ * ∑ x ∈ B, convR (indR A) (muR W) x =
        convR (indR A) (convR (muR B) (muR W)) 0 := by
      have h1 : (B.card : ℝ)⁻¹ * ∑ x ∈ B, convR (indR A) (muR W) x =
          convR (convR (indR A) (muR W)) (muR B) 0 := by
        change (B.card : ℝ)⁻¹ * ∑ x ∈ B, convR (indR A) (muR W) x =
            ∑ x : G, convR (indR A) (muR W) x * (if 0 - x ∈ B then (B.card : ℝ)⁻¹ else 0)
        have hterm : ∀ x : G, convR (indR A) (muR W) x * (if 0 - x ∈ B then (B.card : ℝ)⁻¹ else 0) =
            if x ∈ B then (B.card : ℝ)⁻¹ * convR (indR A) (muR W) x else 0 := by
          intro x
          have hmem : 0 - x ∈ B ↔ x ∈ B := by
            rw [zero_sub]
            exact ⟨fun h => by simpa using neg_mem_bohr h, fun h => neg_mem_bohr h⟩
          by_cases hx : x ∈ B
          · rw [if_pos hx, if_pos (hmem.2 hx), mul_comm]
          · rw [if_neg hx, if_neg (mt hmem.1 hx), mul_zero]
        simp_rw [hterm]
        have hsub_s : ∑ x : G, (if x ∈ B then (B.card : ℝ)⁻¹ * convR (indR A) (muR W) x else 0) =
            ∑ x ∈ B, (B.card : ℝ)⁻¹ * convR (indR A) (muR W) x := by
          rw [← Finset.sum_subset (Finset.subset_univ B)]
          · refine Finset.sum_congr rfl fun x hx => by simp [hx]
          · intro x _ hx; simp [hx]
        rw [hsub_s, ← Finset.mul_sum]
      rw [h1, convR_assoc]
      congr 1; funext y; exact convR_comm (muR W) (muR B) y
    have hbase : convR (indR A) (muR B) 0 = α := by
      unfold convR indR muR
      have hterm : ∀ y : G, (if y ∈ A then (1 : ℝ) else 0) * (if 0 - y ∈ B then (B.card : ℝ)⁻¹ else 0) =
          if y ∈ A then (B.card : ℝ)⁻¹ else 0 := by
        intro y
        by_cases hy : y ∈ A
        · have hyB : 0 - y ∈ B := by rw [zero_sub]; exact neg_mem_bohr (hAB hy)
          rw [if_pos hy, if_pos hyB, one_mul, if_pos hy]
        · simp [hy]
      simp_rw [hterm, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      have hfilt : (Finset.univ.filter fun y => y ∈ A) = A := by ext y; simp
      rw [hfilt]; dsimp only [α]; rw [div_eq_mul_inv]
    rw [hsum_eq]
    have hdiff : |convR (indR A) (convR (muR B) (muR W)) 0 - α| ≤ 200 * (Γ.card : ℝ) * δ := by
      rw [← hbase, ← convR_sub_right]
      unfold convR
      calc |∑ y : G, indR A y * (convR (muR B) (muR W) (0 - y) - muR B (0 - y))|
          ≤ ∑ y : G, |indR A y * (convR (muR B) (muR W) (0 - y) - muR B (0 - y))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ y : G, |convR (muR B) (muR W) (0 - y) - muR B (0 - y)| := by
            refine Finset.sum_le_sum fun y _ => ?_
            rw [abs_mul]
            have hind : |indR A y| ≤ 1 := by unfold indR; split_ifs <;> norm_num
            calc |indR A y| * |convR (muR B) (muR W) (0 - y) - muR B (0 - y)|
                ≤ 1 * |convR (muR B) (muR W) (0 - y) - muR B (0 - y)| :=
                  mul_le_mul_of_nonneg_right hind (abs_nonneg _)
              _ = _ := one_mul _
        _ = ∑ z : G, |convR (muR B) (muR W) z - muR B z| :=
            Fintype.sum_equiv (Equiv.subLeft 0) _ _ (fun _ => rfl)
        _ ≤ 200 * (Γ.card : ℝ) * δ := hL1
    have := (abs_le.1 hdiff).1
    linarith
  -- Sum the 3 averages and pigeonhole over `x ∈ B`.
  have hsum3 : (297 / 100 : ℝ) * α ≤
      (B.card : ℝ)⁻¹ * ∑ x ∈ B,
        (convR (indR A) (muR W₁) x + convR (indR A) (muR W₂) x + convR (indR A) (muR W₃) x) := by
    have h1 := havg W₁ hW₁ne hW₁sub
    have h2 := havg W₂ hW₂ne hW₂sub
    have h3 := havg W₃ hW₃ne hW₃sub
    simp_rw [Finset.sum_add_distrib, mul_add]
    linarith
  have hex_x : ∃ x ∈ B,
      (297 / 100 : ℝ) * α ≤
        convR (indR A) (muR W₁) x + convR (indR A) (muR W₂) x + convR (indR A) (muR W₃) x := by
    by_contra hall
    push Not at hall
    have hlt : ∑ x ∈ B,
        (convR (indR A) (muR W₁) x + convR (indR A) (muR W₂) x + convR (indR A) (muR W₃) x) <
        ∑ _x ∈ B, ((297 / 100 : ℝ) * α) :=
      Finset.sum_lt_sum_of_nonempty hBne hall
    simp only [Finset.sum_const, nsmul_eq_mul] at hlt
    have hmul := mul_lt_mul_of_pos_left hlt (inv_pos.2 hBpos)
    rw [inv_mul_cancel_left₀ hBpos.ne'] at hmul
    linarith
  by_cases h1 : ∃ x : G, (11 / 10 : ℝ) * α ≤ convR (indR A) (muR W₁) x
  · exact Or.inl h1
  by_cases h2 : ∃ x : G, (11 / 10 : ℝ) * α ≤ convR (indR A) (muR W₂) x
  · exact Or.inr (Or.inl h2)
  by_cases h3 : ∃ x : G, (11 / 10 : ℝ) * α ≤ convR (indR A) (muR W₃) x
  · exact Or.inr (Or.inr (Or.inl h3))
  push Not at h1 h2 h3
  obtain ⟨x, hxB, hxsum⟩ := hex_x
  refine Or.inr (Or.inr (Or.inr ⟨x, hxB, ?_, ?_, ?_⟩))
  · linarith [h2 x, h3 x]
  · linarith [h1 x, h3 x]
  · linarith [h1 x, h2 x]

/-- Collision count for distinctness: if `A₀ ⊆ ZMod P` is `SolFreeMod`, `A_X, A_Z, A₁, A₄ ⊆ A₀`
with `Disjoint A₁ A₄` and `1 ≤ A₄.card`, then
`(1_{-3 A₁} * 1_{-A_X} * 1_{2 A_Z + 2 A₄})(0) ≤ 5 |A₁| |A₄|`. -/
lemma distinct_collision_count (hP : 5 ≤ P)
    {A₀ A_X A_Z A₁ A₄ : Finset (ZMod P)}
    (hSol : SolFreeMod A₀)
    (hX0 : A_X ⊆ A₀) (hZ0 : A_Z ⊆ A₀) (h10 : A₁ ⊆ A₀) (h40 : A₄ ⊆ A₀)
    (hdisj : Disjoint A₁ A₄) (hA₄ : 1 ≤ A₄.card) :
    let S₂₄ : Finset (ZMod P) := (A_Z ×ˢ A₄).image (fun p => 2 * p.1 + 2 * p.2)
    convR (convR (indR (A₁.image (fun y => -(3 * y)))) (indR (A_X.image (fun x => -x))))
      (indR S₂₄) 0 ≤ 5 * (A₁.card : ℝ) * (A₄.card : ℝ) := by
  intro S₂₄
  have h3ne : (3 : ZMod P) ≠ 0 := three_ne_zero_zmod hP
  have hneg3_inj : Function.Injective (fun y : ZMod P => -(3 * y)) := by
    intro a b hab
    have h1 : 3 * a = 3 * b := neg_injective hab
    exact mul_left_cancel₀ h3ne h1
  let badPairs : Finset (ZMod P × ZMod P) := (A₁ ×ˢ A_X).filter (fun p => p.2 + 3 * p.1 ∈ S₂₄)
  -- Step 1: Identify the triple convolution at `0` with `badPairs.card`.
  have hconv_eq :
      convR (convR (indR (A₁.image (fun y => -(3 * y)))) (indR (A_X.image (fun x => -x))))
        (indR S₂₄) 0 = (badPairs.card : ℝ) := by
    unfold convR indR
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    have hinner : ∀ v : ZMod P,
        ∑ u : ZMod P,
          (if v ∈ A₁.image (fun y => -(3 * y)) then (1 : ℝ) else 0) *
            (if u - v ∈ A_X.image (fun x => -x) then 1 else 0) *
            (if 0 - u ∈ S₂₄ then 1 else 0) =
        if v ∈ A₁.image (fun y => -(3 * y)) then
          ∑ x ∈ A_X, if x - v ∈ S₂₄ then (1 : ℝ) else 0
        else 0 := by
      intro v
      by_cases hv : v ∈ A₁.image (fun y => -(3 * y))
      · rw [if_pos hv, if_pos hv]
        have h1 : ∑ u : ZMod P, (1 : ℝ) * (if u - v ∈ A_X.image (fun x => -x) then 1 else 0) *
            (if 0 - u ∈ S₂₄ then 1 else 0) =
            ∑ w : ZMod P, if w ∈ A_X then (if w - v ∈ S₂₄ then (1 : ℝ) else 0) else 0 := by
          refine Fintype.sum_equiv
            { toFun := fun u => v - u
              invFun := fun w => v - w
              left_inv := fun u => by ring
              right_inv := fun w => by ring } _ _ fun u => ?_
          have hmem : u - v ∈ A_X.image (fun x => -x) ↔ v - u ∈ A_X := by
            simp only [Finset.mem_image]
            constructor
            · rintro ⟨x, hx, hxu⟩
              have : v - u = x := by rw [← neg_sub u v, ← hxu, neg_neg]
              rwa [this]
            · intro hvu
              exact ⟨v - u, hvu, by ring⟩
          have hsub : 0 - u = (v - u) - v := by ring
          by_cases hu : v - u ∈ A_X
          · have hu' : u - v ∈ A_X.image (fun x => -x) := hmem.2 hu
            simp [hu, hu', hsub]
          · have hu' : u - v ∉ A_X.image (fun x => -x) := fun hc => hu (hmem.1 hc)
            simp [hu, hu']
        rw [h1]
        have hsub2 : ∑ w : ZMod P, (if w ∈ A_X then if w - v ∈ S₂₄ then (1 : ℝ) else 0 else 0) =
            ∑ x ∈ A_X, if x - v ∈ S₂₄ then (1 : ℝ) else 0 := by
          rw [← Finset.sum_subset (Finset.subset_univ A_X)]
          · refine Finset.sum_congr rfl fun x hx => by simp [hx]
          · intro x _ hx; simp [hx]
        exact hsub2
      · simp [hv]
    simp_rw [hinner]
    have houter :
        ∑ v : ZMod P, (if v ∈ A₁.image (fun y => -(3 * y)) then
          ∑ x ∈ A_X, if x - v ∈ S₂₄ then (1 : ℝ) else 0 else 0) =
        ∑ y ∈ A₁, ∑ x ∈ A_X, if x + 3 * y ∈ S₂₄ then (1 : ℝ) else 0 := by
      have hsub1 :
          ∑ v : ZMod P, (if v ∈ A₁.image (fun y => -(3 * y)) then
            ∑ x ∈ A_X, if x - v ∈ S₂₄ then (1 : ℝ) else 0 else 0) =
          ∑ v ∈ A₁.image (fun y => -(3 * y)), ∑ x ∈ A_X, if x - v ∈ S₂₄ then (1 : ℝ) else 0 := by
        rw [← Finset.sum_subset (Finset.subset_univ _)]
        · refine Finset.sum_congr rfl fun v hv => by simp [hv]
        · intro v _ hv; simp [hv]
      rw [hsub1, Finset.sum_image (fun a _ b _ h => hneg3_inj h)]
      refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
      have harg : x - -(3 * y) = x + 3 * y := by abel
      rw [harg]
    rw [houter, ← Finset.sum_product']
    simp only [badPairs, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul, mul_one]
  rw [hconv_eq]
  -- Step 2: Cover `badPairs` by the 5 degenerate-collision families.
  let E₁ : Finset (ZMod P × ZMod P) := A₁.image (fun y => (y, y))
  let E₂ : Finset (ZMod P × ZMod P) := (A₁ ×ˢ A₄).image (fun p => (p.1, 3 * p.1 - 2 * p.2))
  let E₃ : Finset (ZMod P × ZMod P) := A₁ ×ˢ A₄
  let E₄ : Finset (ZMod P × ZMod P) := (A₁ ×ˢ A₄).image (fun p => (p.1, 2 * p.2 - p.1))
  let E₅ : Finset (ZMod P × ZMod P) := (A₁ ×ˢ A₄).image (fun p => (p.1, 4 * p.2 - 3 * p.1))
  have hcover : badPairs ⊆ E₁ ∪ E₂ ∪ E₃ ∪ E₄ ∪ E₅ := by
    intro p hp
    rcases p with ⟨y, x⟩
    have hp' := Finset.mem_filter.1 hp
    have hy : y ∈ A₁ := (Finset.mem_product.1 hp'.1).1
    have hx : x ∈ A_X := (Finset.mem_product.1 hp'.1).2
    rcases Finset.mem_image.1 hp'.2 with ⟨⟨z, w⟩, hzw, heq⟩
    have hz : z ∈ A_Z := (Finset.mem_product.1 hzw).1
    have hw : w ∈ A₄ := (Finset.mem_product.1 hzw).2
    have hnot_nodup : ¬ ([x, y, z, w].Nodup) := fun hnd =>
      hSol x (hX0 hx) y (h10 hy) z (hZ0 hz) w (h40 hw) hnd heq.symm
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true] at hnot_nodup
    have hcases : x = y ∨ x = z ∨ x = w ∨ y = z ∨ y = w ∨ z = w := by tauto
    simp only [Finset.mem_union]
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · left; left; left; left
      exact Finset.mem_image.2 ⟨x, hy, rfl⟩
    · left; left; left; right
      have hx_eq : x = 3 * y - 2 * w := by
        have : 2 * x + 2 * w - x - 2 * w = x + 3 * y - x - 2 * w :=
          congrArg (fun t => t - x - 2 * w) heq
        ring_nf at this ⊢; exact this
      exact Finset.mem_image.2 ⟨(y, w), Finset.mem_product.2 ⟨hy, hw⟩, Prod.ext rfl hx_eq.symm⟩
    · left; left; right
      exact Finset.mem_product.2 ⟨hy, hw⟩
    · left; right
      have hx_eq : x = 2 * w - y := by
        have : 2 * y + 2 * w - 3 * y = x + 3 * y - 3 * y :=
          congrArg (fun t => t - 3 * y) heq
        ring_nf at this ⊢; exact this.symm
      exact Finset.mem_image.2 ⟨(y, w), Finset.mem_product.2 ⟨hy, hw⟩, Prod.ext rfl hx_eq.symm⟩
    · exact absurd hw (Finset.disjoint_left.1 hdisj hy)
    · right
      have hx_eq : x = 4 * z - 3 * y := by
        have : 2 * z + 2 * z - 3 * y = x + 3 * y - 3 * y :=
          congrArg (fun t => t - 3 * y) heq
        ring_nf at this ⊢; exact this.symm
      exact Finset.mem_image.2 ⟨(y, z), Finset.mem_product.2 ⟨hy, hw⟩, Prod.ext rfl hx_eq.symm⟩
  have hcard_le : badPairs.card ≤ 5 * A₁.card * A₄.card := by
    have h1 : E₁.card ≤ A₁.card := Finset.card_image_le
    have h2 : E₂.card ≤ A₁.card * A₄.card := Finset.card_image_le.trans (by rw [Finset.card_product])
    have h3 : E₃.card = A₁.card * A₄.card := Finset.card_product A₁ A₄
    have h4 : E₄.card ≤ A₁.card * A₄.card := Finset.card_image_le.trans (by rw [Finset.card_product])
    have h5 : E₅.card ≤ A₁.card * A₄.card := Finset.card_image_le.trans (by rw [Finset.card_product])
    have hu : badPairs.card ≤ E₁.card + E₂.card + E₃.card + E₄.card + E₅.card := by
      calc badPairs.card
          ≤ (E₁ ∪ E₂ ∪ E₃ ∪ E₄ ∪ E₅).card := Finset.card_le_card hcover
        _ ≤ (E₁ ∪ E₂ ∪ E₃ ∪ E₄).card + E₅.card := Finset.card_union_le _ _
        _ ≤ (E₁ ∪ E₂ ∪ E₃).card + E₄.card + E₅.card := by gcongr; exact Finset.card_union_le _ _
        _ ≤ (E₁ ∪ E₂).card + E₃.card + E₄.card + E₅.card := by gcongr; exact Finset.card_union_le _ _
        _ ≤ E₁.card + E₂.card + E₃.card + E₄.card + E₅.card := by gcongr; exact Finset.card_union_le _ _
    have hA1_le : A₁.card ≤ A₁.card * A₄.card := Nat.le_mul_of_pos_right A₁.card hA₄
    have h5mul : 5 * A₁.card * A₄.card = 5 * (A₁.card * A₄.card) := by ring
    omega
  exact_mod_cast hcard_le

/-- Explicit polylog bound on `d'` and radius in `linfty_ap_bohr` when `ε ≥ 1/40`,
`η = (77/100) α`, `K = 4000 / α`. -/
private lemma ap_params_bound {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    {ε : ℝ} (hεlo : 1 / 40 ≤ ε) (_hε1 : ε ≤ 1) :
    let L : ℝ := Real.log (4 / α)
    let ε₁ : ℝ := ε / 4
    let η : ℝ := (77 / 100 : ℝ) * α
    let ν : ℝ := ε₁ * Real.sqrt η
    let K : ℝ := 4000 / α
    let k : ℕ := Nat.ceil (Real.log (2 / ν) / Real.log 2) + 1
    let m : ℕ := Nat.ceil (Real.log (2 / η)) + 1
    let r : ℕ := Nat.ceil (1600 * (m : ℝ) * (k : ℝ) ^ 2 / (ε₁ / 2) ^ 2) + 1
    let d' : ℕ := Nat.floor (16 * (1 + Real.log (2 * K ^ r)))
    1 < L ∧ (d' : ℝ) ≤ 2e13 * L ^ 4 ∧ (1 / 200 : ℝ) * α ≤ ν := by
  intro L ε₁ η ν K k m r d'
  have h4α_ge : (4 : ℝ) ≤ 4 / α := by rw [le_div_iff₀ hα0]; linarith only [hα1]
  have hL_gt1 : 1 < L := by
    dsimp only [L]
    have hexp1 : Real.exp 1 < 4 := by have := Real.exp_one_lt_d9; linarith only [this]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log (4 / α) := Real.log_lt_log (Real.exp_pos 1) (lt_of_lt_of_le hexp1 h4α_ge)
  have hL_pos : 0 < L := by linarith only [hL_gt1]
  have hε₁_lo : (1 / 160 : ℝ) ≤ ε₁ := by dsimp only [ε₁]; linarith only [hεlo]
  have hε₁_pos : 0 < ε₁ := by linarith only [hε₁_lo]
  have hη_pos : 0 < η := by dsimp only [η]; positivity
  have hν_ge : (1 / 200 : ℝ) * α ≤ ν := by
    dsimp only [ν, η]
    have hsq : (4 / 5 : ℝ) * α ≤ Real.sqrt ((77 / 100 : ℝ) * α) := by
      have h1 : ((4 / 5 : ℝ) * α) ^ 2 ≤ (77 / 100 : ℝ) * α := by
        nlinarith only [hα0, hα1]
      calc (4 / 5 : ℝ) * α = Real.sqrt (((4 / 5 : ℝ) * α) ^ 2) :=
            (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt ((77 / 100 : ℝ) * α) := Real.sqrt_le_sqrt h1
    have hmul := mul_le_mul hε₁_lo hsq (by positivity) hε₁_pos.le
    linarith only [hmul]
  have hν_pos : 0 < ν := lt_of_lt_of_le (by positivity) hν_ge
  -- Bound `k ≤ 12 * L`
  have hk_le : (k : ℝ) ≤ 12 * L := by
    have h2ν_le : 2 / ν ≤ (4 / α) ^ 5 := by
      have h1 : 2 / ν ≤ 400 / α := by
        rw [div_le_div_iff₀ hν_pos hα0]; linarith only [hν_ge]
      have h2 : (400 : ℝ) / α ≤ (4 / α) ^ 5 := by
        rw [div_pow, div_le_div_iff₀ hα0 (pow_pos hα0 5)]
        have hα4 : α ^ 4 ≤ 1 := pow_le_one₀ hα0.le hα1
        have h400 : (400 : ℝ) * α ^ 5 = (400 * α ^ 4) * α := by ring
        have h1024 : (4 : ℝ) ^ 5 * α = 1024 * α := by ring
        nlinarith only [hα0, hα4, h400, h1024]
      exact h1.trans h2
    have hlog_2ν : Real.log (2 / ν) ≤ 5 * L := by
      have h := Real.log_le_log (by positivity) h2ν_le
      rw [Real.log_pow] at h
      simpa [L] using h
    have hlog2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have hexp : Real.exp (1 / 2 : ℝ) ≤ 2 := by
        have h1 : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by rw [sq, ← Real.exp_add]; norm_num
        have h2 : Real.exp 1 < 4 := by have := Real.exp_one_lt_d9; linarith only [this]
        nlinarith only [Real.exp_pos (1 / 2 : ℝ), h1, h2]
      calc (1 / 2 : ℝ) = Real.log (Real.exp (1 / 2)) := (Real.log_exp _).symm
        _ ≤ Real.log 2 := Real.log_le_log (Real.exp_pos _) hexp
    have hlog2_pos : 0 < Real.log 2 := by linarith only [hlog2_ge]
    have hdiv_le : Real.log (2 / ν) / Real.log 2 ≤ 10 * L := by
      rw [div_le_iff₀ hlog2_pos]
      nlinarith only [hlog_2ν, hlog2_ge, hL_pos]
    have hceil_le : (Nat.ceil (Real.log (2 / ν) / Real.log 2) : ℝ) ≤ 10 * L + 1 := by
      by_cases hnn : 0 ≤ Real.log (2 / ν) / Real.log 2
      · linarith only [Nat.ceil_lt_add_one hnn, hdiv_le]
      · push Not at hnn
        rw [Nat.ceil_eq_zero.2 hnn.le, Nat.cast_zero]
        linarith only [hL_pos]
    have hk_eq : (k : ℝ) = (Nat.ceil (Real.log (2 / ν) / Real.log 2) : ℝ) + 1 := by
      dsimp only [k]; push_cast; rfl
    linarith only [hk_eq, hceil_le, hL_gt1]
  -- Bound `m ≤ 3 * L`
  have hm_le : (m : ℝ) ≤ 3 * L := by
    have h2η_le : 2 / η ≤ 4 / α := by
      dsimp only [η]; rw [div_le_div_iff₀ (by positivity) hα0]; linarith only [hα0]
    have hlog_2η : Real.log (2 / η) ≤ L := Real.log_le_log (by positivity) h2η_le
    have h2η_ge1 : 1 ≤ 2 / η := by
      dsimp only [η]; rw [one_le_div (by positivity)]; linarith only [hα1]
    have hceil_le : (Nat.ceil (Real.log (2 / η)) : ℝ) ≤ L + 1 := by
      linarith only [Nat.ceil_lt_add_one (Real.log_nonneg h2η_ge1), hlog_2η]
    have hm_eq : (m : ℝ) = (Nat.ceil (Real.log (2 / η)) : ℝ) + 1 := by
      dsimp only [m]; push_cast; rfl
    linarith only [hm_eq, hceil_le, hL_gt1]
  -- Bound `r ≤ 1e11 * L^3`
  have hr_le : (r : ℝ) ≤ 1e11 * L ^ 3 := by
    have hden_ge : (1 / 320 : ℝ) ^ 2 ≤ (ε₁ / 2) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith only [hε₁_lo]) 2
    have hnum_le : 1600 * (m : ℝ) * (k : ℝ) ^ 2 ≤ 1600 * (3 * L) * (12 * L) ^ 2 := by
      have hk2 : (k : ℝ) ^ 2 ≤ (12 * L) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hk_le 2
      have h1 : 1600 * (m : ℝ) ≤ 1600 * (3 * L) := by linarith only [hm_le]
      exact mul_le_mul h1 hk2 (sq_nonneg _) (by positivity)
    have hfrac_le : 1600 * (m : ℝ) * (k : ℝ) ^ 2 / (ε₁ / 2) ^ 2 ≤ 8e10 * L ^ 3 := by
      have hL3pos : 0 < L ^ 3 := pow_pos hL_pos 3
      calc 1600 * (m : ℝ) * (k : ℝ) ^ 2 / (ε₁ / 2) ^ 2
          ≤ (1600 * (3 * L) * (12 * L) ^ 2) / (1 / 320 : ℝ) ^ 2 :=
            div_le_div₀ (by positivity) hnum_le (by positivity) hden_ge
        _ = 70778880000 * L ^ 3 := by ring
        _ ≤ 8e10 * L ^ 3 := by linarith only [hL3pos]
    have hceil_le : (Nat.ceil (1600 * (m : ℝ) * (k : ℝ) ^ 2 / (ε₁ / 2) ^ 2) : ℝ) ≤ 8e10 * L ^ 3 + 1 := by
      linarith only [Nat.ceil_lt_add_one (show 0 ≤ 1600 * (m : ℝ) * (k : ℝ) ^ 2 / (ε₁ / 2) ^ 2 by positivity), hfrac_le]
    have hr_eq : (r : ℝ) = (Nat.ceil (1600 * (m : ℝ) * (k : ℝ) ^ 2 / (ε₁ / 2) ^ 2) : ℝ) + 1 := by
      dsimp only [r]; push_cast; rfl
    have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL_gt1.le
    linarith only [hr_eq, hceil_le, hL3]
  -- Bound `d' ≤ 2e13 * L^4`
  have hd'_le : (d' : ℝ) ≤ 2e13 * L ^ 4 := by
    have hK_le : K ≤ (4 / α) ^ 7 := by
      dsimp only [K]
      rw [div_pow, div_le_div_iff₀ hα0 (pow_pos hα0 7)]
      have hα6 : α ^ 6 ≤ 1 := pow_le_one₀ hα0.le hα1
      have h1 : (4000 : ℝ) * α ^ 7 = (4000 * α ^ 6) * α := by ring
      have h2 : (4 : ℝ) ^ 7 * α = 16384 * α := by ring
      nlinarith only [hα0, hα6, h1, h2]
    have hlogK : Real.log K ≤ 7 * L := by
      have h := Real.log_le_log (show 0 < K by dsimp only [K]; positivity) hK_le
      rw [Real.log_pow] at h
      simpa [L] using h
    have hlog2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith only [h4α_ge])
    have hlog_prod : Real.log (2 * K ^ r) ≤ 8e11 * L ^ 4 := by
      have hKpos : 0 < K := by dsimp only [K]; positivity
      rw [Real.log_mul (by norm_num) (pow_pos hKpos r).ne', Real.log_pow]
      have hrK : (r : ℝ) * Real.log K ≤ (1e11 * L ^ 3) * (7 * L) :=
        mul_le_mul hr_le hlogK (Real.log_nonneg (by dsimp only [K]; rw [one_le_div hα0]; linarith only [hα1]))
          (by positivity)
      have hL_le4 : L ≤ L ^ 4 := by
        have : L ^ 1 ≤ L ^ 4 := pow_le_pow_right₀ hL_gt1.le (by norm_num)
        simpa using this
      have hprod : (1e11 * L ^ 3) * (7 * L) = 7e11 * L ^ 4 := by ring
      have hL4_nn : 0 ≤ L ^ 4 := by positivity
      linarith only [hlog2, hrK, hL_le4, hprod, hL4_nn]
    have hfl_le : (d' : ℝ) ≤ 16 * (1 + Real.log (2 * K ^ r)) := by
      dsimp only [d']
      have hKge1 : 1 ≤ K := by dsimp only [K]; rw [one_le_div hα0]; linarith only [hα1]
      have hnn : 0 ≤ 16 * (1 + Real.log (2 * K ^ r)) := by
        have h2K : (1 : ℝ) ≤ 2 * K ^ r := by
          have := one_le_pow₀ hKge1 (n := r); linarith only [this]
        linarith only [Real.log_nonneg h2K]
      exact Nat.floor_le hnn
    have hL4 : 1 ≤ L ^ 4 := one_le_pow₀ hL_gt1.le
    linarith only [hfl_le, hlog_prod, hL4]
  exact ⟨hL_gt1, hd'_le, hν_ge⟩

/-- Rearrangement identity for `((1_A * 1_M * 1_L) * μ_T)(0)`. -/
private lemma convR_triple_muR_zero (A_thm M_thm L_thm T : Finset (ZMod P)) :
    convR (convR (convR (indR A_thm) (indR M_thm)) (indR L_thm)) (muR T) 0 =
    ∑ a ∈ A_thm, ∑ l ∈ L_thm, convR (indR M_thm) (muR T) (-(a + l)) := by
  have h1 : convR (convR (convR (indR A_thm) (indR M_thm)) (indR L_thm)) (muR T) 0 =
      convR (convR (indR A_thm) (indR L_thm)) (convR (indR M_thm) (muR T)) 0 := by
    rw [convR_assoc, convR_assoc]
    have hc : convR (indR M_thm) (convR (indR L_thm) (muR T)) =
        convR (indR L_thm) (convR (indR M_thm) (muR T)) := by
      funext z
      rw [← convR_assoc, show convR (indR M_thm) (indR L_thm) = convR (indR L_thm) (indR M_thm)
        from funext (convR_comm _ _), convR_assoc]
    rw [hc, ← convR_assoc]
  rw [h1]
  change ∑ u : ZMod P, (∑ a : ZMod P, (if a ∈ A_thm then (1 : ℝ) else 0) * (if u - a ∈ L_thm then 1 else 0)) *
      convR (indR M_thm) (muR T) (0 - u) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hstep1 : ∀ a : ZMod P,
      ∑ u : ZMod P, (if a ∈ A_thm then (1 : ℝ) else 0) * (if u - a ∈ L_thm then 1 else 0) *
        convR (indR M_thm) (muR T) (0 - u) =
      if a ∈ A_thm then ∑ l ∈ L_thm, convR (indR M_thm) (muR T) (-(a + l)) else 0 := by
    intro a
    by_cases ha : a ∈ A_thm
    · rw [if_pos ha, if_pos ha]
      have hsh : ∑ u : ZMod P, (1 : ℝ) * (if u - a ∈ L_thm then 1 else 0) *
          convR (indR M_thm) (muR T) (0 - u) =
          ∑ l : ZMod P, if l ∈ L_thm then convR (indR M_thm) (muR T) (-(a + l)) else 0 := by
        refine Fintype.sum_equiv (Equiv.subRight a) _ _ fun u => ?_
        simp only [Equiv.subRight_apply]
        have hsub : 0 - u = -(a + (u - a)) := by abel
        by_cases hl : u - a ∈ L_thm <;> simp [hl, hsub]
      rw [hsh, ← Finset.sum_subset (Finset.subset_univ L_thm)]
      · refine Finset.sum_congr rfl fun l hl => by simp [hl]
      · intro l _ hl; simp [hl]
    · simp [ha]
  simp_rw [hstep1]
  rw [← Finset.sum_subset (Finset.subset_univ A_thm)]
  · refine Finset.sum_congr rfl fun a ha => by simp [ha]
  · intro a _ ha; simp [ha]

/-- Radius lower bound combining `ρ₂ ≥ ρ α / (4.8e9 d^2)`, `ν_S ≥ 1 / (200 d)`, and `ap_params_bound`. -/
private lemma ap_radius_lower_bound {d : ℕ} (hd : 1 ≤ d) {ρ ρ₂ α ν_S ε : ℝ}
    (hρ0 : 0 < ρ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hρ₂_lo : ρ * α / (4.8e9 * (d : ℝ) ^ 2) ≤ ρ₂)
    (hνS_lo : 1 / (200 * (d : ℝ)) ≤ ν_S)
    (hεlo : 1 / 40 ≤ ε) (hε1 : ε ≤ 1) :
    let L : ℝ := Real.log (4 / α)
    let ε₁ : ℝ := ε / 4
    let η : ℝ := (77 / 100 : ℝ) * α
    let ν : ℝ := ε₁ * Real.sqrt η
    let K : ℝ := 4000 / α
    let k : ℕ := Nat.ceil (Real.log (2 / ν) / Real.log 2) + 1
    let m : ℕ := Nat.ceil (Real.log (2 / η)) + 1
    let r : ℕ := Nat.ceil (1600 * (m : ℝ) * (k : ℝ) ^ 2 / (ε₁ / 2) ^ 2) + 1
    let d' : ℕ := Nat.floor (16 * (1 + Real.log (2 * K ^ r)))
    ρ * α ^ 2 / (2e34 * (d : ℝ) ^ 5 * L ^ 4) ≤
      (ν_S * ρ₂) * ν / (1000000 * (d : ℝ) ^ 2 * ((3 * d' + 4 : ℕ) : ℝ)) := by
  intro L ε₁ η ν K k m r d'
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.2 (by omega)
  have hpb := ap_params_bound hα0 hα1 hεlo hε1
  have hL_gt1 : 1 < L := hpb.1
  have hL_pos : 0 < L := by linarith only [hL_gt1]
  have hL4_ge1 : 1 ≤ L ^ 4 := one_le_pow₀ hL_gt1.le
  have hd'_le : (d' : ℝ) ≤ 2e13 * L ^ 4 := hpb.2.1
  have hν_ge : (1 / 200 : ℝ) * α ≤ ν := hpb.2.2
  have hνS_pos : 0 < ν_S := lt_of_lt_of_le (by positivity) hνS_lo
  have hρ₂_pos : 0 < ρ₂ := lt_of_lt_of_le (by positivity) hρ₂_lo
  have hν_pos : 0 < ν := lt_of_lt_of_le (by positivity) hν_ge
  have hρS_lo : ρ * α / (1e12 * (d : ℝ) ^ 3) ≤ ν_S * ρ₂ := by
    have hmul := mul_le_mul hνS_lo hρ₂_lo (by positivity) (by positivity)
    have hsimp : (1 / (200 * (d : ℝ))) * (ρ * α / (4.8e9 * (d : ℝ) ^ 2)) =
        ρ * α / (9.6e11 * (d : ℝ) ^ 3) := by field_simp [hd_pos.ne']; ring
    have hd3pos : (0 : ℝ) < (d : ℝ) ^ 3 := pow_pos hd_pos 3
    have hle : ρ * α / (1e12 * (d : ℝ) ^ 3) ≤ ρ * α / (9.6e11 * (d : ℝ) ^ 3) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith only [hd3pos])
    linarith only [hmul, hsimp, hle]
  have hnum_ge : ρ * α ^ 2 / (2e14 * (d : ℝ) ^ 3) ≤ (ν_S * ρ₂) * ν := by
    have hmul := mul_le_mul hρS_lo hν_ge (by positivity) (by positivity)
    have hsimp : (ρ * α / (1e12 * (d : ℝ) ^ 3)) * ((1 / 200 : ℝ) * α) =
        ρ * α ^ 2 / (2e14 * (d : ℝ) ^ 3) := by field_simp [hd_pos.ne']; ring
    linarith only [hmul, hsimp]
  have hden_le : 1000000 * (d : ℝ) ^ 2 * ((3 * d' + 4 : ℕ) : ℝ) ≤
      1e20 * (d : ℝ) ^ 2 * L ^ 4 := by
    have h34 : ((3 * d' + 4 : ℕ) : ℝ) ≤ 1e14 * L ^ 4 := by
      push_cast; linarith only [hd'_le, hL4_ge1]
    have hmul := mul_le_mul_of_nonneg_left h34 (show (0 : ℝ) ≤ 1000000 * (d : ℝ) ^ 2 by positivity)
    have hsimp : 1000000 * (d : ℝ) ^ 2 * (1e14 * L ^ 4) = 1e20 * (d : ℝ) ^ 2 * L ^ 4 := by ring
    linarith only [hmul, hsimp]
  calc ρ * α ^ 2 / (2e34 * (d : ℝ) ^ 5 * L ^ 4)
      = (ρ * α ^ 2 / (2e14 * (d : ℝ) ^ 3)) / (1e20 * (d : ℝ) ^ 2 * L ^ 4) := by
        field_simp [hd_pos.ne', hL_pos.ne']; ring
    _ ≤ ((ν_S * ρ₂) * ν) / (1000000 * (d : ℝ) ^ 2 * ((3 * d' + 4 : ℕ) : ℝ)) :=
        div_le_div₀ (by positivity) hnum_ge (by positivity) hden_le

/-- Case 1 of `density_increment_step`: small sumset `|2 A_Z + 2 A₄| ≤ (1/2) |U₀|`. -/
private lemma density_increment_small_sumset (hP : 5 ≤ P)
    {Γ Γ₂ : Finset (AddChar (ZMod P) ℂ)} (hΓ : Γ.Nonempty) (hΓ₂_card : Γ₂.card = Γ.card)
    {ρ ρ₁ ρ₂ α : ℝ} (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 2) (hρ₁_le : ρ₁ ≤ ρ)
    (hρ₂_pos : 0 < ρ₂) (hρ₂_le_ρ₁ : ρ₂ ≤ ρ₁)
    (hρ₂_lo : ρ * α / (4.8e9 * (Γ.card : ℝ) ^ 2) ≤ ρ₂)
    (hreg_U₁ : IsRegularBohr Γ₂ ρ₂)
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    {A₀ A_Z A₄ : Finset (ZMod P)} (hSol₀ : SolFreeMod A₀)
    (hAZ_sub : A_Z ⊆ A₀) (hAZ_ne : A_Z.Nonempty) (hA₄_ne : A₄.Nonempty)
    (hA₄_sub_U₁ : A₄ ⊆ bohr Γ₂ ρ₂)
    (hAZ_dens : (77 / 100 : ℝ) * α * ((bohr Γ₂ ρ₁).card : ℝ) ≤ (A_Z.card : ℝ))
    (hU₁_le : 2 * ((bohr Γ₂ ρ₂).card : ℝ) ≤ (4000 / α) * (A₄.card : ℝ))
    (hsmall : (((A_Z ×ˢ A₄).image (fun p => 2 * p.1 + 2 * p.2)).card : ℝ) ≤
      (1 / 2 : ℝ) * ((bohr Γ₂ ρ₁).card : ℝ)) :
    let L : ℝ := Real.log (4 / α)
    ∃ (Γ' : Finset (AddChar (ZMod P) ℂ)) (ρ' : ℝ) (A' : Finset (ZMod P)),
      Γ'.Nonempty ∧
      (Γ'.card : ℝ) ≤ (Γ.card : ℝ) + 2e13 * L ^ 4 ∧
      0 < ρ' ∧ ρ' ≤ ρ ∧
      ρ * α ^ 2 / (2e34 * (Γ.card : ℝ) ^ 5 * L ^ 4) ≤ ρ' ∧
      IsRegularBohr Γ' ρ' ∧
      A' ⊆ bohr Γ' ρ' ∧ SolFreeMod A' ∧ A'.Nonempty ∧
      (11 / 10 : ℝ) * α ≤ (A'.card : ℝ) / ((bohr Γ' ρ').card : ℝ) := by
  intro L
  let U₀ := bohr Γ₂ ρ₁
  let U₁ := bohr Γ₂ ρ₂
  let α' : ℝ := (77 / 100 : ℝ) * α
  have hα'_pos : 0 < α' := by dsimp only [α']; positivity
  have hd_pos : (0 : ℝ) < (Γ.card : ℝ) := Nat.cast_pos.2 hΓ.card_pos
  have hd_ge1 : (1 : ℝ) ≤ (Γ.card : ℝ) := Nat.one_le_cast.2 hΓ.card_pos
  have hU₀_pos : (0 : ℝ) < (U₀.card : ℝ) := Nat.cast_pos.2 (bohr_card_pos Γ₂ (hρ₂_pos.trans_le hρ₂_le_ρ₁).le)
  let e2 : ZMod P ≃+ ZMod P := mulEquivZMod 2 (two_ne_zero_zmod hP)
  let S₂₄ : Finset (ZMod P) := (A_Z ×ˢ A₄).image (fun p => 2 * p.1 + 2 * p.2)
  have hS₂₄_ne : S₂₄.Nonempty :=
    ⟨2 * hAZ_ne.choose + 2 * hA₄_ne.choose,
      Finset.mem_image.2 ⟨(hAZ_ne.choose, hA₄_ne.choose),
        Finset.mem_product.2 ⟨hAZ_ne.choose_spec, hA₄_ne.choose_spec⟩, rfl⟩⟩
  let Γ_S : Finset (AddChar (ZMod P) ℂ) :=
    Γ₂.image fun γ => γ.compAddMonoidHom e2.symm.toAddMonoidHom
  have hΓS_card : Γ_S.card = Γ.card := (card_image_freq_addEquiv e2 Γ₂).trans hΓ₂_card
  have hΓS_ne : Γ_S.Nonempty := Finset.card_pos.1 (hΓS_card ▸ hΓ.card_pos)
  have h2U₁_eq : U₁.image e2 = bohr Γ_S ρ₂ := image_bohr_addEquiv e2 Γ₂ ρ₂
  have hreg_2U₁ : IsRegularBohr Γ_S ρ₂ := isRegularBohr_image_addEquiv e2 hreg_U₁
  let ν₀ : ℝ := 1 / (100 * (Γ.card : ℝ))
  obtain ⟨t_S, htS_lo, htS_hi, hreg_S_raw⟩ :=
    exists_regular_bohr Γ_S hΓS_ne (show 0 < ν₀ * ρ₂ by dsimp only [ν₀]; positivity)
  let ν_S : ℝ := t_S * ν₀
  have hνS_lo : 1 / (200 * (Γ.card : ℝ)) ≤ ν_S := by
    dsimp only [ν_S, ν₀]
    calc 1 / (200 * (Γ.card : ℝ)) = (1 / 2) * (1 / (100 * (Γ.card : ℝ))) := by ring
      _ ≤ t_S * (1 / (100 * (Γ.card : ℝ))) := mul_le_mul_of_nonneg_right htS_lo (by positivity)
  have hνS_hi : ν_S ≤ 1 / (100 * (Γ.card : ℝ)) := by
    dsimp only [ν_S, ν₀]
    calc t_S * (1 / (100 * (Γ.card : ℝ))) ≤ 1 * (1 / (100 * (Γ.card : ℝ))) :=
          mul_le_mul_of_nonneg_right htS_hi (by positivity)
      _ = 1 / (100 * (Γ.card : ℝ)) := one_mul _
  have hνS_pos : 0 < ν_S := lt_of_lt_of_le (by positivity) hνS_lo
  have hνS1 : ν_S ≤ 1 := hνS_hi.trans (by rw [div_le_one (by positivity)]; linarith only [hd_ge1])
  let ρ_S : ℝ := ν_S * ρ₂
  have hρS_pos : 0 < ρ_S := by dsimp only [ρ_S]; positivity
  have hρS_le_ρ₂ : ρ_S ≤ ρ₂ := mul_le_of_le_one_left hρ₂_pos.le hνS1
  have hreg_S : IsRegularBohr Γ_S ρ_S := by
    have heq : ρ_S = t_S * (ν₀ * ρ₂) := by dsimp only [ρ_S, ν_S]; ring
    rwa [heq]
  let A_thm : Finset (ZMod P) := A₄.image e2
  let M_thm : Finset (ZMod P) := A_Z.image e2
  let L_thm : Finset (ZMod P) := S₂₄.image (fun z => -z)
  have hA_thm_card : A_thm.card = A₄.card := Finset.card_image_of_injective _ e2.injective
  have hM_thm_card : M_thm.card = A_Z.card := Finset.card_image_of_injective _ e2.injective
  have hL_thm_card : L_thm.card = S₂₄.card := Finset.card_image_of_injective _ neg_injective
  have hAS_bd : ((A_thm.image (fun a => a) ×ˢ bohr Γ_S ρ_S).image (fun p => p.1 + p.2)).card ≤
      (4000 / α) * (A_thm.card : ℝ) := by
    have hsub : (A_thm.image (fun a => a) ×ˢ bohr Γ_S ρ_S).image (fun p => p.1 + p.2) ⊆
        bohr Γ_S ((1 + ν_S) * ρ₂) := by
      intro z hz
      rcases Finset.mem_image.1 hz with ⟨⟨a, s⟩, has, rfl⟩
      have ha : a ∈ A_thm := by simpa using (Finset.mem_product.1 has).1
      have hs : s ∈ bohr Γ_S ρ_S := (Finset.mem_product.1 has).2
      have ha_bohr : a ∈ bohr Γ_S ρ₂ := by
        rw [← h2U₁_eq]
        rcases Finset.mem_image.1 ha with ⟨w, hw, rfl⟩
        exact Finset.mem_image_of_mem e2 (hA₄_sub_U₁ hw)
      have hsum := add_mem_bohr ha_bohr hs
      have heq : ρ₂ + ρ_S = (1 + ν_S) * ρ₂ := by dsimp only [ρ_S]; ring
      rwa [heq] at hsum
    have hreg_up := (hreg_2U₁ ν_S (by rwa [hΓS_card, abs_of_nonneg hνS_pos.le])).2
    rw [hΓS_card, abs_of_nonneg hνS_pos.le] at hreg_up
    have h12 : 1 + 100 * (Γ.card : ℝ) * ν_S ≤ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hνS_hi (show (0 : ℝ) ≤ 100 * (Γ.card : ℝ) by positivity)
      have hsimp : 100 * (Γ.card : ℝ) * (1 / (100 * (Γ.card : ℝ))) = 1 := by field_simp [hd_pos.ne']
      linarith only [hmul, hsimp]
    have h2U₁_card : (bohr Γ_S ρ₂).card = U₁.card := by
      rw [← h2U₁_eq, Finset.card_image_of_injective _ e2.injective]
    calc (((A_thm.image (fun a => a) ×ˢ bohr Γ_S ρ_S).image (fun p => p.1 + p.2)).card : ℝ)
        ≤ ((bohr Γ_S ((1 + ν_S) * ρ₂)).card : ℝ) := Nat.cast_le.2 (Finset.card_le_card hsub)
      _ ≤ (1 + 100 * (Γ.card : ℝ) * ν_S) * ((bohr Γ_S ρ₂).card : ℝ) := hreg_up
      _ ≤ 2 * (U₁.card : ℝ) := by rw [h2U₁_card]; gcongr
      _ ≤ (4000 / α) * (A₄.card : ℝ) := hU₁_le
      _ = (4000 / α) * (A_thm.card : ℝ) := by rw [hA_thm_card]
  have hη_le : α' ≤ (M_thm.card : ℝ) / (L_thm.card : ℝ) := by
    rw [hM_thm_card, hL_thm_card, le_div_iff₀ (Nat.cast_pos.2 hS₂₄_ne.card_pos)]
    have hhalf : (1 / 2 : ℝ) * (U₀.card : ℝ) ≤ (U₀.card : ℝ) := by linarith only [hU₀_pos]
    exact (mul_le_mul_of_nonneg_left (hsmall.trans hhalf) hα'_pos.le).trans hAZ_dens
  have hK_ge1 : (1 : ℝ) ≤ 4000 / α := by rw [one_le_div hα0]; linarith only [hα1]
  obtain ⟨Γ_T, ρ_T, hΓT_ne, hΓT_card, hρT_pos, hρT_le, hρT_ge, hreg_T, hTap⟩ :=
    linfty_ap_bohr (hA₄_ne.image e2) (hAZ_ne.image e2) (hS₂₄_ne.image _)
      hΓS_ne hρS_pos (hρS_le_ρ₂.trans (hρ₂_le_ρ₁.trans (hρ₁_le.trans hρ2))) hreg_S
      hK_ge1 hAS_bd (show (0 : ℝ) < 1 / 10 by norm_num) (by norm_num)
      hα'_pos (by dsimp only [α']; linarith only [hα1]) hη_le
  -- Evaluate at `0`: `1_{2 A₄} * 1_{2 A_Z} * 1_{-S₂₄}(0) = |A₄| * |A_Z|`.
  have hbase0 : convR (convR (indR A_thm) (indR M_thm)) (indR L_thm) 0 =
      (A_thm.card : ℝ) * (M_thm.card : ℝ) := by
    unfold convR indR
    have hterm : ∀ u : ZMod P,
        (∑ y : ZMod P, (if y ∈ A_thm then (1 : ℝ) else 0) * (if u - y ∈ M_thm then 1 else 0)) *
          (if 0 - u ∈ L_thm then 1 else 0) =
        ∑ y : ZMod P, (if y ∈ A_thm then (1 : ℝ) else 0) * (if u - y ∈ M_thm then 1 else 0) := by
      intro u
      by_cases hu : 0 - u ∈ L_thm
      · rw [if_pos hu, mul_one]
      · rw [if_neg hu, mul_zero]; symm
        refine Finset.sum_eq_zero fun y _ => ?_
        by_cases hy : y ∈ A_thm
        · by_cases huy : u - y ∈ M_thm
          · exfalso; apply hu
            rcases Finset.mem_image.1 hy with ⟨w, hw, rfl⟩
            rcases Finset.mem_image.1 huy with ⟨z, hz, hz_eq⟩
            refine Finset.mem_image.2 ⟨2 * z + 2 * w,
              Finset.mem_image.2 ⟨(z, w), Finset.mem_product.2 ⟨hz, hw⟩, rfl⟩, ?_⟩
            have hu_eq : u = e2 z + e2 w := by rw [hz_eq]; abel
            change u = 2 * z + 2 * w at hu_eq
            rw [hu_eq]; ring
          · simp [huy]
        · simp [hy]
    simp_rw [hterm]
    rw [Finset.sum_comm]
    have hinner : ∀ y : ZMod P,
        ∑ u : ZMod P, (if y ∈ A_thm then (1 : ℝ) else 0) * (if u - y ∈ M_thm then 1 else 0) =
        (if y ∈ A_thm then (1 : ℝ) else 0) * (M_thm.card : ℝ) := by
      intro y
      rw [← Finset.mul_sum]; congr 1
      exact (Fintype.sum_equiv (Equiv.subRight y) _ (fun z => indR M_thm z) (fun _ => rfl)).trans
        (sum_indR M_thm)
    simp_rw [hinner, ← Finset.sum_mul]
    exact congrArg (· * (M_thm.card : ℝ)) (sum_indR A_thm)
  have hap0 := (abs_le.1 (hTap 0)).1
  rw [hbase0] at hap0
  have hge0 : (9 / 10 : ℝ) * (A_thm.card : ℝ) * (M_thm.card : ℝ) ≤
      convR (convR (convR (indR A_thm) (indR M_thm)) (indR L_thm)) (muR (bohr Γ_T ρ_T)) 0 := by
    linarith only [hap0]
  have hrearr := convR_triple_muR_zero A_thm M_thm L_thm (bohr Γ_T ρ_T)
  have hex_x : ∃ x : ZMod P, (11 / 10 : ℝ) * α ≤ convR (indR M_thm) (muR (bohr Γ_T ρ_T)) x := by
    by_contra hall
    push Not at hall
    have hbound : ∑ a ∈ A_thm, ∑ l ∈ L_thm,
        convR (indR M_thm) (muR (bohr Γ_T ρ_T)) (-(a + l)) <
        (A_thm.card : ℝ) * (L_thm.card : ℝ) * ((11 / 10 : ℝ) * α) := by
      have hlt : ∑ a ∈ A_thm, ∑ l ∈ L_thm,
          convR (indR M_thm) (muR (bohr Γ_T ρ_T)) (-(a + l)) <
          ∑ _a ∈ A_thm, ∑ _l ∈ L_thm, ((11 / 10 : ℝ) * α) :=
        Finset.sum_lt_sum_of_nonempty (hA₄_ne.image e2) fun a _ =>
          Finset.sum_lt_sum_of_nonempty (hS₂₄_ne.image _) fun l _ => hall _
      simpa [Finset.sum_const, nsmul_eq_mul, mul_assoc] using hlt
    rw [← hrearr] at hbound
    have hcmp : (A_thm.card : ℝ) * (L_thm.card : ℝ) * ((11 / 10 : ℝ) * α) ≤
        (9 / 10 : ℝ) * (A_thm.card : ℝ) * (M_thm.card : ℝ) := by
      rw [hL_thm_card, hM_thm_card]
      have hαU_pos : 0 < α * (U₀.card : ℝ) := mul_pos hα0 hU₀_pos
      have h1 : (S₂₄.card : ℝ) * ((11 / 10 : ℝ) * α) ≤ (9 / 10 : ℝ) * (A_Z.card : ℝ) := by
        calc (S₂₄.card : ℝ) * ((11 / 10 : ℝ) * α)
            ≤ ((1 / 2 : ℝ) * (U₀.card : ℝ)) * ((11 / 10 : ℝ) * α) :=
              mul_le_mul_of_nonneg_right hsmall (by positivity)
          _ = (55 / 100 : ℝ) * (α * (U₀.card : ℝ)) := by ring
          _ ≤ (693 / 1000 : ℝ) * (α * (U₀.card : ℝ)) := by linarith only [hαU_pos]
          _ = (9 / 10 : ℝ) * (α' * (U₀.card : ℝ)) := by dsimp only [α']; ring
          _ ≤ (9 / 10 : ℝ) * (A_Z.card : ℝ) := mul_le_mul_of_nonneg_left hAZ_dens (by norm_num)
      have hmul := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg A_thm.card)
      linarith only [hmul]
    linarith only [hge0, hbound, hcmp]
  obtain ⟨x_hit, hx_hit⟩ := hex_x
  -- Pull `bohr Γ_T ρ_T` back by `e2.symm` (`2⁻¹ • T`)!
  let Γ_out : Finset (AddChar (ZMod P) ℂ) :=
    Γ_T.image fun γ => γ.compAddMonoidHom e2.toAddMonoidHom
  have hΓ_out_card : Γ_out.card = Γ_T.card := card_image_freq_addEquiv e2.symm Γ_T
  have hΓ_out_ne : Γ_out.Nonempty := Finset.card_pos.1 (hΓ_out_card ▸ hΓT_ne.card_pos)
  have hreg_out : IsRegularBohr Γ_out ρ_T := isRegularBohr_image_addEquiv e2.symm hreg_T
  have hT_eq : (bohr Γ_out ρ_T).image e2 = bohr Γ_T ρ_T := by
    have h1 : (bohr Γ_T ρ_T).image e2.symm = bohr Γ_out ρ_T := image_bohr_addEquiv e2.symm Γ_T ρ_T
    rw [← h1, Finset.image_image]
    have hid : (e2 ∘ e2.symm) = id := funext e2.apply_symm_apply
    simp [hid]
  rw [← hT_eq, convR_indR_muR_image_addEquiv e2 A_Z (bohr Γ_out ρ_T) x_hit,
    convR_indR_muR_eq_density_translate A_Z (bohr Γ_out ρ_T) (fun _ hw => neg_mem_bohr hw)] at hx_hit
  let A' : Finset (ZMod P) := A_Z.image (fun a => a - e2.symm x_hit) ∩ bohr Γ_out ρ_T
  change (11 / 10 : ℝ) * α ≤ (A'.card : ℝ) / ((bohr Γ_out ρ_T).card : ℝ) at hx_hit
  have hA'ne : A'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he; rw [he, Finset.card_empty, Nat.cast_zero, zero_div] at hx_hit; linarith only [hα0, hx_hit]
  have hpb := ap_params_bound hα0 hα1 (show (1 / 40 : ℝ) ≤ 1 / 10 by norm_num) (by norm_num)
  have hcard_le : (Γ_out.card : ℝ) ≤ (Γ.card : ℝ) + 2e13 * L ^ 4 := by
    rw [hΓ_out_card]
    have h1 : (Γ_T.card : ℝ) ≤ (Γ.card : ℝ) +
        ((Nat.floor (16 * (1 + Real.log (2 * (4000 / α) ^
          (Nat.ceil (1600 * ((Nat.ceil (Real.log (2 / α')) + 1 : ℕ) : ℝ) *
            ((Nat.ceil (Real.log (2 / ((1 / 10 / 4 : ℝ) * Real.sqrt α')) / Real.log 2) + 1 : ℕ) : ℝ) ^ 2 /
            ((1 / 10 / 4 : ℝ) / 2) ^ 2) + 1)))) : ℕ) : ℝ) := by
      rw [← hΓS_card]; exact_mod_cast hΓT_card
    linarith only [h1, hpb.2.1]
  have hrad_ge := ap_radius_lower_bound hΓ.card_pos hρ0 hα0 hα1 hρ₂_lo hνS_lo
    (show (1 / 40 : ℝ) ≤ 1 / 10 by norm_num) (by norm_num)
  rw [hΓS_card] at hρT_ge
  refine ⟨Γ_out, ρ_T, A', hΓ_out_ne, hcard_le, hρT_pos,
    hρT_le.trans (hρS_le_ρ₂.trans (hρ₂_le_ρ₁.trans hρ₁_le)), hrad_ge.trans hρT_ge, hreg_out,
    Finset.inter_subset_right,
    solFreeMod_subset Finset.inter_subset_left
      (solFreeMod_translate (solFreeMod_subset hAZ_sub hSol₀) _),
    hA'ne, hx_hit⟩

/-- Case 2 of `density_increment_step`: large sumset `|2 A_Z + 2 A₄| > (1/2) |U₀|`. -/
private lemma density_increment_large_sumset (hP : 5 ≤ P)
    {Γ Γ₂ : Finset (AddChar (ZMod P) ℂ)} (hΓ : Γ.Nonempty) (hΓ₂_card : Γ₂.card = Γ.card)
    {ρ ρ₁ ρ₂ δ₂ α : ℝ} (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 2) (hρ₁_le : ρ₁ ≤ ρ)
    (hρ₂_pos : 0 < ρ₂) (hρ₂_le_ρ₁ : ρ₂ ≤ ρ₁)
    (hρ₂_lo : ρ * α / (4.8e9 * (Γ.card : ℝ) ^ 2) ≤ ρ₂)
    (hδ₂_pos : 0 < δ₂) (hδ₂_hi : δ₂ ≤ 1 / (30000 * (Γ.card : ℝ))) (hρ₂_def : ρ₂ = δ₂ * ρ₁)
    (hreg_U₀ : IsRegularBohr Γ₂ ρ₁) (hreg_U₁ : IsRegularBohr Γ₂ ρ₂)
    (hU₀_eq : (bohr Γ ρ₁).image (mulEquivZMod 2 (two_ne_zero_zmod hP)) = bohr Γ₂ ρ₁)
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    {A₀ A_Z A_X A₁ A₄ : Finset (ZMod P)} (hSol₀ : SolFreeMod A₀)
    (hAZ_sub_A₀ : A_Z ⊆ A₀) (hAZ_sub_B' : A_Z ⊆ bohr Γ ρ₁)
    (hAX_sub_A₀ : A_X ⊆ A₀) (hAX_sub_U₀ : A_X ⊆ bohr Γ₂ ρ₁)
    (hA₁_sub_A₀ : A₁ ⊆ A₀) (hA₁_sub_U₁ : A₁ ⊆ bohr Γ₂ ρ₂)
    (hA₄_sub_A₀ : A₄ ⊆ A₀) (hA₄_sub_U₁ : A₄ ⊆ bohr Γ₂ ρ₂)
    (hA₁_A₄_disj : Disjoint A₁ A₄)
    (hAX_ne : A_X.Nonempty) (hA₁_ne : A₁.Nonempty) (hA₄_ne : A₄.Nonempty)
    (hA₄_le_AX : (A₄.card : ℝ) ≤ (1 / 500 : ℝ) * (A_X.card : ℝ))
    (hAX_dens : (77 / 100 : ℝ) * α * ((bohr Γ₂ ρ₁).card : ℝ) ≤ (A_X.card : ℝ))
    (hU₁_le : 2 * ((bohr Γ₂ ρ₂).card : ℝ) ≤ (4000 / α) * (A₁.card : ℝ))
    (hlarge : (1 / 2 : ℝ) * ((bohr Γ₂ ρ₁).card : ℝ) <
      (((A_Z ×ˢ A₄).image (fun p => 2 * p.1 + 2 * p.2)).card : ℝ)) :
    let L : ℝ := Real.log (4 / α)
    ∃ (Γ' : Finset (AddChar (ZMod P) ℂ)) (ρ' : ℝ) (A' : Finset (ZMod P)),
      Γ'.Nonempty ∧
      (Γ'.card : ℝ) ≤ (Γ.card : ℝ) + 2e13 * L ^ 4 ∧
      0 < ρ' ∧ ρ' ≤ ρ ∧
      ρ * α ^ 2 / (2e34 * (Γ.card : ℝ) ^ 5 * L ^ 4) ≤ ρ' ∧
      IsRegularBohr Γ' ρ' ∧
      A' ⊆ bohr Γ' ρ' ∧ SolFreeMod A' ∧ A'.Nonempty ∧
      (11 / 10 : ℝ) * α ≤ (A'.card : ℝ) / ((bohr Γ' ρ').card : ℝ) := by
  intro L
  let U₀ := bohr Γ₂ ρ₁
  let U₁ := bohr Γ₂ ρ₂
  let α' : ℝ := (77 / 100 : ℝ) * α
  have hα'_pos : 0 < α' := by dsimp only [α']; positivity
  have hd_pos : (0 : ℝ) < (Γ.card : ℝ) := Nat.cast_pos.2 hΓ.card_pos
  have hd_ge1 : (1 : ℝ) ≤ (Γ.card : ℝ) := Nat.one_le_cast.2 hΓ.card_pos
  have hρ₁_pos : 0 < ρ₁ := hρ₂_pos.trans_le hρ₂_le_ρ₁
  have hU₀_pos : (0 : ℝ) < (U₀.card : ℝ) := Nat.cast_pos.2 (bohr_card_pos Γ₂ hρ₁_pos.le)
  let e3 : ZMod P ≃+ ZMod P := mulEquivZMod 3 (three_ne_zero_zmod hP)
  let S₂₄ : Finset (ZMod P) := (A_Z ×ˢ A₄).image (fun p => 2 * p.1 + 2 * p.2)
  let U : Finset (ZMod P) := bohr Γ₂ ((1 + 3 * δ₂) * ρ₁)
  have h3δ₂_le : 3 * δ₂ ≤ 1 / (100 * (Γ.card : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hδ₂_hi (show (0 : ℝ) ≤ 3 by norm_num)
    have h1 : 3 * (1 / (30000 * (Γ.card : ℝ))) = 1 / (10000 * (Γ.card : ℝ)) := by
      field_simp [hd_pos.ne']; ring
    have h2 : 1 / (10000 * (Γ.card : ℝ)) ≤ 1 / (100 * (Γ.card : ℝ)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith only [hd_pos])
    linarith only [hmul, h1, h2]
  have hU_card : (U.card : ℝ) ≤ (101 / 100 : ℝ) * (U₀.card : ℝ) := by
    have hreg_up := (hreg_U₀ (3 * δ₂) (by rwa [hΓ₂_card, abs_of_nonneg (by positivity)])).2
    rw [hΓ₂_card, abs_of_nonneg (by positivity)] at hreg_up
    have h101 : 1 + 100 * (Γ.card : ℝ) * (3 * δ₂) ≤ 101 / 100 := by
      have hmul := mul_le_mul_of_nonneg_left hδ₂_hi (show (0 : ℝ) ≤ 300 * (Γ.card : ℝ) by positivity)
      have hsimp : 300 * (Γ.card : ℝ) * (1 / (30000 * (Γ.card : ℝ))) = 1 / 100 := by
        field_simp [hd_pos.ne']; ring
      linarith only [hmul, hsimp]
    exact hreg_up.trans (mul_le_mul_of_nonneg_right h101 hU₀_pos.le)
  have hS₂₄_sub_U : S₂₄ ⊆ U := by
    intro s hs
    rcases Finset.mem_image.1 hs with ⟨⟨z, w⟩, hzw, rfl⟩
    have hz_U₀ : 2 * z ∈ U₀ := by
      dsimp only [U₀]; rw [← hU₀_eq]
      exact Finset.mem_image.2 ⟨z, hAZ_sub_B' (Finset.mem_product.1 hzw).1, rfl⟩
    have hw_U₁ : w ∈ U₁ := hA₄_sub_U₁ (Finset.mem_product.1 hzw).2
    have h2w : 2 * w ∈ bohr Γ₂ (2 * ρ₂) := by
      have h2 := nsmul_mem_bohr hρ₂_pos.le hw_U₁ 2
      simpa [two_nsmul, two_mul] using h2
    have hadd := add_mem_bohr hz_U₀ h2w
    refine bohr_mono_radius Γ₂ ?_ hadd
    rw [hρ₂_def]; have hmul : 0 < δ₂ * ρ₁ := mul_pos hδ₂_pos hρ₁_pos; linarith only [hmul]
  let L_thm : Finset (ZMod P) := U \ S₂₄
  have hL_card_le : (L_thm.card : ℝ) ≤ (51 / 100 : ℝ) * (U₀.card : ℝ) := by
    have h1 : L_thm.card + S₂₄.card = U.card := Finset.card_sdiff_add_card_eq_card hS₂₄_sub_U
    have h2 : (L_thm.card : ℝ) + (S₂₄.card : ℝ) = (U.card : ℝ) := by exact_mod_cast h1
    linarith only [h2, hU_card, hlarge]
  let A_thm : Finset (ZMod P) := A₁.image (fun y => -(3 * y))
  let M_thm : Finset (ZMod P) := A_X.image (fun x => -x)
  have hneg3_inj : Function.Injective (fun y : ZMod P => -(3 * y)) := fun a b hab =>
    mul_left_cancel₀ (three_ne_zero_zmod hP) (neg_injective hab)
  have hA_thm_card : A_thm.card = A₁.card := Finset.card_image_of_injective _ hneg3_inj
  have hM_thm_card : M_thm.card = A_X.card := Finset.card_image_of_injective _ neg_injective
  -- Evaluate `1_{-3 A₁} * 1_{-A_X} * 1_U(0) = |A₁| * |A_X|`.
  have hbaseU : convR (convR (indR A_thm) (indR M_thm)) (indR U) 0 =
      (A_thm.card : ℝ) * (M_thm.card : ℝ) := by
    unfold convR indR
    have hterm : ∀ u : ZMod P,
        (∑ y : ZMod P, (if y ∈ A_thm then (1 : ℝ) else 0) * (if u - y ∈ M_thm then 1 else 0)) *
          (if 0 - u ∈ U then 1 else 0) =
        ∑ y : ZMod P, (if y ∈ A_thm then (1 : ℝ) else 0) * (if u - y ∈ M_thm then 1 else 0) := by
      intro u
      by_cases hu : 0 - u ∈ U
      · rw [if_pos hu, mul_one]
      · rw [if_neg hu, mul_zero]; symm
        refine Finset.sum_eq_zero fun y _ => ?_
        by_cases hy : y ∈ A_thm
        · by_cases huy : u - y ∈ M_thm
          · exfalso; apply hu
            rcases Finset.mem_image.1 hy with ⟨y', hy', rfl⟩
            rcases Finset.mem_image.1 huy with ⟨x', hx', hx'_eq⟩
            have hu_eq : 0 - u = x' + 3 * y' := by
              have : u = -x' + -(3 * y') := by rw [hx'_eq]; abel
              rw [this]; ring
            rw [hu_eq]
            have h3y : 3 * y' ∈ bohr Γ₂ (3 * ρ₂) := by
              have h3 := nsmul_mem_bohr hρ₂_pos.le (hA₁_sub_U₁ hy') 3
              have heq : (3 : ℕ) • y' = 3 * y' := by simp [nsmul_eq_mul]
              simpa [heq] using h3
            have hadd := add_mem_bohr (hAX_sub_U₀ hx') h3y
            have heq2 : ρ₁ + 3 * ρ₂ = (1 + 3 * δ₂) * ρ₁ := by rw [hρ₂_def]; ring
            rwa [heq2] at hadd
          · simp [huy]
        · simp [hy]
    simp_rw [hterm]
    rw [Finset.sum_comm]
    have hinner : ∀ y : ZMod P,
        ∑ u : ZMod P, (if y ∈ A_thm then (1 : ℝ) else 0) * (if u - y ∈ M_thm then 1 else 0) =
        (if y ∈ A_thm then (1 : ℝ) else 0) * (M_thm.card : ℝ) := by
      intro y
      rw [← Finset.mul_sum]; congr 1
      exact (Fintype.sum_equiv (Equiv.subRight y) _ (fun z => indR M_thm z) (fun _ => rfl)).trans
        (sum_indR M_thm)
    simp_rw [hinner, ← Finset.sum_mul]
    exact congrArg (· * (M_thm.card : ℝ)) (sum_indR A_thm)
  -- Combine with `distinct_collision_count`: `1_{-3 A₁} * 1_{-A_X} * 1_{L_thm}(0) ≥ (99/100) |A₁| |A_X|`.
  have hL_ge0 : (99 / 100 : ℝ) * (A_thm.card : ℝ) * (M_thm.card : ℝ) ≤
      convR (convR (indR A_thm) (indR M_thm)) (indR L_thm) 0 := by
    have hind_split : ∀ z : ZMod P, indR L_thm z = indR U z - indR S₂₄ z := by
      intro z; unfold indR; dsimp only [L_thm]
      by_cases h1 : z ∈ U <;> by_cases h2 : z ∈ S₂₄
      · simp [h1, h2]
      · simp [h1, h2]
      · exact absurd (hS₂₄_sub_U h2) h1
      · simp [h1, h2]
    have hconv_split : convR (convR (indR A_thm) (indR M_thm)) (indR L_thm) 0 =
        convR (convR (indR A_thm) (indR M_thm)) (indR U) 0 -
        convR (convR (indR A_thm) (indR M_thm)) (indR S₂₄) 0 := by
      rw [show indR L_thm = fun z => indR U z - indR S₂₄ z from funext hind_split, convR_sub_right]
    have hcoll := distinct_collision_count hP hSol₀ hAX_sub_A₀ hAZ_sub_A₀
      hA₁_sub_A₀ hA₄_sub_A₀ hA₁_A₄_disj hA₄_ne.card_pos
    have hcoll2 : 5 * (A₁.card : ℝ) * (A₄.card : ℝ) ≤ (1 / 100 : ℝ) * (A_thm.card : ℝ) * (M_thm.card : ℝ) := by
      rw [hA_thm_card, hM_thm_card]
      have hmul := mul_le_mul_of_nonneg_left hA₄_le_AX (show (0 : ℝ) ≤ 5 * (A₁.card : ℝ) by positivity)
      linarith only [hmul]
    rw [hconv_split, hbaseU]
    linarith only [hcoll, hcoll2]
  have hL_ne : L_thm.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hLe
    have hzero : convR (convR (indR A_thm) (indR M_thm)) (indR L_thm) 0 = 0 := by
      simp [hLe, convR, indR]
    rw [hzero] at hL_ge0
    have hpos : (0 : ℝ) < (99 / 100 : ℝ) * (A_thm.card : ℝ) * (M_thm.card : ℝ) := by
      rw [hA_thm_card, hM_thm_card]
      have h1 : (0 : ℝ) < (A₁.card : ℝ) := Nat.cast_pos.2 hA₁_ne.card_pos
      have h2 : (0 : ℝ) < (A_X.card : ℝ) := Nat.cast_pos.2 hAX_ne.card_pos
      positivity
    linarith only [hL_ge0, hpos]
  -- Construct regular Bohr set `S = (3 • U₁)_{ν_S}` and apply `linfty_ap_bohr` with `ε = 1/40`.
  let Γ_S : Finset (AddChar (ZMod P) ℂ) :=
    Γ₂.image fun γ => γ.compAddMonoidHom e3.symm.toAddMonoidHom
  have hΓS_card : Γ_S.card = Γ.card := (card_image_freq_addEquiv e3 Γ₂).trans hΓ₂_card
  have hΓS_ne : Γ_S.Nonempty := Finset.card_pos.1 (hΓS_card ▸ hΓ.card_pos)
  have h3U₁_eq : U₁.image e3 = bohr Γ_S ρ₂ := image_bohr_addEquiv e3 Γ₂ ρ₂
  have hreg_3U₁ : IsRegularBohr Γ_S ρ₂ := isRegularBohr_image_addEquiv e3 hreg_U₁
  let ν₀ : ℝ := 1 / (100 * (Γ.card : ℝ))
  obtain ⟨t_S, htS_lo, htS_hi, hreg_S_raw⟩ :=
    exists_regular_bohr Γ_S hΓS_ne (show 0 < ν₀ * ρ₂ by dsimp only [ν₀]; positivity)
  let ν_S : ℝ := t_S * ν₀
  have hνS_lo : 1 / (200 * (Γ.card : ℝ)) ≤ ν_S := by
    dsimp only [ν_S, ν₀]
    calc 1 / (200 * (Γ.card : ℝ)) = (1 / 2) * (1 / (100 * (Γ.card : ℝ))) := by ring
      _ ≤ t_S * (1 / (100 * (Γ.card : ℝ))) := mul_le_mul_of_nonneg_right htS_lo (by positivity)
  have hνS_hi : ν_S ≤ 1 / (100 * (Γ.card : ℝ)) := by
    dsimp only [ν_S, ν₀]
    calc t_S * (1 / (100 * (Γ.card : ℝ))) ≤ 1 * (1 / (100 * (Γ.card : ℝ))) :=
          mul_le_mul_of_nonneg_right htS_hi (by positivity)
      _ = 1 / (100 * (Γ.card : ℝ)) := one_mul _
  have hνS_pos : 0 < ν_S := lt_of_lt_of_le (by positivity) hνS_lo
  have hνS1 : ν_S ≤ 1 := hνS_hi.trans (by rw [div_le_one (by positivity)]; linarith only [hd_ge1])
  let ρ_S : ℝ := ν_S * ρ₂
  have hρS_pos : 0 < ρ_S := by dsimp only [ρ_S]; positivity
  have hρS_le_ρ₂ : ρ_S ≤ ρ₂ := mul_le_of_le_one_left hρ₂_pos.le hνS1
  have hreg_S : IsRegularBohr Γ_S ρ_S := by
    have heq : ρ_S = t_S * (ν₀ * ρ₂) := by dsimp only [ρ_S, ν_S]; ring
    rwa [heq]
  have hAS_bd : ((A_thm.image (fun a => a) ×ˢ bohr Γ_S ρ_S).image (fun p => p.1 + p.2)).card ≤
      (4000 / α) * (A_thm.card : ℝ) := by
    have hsub : (A_thm.image (fun a => a) ×ˢ bohr Γ_S ρ_S).image (fun p => p.1 + p.2) ⊆
        bohr Γ_S ((1 + ν_S) * ρ₂) := by
      intro z hz
      rcases Finset.mem_image.1 hz with ⟨⟨a, s⟩, has, rfl⟩
      have ha : a ∈ A_thm := by simpa using (Finset.mem_product.1 has).1
      have hs : s ∈ bohr Γ_S ρ_S := (Finset.mem_product.1 has).2
      have ha_bohr : a ∈ bohr Γ_S ρ₂ := by
        rcases Finset.mem_image.1 ha with ⟨y', hy', rfl⟩
        have hy_3U₁ : e3 y' ∈ bohr Γ_S ρ₂ := by
          rw [← h3U₁_eq]
          exact Finset.mem_image_of_mem e3 (hA₁_sub_U₁ hy')
        exact neg_mem_bohr hy_3U₁
      have hsum := add_mem_bohr ha_bohr hs
      have heq : ρ₂ + ρ_S = (1 + ν_S) * ρ₂ := by dsimp only [ρ_S]; ring
      rwa [heq] at hsum
    have hreg_up := (hreg_3U₁ ν_S (by rwa [hΓS_card, abs_of_nonneg hνS_pos.le])).2
    rw [hΓS_card, abs_of_nonneg hνS_pos.le] at hreg_up
    have h12 : 1 + 100 * (Γ.card : ℝ) * ν_S ≤ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hνS_hi (show (0 : ℝ) ≤ 100 * (Γ.card : ℝ) by positivity)
      have hsimp : 100 * (Γ.card : ℝ) * (1 / (100 * (Γ.card : ℝ))) = 1 := by field_simp [hd_pos.ne']
      linarith only [hmul, hsimp]
    have h3U₁_card : (bohr Γ_S ρ₂).card = U₁.card := by
      rw [← h3U₁_eq, Finset.card_image_of_injective _ e3.injective]
    calc (((A_thm.image (fun a => a) ×ˢ bohr Γ_S ρ_S).image (fun p => p.1 + p.2)).card : ℝ)
        ≤ ((bohr Γ_S ((1 + ν_S) * ρ₂)).card : ℝ) := Nat.cast_le.2 (Finset.card_le_card hsub)
      _ ≤ (1 + 100 * (Γ.card : ℝ) * ν_S) * ((bohr Γ_S ρ₂).card : ℝ) := hreg_up
      _ ≤ 2 * (U₁.card : ℝ) := by rw [h3U₁_card]; gcongr
      _ ≤ (4000 / α) * (A₁.card : ℝ) := hU₁_le
      _ = (4000 / α) * (A_thm.card : ℝ) := by rw [hA_thm_card]
  have hη_le : α' ≤ (M_thm.card : ℝ) / (L_thm.card : ℝ) := by
    rw [hM_thm_card, le_div_iff₀ (Nat.cast_pos.2 hL_ne.card_pos)]
    have h51 : (51 / 100 : ℝ) * (U₀.card : ℝ) ≤ (U₀.card : ℝ) := by linarith only [hU₀_pos]
    exact (mul_le_mul_of_nonneg_left (hL_card_le.trans h51) hα'_pos.le).trans hAX_dens
  have hK_ge1 : (1 : ℝ) ≤ 4000 / α := by rw [one_le_div hα0]; linarith only [hα1]
  obtain ⟨Γ_T, ρ_T, hΓT_ne, hΓT_card, hρT_pos, hρT_le, hρT_ge, hreg_T, hTap⟩ :=
    linfty_ap_bohr (hA₁_ne.image _) (hAX_ne.image _) hL_ne
      hΓS_ne hρS_pos (hρS_le_ρ₂.trans (hρ₂_le_ρ₁.trans (hρ₁_le.trans hρ2))) hreg_S
      hK_ge1 hAS_bd (show (0 : ℝ) < 1 / 40 by norm_num) (by norm_num)
      hα'_pos (by dsimp only [α']; linarith only [hα1]) hη_le
  have hap0 := (abs_le.1 (hTap 0)).1
  have hge0 : (965 / 1000 : ℝ) * (A_thm.card : ℝ) * (M_thm.card : ℝ) ≤
      convR (convR (convR (indR A_thm) (indR M_thm)) (indR L_thm)) (muR (bohr Γ_T ρ_T)) 0 := by
    linarith only [hap0, hL_ge0]
  have hrearr := convR_triple_muR_zero A_thm M_thm L_thm (bohr Γ_T ρ_T)
  have hex_x : ∃ x : ZMod P, (11 / 10 : ℝ) * α ≤ convR (indR M_thm) (muR (bohr Γ_T ρ_T)) x := by
    by_contra hall
    push Not at hall
    have hbound : ∑ a ∈ A_thm, ∑ l ∈ L_thm,
        convR (indR M_thm) (muR (bohr Γ_T ρ_T)) (-(a + l)) <
        (A_thm.card : ℝ) * (L_thm.card : ℝ) * ((11 / 10 : ℝ) * α) := by
      have hlt : ∑ a ∈ A_thm, ∑ l ∈ L_thm,
          convR (indR M_thm) (muR (bohr Γ_T ρ_T)) (-(a + l)) <
          ∑ _a ∈ A_thm, ∑ _l ∈ L_thm, ((11 / 10 : ℝ) * α) :=
        Finset.sum_lt_sum_of_nonempty (hA₁_ne.image _) fun a _ =>
          Finset.sum_lt_sum_of_nonempty hL_ne fun l _ => hall _
      simpa [Finset.sum_const, nsmul_eq_mul, mul_assoc] using hlt
    rw [← hrearr] at hbound
    have hcmp : (A_thm.card : ℝ) * (L_thm.card : ℝ) * ((11 / 10 : ℝ) * α) ≤
        (965 / 1000 : ℝ) * (A_thm.card : ℝ) * (M_thm.card : ℝ) := by
      rw [hM_thm_card]
      have hαU_pos : 0 < α * (U₀.card : ℝ) := mul_pos hα0 hU₀_pos
      have h1 : (L_thm.card : ℝ) * ((11 / 10 : ℝ) * α) ≤ (965 / 1000 : ℝ) * (A_X.card : ℝ) := by
        calc (L_thm.card : ℝ) * ((11 / 10 : ℝ) * α)
            ≤ ((51 / 100 : ℝ) * (U₀.card : ℝ)) * ((11 / 10 : ℝ) * α) :=
              mul_le_mul_of_nonneg_right hL_card_le (by positivity)
          _ = (561 / 1000 : ℝ) * (α * (U₀.card : ℝ)) := by ring
          _ ≤ (74305 / 100000 : ℝ) * (α * (U₀.card : ℝ)) := by linarith only [hαU_pos]
          _ = (965 / 1000 : ℝ) * (α' * (U₀.card : ℝ)) := by dsimp only [α']; ring
          _ ≤ (965 / 1000 : ℝ) * (A_X.card : ℝ) := mul_le_mul_of_nonneg_left hAX_dens (by norm_num)
      have hmul := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg A_thm.card)
      linarith only [hmul]
    linarith only [hge0, hbound, hcmp]
  obtain ⟨x_hit, hx_hit⟩ := hex_x
  -- Symmetry: `(bohr Γ_T ρ_T).image negEquivZMod = bohr Γ_T ρ_T`.
  have hT_neg : (bohr Γ_T ρ_T).image negEquivZMod = bohr Γ_T ρ_T := by
    ext y; simp only [Finset.mem_image, negEquivZMod, AddEquiv.coe_mk, Equiv.coe_fn_mk]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact neg_mem_bohr hw
    · intro hy; exact ⟨-y, neg_mem_bohr hy, neg_neg y⟩
  have hM_neg : M_thm = A_X.image negEquivZMod := rfl
  rw [hM_neg, ← hT_neg, convR_indR_muR_image_addEquiv negEquivZMod A_X (bohr Γ_T ρ_T) x_hit,
    convR_indR_muR_eq_density_translate A_X (bohr Γ_T ρ_T) (fun _ hw => neg_mem_bohr hw)] at hx_hit
  let A' : Finset (ZMod P) := A_X.image (fun a => a - negEquivZMod.symm x_hit) ∩ bohr Γ_T ρ_T
  change (11 / 10 : ℝ) * α ≤ (A'.card : ℝ) / ((bohr Γ_T ρ_T).card : ℝ) at hx_hit
  have hA'ne : A'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he; rw [he, Finset.card_empty, Nat.cast_zero, zero_div] at hx_hit; linarith only [hα0, hx_hit]
  have hpb := ap_params_bound hα0 hα1 (show (1 / 40 : ℝ) ≤ 1 / 40 by norm_num) (by norm_num)
  have hcard_le : (Γ_T.card : ℝ) ≤ (Γ.card : ℝ) + 2e13 * L ^ 4 := by
    have h1 : (Γ_T.card : ℝ) ≤ (Γ.card : ℝ) +
        ((Nat.floor (16 * (1 + Real.log (2 * (4000 / α) ^
          (Nat.ceil (1600 * ((Nat.ceil (Real.log (2 / α')) + 1 : ℕ) : ℝ) *
            ((Nat.ceil (Real.log (2 / ((1 / 40 / 4 : ℝ) * Real.sqrt α')) / Real.log 2) + 1 : ℕ) : ℝ) ^ 2 /
            ((1 / 40 / 4 : ℝ) / 2) ^ 2) + 1)))) : ℕ) : ℝ) := by
      rw [← hΓS_card]; exact_mod_cast hΓT_card
    linarith only [h1, hpb.2.1]
  have hrad_ge := ap_radius_lower_bound hΓ.card_pos hρ0 hα0 hα1 hρ₂_lo hνS_lo
    (show (1 / 40 : ℝ) ≤ 1 / 40 by norm_num) (by norm_num)
  rw [hΓS_card] at hρT_ge
  refine ⟨Γ_T, ρ_T, A', hΓT_ne, hcard_le, hρT_pos,
    hρT_le.trans (hρS_le_ρ₂.trans (hρ₂_le_ρ₁.trans hρ₁_le)), hrad_ge.trans hρT_ge, hreg_T,
    Finset.inter_subset_right,
    solFreeMod_subset Finset.inter_subset_left
      (solFreeMod_translate (solFreeMod_subset hAX_sub_A₀ hSol₀) _),
    hA'ne, hx_hit⟩

set_option maxHeartbeats 600000 in
/-- Main density increment step (`Proposition 6.1` of Schoen–Sisask adapted to `x + 3y = 2z + 2w`
with distinct elements on `ZMod P`, `P ≥ 5` prime). -/
lemma density_increment_step (hP : 5 ≤ P)
    {Γ : Finset (AddChar (ZMod P) ℂ)} (hΓ : Γ.Nonempty)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 2) (hreg : IsRegularBohr Γ ρ)
    {A : Finset (ZMod P)} (hAB : A ⊆ bohr Γ ρ) (hSol : SolFreeMod A)
    (hAne : A.Nonempty)
    (hBbig : 2000 * (3e10 * (Γ.card : ℝ) ^ 2 / ((A.card : ℝ) / ((bohr Γ ρ).card : ℝ))) ^ (Γ.card + 1) ≤
      ((bohr Γ ρ).card : ℝ)) :
    let α : ℝ := (A.card : ℝ) / ((bohr Γ ρ).card : ℝ)
    let L : ℝ := Real.log (4 / α)
    ∃ (Γ' : Finset (AddChar (ZMod P) ℂ)) (ρ' : ℝ) (A' : Finset (ZMod P)),
      Γ'.Nonempty ∧
      (Γ'.card : ℝ) ≤ (Γ.card : ℝ) + 2e13 * L ^ 4 ∧
      0 < ρ' ∧ ρ' ≤ ρ ∧
      ρ * α ^ 2 / (2e34 * (Γ.card : ℝ) ^ 5 * L ^ 4) ≤ ρ' ∧
      IsRegularBohr Γ' ρ' ∧
      A' ⊆ bohr Γ' ρ' ∧ SolFreeMod A' ∧ A'.Nonempty ∧
      (11 / 10 : ℝ) * α ≤ (A'.card : ℝ) / ((bohr Γ' ρ').card : ℝ) := by
  intro α L
  let B := bohr Γ ρ
  have hBpos : (0 : ℝ) < (B.card : ℝ) := Nat.cast_pos.2 (bohr_card_pos Γ hρ0.le)
  have hApos : (0 : ℝ) < (A.card : ℝ) := Nat.cast_pos.2 hAne.card_pos
  have hα0 : 0 < α := div_pos hApos hBpos
  have hα1 : α ≤ 1 := by
    dsimp only [α]; rw [div_le_one hBpos]; exact Nat.cast_le.2 (Finset.card_le_card hAB)
  have hd_pos : (0 : ℝ) < (Γ.card : ℝ) := Nat.cast_pos.2 hΓ.card_pos
  have hd_ge1 : (1 : ℝ) ≤ (Γ.card : ℝ) := Nat.one_le_cast.2 hΓ.card_pos
  have hL_gt1 : 1 < L := (ap_params_bound hα0 hα1 (by norm_num : (1 / 40 : ℝ) ≤ 1 / 40) (by norm_num)).1
  have hL4_ge1 : 1 ≤ L ^ 4 := one_le_pow₀ hL_gt1.le
  -- Construct the three scales `B'`, `U₀ = 2 • B'`, `U₁ = (U₀)_{δ₂}` inside `B_{2 δ₁}`.
  let δ₁₀ : ℝ := α / (40000 * (Γ.card : ℝ))
  obtain ⟨t₁, ht₁_lo, ht₁_hi, hreg_B'⟩ :=
    exists_regular_bohr Γ hΓ (show 0 < δ₁₀ * ρ by dsimp only [δ₁₀]; positivity)
  let δ₁ : ℝ := t₁ * δ₁₀
  have hδ₁_lo : α / (80000 * (Γ.card : ℝ)) ≤ δ₁ := by
    dsimp only [δ₁, δ₁₀]
    calc α / (80000 * (Γ.card : ℝ)) = (1 / 2) * (α / (40000 * (Γ.card : ℝ))) := by ring
      _ ≤ t₁ * (α / (40000 * (Γ.card : ℝ))) := mul_le_mul_of_nonneg_right ht₁_lo (by positivity)
  have hδ₁_hi : δ₁ ≤ α / (40000 * (Γ.card : ℝ)) := by
    dsimp only [δ₁, δ₁₀]
    calc t₁ * (α / (40000 * (Γ.card : ℝ))) ≤ 1 * (α / (40000 * (Γ.card : ℝ))) :=
          mul_le_mul_of_nonneg_right ht₁_hi (by positivity)
      _ = α / (40000 * (Γ.card : ℝ)) := one_mul _
  have hδ₁_pos : 0 < δ₁ := lt_of_lt_of_le (by positivity) hδ₁_lo
  have hδ₁_le1 : δ₁ ≤ 1 := hδ₁_hi.trans (by rw [div_le_one (by positivity)]; linarith only [hα1, hd_ge1])
  let ρ₁ : ℝ := δ₁ * ρ
  have hρ₁_eq : ρ₁ = t₁ * (δ₁₀ * ρ) := by dsimp only [ρ₁, δ₁]; ring
  have hρ₁_pos : 0 < ρ₁ := by dsimp only [ρ₁]; positivity
  have hρ₁_le : ρ₁ ≤ ρ := mul_le_of_le_one_left hρ0.le hδ₁_le1
  have hreg_B'2 : IsRegularBohr Γ ρ₁ := by rwa [hρ₁_eq]
  let B' := bohr Γ ρ₁
  let e2 : ZMod P ≃+ ZMod P := mulEquivZMod 2 (two_ne_zero_zmod hP)
  let Γ₂ : Finset (AddChar (ZMod P) ℂ) :=
    Γ.image fun γ => γ.compAddMonoidHom e2.symm.toAddMonoidHom
  have hΓ₂_card : Γ₂.card = Γ.card := card_image_freq_addEquiv e2 Γ
  have hΓ₂_ne : Γ₂.Nonempty := Finset.card_pos.1 (hΓ₂_card ▸ hΓ.card_pos)
  have hU₀_eq : B'.image e2 = bohr Γ₂ ρ₁ := image_bohr_addEquiv e2 Γ ρ₁
  have hreg_U₀ : IsRegularBohr Γ₂ ρ₁ := isRegularBohr_image_addEquiv e2 hreg_B'2
  let U₀ := bohr Γ₂ ρ₁
  have hU₀_card : U₀.card = B'.card := by
    dsimp only [U₀]; rw [← hU₀_eq, Finset.card_image_of_injective _ e2.injective]
  -- Pick regular `U₁ = (U₀)_{δ₂}` with `δ₂ ∈ [1/(60000 d), 1/(30000 d)]`.
  let δ₂₀ : ℝ := 1 / (30000 * (Γ.card : ℝ))
  obtain ⟨t₂, ht₂_lo, ht₂_hi, hreg_U₁_raw⟩ :=
    exists_regular_bohr Γ₂ hΓ₂_ne (show 0 < δ₂₀ * ρ₁ by dsimp only [δ₂₀]; positivity)
  let δ₂ : ℝ := t₂ * δ₂₀
  have hδ₂_lo : 1 / (60000 * (Γ.card : ℝ)) ≤ δ₂ := by
    dsimp only [δ₂, δ₂₀]
    calc 1 / (60000 * (Γ.card : ℝ)) = (1 / 2) * (1 / (30000 * (Γ.card : ℝ))) := by ring
      _ ≤ t₂ * (1 / (30000 * (Γ.card : ℝ))) := mul_le_mul_of_nonneg_right ht₂_lo (by positivity)
  have hδ₂_hi : δ₂ ≤ 1 / (30000 * (Γ.card : ℝ)) := by
    dsimp only [δ₂, δ₂₀]
    calc t₂ * (1 / (30000 * (Γ.card : ℝ))) ≤ 1 * (1 / (30000 * (Γ.card : ℝ))) :=
          mul_le_mul_of_nonneg_right ht₂_hi (by positivity)
      _ = 1 / (30000 * (Γ.card : ℝ)) := one_mul _
  have hδ₂_pos : 0 < δ₂ := lt_of_lt_of_le (by positivity) hδ₂_lo
  have hδ₂_le1 : δ₂ ≤ 1 := hδ₂_hi.trans (by rw [div_le_one (by positivity)]; linarith only [hd_ge1])
  let ρ₂ : ℝ := δ₂ * ρ₁
  have hρ₂_eq : ρ₂ = t₂ * (δ₂₀ * ρ₁) := by dsimp only [ρ₂, δ₂]; ring
  have hρ₂_pos : 0 < ρ₂ := by dsimp only [ρ₂]; positivity
  have hρ₂_le_ρ₁ : ρ₂ ≤ ρ₁ := mul_le_of_le_one_left hρ₁_pos.le hδ₂_le1
  have hreg_U₁ : IsRegularBohr Γ₂ ρ₂ := by rwa [hρ₂_eq]
  let U₁ := bohr Γ₂ ρ₂
  -- Verify all three `B', U₀, U₁` lie inside `bohr Γ (2 * δ₁ * ρ)`.
  have hB'_sub : B' ⊆ bohr Γ ((2 * δ₁) * ρ) :=
    bohr_mono_radius Γ (by dsimp only [ρ₁]; have h := mul_pos hδ₁_pos hρ0; linarith only [h])
  have hU₀_sub : U₀ ⊆ bohr Γ ((2 * δ₁) * ρ) := by
    intro y hy
    dsimp only [U₀] at hy; rw [← hU₀_eq] at hy
    rcases Finset.mem_image.1 hy with ⟨x, hx, rfl⟩
    have h2x : e2 x = 2 • x := by dsimp only [e2, mulEquivZMod]; simp [two_mul]
    rw [h2x]
    have hm := nsmul_mem_bohr hρ₁_pos.le hx 2
    have heq : ((2 : ℕ) : ℝ) * ρ₁ = (2 * δ₁) * ρ := by push_cast; dsimp only [ρ₁]; ring
    rwa [heq] at hm
  have hU₁_sub_U₀ : U₁ ⊆ U₀ := bohr_mono_radius Γ₂ hρ₂_le_ρ₁
  have hU₁_sub : U₁ ⊆ bohr Γ ((2 * δ₁) * ρ) := hU₁_sub_U₀.trans hU₀_sub
  -- Lower bound on `ρ₂`:
  have hρ₂_lo : ρ * α / (4.8e9 * (Γ.card : ℝ) ^ 2) ≤ ρ₂ := by
    dsimp only [ρ₂, ρ₁]
    have hmul : (1 / (60000 * (Γ.card : ℝ))) * (α / (80000 * (Γ.card : ℝ))) ≤ δ₂ * δ₁ :=
      mul_le_mul hδ₂_lo hδ₁_lo (by positivity) (by positivity)
    have h2 := mul_le_mul_of_nonneg_right hmul hρ0.le
    have hsimp : (1 / (60000 * (Γ.card : ℝ))) * (α / (80000 * (Γ.card : ℝ))) * ρ =
        ρ * α / (4.8e9 * (Γ.card : ℝ) ^ 2) := by field_simp [hd_pos.ne']; ring
    linarith only [h2, hsimp]
  have hρ₂_ge_target : ρ * α ^ 2 / (2e34 * (Γ.card : ℝ) ^ 5 * L ^ 4) ≤ ρ₂ := by
    have hnum : ρ * α ^ 2 ≤ ρ * α := by
      have hα2 : α ^ 2 ≤ α := by rw [sq]; exact mul_le_of_le_one_right hα0.le hα1
      exact mul_le_mul_of_nonneg_left hα2 hρ0.le
    have hden : 4.8e9 * (Γ.card : ℝ) ^ 2 ≤ 2e34 * (Γ.card : ℝ) ^ 5 * L ^ 4 := by
      have hd25 : (Γ.card : ℝ) ^ 2 ≤ (Γ.card : ℝ) ^ 5 := pow_le_pow_right₀ hd_ge1 (by norm_num)
      have hd5 : (Γ.card : ℝ) ^ 5 ≤ (Γ.card : ℝ) ^ 5 * L ^ 4 :=
        le_mul_of_one_le_right (by positivity) hL4_ge1
      have h1 : (Γ.card : ℝ) ^ 2 ≤ (Γ.card : ℝ) ^ 5 * L ^ 4 := hd25.trans hd5
      have h2 : (0 : ℝ) < (Γ.card : ℝ) ^ 5 * L ^ 4 := by positivity
      linarith only [h1, h2]
    exact (div_le_div₀ (by positivity) hnum (by positivity) hden).trans hρ₂_lo
  -- Apply `three_scales_dichotomy` to `W₁ = B'`, `W₂ = U₀`, `W₃ = U₁`.
  have h2δ₁_le : 2 * δ₁ ≤ α / (20000 * (Γ.card : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hδ₁_hi (show (0 : ℝ) ≤ 2 by norm_num)
    have hsimp : 2 * (α / (40000 * (Γ.card : ℝ))) = α / (20000 * (Γ.card : ℝ)) := by ring
    linarith only [hmul, hsimp]
  have hdich := three_scales_dichotomy hΓ hρ0 hreg hAB (by positivity) h2δ₁_le
    (bohr_nonempty Γ hρ₁_pos.le) (bohr_nonempty Γ₂ hρ₁_pos.le) (bohr_nonempty Γ₂ hρ₂_pos.le)
    hB'_sub hU₀_sub hU₁_sub
  -- Handle the 3 early-exit branches uniformly!
  have hearly : ∀ (Γ_w : Finset (AddChar (ZMod P) ℂ)) (ρ_w : ℝ),
      Γ_w.Nonempty → Γ_w.card = Γ.card →
      ρ₂ ≤ ρ_w → ρ_w ≤ ρ → IsRegularBohr Γ_w ρ_w →
      (∃ x : ZMod P, (11 / 10 : ℝ) * α ≤ convR (indR A) (muR (bohr Γ_w ρ_w)) x) →
      ∃ (Γ' : Finset (AddChar (ZMod P) ℂ)) (ρ' : ℝ) (A' : Finset (ZMod P)),
        Γ'.Nonempty ∧ (Γ'.card : ℝ) ≤ (Γ.card : ℝ) + 2e13 * L ^ 4 ∧
        0 < ρ' ∧ ρ' ≤ ρ ∧
        ρ * α ^ 2 / (2e34 * (Γ.card : ℝ) ^ 5 * L ^ 4) ≤ ρ' ∧
        IsRegularBohr Γ' ρ' ∧ A' ⊆ bohr Γ' ρ' ∧ SolFreeMod A' ∧ A'.Nonempty ∧
        (11 / 10 : ℝ) * α ≤ (A'.card : ℝ) / ((bohr Γ' ρ').card : ℝ) := by
    intro Γ_w ρ_w hne hcard hρw_lo hρw_hi hreg_w ⟨x, hx⟩
    let A' : Finset (ZMod P) := A.image (fun a => a - x) ∩ bohr Γ_w ρ_w
    have hdens : (11 / 10 : ℝ) * α ≤ (A'.card : ℝ) / ((bohr Γ_w ρ_w).card : ℝ) := by
      rwa [convR_indR_muR_eq_density_translate A (bohr Γ_w ρ_w) (fun _ hw => neg_mem_bohr hw) x] at hx
    have hA'ne : A'.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro he; rw [he, Finset.card_empty, Nat.cast_zero, zero_div] at hdens
      linarith only [hα0, hdens]
    refine ⟨Γ_w, ρ_w, A', hne, by rw [hcard]; linarith only [hL4_ge1],
      lt_of_lt_of_le hρ₂_pos hρw_lo, hρw_hi, hρ₂_ge_target.trans hρw_lo, hreg_w,
      Finset.inter_subset_right, solFreeMod_subset Finset.inter_subset_left (solFreeMod_translate hSol x),
      hA'ne, hdens⟩
  rcases hdich with hW1 | hW2 | hW3 | ⟨x₀, _, hB'd, hU₀d, hU₁d⟩
  · exact hearly Γ ρ₁ hΓ rfl hρ₂_le_ρ₁ hρ₁_le hreg_B'2 hW1
  · exact hearly Γ₂ ρ₁ hΓ₂_ne hΓ₂_card hρ₂_le_ρ₁ hρ₁_le hreg_U₀ hW2
  · exact hearly Γ₂ ρ₂ hΓ₂_ne hΓ₂_card le_rfl (hρ₂_le_ρ₁.trans hρ₁_le) hreg_U₁ hW3
  -- Balanced case at `x₀`:
  let A₀ : Finset (ZMod P) := A.image (fun a => a - x₀)
  have hSol₀ : SolFreeMod A₀ := solFreeMod_translate hSol x₀
  let A_Z : Finset (ZMod P) := A₀ ∩ B'
  let A_X : Finset (ZMod P) := A₀ ∩ U₀
  let A_S : Finset (ZMod P) := A₀ ∩ U₁
  let α' : ℝ := (77 / 100 : ℝ) * α
  have hα'_pos : 0 < α' := by dsimp only [α']; positivity
  have hAZ_dens : α' * (B'.card : ℝ) ≤ (A_Z.card : ℝ) := by
    rw [convR_indR_muR_eq_density_translate A B' (fun _ hw => neg_mem_bohr hw) x₀] at hB'd
    exact (le_div_iff₀ (Nat.cast_pos.2 (bohr_card_pos Γ hρ₁_pos.le))).1 hB'd
  have hAX_dens : α' * (U₀.card : ℝ) ≤ (A_X.card : ℝ) := by
    rw [convR_indR_muR_eq_density_translate A U₀ (fun _ hw => neg_mem_bohr hw) x₀] at hU₀d
    exact (le_div_iff₀ (Nat.cast_pos.2 (bohr_card_pos Γ₂ hρ₁_pos.le))).1 hU₀d
  have hAS_dens : α' * (U₁.card : ℝ) ≤ (A_S.card : ℝ) := by
    rw [convR_indR_muR_eq_density_translate A U₁ (fun _ hw => neg_mem_bohr hw) x₀] at hU₁d
    exact (le_div_iff₀ (Nat.cast_pos.2 (bohr_card_pos Γ₂ hρ₂_pos.le))).1 hU₁d
  have hAZ_dens_U₀ : α' * (U₀.card : ℝ) ≤ (A_Z.card : ℝ) := by rwa [hU₀_card]
  have hAX_ne : A_X.Nonempty := Finset.card_pos.1 (by
    have hU₀p : (0 : ℝ) < (U₀.card : ℝ) := Nat.cast_pos.2 (bohr_card_pos Γ₂ hρ₁_pos.le)
    have : (0 : ℝ) < (A_X.card : ℝ) := lt_of_lt_of_le (mul_pos hα'_pos hU₀p) hAX_dens
    exact_mod_cast this)
  have hAZ_ne : A_Z.Nonempty := Finset.card_pos.1 (by
    have hU₀p : (0 : ℝ) < (U₀.card : ℝ) := Nat.cast_pos.2 (bohr_card_pos Γ₂ hρ₁_pos.le)
    have : (0 : ℝ) < (A_Z.card : ℝ) := lt_of_lt_of_le (mul_pos hα'_pos hU₀p) hAZ_dens_U₀
    exact_mod_cast this)
  -- Show `1000 ≤ A_S.card` from `hBbig` and `bohr_card_decay_ge`!
  have hAS_ge1000 : 1000 ≤ A_S.card := by
    have hU₁_card_eq : U₁.card = (bohr Γ (δ₂ * δ₁ * ρ)).card := by
      have h1 : (bohr Γ (δ₂ * δ₁ * ρ)).image e2 = U₁ := by
        dsimp only [U₁, Γ₂]
        rw [image_bohr_addEquiv]
        congr 1; dsimp only [ρ₂, ρ₁]; ring
      rw [← h1, Finset.card_image_of_injective _ e2.injective]
    have hdec := bohr_card_decay_ge Γ hρ0 (show 0 < δ₂ * δ₁ by positivity)
      (mul_le_one₀ hδ₂_le1 hδ₁_pos.le hδ₁_le1)
    have hrat_ge : α / (3e10 * (Γ.card : ℝ) ^ 2) ≤ δ₂ * δ₁ / 5 := by
      have hmul : (1 / (60000 * (Γ.card : ℝ))) * (α / (80000 * (Γ.card : ℝ))) ≤ δ₂ * δ₁ :=
        mul_le_mul hδ₂_lo hδ₁_lo (by positivity) (by positivity)
      have h1 : α / (2.4e10 * (Γ.card : ℝ) ^ 2) ≤ δ₂ * δ₁ / 5 := by
        have hdiv := div_le_div_of_nonneg_right hmul (show (0 : ℝ) ≤ 5 by norm_num)
        have hsimp : (1 / (60000 * (Γ.card : ℝ))) * (α / (80000 * (Γ.card : ℝ))) / 5 =
            α / (2.4e10 * (Γ.card : ℝ) ^ 2) := by field_simp [hd_pos.ne']; ring
        linarith only [hdiv, hsimp]
      have hd2pos : (0 : ℝ) < (Γ.card : ℝ) ^ 2 := pow_pos hd_pos 2
      have h2 : α / (3e10 * (Γ.card : ℝ) ^ 2) ≤ α / (2.4e10 * (Γ.card : ℝ) ^ 2) :=
        div_le_div_of_nonneg_left hα0.le (by positivity) (by linarith only [hd2pos])
      exact h2.trans h1
    have hU₁_ge : (α / (3e10 * (Γ.card : ℝ) ^ 2)) ^ Γ.card * (B.card : ℝ) ≤ (U₁.card : ℝ) := by
      rw [hU₁_card_eq]
      have hrat_nn : 0 ≤ α / (3e10 * (Γ.card : ℝ) ^ 2) :=
        div_nonneg hα0.le (mul_nonneg (by norm_num) (sq_nonneg _))
      have hpow := pow_le_pow_left₀ hrat_nn hrat_ge Γ.card
      have hmul := mul_le_mul_of_nonneg_right hpow hBpos.le
      exact hmul.trans hdec
    have hAS_R : (1000 : ℝ) ≤ (A_S.card : ℝ) := by
      have hinv : (α / (3e10 * (Γ.card : ℝ) ^ 2)) ^ Γ.card *
          (3e10 * (Γ.card : ℝ) ^ 2 / α) ^ (Γ.card + 1) =
          3e10 * (Γ.card : ℝ) ^ 2 / α := by
        rw [pow_succ _ Γ.card, ← mul_assoc, ← mul_pow]
        have h1 : (α / (3e10 * (Γ.card : ℝ) ^ 2)) * (3e10 * (Γ.card : ℝ) ^ 2 / α) = 1 := by
          field_simp [hα0.ne', hd_pos.ne']
        rw [h1, one_pow, one_mul]
      have hU₁_ge2 : 2000 * (3e10 * (Γ.card : ℝ) ^ 2 / α) ≤ (U₁.card : ℝ) := by
        calc 2000 * (3e10 * (Γ.card : ℝ) ^ 2 / α)
            = (α / (3e10 * (Γ.card : ℝ) ^ 2)) ^ Γ.card *
                (2000 * (3e10 * (Γ.card : ℝ) ^ 2 / α) ^ (Γ.card + 1)) := by
              rw [← mul_left_comm, hinv]
          _ ≤ (α / (3e10 * (Γ.card : ℝ) ^ 2)) ^ Γ.card * (B.card : ℝ) :=
              mul_le_mul_of_nonneg_left hBbig (by positivity)
          _ ≤ (U₁.card : ℝ) := hU₁_ge
      have hmul := mul_le_mul_of_nonneg_left hU₁_ge2 hα'_pos.le
      have hsimp : α' * (2000 * (3e10 * (Γ.card : ℝ) ^ 2 / α)) =
          (77 / 100 : ℝ) * 2000 * 3e10 * (Γ.card : ℝ) ^ 2 := by
        dsimp only [α']; field_simp [hα0.ne']
      have hd2 : (1 : ℝ) ≤ (Γ.card : ℝ) ^ 2 := one_le_pow₀ hd_ge1
      have hbig : (1000 : ℝ) ≤ α' * (2000 * (3e10 * (Γ.card : ℝ) ^ 2 / α)) := by
        rw [hsimp]; linarith only [hd2]
      exact hbig.trans (hmul.trans hAS_dens)
    exact_mod_cast hAS_R
  -- Extract two disjoint subsets `A₁, A₄ ⊆ A_S` of exact size `m_s = A_S.card / 500`.
  let m_s : ℕ := A_S.card / 500
  have hm_s_ge2 : 2 ≤ m_s := by dsimp only [m_s]; omega
  have hm_s_le : m_s ≤ A_S.card := Nat.div_le_self _ _
  obtain ⟨A₁, hA₁_sub, hA₁_card⟩ := Finset.exists_subset_card_eq hm_s_le
  have hrest_ge : m_s ≤ (A_S \ A₁).card := by
    have := Finset.card_sdiff_add_card_eq_card hA₁_sub
    omega
  obtain ⟨A₄, hA₄_sub_sdiff, hA₄_card⟩ := Finset.exists_subset_card_eq hrest_ge
  have hA₄_sub : A₄ ⊆ A_S := hA₄_sub_sdiff.trans Finset.sdiff_subset
  have hA₁_A₄_disj : Disjoint A₁ A₄ :=
    Finset.disjoint_left.2 fun a ha₁ ha₄ => (Finset.mem_sdiff.1 (hA₄_sub_sdiff ha₄)).2 ha₁
  have hA₁_ne : A₁.Nonempty := Finset.card_pos.1 (by omega)
  have hA₄_ne : A₄.Nonempty := Finset.card_pos.1 (by omega)
  have hAS_sub_AX : A_S ⊆ A_X := Finset.inter_subset_inter_left hU₁_sub_U₀
  have hA₄_le_AX : (A₄.card : ℝ) ≤ (1 / 500 : ℝ) * (A_X.card : ℝ) := by
    have h1 : 500 * A₄.card ≤ A_S.card := by rw [hA₄_card]; exact Nat.mul_div_le A_S.card 500
    have h2 : A_S.card ≤ A_X.card := Finset.card_le_card hAS_sub_AX
    have h3 : (500 : ℝ) * (A₄.card : ℝ) ≤ (A_X.card : ℝ) := by exact_mod_cast h1.trans h2
    linarith only [h3]
  have hU₁_le_ms : 2 * (U₁.card : ℝ) ≤ (4000 / α) * (m_s : ℝ) := by
    have h1 : A_S.card ≤ 1000 * m_s := by dsimp only [m_s]; omega
    have h2 : (A_S.card : ℝ) ≤ 1000 * (m_s : ℝ) := by exact_mod_cast h1
    have h3 : (77 / 100 : ℝ) * α * (U₁.card : ℝ) ≤ 1000 * (m_s : ℝ) := hAS_dens.trans h2
    have hms_nn : (0 : ℝ) ≤ (m_s : ℝ) := Nat.cast_nonneg _
    rw [div_mul_eq_mul_div, le_div_iff₀ hα0]
    have h4 : 2 * (U₁.card : ℝ) * α ≤ (200 / 77 : ℝ) * (1000 * (m_s : ℝ)) := by linarith only [h3]
    linarith only [h4, hms_nn]
  -- Split on `|2 • A_Z + 2 • A₄|` vs `(1 / 2) * |U₀|`!
  by_cases hsmall : (((A_Z ×ˢ A₄).image (fun p => 2 * p.1 + 2 * p.2)).card : ℝ) ≤
      (1 / 2 : ℝ) * (U₀.card : ℝ)
  · exact density_increment_small_sumset hP hΓ hΓ₂_card hρ0 hρ2 hρ₁_le hρ₂_pos hρ₂_le_ρ₁
      hρ₂_lo hreg_U₁ hα0 hα1 hSol₀ Finset.inter_subset_left hAZ_ne hA₄_ne
      (hA₄_sub.trans Finset.inter_subset_right) hAZ_dens_U₀
      (by rwa [hA₄_card]) hsmall
  · push Not at hsmall
    exact density_increment_large_sumset hP hΓ hΓ₂_card hρ0 hρ2 hρ₁_le hρ₂_pos hρ₂_le_ρ₁
      hρ₂_lo hδ₂_pos hδ₂_hi rfl hreg_U₀ hreg_U₁ hU₀_eq hα0 hα1 hSol₀
      Finset.inter_subset_left Finset.inter_subset_right
      Finset.inter_subset_left Finset.inter_subset_right
      (hA₁_sub.trans Finset.inter_subset_left) (hA₁_sub.trans Finset.inter_subset_right)
      (hA₄_sub.trans Finset.inter_subset_left) (hA₄_sub.trans Finset.inter_subset_right)
      hA₁_A₄_disj hAX_ne hA₁_ne hA₄_ne hA₄_le_AX hAX_dens (by rwa [hA₁_card]) hsmall

end DensityIncrement

/- ## Section 6: Iteration on `ZMod P` and Final Upper Bound for `Green16.f` -/

section IterationAndMain

/-- Numerical helper: `11 * log(11/10) ≥ 1`. -/
private lemma eleven_mul_log_eleven_tenths_ge_one :
    (1 : ℝ) ≤ 11 * Real.log (11 / 10 : ℝ) := by
  -- Equivalent to `exp(1/11) ≤ 11/10`
  have hexp : Real.exp (1 / 11 : ℝ) ≤ 11 / 10 := by
    have h1 := Real.exp_bound (x := (1 / 11 : ℝ)) (n := 3) (by norm_num) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, pow_one, Nat.factorial_one, zero_add] at h1
    have habs := (abs_le.1 h1).2
    norm_num at habs
    linarith
  have hlog : (1 / 11 : ℝ) ≤ Real.log (11 / 10 : ℝ) := by
    calc (1 / 11 : ℝ) = Real.log (Real.exp (1 / 11)) := (Real.log_exp _).symm
      _ ≤ Real.log (11 / 10) := Real.log_le_log (Real.exp_pos _) hexp
  linarith

/-- Fast log bound from `10^3 = 1000 ≤ 1024 = 2^10 ≤ e^10`: if `0 < x ≤ (10^3)^k`,
then `log x ≤ 10 * k`. -/
private lemma log_le_of_le_ten_pow {x : ℝ} (hx : 0 < x) {k : ℕ}
    (h : x ≤ ((10 : ℝ) ^ 3) ^ k) : Real.log x ≤ (10 * k : ℝ) := by
  have h1000 : (10 : ℝ) ^ 3 ≤ (2 : ℝ) ^ 10 := by norm_num
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith only [this]
  have hstep : (10 : ℝ) ^ 3 ≤ Real.exp 10 := by
    calc (10 : ℝ) ^ 3 ≤ (2 : ℝ) ^ 10 := h1000
      _ ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) h2e 10
      _ = Real.exp 10 := by rw [← Real.exp_nat_mul]; norm_num
  have hexp : x ≤ Real.exp (10 * k : ℝ) := by
    calc x ≤ ((10 : ℝ) ^ 3) ^ k := h
      _ ≤ (Real.exp 10) ^ k := pow_le_pow_left₀ (by positivity) hstep k
      _ = Real.exp (10 * k : ℝ) := by rw [← Real.exp_nat_mul]; congr 1; ring
  calc Real.log x ≤ Real.log (Real.exp (10 * k : ℝ)) := Real.log_le_log hx hexp
    _ = (10 * k : ℝ) := Real.log_exp _

/-- Upper bound for `SolFreeMod` subsets of `ZMod P` (`P ≥ 5` prime):
`|A| ≤ 4 * P * exp(-c * (log P)^(1/7))` with `c = (2e18)^(-1/7)`. -/
lemma zmod_solfree_upper_bound {P : ℕ} [Fact P.Prime] (hP : 5 ≤ P)
    {A : Finset (ZMod P)} (hSol : SolFreeMod A) :
    (A.card : ℝ) ≤
      4 * (P : ℝ) * Real.exp (-((2e18 : ℝ) ^ (-(1 / 7 : ℝ))) * (Real.log (P : ℝ)) ^ (1 / 7 : ℝ)) := by
  by_cases hAempty : A = ∅
  · rw [hAempty, Finset.card_empty, Nat.cast_zero]
    positivity
  have hAne : A.Nonempty := Finset.nonempty_iff_ne_empty.2 hAempty
  have hPpos : (0 : ℝ) < (P : ℝ) := Nat.cast_pos.2 (by omega)
  have hcardG : (Fintype.card (ZMod P) : ℝ) = (P : ℝ) := by rw [ZMod.card]
  let α₀ : ℝ := (A.card : ℝ) / (P : ℝ)
  have hα₀_pos : 0 < α₀ := div_pos (Nat.cast_pos.2 hAne.card_pos) hPpos
  have hα₀_le1 : α₀ ≤ 1 := by
    dsimp only [α₀]; rw [div_le_one hPpos, ← hcardG]
    exact Nat.cast_le.2 (Finset.card_le_univ A)
  let L₀ : ℝ := Real.log (4 / α₀)
  have hL₀_gt1 : 1 < L₀ := by
    dsimp only [L₀]
    have h4α : (4 : ℝ) ≤ 4 / α₀ := by rw [le_div_iff₀ hα₀_pos]; linarith only [hα₀_le1]
    have hexp1 : Real.exp 1 < 4 := by have := Real.exp_one_lt_d9; linarith only [this]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log (4 / α₀) := Real.log_lt_log (Real.exp_pos 1) (lt_of_lt_of_le hexp1 h4α)
  have hL₀_pos : 0 < L₀ := by linarith only [hL₀_gt1]
  -- Induction on step count `j`: either iteration survives to step `j`, or `log P ≤ 2e18 * L₀^7`.
  have hiter : ∀ j : ℕ,
      (∃ (Γ : Finset (AddChar (ZMod P) ℂ)) (ρ : ℝ) (Aj : Finset (ZMod P)),
        Γ.Nonempty ∧
        (Γ.card : ℝ) ≤ 1 + (j : ℝ) * (2e13 * L₀ ^ 4) ∧
        0 < ρ ∧ ρ ≤ 2 ∧
        Real.log (2 / ρ) ≤ (j : ℝ) * (400 * L₀) ∧
        IsRegularBohr Γ ρ ∧
        Aj ⊆ bohr Γ ρ ∧ SolFreeMod Aj ∧ Aj.Nonempty ∧
        (11 / 10 : ℝ) ^ j * α₀ ≤ (Aj.card : ℝ) / ((bohr Γ ρ).card : ℝ)) ∨
      Real.log (P : ℝ) ≤ 2e18 * L₀ ^ 7 := by
    intro j
    induction j with
    | zero =>
      left
      refine ⟨{(1 : AddChar (ZMod P) ℂ)}, 2, A, Finset.singleton_nonempty _,
        by simp, by norm_num, le_rfl, by simp,
        isRegularBohr_singleton_one 2 (by norm_num),
        by rw [bohr_singleton_one 2 (by norm_num)]; exact Finset.subset_univ A,
        hSol, hAne, ?_⟩
      rw [bohr_singleton_one 2 (by norm_num), Finset.card_univ, ZMod.card, pow_zero, one_mul]
    | succ j ih =>
      rcases ih with ⟨Γ, ρ, Aj, hΓ, hΓc, hρ0, hρ2, hρlog, hreg, hAjB, hSolj, hAjne, hdens⟩ | hdone
      · let αj : ℝ := (Aj.card : ℝ) / ((bohr Γ ρ).card : ℝ)
        have hBjpos : (0 : ℝ) < ((bohr Γ ρ).card : ℝ) :=
          Nat.cast_pos.2 (bohr_card_pos Γ hρ0.le)
        have hαj_le1 : αj ≤ 1 := by
          dsimp only [αj]; rw [div_le_one hBjpos]; exact Nat.cast_le.2 (Finset.card_le_card hAjB)
        have hα₀_le_αj : α₀ ≤ αj := by
          have h1 : (1 : ℝ) ≤ (11 / 10 : ℝ) ^ j := one_le_pow₀ (by norm_num)
          calc α₀ = 1 * α₀ := (one_mul _).symm
            _ ≤ (11 / 10 : ℝ) ^ j * α₀ := mul_le_mul_of_nonneg_right h1 hα₀_pos.le
            _ ≤ αj := hdens
        have hαj_pos : 0 < αj := lt_of_lt_of_le hα₀_pos hα₀_le_αj
        -- Bound `j ≤ 11 * L₀` from `(11/10)^j * α₀ ≤ 1`.
        have hj_le : (j : ℝ) ≤ 11 * L₀ := by
          have hpow_le : (11 / 10 : ℝ) ^ j ≤ 1 / α₀ := by
            rw [le_div_iff₀ hα₀_pos]; linarith only [hdens, hαj_le1]
          have hlog_pow := Real.log_le_log (by positivity) hpow_le
          rw [Real.log_pow] at hlog_pow
          have h1α : Real.log (1 / α₀) ≤ L₀ :=
            Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) hα₀_pos.le)
          have h11 := eleven_mul_log_eleven_tenths_ge_one
          have hmul := mul_le_mul_of_nonneg_left (hlog_pow.trans h1α) (show (0 : ℝ) ≤ 11 by norm_num)
          have h11j : (j : ℝ) ≤ (j : ℝ) * (11 * Real.log (11 / 10 : ℝ)) :=
            le_mul_of_one_le_right (Nat.cast_nonneg j) h11
          linarith only [hmul, h11j]
        -- Hence `d_j ≤ 3e14 * L₀^5`.
        have hL5_ge1 : 1 ≤ L₀ ^ 5 := one_le_pow₀ hL₀_gt1.le
        have hd_le : (Γ.card : ℝ) ≤ 3e14 * L₀ ^ 5 := by
          have hmul : (j : ℝ) * (2e13 * L₀ ^ 4) ≤ (11 * L₀) * (2e13 * L₀ ^ 4) :=
            mul_le_mul_of_nonneg_right hj_le (by positivity)
          have hprod : (11 * L₀) * (2e13 * L₀ ^ 4) = 2.2e14 * L₀ ^ 5 := by ring
          linarith only [hΓc, hmul, hprod, hL5_ge1]
        have hd_ge1 : (1 : ℝ) ≤ (Γ.card : ℝ) := Nat.one_le_cast.2 hΓ.card_pos
        -- Split on whether `|bohr Γ ρ|` is large enough for `density_increment_step`!
        by_cases hBbig :
            2000 * (3e10 * (Γ.card : ℝ) ^ 2 / αj) ^ (Γ.card + 1) ≤ ((bohr Γ ρ).card : ℝ)
        · left
          obtain ⟨Γ', ρ', A', hΓ', hΓ'c, hρ'0, hρ'le, hρ'ge, hreg', hA'B', hSol', hA'ne, hdens'⟩ :=
            density_increment_step hP hΓ hρ0 hρ2 hreg hAjB hSolj hAjne hBbig
          change (Γ'.card : ℝ) ≤ (Γ.card : ℝ) + 2e13 * Real.log (4 / αj) ^ 4 at hΓ'c
          change ρ * αj ^ 2 / (2e34 * (Γ.card : ℝ) ^ 5 * Real.log (4 / αj) ^ 4) ≤ ρ' at hρ'ge
          have hLj_le : Real.log (4 / αj) ≤ L₀ :=
            Real.log_le_log (by positivity) (div_le_div_of_nonneg_left (by norm_num) hα₀_pos hα₀_le_αj)
          have hLj_pos : 0 < Real.log (4 / αj) := by
            have h4 : (4 : ℝ) ≤ 4 / αj := by rw [le_div_iff₀ hαj_pos]; linarith only [hαj_le1]
            exact Real.log_pos (by linarith only [h4])
          have hLj4_le : Real.log (4 / αj) ^ 4 ≤ L₀ ^ 4 :=
            pow_le_pow_left₀ hLj_pos.le hLj_le 4
          have hΓ'c_new : (Γ'.card : ℝ) ≤ 1 + ((j + 1 : ℕ) : ℝ) * (2e13 * L₀ ^ 4) := by
            push_cast
            have hstep : 2e13 * Real.log (4 / αj) ^ 4 ≤ 2e13 * L₀ ^ 4 :=
              mul_le_mul_of_nonneg_left hLj4_le (by norm_num)
            have hexp : 1 + ((j : ℝ) + 1) * (2e13 * L₀ ^ 4) =
                (1 + (j : ℝ) * (2e13 * L₀ ^ 4)) + 2e13 * L₀ ^ 4 := by ring
            linarith only [hΓ'c, hΓc, hstep, hexp]
          -- Bound `log(2 / ρ') ≤ (j + 1) * (400 * L₀)`.
          have hρ'log : Real.log (2 / ρ') ≤ ((j + 1 : ℕ) : ℝ) * (400 * L₀) := by
            have hstep_ratio : ρ / ρ' ≤ 2e34 * (Γ.card : ℝ) ^ 5 * L₀ ^ 4 / α₀ ^ 2 := by
              have hden_le : 2e34 * (Γ.card : ℝ) ^ 5 * Real.log (4 / αj) ^ 4 ≤
                  2e34 * (Γ.card : ℝ) ^ 5 * L₀ ^ 4 := by gcongr
              have hα2 : α₀ ^ 2 ≤ αj ^ 2 := pow_le_pow_left₀ hα₀_pos.le hα₀_le_αj 2
              have hge : ρ * α₀ ^ 2 / (2e34 * (Γ.card : ℝ) ^ 5 * L₀ ^ 4) ≤ ρ' := by
                calc ρ * α₀ ^ 2 / (2e34 * (Γ.card : ℝ) ^ 5 * L₀ ^ 4)
                    ≤ ρ * αj ^ 2 / (2e34 * (Γ.card : ℝ) ^ 5 * Real.log (4 / αj) ^ 4) :=
                      div_le_div₀ (by positivity) (by gcongr) (by positivity) hden_le
                  _ ≤ ρ' := hρ'ge
              rw [div_le_div_iff₀ hρ'0 (pow_pos hα₀_pos 2)]
              have hmul := (div_le_iff₀ (show (0 : ℝ) < 2e34 * (Γ.card : ℝ) ^ 5 * L₀ ^ 4 by positivity)).1 hge
              linarith only [hmul]
            have hstep_log : Real.log (ρ / ρ') ≤ 400 * L₀ := by
              have hd5 : (Γ.card : ℝ) ^ 5 ≤ (3e14 * L₀ ^ 5) ^ 5 :=
                pow_le_pow_left₀ (by positivity) hd_le 5
              have h1 : 2e34 * (Γ.card : ℝ) ^ 5 * L₀ ^ 4 / α₀ ^ 2 ≤
                  (2e34 * (3e14 : ℝ) ^ 5) * L₀ ^ 29 * (4 / α₀) ^ 2 := by
                have h2 : (2e34 : ℝ) * (3e14 * L₀ ^ 5) ^ 5 * L₀ ^ 4 =
                    (2e34 * (3e14 : ℝ) ^ 5) * L₀ ^ 29 := by ring
                have hα_4 : 1 / α₀ ^ 2 ≤ (4 / α₀) ^ 2 := by
                  rw [div_pow 4 α₀]
                  exact div_le_div_of_nonneg_right (show (1 : ℝ) ≤ (4 : ℝ) ^ 2 by norm_num)
                    (pow_nonneg hα₀_pos.le 2)
                calc 2e34 * (Γ.card : ℝ) ^ 5 * L₀ ^ 4 / α₀ ^ 2
                    = (2e34 * (Γ.card : ℝ) ^ 5 * L₀ ^ 4) * (1 / α₀ ^ 2) := by ring
                  _ ≤ ((2e34 * (3e14 : ℝ) ^ 5) * L₀ ^ 29) * (4 / α₀) ^ 2 := by
                      rw [← h2]; exact mul_le_mul (by gcongr) hα_4 (by positivity) (by positivity)
                  _ = (2e34 * (3e14 : ℝ) ^ 5) * L₀ ^ 29 * (4 / α₀) ^ 2 := by ring
              have hlog1 := Real.log_le_log (div_pos hρ0 hρ'0) (hstep_ratio.trans h1)
              have hc_pos : (0 : ℝ) < 2e34 * (3e14 : ℝ) ^ 5 := by positivity
              rw [Real.log_mul (by positivity) (by positivity),
                Real.log_mul hc_pos.ne' (pow_pos hL₀_pos 29).ne',
                Real.log_pow, Real.log_pow] at hlog1
              have hlog_const : Real.log (2e34 * (3e14 : ℝ) ^ 5) ≤ 360 := by
                have h2e34 : (2e34 : ℝ) = 2 * (10 : ℝ) ^ 34 := by norm_num
                have h3e14 : (3e14 : ℝ) = 3 * (10 : ℝ) ^ 14 := by norm_num
                have hle : (2e34 : ℝ) * (3e14 : ℝ) ^ 5 ≤ ((10 : ℝ) ^ 3) ^ 36 := by
                  rw [h2e34, h3e14]
                  have heq1 : 2 * (10 : ℝ) ^ 34 * (3 * (10 : ℝ) ^ 14) ^ 5 = 486 * (10 : ℝ) ^ 104 := by ring
                  have heq2 : ((10 : ℝ) ^ 3) ^ 36 = 10000 * (10 : ℝ) ^ 104 := by ring
                  rw [heq1, heq2]
                  exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
                exact (log_le_of_le_ten_pow hc_pos hle).trans (by norm_num)
              have hlog_L₀ : Real.log L₀ ≤ L₀ := (Real.log_le_sub_one_of_pos hL₀_pos).trans (by linarith only [])
              have h29 : ((29 : ℕ) : ℝ) * Real.log L₀ ≤ 29 * L₀ := by
                push_cast; linarith only [hlog_L₀]
              have h2L : ((2 : ℕ) : ℝ) * Real.log (4 / α₀) = 2 * L₀ := by
                push_cast; rfl
              have hcomb1 : Real.log (ρ / ρ') ≤ 360 + 29 * L₀ + 2 * L₀ := by
                rw [h2L] at hlog1
                exact hlog1.trans (add_le_add (add_le_add hlog_const h29) le_rfl)
              linarith only [hcomb1, hL₀_gt1]
            have hsplit : Real.log (2 / ρ') = Real.log (2 / ρ) + Real.log (ρ / ρ') := by
              rw [← Real.log_mul (by positivity) (by positivity)]
              congr 1; field_simp [hρ0.ne', hρ'0.ne']
            rw [hsplit]
            push_cast
            have hexp : ((j : ℝ) + 1) * (400 * L₀) = (j : ℝ) * (400 * L₀) + 400 * L₀ := by ring
            linarith only [hρlog, hstep_log, hexp]
          have hdens_new : (11 / 10 : ℝ) ^ (j + 1) * α₀ ≤ (A'.card : ℝ) / ((bohr Γ' ρ').card : ℝ) := by
            rw [pow_succ', mul_assoc]
            exact (mul_le_mul_of_nonneg_left hdens (by norm_num)).trans hdens'
          exact ⟨Γ', ρ', A', hΓ', hΓ'c_new, hρ'0, hρ'le.trans hρ2, hρ'log, hreg', hA'B', hSol',
            hA'ne, hdens_new⟩
        · -- Stopping condition triggered: deduce `log P ≤ 2e18 * L₀^7`!
          right
          push Not at hBbig
          have hlow := bohr_card_ge Γ hρ0 hρ2
          rw [hcardG] at hlow
          have hcomb : (ρ / 9) ^ Γ.card * (P : ℝ) <
              2000 * (3e10 * (Γ.card : ℝ) ^ 2 / α₀) ^ (Γ.card + 1) := by
            have h1 : (3e10 * (Γ.card : ℝ) ^ 2 / αj) ^ (Γ.card + 1) ≤
                (3e10 * (Γ.card : ℝ) ^ 2 / α₀) ^ (Γ.card + 1) :=
              pow_le_pow_left₀ (by positivity)
                (div_le_div_of_nonneg_left (by positivity) hα₀_pos hα₀_le_αj) _
            calc (ρ / 9) ^ Γ.card * (P : ℝ) ≤ ((bohr Γ ρ).card : ℝ) := hlow
              _ < 2000 * (3e10 * (Γ.card : ℝ) ^ 2 / αj) ^ (Γ.card + 1) := hBbig
              _ ≤ 2000 * (3e10 * (Γ.card : ℝ) ^ 2 / α₀) ^ (Γ.card + 1) :=
                  mul_le_mul_of_nonneg_left h1 (by norm_num)
          have hP_lt : (P : ℝ) <
              (9 / ρ) ^ Γ.card * (2000 * (3e10 * (Γ.card : ℝ) ^ 2 / α₀) ^ (Γ.card + 1)) := by
            have hmul := mul_lt_mul_of_pos_left hcomb (show (0 : ℝ) < (9 / ρ) ^ Γ.card by positivity)
            have hlhs : (9 / ρ) ^ Γ.card * ((ρ / 9) ^ Γ.card * (P : ℝ)) = (P : ℝ) := by
              rw [← mul_assoc, ← mul_pow]
              have : (9 / ρ) * (ρ / 9) = 1 := by field_simp [hρ0.ne']
              rw [this, one_pow, one_mul]
            linarith only [hmul, hlhs]
          have hlogP := Real.log_le_log hPpos hP_lt.le
          rw [Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by norm_num) (by positivity),
            Real.log_pow, Real.log_pow] at hlogP
          -- Bound each term cleanly!
          have hlog_9ρ : Real.log (9 / ρ) ≤ 4402 * L₀ ^ 2 := by
            have h1 : Real.log (9 / ρ) = Real.log (9 / 2) + Real.log (2 / ρ) := by
              rw [← Real.log_mul (by norm_num) (by positivity)]
              congr 1; ring
            have hlog92 : Real.log (9 / 2 : ℝ) ≤ 2 := by
              have h2 : (9 / 2 : ℝ) ≤ Real.exp 2 := by
                have h1' : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith only [this]
                have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
                have hmul := mul_le_mul h1' h1' (by norm_num) (Real.exp_pos 1).le
                linarith only [hsq, hmul]
              calc Real.log (9 / 2 : ℝ) ≤ Real.log (Real.exp 2) := Real.log_le_log (by norm_num) h2
                _ = 2 := Real.log_exp 2
            have h2ρ : Real.log (2 / ρ) ≤ 4400 * L₀ ^ 2 := by
              have hmul : (j : ℝ) * (400 * L₀) ≤ (11 * L₀) * (400 * L₀) :=
                mul_le_mul_of_nonneg_right hj_le (by positivity)
              have hprod : (11 * L₀) * (400 * L₀) = 4400 * L₀ ^ 2 := by ring
              linarith only [hρlog, hmul, hprod]
            have hL2 : 1 ≤ L₀ ^ 2 := one_le_pow₀ hL₀_gt1.le
            linarith only [h1, hlog92, h2ρ, hL2]
          have hlog_2000 : Real.log 2000 ≤ 20 := by
            have hlg := log_le_of_le_ten_pow (by norm_num : (0 : ℝ) < 2000)
              (by norm_num : (2000 : ℝ) ≤ ((10 : ℝ) ^ 3) ^ 2)
            norm_num at hlg; exact hlg
          have hlog_base : Real.log (3e10 * (Γ.card : ℝ) ^ 2 / α₀) ≤ 151 * L₀ := by
            have h1 : 3e10 * (Γ.card : ℝ) ^ 2 / α₀ ≤ (3e10 * (3e14 : ℝ) ^ 2) * L₀ ^ 10 * (4 / α₀) := by
              have hd2 : (Γ.card : ℝ) ^ 2 ≤ (3e14 * L₀ ^ 5) ^ 2 :=
                pow_le_pow_left₀ (by positivity) hd_le 2
              have h2 : 3e10 * (3e14 * L₀ ^ 5) ^ 2 = (3e10 * (3e14 : ℝ) ^ 2) * L₀ ^ 10 := by ring
              calc 3e10 * (Γ.card : ℝ) ^ 2 / α₀
                  ≤ (3e10 * (3e14 * L₀ ^ 5) ^ 2) * (1 / α₀) := by
                    rw [mul_one_div]; exact div_le_div_of_nonneg_right (by gcongr) hα₀_pos.le
                _ ≤ ((3e10 * (3e14 : ℝ) ^ 2) * L₀ ^ 10) * (4 / α₀) := by
                    rw [h2]
                    exact mul_le_mul_of_nonneg_left
                      (div_le_div_of_nonneg_right (by norm_num) hα₀_pos.le) (by positivity)
            have hlg := Real.log_le_log (by positivity) h1
            have hc_pos : (0 : ℝ) < 3e10 * (3e14 : ℝ) ^ 2 := by positivity
            rw [Real.log_mul (by positivity) (by positivity),
              Real.log_mul hc_pos.ne' (pow_pos hL₀_pos 10).ne', Real.log_pow] at hlg
            have hlog_c : Real.log (3e10 * (3e14 : ℝ) ^ 2) ≤ 140 := by
              have h3e10 : (3e10 : ℝ) = 3 * (10 : ℝ) ^ 10 := by norm_num
              have h3e14 : (3e14 : ℝ) = 3 * (10 : ℝ) ^ 14 := by norm_num
              have hle : (3e10 : ℝ) * (3e14 : ℝ) ^ 2 ≤ ((10 : ℝ) ^ 3) ^ 14 := by
                rw [h3e10, h3e14]
                have heq1 : 3 * (10 : ℝ) ^ 10 * (3 * (10 : ℝ) ^ 14) ^ 2 = 27 * (10 : ℝ) ^ 38 := by ring
                have heq2 : ((10 : ℝ) ^ 3) ^ 14 = 10000 * (10 : ℝ) ^ 38 := by ring
                rw [heq1, heq2]
                exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
              exact (log_le_of_le_ten_pow hc_pos hle).trans (by norm_num)
            have hlog_L₀ : Real.log L₀ ≤ L₀ := (Real.log_le_sub_one_of_pos hL₀_pos).trans (by linarith only [])
            have h10 : ((10 : ℕ) : ℝ) * Real.log L₀ ≤ 10 * L₀ := by
              push_cast; linarith only [hlog_L₀]
            have hL_eq : Real.log (4 / α₀) = L₀ := rfl
            have hcomb2 : Real.log (3e10 * (Γ.card : ℝ) ^ 2 / α₀) ≤ 140 + 10 * L₀ + L₀ := by
              rw [hL_eq] at hlg
              exact hlg.trans (add_le_add (add_le_add hlog_c h10) le_rfl)
            linarith only [hcomb2, hL₀_gt1]
          have hd1_le : ((Γ.card + 1 : ℕ) : ℝ) ≤ 6e14 * L₀ ^ 5 := by
            push_cast; linarith only [hd_le, hL5_ge1]
          have hterm1 : (Γ.card : ℝ) * Real.log (9 / ρ) ≤ (3e14 * L₀ ^ 5) * (4402 * L₀ ^ 2) :=
            mul_le_mul hd_le hlog_9ρ (Real.log_nonneg (by rw [one_le_div hρ0]; linarith only [hρ2])) (by positivity)
          have hbase_ge1 : (1 : ℝ) ≤ 3e10 * (Γ.card : ℝ) ^ 2 / α₀ := by
            rw [one_le_div hα₀_pos]
            have hd2 : (1 : ℝ) ≤ (Γ.card : ℝ) ^ 2 := one_le_pow₀ hd_ge1
            linarith only [hd2, hα₀_le1]
          have hterm2 : ((Γ.card + 1 : ℕ) : ℝ) * Real.log (3e10 * (Γ.card : ℝ) ^ 2 / α₀) ≤
              (6e14 * L₀ ^ 5) * (151 * L₀) :=
            mul_le_mul hd1_le hlog_base (Real.log_nonneg hbase_ge1) (by positivity)
          have hL6_le7 : L₀ ^ 6 ≤ L₀ ^ 7 := pow_le_pow_right₀ hL₀_gt1.le (by norm_num)
          have hL7_ge1 : 1 ≤ L₀ ^ 7 := one_le_pow₀ hL₀_gt1.le
          have hprod1 : (3e14 * L₀ ^ 5) * (4402 * L₀ ^ 2) = 1.3206e18 * L₀ ^ 7 := by ring
          have hprod2 : (6e14 * L₀ ^ 5) * (151 * L₀) = 9.06e16 * L₀ ^ 6 := by ring
          linarith only [hlogP, hterm1, hterm2, hlog_2000, hL6_le7, hL7_ge1, hprod1, hprod2]
      · exact Or.inr hdone
  -- Evaluate `hiter` at `J = Nat.ceil (11 * L₀) + 1`, where Case 1 is impossible!
  let J : ℕ := Nat.ceil (11 * L₀) + 1
  have hlogP_le : Real.log (P : ℝ) ≤ 2e18 * L₀ ^ 7 := by
    rcases hiter J with ⟨Γ, ρ, AJ, _, _, hρ0, _, _, _, hAJB, _, _, hdens⟩ | hdone
    · exfalso
      have hAJ_le1 : (AJ.card : ℝ) / ((bohr Γ ρ).card : ℝ) ≤ 1 := by
        rw [div_le_one (Nat.cast_pos.2 (bohr_card_pos Γ hρ0.le))]
        exact Nat.cast_le.2 (Finset.card_le_card hAJB)
      have hJ_gt : 11 * L₀ < (J : ℝ) := by
        have h1 := Nat.le_ceil (11 * L₀)
        have h2 : (J : ℝ) = (Nat.ceil (11 * L₀) : ℝ) + 1 := by dsimp only [J]; push_cast; rfl
        linarith only [h1, h2]
      have hexp_gt : 4 / α₀ < (11 / 10 : ℝ) ^ J := by
        have h11 := eleven_mul_log_eleven_tenths_ge_one
        have hlog11 : 0 < Real.log (11 / 10 : ℝ) := Real.log_pos (by norm_num)
        have hmul := mul_lt_mul_of_pos_right hJ_gt hlog11
        have h11L : L₀ ≤ 11 * L₀ * Real.log (11 / 10 : ℝ) := by
          have := mul_le_mul_of_nonneg_left h11 hL₀_pos.le
          linarith only [this]
        have hL_lt : L₀ < (J : ℝ) * Real.log (11 / 10 : ℝ) := lt_of_le_of_lt h11L hmul
        have h2 := Real.exp_lt_exp.2 hL_lt
        rw [Real.exp_log (by positivity), Real.exp_nat_mul, Real.exp_log (by norm_num)] at h2
        exact h2
      have h4_lt : (4 : ℝ) < (11 / 10 : ℝ) ^ J * α₀ := by
        have hmul := mul_lt_mul_of_pos_right hexp_gt hα₀_pos
        rwa [div_mul_cancel₀ _ hα₀_pos.ne'] at hmul
      linarith only [h4_lt, hdens, hAJ_le1]
    · exact hdone
  -- Rearrange `log P ≤ 2e18 * L₀^7` into `|A| ≤ 4 * P * exp(-c * (log P)^(1/7))`.
  set c : ℝ := (2e18 : ℝ) ^ (-(1 / 7 : ℝ))
  have hlogP_pos : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < P by omega))
  have hc_bound : c * (Real.log (P : ℝ)) ^ (1 / 7 : ℝ) ≤ L₀ := by
    have hdiv : Real.log (P : ℝ) / 2e18 ≤ L₀ ^ 7 := by
      rw [div_le_iff₀ (by norm_num)]; linarith only [hlogP_le]
    have hrpow := Real.rpow_le_rpow (by positivity) hdiv (show (0 : ℝ) ≤ 1 / 7 by norm_num)
    have hrhs : (L₀ ^ 7) ^ (1 / 7 : ℝ) = L₀ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL₀_pos.le]; norm_num
    have hlhs : (Real.log (P : ℝ) / 2e18) ^ (1 / 7 : ℝ) = c * (Real.log (P : ℝ)) ^ (1 / 7 : ℝ) := by
      rw [div_eq_mul_inv, Real.mul_rpow hlogP_pos.le (by positivity), mul_comm]
      congr 1
      dsimp only [c]
      rw [Real.rpow_neg (by norm_num), Real.inv_rpow (by norm_num)]
    linarith only [hrpow, hrhs, hlhs]
  have hexp_le : Real.exp (c * (Real.log (P : ℝ)) ^ (1 / 7 : ℝ)) ≤ 4 / α₀ := by
    calc Real.exp (c * (Real.log (P : ℝ)) ^ (1 / 7 : ℝ))
        ≤ Real.exp L₀ := Real.exp_le_exp.2 hc_bound
      _ = 4 / α₀ := Real.exp_log (by positivity)
  have hα_le : α₀ ≤ 4 * Real.exp (-c * (Real.log (P : ℝ)) ^ (1 / 7 : ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_left hexp_le hα₀_pos.le
    rw [mul_div_cancel₀ _ hα₀_pos.ne'] at h1
    have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-c * (Real.log (P : ℝ)) ^ (1 / 7 : ℝ))).le
    rw [mul_assoc, ← Real.exp_add] at h2
    have hzero : c * (Real.log (P : ℝ)) ^ (1 / 7 : ℝ) + -c * (Real.log (P : ℝ)) ^ (1 / 7 : ℝ) = 0 := by ring
    rw [hzero, Real.exp_zero, mul_one] at h2
    exact h2
  have hmul := mul_le_mul_of_nonneg_left hα_le hPpos.le
  dsimp only [α₀] at hmul
  rw [mul_div_cancel₀ _ hPpos.ne'] at hmul
  linarith only [hmul]

/-- Embedding `[1, N]` into `ZMod P` via Bertrand's postulate gives the bound on `Green16.f N`. -/
lemma green_16_f_le_bound {N : ℕ} (hN : 2 ≤ N) :
    (Green16.f N : ℝ) ≤
      32 * (N : ℝ) *
        Real.exp (-((2e18 : ℝ) ^ (-(1 / 7 : ℝ))) * (Real.log (N : ℝ)) ^ (1 / 7 : ℝ)) := by
  set c : ℝ := (2e18 : ℝ) ^ (-(1 / 7 : ℝ))
  have hc_pos : 0 < c := by dsimp only [c]; positivity
  -- Bertrand's postulate: prime `P` with `4 * N < P ≤ 8 * N`.
  obtain ⟨P, hPprime, hP_gt, hP_le⟩ := Nat.exists_prime_lt_and_le_two_mul (4 * N) (by omega)
  have : Fact P.Prime := ⟨hPprime⟩
  have hP5 : 5 ≤ P := by omega
  have hA_bound : ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → Green16.SolutionFree A →
      (A.card : ℝ) ≤ 32 * (N : ℝ) * Real.exp (-c * (Real.log (N : ℝ)) ^ (1 / 7 : ℝ)) := by
    intro A hAN hSol
    let AG : Finset (ZMod P) := A.image (Nat.cast : ℕ → ZMod P)
    have hinj : Set.InjOn (Nat.cast : ℕ → ZMod P) (A : Set ℕ) := by
      intro a ha b hb hab
      have haN : a < P := lt_of_le_of_lt (Finset.mem_Icc.1 (hAN ha)).2 (by omega)
      have hbN : b < P := lt_of_le_of_lt (Finset.mem_Icc.1 (hAN hb)).2 (by omega)
      have hmod := (ZMod.natCast_eq_natCast_iff' a b P).1 hab
      rwa [Nat.mod_eq_of_lt haN, Nat.mod_eq_of_lt hbN] at hmod
    have hcard_eq : AG.card = A.card := Finset.card_image_of_injOn hinj
    have hSolG : SolFreeMod AG := by
      intro x hx y hy z hz w hw hnd heq
      rcases Finset.mem_image.1 hx with ⟨x', hx', rfl⟩
      rcases Finset.mem_image.1 hy with ⟨y', hy', rfl⟩
      rcases Finset.mem_image.1 hz with ⟨z', hz', rfl⟩
      rcases Finset.mem_image.1 hw with ⟨w', hw', rfl⟩
      have hnd' : [x', y', z', w'].Nodup := by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
          not_false_eq_true, List.nodup_nil, and_true] at hnd ⊢
        rcases hnd with ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6⟩
        exact ⟨⟨fun h => h1 (by rw [h]), fun h => h2 (by rw [h]), fun h => h3 (by rw [h])⟩,
          ⟨fun h => h4 (by rw [h]), fun h => h5 (by rw [h])⟩, fun h => h6 (by rw [h])⟩
      have heq_cast : ((x' + 3 * y' : ℕ) : ZMod P) = ((2 * z' + 2 * w' : ℕ) : ZMod P) := by
        push_cast; exact heq
      have hmod := (ZMod.natCast_eq_natCast_iff' (x' + 3 * y') (2 * z' + 2 * w') P).1 heq_cast
      have hxN := (Finset.mem_Icc.1 (hAN hx')).2
      have hyN := (Finset.mem_Icc.1 (hAN hy')).2
      have hzN := (Finset.mem_Icc.1 (hAN hz')).2
      have hwN := (Finset.mem_Icc.1 (hAN hw')).2
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
      exact hSol x' hx' y' hy' z' hz' w' hw' hnd' hmod
    have hbd := zmod_solfree_upper_bound hP5 hSolG
    rw [hcard_eq] at hbd
    have hP_leR : (P : ℝ) ≤ 8 * (N : ℝ) := by exact_mod_cast (show P ≤ 8 * N by omega)
    have hN_le_P : (N : ℝ) ≤ (P : ℝ) := by exact_mod_cast (show N ≤ P by omega)
    have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.2 (by omega)
    have hlog_le : Real.log (N : ℝ) ≤ Real.log (P : ℝ) := Real.log_le_log hN_pos hN_le_P
    have hlogN_nn : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    have hrpow_le : (Real.log (N : ℝ)) ^ (1 / 7 : ℝ) ≤ (Real.log (P : ℝ)) ^ (1 / 7 : ℝ) :=
      Real.rpow_le_rpow hlogN_nn hlog_le (by norm_num)
    have hexp_le : Real.exp (-c * (Real.log (P : ℝ)) ^ (1 / 7 : ℝ)) ≤
        Real.exp (-c * (Real.log (N : ℝ)) ^ (1 / 7 : ℝ)) := by
      apply Real.exp_le_exp.2
      have hmul := mul_le_mul_of_nonneg_left hrpow_le hc_pos.le
      linarith only [hmul]
    calc (A.card : ℝ)
        ≤ 4 * (P : ℝ) * Real.exp (-c * (Real.log (P : ℝ)) ^ (1 / 7 : ℝ)) := hbd
      _ ≤ 4 * (8 * (N : ℝ)) * Real.exp (-c * (Real.log (N : ℝ)) ^ (1 / 7 : ℝ)) := by gcongr
      _ = 32 * (N : ℝ) * Real.exp (-c * (Real.log (N : ℝ)) ^ (1 / 7 : ℝ)) := by ring
  -- Bound `Green16.f N = sSup {k | ∃ A ⊆ Icc 1 N, SolutionFree A ∧ A.card = k}`.
  set S : Set ℕ := {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ Green16.SolutionFree A ∧ A.card = k}
  have hSne : S.Nonempty := ⟨0, ∅, Finset.empty_subset _, fun _ hx => absurd hx (Finset.notMem_empty _), rfl⟩
  have hSbdd : BddAbove S := ⟨N, fun k hk => by
    rcases hk with ⟨A, hAN, _, rfl⟩
    exact (Finset.card_le_card hAN).trans (by simp)⟩
  have hmem : Green16.f N ∈ S := Nat.sSup_mem hSne hSbdd
  rcases hmem with ⟨A, hAN, hSol, hcard⟩
  rw [← hcard]
  exact hA_bound A hAN hSol

end IterationAndMain

end Green16TryB

theorem OMA.solution : type_of% @Green16.green_16_upper_bound := by
  refine ⟨(2e18 : ℝ) ^ (-(1 / 7 : ℝ)), by positivity, ?_⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨32, Filter.eventually_atTop.2 ⟨2, fun N hN => ?_⟩⟩
  have hbd := Green16TryB.green_16_f_le_bound hN
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)]
  linarith

